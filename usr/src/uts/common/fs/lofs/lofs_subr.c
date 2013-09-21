/*
 * CDDL HEADER START
 *
 * The contents of this file are subject to the terms of the
 * Common Development and Distribution License (the "License").
 * You may not use this file except in compliance with the License.
 *
 * You can obtain a copy of the license at usr/src/OPENSOLARIS.LICENSE
 * or http://www.opensolaris.org/os/licensing.
 * See the License for the specific language governing permissions
 * and limitations under the License.
 *
 * When distributing Covered Code, include this CDDL HEADER in each
 * file and include the License file at usr/src/OPENSOLARIS.LICENSE.
 * If applicable, add the following below this CDDL HEADER, with the
 * fields enclosed by brackets "[]" replaced with your own identifying
 * information: Portions Copyright [yyyy] [name of copyright owner]
 *
 * CDDL HEADER END
 */
/*
 * Copyright 2008 Sun Microsystems, Inc.  All rights reserved.
 * Use is subject to license terms.
 */

#pragma ident	"%Z%%M%	%I%	%E% SMI"

/*
 * The idea behind composition-based stacked filesystems is to add a
 * vnode to the stack of vnodes for each mount. These vnodes have their
 * own set of mount options and filesystem-specific functions, so they
 * can modify data or operations before they are passed along. Such a
 * filesystem must maintain a mapping from the underlying vnodes to its
 * interposing vnodes.
 *
 * In lofs, this mapping is implemented by a hashtable. Each bucket
 * contains a count of the number of nodes currently contained, the
 * chain of vnodes, and a lock to protect the list of vnodes. The
 * hashtable dynamically grows if the number of vnodes in the table as a
 * whole exceeds the size of the table left-shifted by
 * lo_resize_threshold. In order to minimize lock contention, there is
 * no global lock protecting the hashtable, hence obtaining the
 * per-bucket locks consists of a dance to make sure we've actually
 * locked the correct bucket. Acquiring a bucket lock doesn't involve
 * locking the hashtable itself, so we refrain from freeing old
 * hashtables, and store them in a linked list of retired hashtables;
 * the list is freed when the filesystem is unmounted.
 */

#include <sys/param.h>
#include <sys/kmem.h>
#include <sys/vfs.h>
#include <sys/vnode.h>
#include <sys/cmn_err.h>
#include <sys/systm.h>
#include <sys/t_lock.h>
#include <sys/debug.h>
#include <sys/atomic.h>

#include <sys/fs/lofs_node.h>
#include <sys/fs/lofs_info.h>
/*
 * Due to the hashing algorithm, the size of the hash table needs to be a
 * power of 2.
 */
#define	LOFS_DEFAULT_HTSIZE	(1 << 6)

#define	ltablehash(uvp, lvp, tblsz)	(((((intptr_t)(uvp))>>10)|(((intptr_t)(lvp))>>10)) & ((tblsz)-1))

/*
 * The following macros can only be safely used when the desired bucket
 * is already locked.
 */
/*
 * The lock in the hashtable associated with the given vnode.
 */
#define	TABLE_LOCK(uvp, lvp, li)      \
	(&(li)->li_hashtable[ltablehash((uvp), (lvp), (li)->li_htsize)].lh_lock)

/*
 * The bucket in the hashtable that the given vnode hashes to.
 */
#define	TABLE_BUCKET(uvp, lvp, li)    \
	((li)->li_hashtable[ltablehash((uvp), (lvp), (li)->li_htsize)].lh_chain)

/*
 * Number of elements currently in the bucket that the vnode hashes to.
 */
#define	TABLE_COUNT(uvp, lvp, li)	\
	((li)->li_hashtable[ltablehash((uvp), (lvp), (li)->li_htsize)].lh_count)

/*
 * Grab/Drop the lock for the bucket this vnode hashes to.
 */
#define	TABLE_LOCK_ENTER(uvp, lvp, li)	table_lock_enter(uvp, lvp, li)
#define	TABLE_LOCK_EXIT(uvp, lvp, li)		\
	mutex_exit(&(li)->li_hashtable[ltablehash((uvp), (lvp),	\
	    (li)->li_htsize)].lh_lock)

static lnode_t *lfind(struct vnode *, struct vnode *, struct loinfo *);
static void lsave(lnode_t *, struct loinfo *);
static struct vfs *makelfsnode(struct vfs *, struct loinfo *);
static struct lfsnode *lfsfind(struct vfs *, struct loinfo *);

uint_t lo_resize_threshold = 1;
uint_t lo_resize_factor = 2;

static kmem_cache_t *lnode_cache;
static kmem_cache_t *lnode_status_cache;

/*
 * Since the hashtable itself isn't protected by a lock, obtaining a
 * per-bucket lock proceeds as follows:
 *
 * (a) li->li_htlock protects li->li_hashtable, li->li_htsize, and
 * li->li_retired.
 *
 * (b) Per-bucket locks (lh_lock) protect the contents of the bucket.
 *
 * (c) Locking order for resizing the hashtable is li_htlock then
 * lh_lock.
 *
 * To grab the bucket lock we:
 *
 * (1) Stash away the htsize and the pointer to the hashtable to make
 * sure neither change while we're using them.
 *
 * (2) lgrow() updates the pointer to the hashtable before it updates
 * the size: the worst case scenario is that we have the wrong size (but
 * the correct table), so we hash to the wrong bucket, grab the wrong
 * lock, and then realize that things have changed, rewind and start
 * again. If both the size and the table changed since we loaded them,
 * we'll realize that too and restart.
 *
 * (3) The protocol for growing the hashtable involves holding *all* the
 * locks in the table, hence the unlocking code (TABLE_LOCK_EXIT())
 * doesn't need to do any dances, since neither the table nor the size
 * can change while any bucket lock is held.
 *
 * (4) If the hashtable is growing (by thread t1) while another thread
 * (t2) is trying to grab a bucket lock, t2 might have a stale reference
 * to li->li_htsize:
 *
 * - t1 grabs all locks in lgrow()
 * 	- t2 loads li->li_htsize and li->li_hashtable
 * - t1 changes li->hashtable
 * 	- t2 loads from an offset in the "stale" hashtable and tries to grab
 * 	the relevant mutex.
 *
 * If t1 had free'd the stale hashtable, t2 would be in trouble. Hence,
 * stale hashtables are not freed but stored in a list of "retired"
 * hashtables, which is emptied when the filesystem is unmounted.
 */
static void
table_lock_enter(vnode_t *uvp, vnode_t *lvp, struct loinfo *li)
{
	struct lobucket *chain;
	uint_t htsize;
	uint_t hash;

	for (;;) {
		htsize = li->li_htsize;
		membar_consumer();
		chain = (struct lobucket *)li->li_hashtable;
		hash = ltablehash(uvp, lvp, htsize);
		mutex_enter(&chain[hash].lh_lock);
		if (li->li_hashtable == chain && li->li_htsize == htsize)
			break;
		mutex_exit(&chain[hash].lh_lock);
	}
}

void
lofs_subrinit(void)
{
	/*
	 * Initialize the cache.
	 */
	lnode_cache = kmem_cache_create("lnode_cache", sizeof (lnode_t),
	    0, NULL, NULL, NULL, NULL, NULL, 0);
	lnode_status_cache = kmem_cache_create("lnode_status_cache", sizeof (lnode_status_t),
	    0, NULL, NULL, NULL, NULL, NULL, 0);
}

void
lofs_subrfini(void)
{
	kmem_cache_destroy(lnode_cache);
	kmem_cache_destroy(lnode_status_cache);
}

/*
 * Initialize a (struct loinfo), and initialize the hashtable to have
 * htsize buckets.
 */
void
lsetup(struct loinfo *li, uint_t htsize)
{
	li->li_refct = 0;
	li->li_lfs = NULL;
	if (htsize == 0)
		htsize = LOFS_DEFAULT_HTSIZE;
	li->li_htsize = htsize;
	li->li_hashtable = kmem_zalloc(htsize * sizeof (*li->li_hashtable),
	    KM_SLEEP);
	mutex_init(&li->li_lfslock, NULL, MUTEX_DEFAULT, NULL);
	mutex_init(&li->li_htlock, NULL, MUTEX_DEFAULT, NULL);
	li->li_retired = NULL;
}

/*
 * Destroy a (struct loinfo)
 */
void
ldestroy(struct loinfo *li)
{
	uint_t i, htsize;
	struct lobucket *table;
	struct lo_retired_ht *lrhp, *trhp;

	mutex_destroy(&li->li_htlock);
	mutex_destroy(&li->li_lfslock);
	htsize = li->li_htsize;
	table = li->li_hashtable;
	for (i = 0; i < htsize; i++)
		mutex_destroy(&table[i].lh_lock);
	kmem_free(table, htsize * sizeof (*li->li_hashtable));

	/*
	 * Free the retired hashtables.
	 */
	lrhp = li->li_retired;
	while (lrhp != NULL) {
		trhp = lrhp;
		lrhp = lrhp->lrh_next;
		kmem_free(trhp->lrh_table,
		    trhp->lrh_size * sizeof (*li->li_hashtable));
		kmem_free(trhp, sizeof (*trhp));
	}
	li->li_retired = NULL;
}

/*
 * Return a looped back vnode for the given vnode.
 * If no lnode exists for this vnode create one and put it
 * in a table hashed by vnode.  If the lnode for
 * this vnode is already in the table return it (ref count is
 * incremented by lfind).  The lnode will be flushed from the
 * table when lo_inactive calls freelonode.  The creation of
 * a new lnode can be forced via the LOF_FORCE flag even if
 * the vnode exists in the table.  This is used in the creation
 * of a terminating lnode when looping is detected.  A unique
 * lnode is required for the correct evaluation of the current
 * working directory.
 * NOTE: vp is assumed to be a held vnode.
 */
struct vnode *
makelonode(struct vnode *uvp, struct vnode *lvp, struct loinfo *li, int flag)
{
	lnode_t *lp, *tlp;
	struct vfs *vfsp;
	vnode_t *nvp;

	lp = NULL;
	TABLE_LOCK_ENTER(uvp, lvp, li);
	if (flag != LOF_FORCE)
		lp = lfind(uvp, lvp, li);
	if ((flag == LOF_FORCE) || (lp == NULL)) {
		/*
		 * Optimistically assume that we won't need to sleep.
		 */
		lp = kmem_cache_alloc(lnode_cache, KM_NOSLEEP);
		nvp = vn_alloc(KM_NOSLEEP);
		if (lp == NULL || nvp == NULL) {
			TABLE_LOCK_EXIT(uvp, lvp, li);
			/* The lnode allocation may have succeeded, save it */
			tlp = lp;
			if (tlp == NULL) {
				tlp = kmem_cache_alloc(lnode_cache, KM_SLEEP);
			}
			if (nvp == NULL) {
				nvp = vn_alloc(KM_SLEEP);
			}
			lp = NULL;
			TABLE_LOCK_ENTER(uvp, lvp, li);
			if (flag != LOF_FORCE)
				lp = lfind(uvp, lvp, li);
			if (lp != NULL) {
				kmem_cache_free(lnode_cache, tlp);
				vn_free(nvp);
				if (uvp != NULLVP)
					VN_RELE(uvp);
				if (lvp != NULLVP)
					VN_RELE(lvp);
				goto found_lnode;
			}
			lp = tlp;
		}
		atomic_add_32(&li->li_refct, 1);
		if (uvp != NULLVP) {
			vfsp = makelfsnode(uvp->v_vfsp, li);
			VN_SET_VFS_TYPE_DEV(nvp, vfsp, uvp->v_type, uvp->v_rdev);
			nvp->v_flag |= (uvp->v_flag & (VNOMOUNT|VNOMAP|VDIROPEN));
		} else {
			vfsp = makelfsnode(lvp->v_vfsp, li);
			VN_SET_VFS_TYPE_DEV(nvp, vfsp, lvp->v_type, lvp->v_rdev);
			nvp->v_flag |= (lvp->v_flag & (VNOMOUNT|VNOMAP|VDIROPEN));
		}
		vn_setops(nvp, lo_vnodeops);
		nvp->v_data = (caddr_t)lp;
		lp->lo_vnode = nvp;
		lp->lo_uvp = uvp;
		lp->lo_lvp = lvp;
		lp->lo_looping = 0;
		lp->lo_status = NULL;
		lsave(lp, li);
		if (uvp != NULLVP)
			vn_exists(uvp);
		if (lvp != NULLVP)
			vn_exists(lvp);
	} else {
		if (uvp != NULLVP)
			VN_RELE(uvp);
		if (lvp != NULLVP)
			VN_RELE(lvp);
	}

found_lnode:
	TABLE_LOCK_EXIT(uvp, lvp, li);
	return (ltov(lp));
}

/* 
 * Add uvp vnode in an lnode and refresh the hash for the cache.
 */
void
updatelonode(struct vnode *vp, struct vnode *uvp, struct loinfo *li) {
	lnode_t *lp, *lt, *ltprev = NULL;

	lp = vtol(vp);

	TABLE_LOCK_ENTER(lp->lo_uvp, lp->lo_lvp, li);

	for (lt = TABLE_BUCKET(lp->lo_uvp, lp->lo_lvp, li); lt != NULL;
	    ltprev = lt, lt = lt->lo_next) {
		if (lt == lp) {
			if (ltprev == NULL) {
				TABLE_BUCKET(lt->lo_uvp, lt->lo_lvp, li) = lt->lo_next;
			} else {
				ltprev->lo_next = lt->lo_next;
			}
			TABLE_COUNT(lt->lo_uvp, lt->lo_lvp, li)--;
			TABLE_LOCK_EXIT(lt->lo_uvp, lt->lo_lvp, li);
			lp->lo_uvp = uvp;
			lsave(lp, li);
			return;
		}
	}
	panic("updatelonode");
	/*NOTREACHED*/
}

/*
 * Get/Make vfs structure for given real vfs
 */
static struct vfs *
makelfsnode(struct vfs *vfsp, struct loinfo *li)
{
	struct lfsnode *lfs;
	struct lfsnode *tlfs;

	/*
	 * Don't grab any locks for the fast (common) case.
	 */
	if (vfsp == li->li_realvfs)
		return (li->li_mountvfs);
	ASSERT(li->li_refct > 0);
	mutex_enter(&li->li_lfslock);
	if ((lfs = lfsfind(vfsp, li)) == NULL) {
		mutex_exit(&li->li_lfslock);
		lfs = kmem_zalloc(sizeof (*lfs), KM_SLEEP);
		mutex_enter(&li->li_lfslock);
		if ((tlfs = lfsfind(vfsp, li)) != NULL) {
			kmem_free(lfs, sizeof (*lfs));
			lfs = tlfs;
			goto found_lfs;
		}
		lfs->lfs_realvfs = vfsp;

		/*
		 * Even though the lfsnode is strictly speaking a private
		 * implementation detail of lofs, it should behave as a regular
		 * vfs_t for the benefit of the rest of the kernel.
		 */
		VFS_INIT(&lfs->lfs_vfs, lo_vfsops, (caddr_t)li);
		lfs->lfs_vfs.vfs_fstype = li->li_mountvfs->vfs_fstype;
		lfs->lfs_vfs.vfs_flag =
		    ((vfsp->vfs_flag | li->li_mflag) & ~li->li_dflag) &
		    INHERIT_VFS_FLAG;
		lfs->lfs_vfs.vfs_bsize = vfsp->vfs_bsize;
		lfs->lfs_vfs.vfs_dev = vfsp->vfs_dev;
		lfs->lfs_vfs.vfs_fsid = vfsp->vfs_fsid;

		if (vfsp->vfs_mntpt != NULL) {
			lfs->lfs_vfs.vfs_mntpt = vfs_getmntpoint(vfsp);
			/* Leave a reference to the mountpoint */
		}

		(void) VFS_ROOT(vfsp, &lfs->lfs_realrootvp);

		/*
		 * We use 1 instead of 0 as the value to associate with
		 * an idle lfs_vfs.  This is to prevent VFS_RELE()
		 * trying to kmem_free() our lfs_t (which is the wrong
		 * size).
		 */
		VFS_HOLD(&lfs->lfs_vfs);
		lfs->lfs_next = li->li_lfs;
		li->li_lfs = lfs;
		vfs_propagate_features(vfsp, &lfs->lfs_vfs);
	}

found_lfs:
	VFS_HOLD(&lfs->lfs_vfs);
	mutex_exit(&li->li_lfslock);
	return (&lfs->lfs_vfs);
}

/*
 * Free lfs node since no longer in use
 */
static void
freelfsnode(struct lfsnode *lfs, struct loinfo *li)
{
	struct lfsnode *prev = NULL;
	struct lfsnode *this;

	ASSERT(MUTEX_HELD(&li->li_lfslock));
	ASSERT(li->li_refct > 0);
	for (this = li->li_lfs; this != NULL; this = this->lfs_next) {
		if (this == lfs) {
			ASSERT(lfs->lfs_vfs.vfs_count == 1);
			if (prev == NULL)
				li->li_lfs = lfs->lfs_next;
			else
				prev->lfs_next = lfs->lfs_next;
			if (lfs->lfs_realrootvp != NULL) {
				VN_RELE(lfs->lfs_realrootvp);
			}
			if (lfs->lfs_vfs.vfs_mntpt != NULL)
				refstr_rele(lfs->lfs_vfs.vfs_mntpt);
			if (lfs->lfs_vfs.vfs_implp != NULL) {
				ASSERT(lfs->lfs_vfs.vfs_femhead == NULL);
				ASSERT(lfs->lfs_vfs.vfs_vskap == NULL);
				ASSERT(lfs->lfs_vfs.vfs_fstypevsp == NULL);
				kmem_free(lfs->lfs_vfs.vfs_implp,
				    sizeof (vfs_impl_t));
			}
			sema_destroy(&lfs->lfs_vfs.vfs_reflock);
			kmem_free(lfs, sizeof (struct lfsnode));
			return;
		}
		prev = this;
	}
	panic("freelfsnode");
	/*NOTREACHED*/
}

/*
 * Find lfs given real vfs and mount instance(li)
 */
static struct lfsnode *
lfsfind(struct vfs *vfsp, struct loinfo *li)
{
	struct lfsnode *lfs;

	ASSERT(MUTEX_HELD(&li->li_lfslock));

	/*
	 * We need to handle the case where a UFS filesystem was forced
	 * unmounted and then a subsequent mount got the same vfs
	 * structure.  If the new mount lies in the lofs hierarchy, then
	 * this will confuse lofs, because the original vfsp (of the
	 * forced unmounted filesystem) is still around. We check for
	 * this condition here.
	 *
	 * If we find a cache vfsp hit, then we check to see if the
	 * cached filesystem was forced unmounted. Skip all such
	 * entries. This should be safe to do since no
	 * makelonode()->makelfsnode()->lfsfind() calls should be
	 * generated for such force-unmounted filesystems (because (ufs)
	 * lookup would've returned an error).
	 */
	for (lfs = li->li_lfs; lfs != NULL; lfs = lfs->lfs_next) {
		if (lfs->lfs_realvfs == vfsp) {
			struct vnode *realvp;

			realvp = lfs->lfs_realrootvp;
			if (realvp == NULL)
				continue;
			if (realvp->v_vfsp == NULL || realvp->v_type == VBAD)
				continue;
			return (lfs);
		}
	}
	return (NULL);
}

/*
 * Find real vfs given loopback vfs
 */
struct vfs *
lo_realvfs(struct vfs *vfsp, struct vnode **realrootvpp)
{
	struct loinfo *li = vtoli(vfsp);
	struct lfsnode *lfs;

	ASSERT(li->li_refct > 0);
	if (vfsp == li->li_mountvfs) {
		if (realrootvpp != NULL)
			*realrootvpp = vtol(li->li_rootvp)->lo_uvp;
		return (li->li_realvfs);
	}
	mutex_enter(&li->li_lfslock);
	for (lfs = li->li_lfs; lfs != NULL; lfs = lfs->lfs_next) {
		if (vfsp == &lfs->lfs_vfs) {
			if (realrootvpp != NULL)
				*realrootvpp = lfs->lfs_realrootvp;
			mutex_exit(&li->li_lfslock);
			return (lfs->lfs_realvfs);
		}
	}
	panic("lo_realvfs");
	/*NOTREACHED*/
}

/*
 * Lnode lookup stuff.
 * These routines maintain a table of lnodes hashed by vp so
 * that the lnode for a vp can be found if it already exists.
 *
 * NB: A lofs shadow vnode causes exactly one VN_HOLD() on the
 * underlying vnode.
 */

/*
 * Retire old hashtables.
 */
static void
lretire(struct loinfo *li, struct lobucket *table, uint_t size)
{
	struct lo_retired_ht *lrhp;

	lrhp = kmem_alloc(sizeof (*lrhp), KM_SLEEP);
	lrhp->lrh_table = table;
	lrhp->lrh_size = size;

	mutex_enter(&li->li_htlock);
	lrhp->lrh_next = li->li_retired;
	li->li_retired = lrhp;
	mutex_exit(&li->li_htlock);
}

/*
 * Grow the hashtable.
 */
static void
lgrow(struct loinfo *li, uint_t newsize)
{
	uint_t oldsize;
	uint_t i;
	struct lobucket *oldtable, *newtable;

	/*
	 * It's OK to not have enough memory to resize the hashtable.
	 * We'll go down this path the next time we add something to the
	 * table, and retry the allocation then.
	 */
	if ((newtable = kmem_zalloc(newsize * sizeof (*li->li_hashtable),
	    KM_NOSLEEP)) == NULL)
		return;

	mutex_enter(&li->li_htlock);
	if (newsize <= li->li_htsize) {
		mutex_exit(&li->li_htlock);
		kmem_free(newtable, newsize * sizeof (*li->li_hashtable));
		return;
	}
	oldsize = li->li_htsize;
	oldtable = li->li_hashtable;

	/*
	 * Grab all locks so TABLE_LOCK_ENTER() calls block until the
	 * resize is complete.
	 */
	for (i = 0; i < oldsize; i++)
		mutex_enter(&oldtable[i].lh_lock);
	/*
	 * li->li_hashtable gets set before li->li_htsize, so in the
	 * time between the two assignments, callers of
	 * TABLE_LOCK_ENTER() cannot hash to a bucket beyond oldsize,
	 * hence we only need to grab the locks up to oldsize.
	 */
	for (i = 0; i < oldsize; i++)
		mutex_enter(&newtable[i].lh_lock);
	/*
	 * Rehash.
	 */
	for (i = 0; i < oldsize; i++) {
		lnode_t *tlp, *nlp;

		for (tlp = oldtable[i].lh_chain; tlp != NULL; tlp = nlp) {
			uint_t hash = ltablehash(tlp->lo_uvp, tlp->lo_lvp, newsize);

			nlp = tlp->lo_next;
			tlp->lo_next = newtable[hash].lh_chain;
			newtable[hash].lh_chain = tlp;
			newtable[hash].lh_count++;
		}
	}

	/*
	 * As soon as we store the new hashtable, future locking operations
	 * will use it.  Therefore, we must ensure that all the state we've
	 * just established reaches global visibility before the new hashtable
	 * does.
	 */
	membar_producer();
	li->li_hashtable = newtable;

	/*
	 * table_lock_enter() relies on the fact that li->li_hashtable
	 * is set to its new value before li->li_htsize.
	 */
	membar_producer();
	li->li_htsize = newsize;

	/*
	 * The new state is consistent now, so we can drop all the locks.
	 */
	for (i = 0; i < oldsize; i++) {
		mutex_exit(&newtable[i].lh_lock);
		mutex_exit(&oldtable[i].lh_lock);
	}
	mutex_exit(&li->li_htlock);

	lretire(li, oldtable, oldsize);
}

/*
 * Put a lnode in the table
 */
static void
lsave(lnode_t *lp, struct loinfo *li)
{
	ASSERT(lp->lo_uvp && lp->lo_lvp);
	ASSERT(MUTEX_HELD(TABLE_LOCK(lp->lo_uvp, lp->lo_lvp, li)));

#ifdef LODEBUG
	lo_dprint(4, "lsave lp %p hash %d\n",
	    lp, ltablehash(lp->lo_uvp, lp->lo_lvp, li));
#endif

	TABLE_COUNT(lp->lo_uvp, lp->lo_lvp, li)++;
	lp->lo_next = TABLE_BUCKET(lp->lo_uvp, lp->lo_lvp, li);
	TABLE_BUCKET(lp->lo_uvp, lp->lo_lvp, li) = lp;

	if (li->li_refct > (li->li_htsize << lo_resize_threshold)) {
		TABLE_LOCK_EXIT(lp->lo_uvp, lp->lo_lvp, li);
		lgrow(li, li->li_htsize << lo_resize_factor);
		TABLE_LOCK_ENTER(lp->lo_uvp, lp->lo_lvp, li);
	}
}

/*
 * Our version of vfs_rele() that stops at 1 instead of 0, and calls
 * freelfsnode() instead of kmem_free().
 */
static void
lfs_rele(struct lfsnode *lfs, struct loinfo *li)
{
	vfs_t *vfsp = &lfs->lfs_vfs;

	ASSERT(MUTEX_HELD(&li->li_lfslock));
	ASSERT(vfsp->vfs_count > 1);
	if (atomic_add_32_nv(&vfsp->vfs_count, -1) == 1)
		freelfsnode(lfs, li);
}

/*
 * Remove a lnode from the table
 */
void
freelonode(lnode_t *lp)
{
	lnode_t *lt;
	lnode_t *ltprev = NULL;
	struct lfsnode *lfs, *nextlfs;
	struct vfs *vfsp;
	struct vnode *vp = ltov(lp);
	struct vnode *realuvp = realuvp(vp);
	struct vnode *reallvp = reallvp(vp);
	struct loinfo *li = vtoli(vp->v_vfsp);
	struct lnode_status *lsp;
	struct lnode_status *lspprev = NULL;

#ifdef LODEBUG
	lo_dprint(4, "freelonode lp %p hash %d\n",
	    lp, ltablehash(lp->lo_uvp, lp->lo_lvp, li));
#endif
	TABLE_LOCK_ENTER(lp->lo_uvp, lp->lo_lvp, li);

	mutex_enter(&vp->v_lock);
	if (vp->v_count > 1) {
		vp->v_count--;	/* release our hold from vn_rele */
		mutex_exit(&vp->v_lock);
		TABLE_LOCK_EXIT(lp->lo_uvp, lp->lo_lvp, li);
		return;
	}
	mutex_exit(&vp->v_lock);

	for (lt = TABLE_BUCKET(lp->lo_uvp, lp->lo_lvp, li); lt != NULL;
	    ltprev = lt, lt = lt->lo_next) {
		if (lt == lp) {
#ifdef LODEBUG
			lo_dprint(4, "freeing %p, vfsp %p\n",
			    vp, vp->v_vfsp);
#endif
			atomic_add_32(&li->li_refct, -1);
			vfsp = vp->v_vfsp;
			vn_invalid(vp);
			if (vfsp != li->li_mountvfs) {
				mutex_enter(&li->li_lfslock);
				/*
				 * Check for unused lfs
				 */
				lfs = li->li_lfs;
				while (lfs != NULL) {
					nextlfs = lfs->lfs_next;
					if (vfsp == &lfs->lfs_vfs) {
						lfs_rele(lfs, li);
						break;
					}
					if (lfs->lfs_vfs.vfs_count == 1) {
						/*
						 * Lfs is idle
						 */
						freelfsnode(lfs, li);
					}
					lfs = nextlfs;
				}
				mutex_exit(&li->li_lfslock);
			}
			lsp = lt->lo_status;
			while(lsp != NULL) {
				lspprev = lsp;
				lsp = lsp->los_next;
				kmem_cache_free(lnode_status_cache, lspprev);
			}
			if (ltprev == NULL) {
				TABLE_BUCKET(lt->lo_uvp, lt->lo_lvp, li) = lt->lo_next;
			} else {
				ltprev->lo_next = lt->lo_next;
			}
			TABLE_COUNT(lt->lo_uvp, lt->lo_lvp, li)--;
			TABLE_LOCK_EXIT(lt->lo_uvp, lt->lo_lvp, li);
			kmem_cache_free(lnode_cache, lt);
			vn_free(vp);
			if (realuvp != NULLVP)
				VN_RELE(realuvp);
			if (reallvp != NULLVP)
				VN_RELE(reallvp);
			return;
		}
	}
	panic("freelonode");
	/*NOTREACHED*/
}

/*
 * Lookup a lnode by vp
 */
static lnode_t *
lfind(struct vnode *uvp, struct vnode *lvp, struct loinfo *li)
{
	lnode_t *lt;

	ASSERT(MUTEX_HELD(TABLE_LOCK(uvp, lvp, li)));

	lt = TABLE_BUCKET(uvp, lvp, li);
	while (lt != NULL) {
		if (lt->lo_uvp == uvp && lt->lo_lvp == lvp) {
			VN_HOLD(ltov(lt));
			return (lt);
		}
		lt = lt->lo_next;
	}
	return (NULL);
}

/*
 * Get/Make the lnode status.
 */
void
getlonodestatus(struct vnode *vp, struct lnode_status **lspp, struct loinfo *li)
{
	lnode_t *lp;
	lnode_status_t *lsp, *tlsp;
	vnode_t *uvp, *lvp;
	pid_t pid;

	uvp = realuvp(vp);
	lvp = reallvp(vp);
	pid = curproc->p_pidp->pid_id;

	TABLE_LOCK_ENTER(uvp, lvp, li);
	lp = lfind(uvp, lvp, li);

	lsp = tlsp = lp->lo_status;
	while (lsp != NULL) {
		if (lsp->los_pid == pid) {
			*lspp = lsp;
			TABLE_LOCK_EXIT(uvp, lvp, li);
			return;
		}
		lsp = lsp->los_next;
	}

	lsp = kmem_cache_alloc(lnode_status_cache, KM_SLEEP);
	lsp->los_pid = pid;
	lsp->los_next = tlsp;
	lsp->los_upper_opencnt = 0;
	lsp->los_lower_opencnt = 0;
	lsp->los_upper_mapcnt = 0;
	lsp->los_lower_mapcnt = 0;
	*lspp = lsp;

	lp->lo_status = lsp;
	TABLE_LOCK_EXIT(uvp, lvp, li);
}

/*
 * Free the lnode status if you can.
 */
void
tryfreelonodestatus(struct lnode *lp, struct lnode_status *lsptofree)
{
	struct vnode *vp = ltov(lp);
	struct loinfo *li = vtoli(vp->v_vfsp);
	lnode_status_t *lsp, *lspprev = NULL;

	ASSERT(lsptofree != NULL);
	
	if (0 < lsptofree->los_upper_opencnt || 0 < lsptofree->los_lower_opencnt ||
		0 < lsptofree->los_upper_mapcnt || 0 < lsptofree->los_lower_mapcnt)
		return;

	TABLE_LOCK_ENTER(lp->lo_uvp, lp->lo_lvp, li);
	lp = lfind(lp->lo_uvp, lp->lo_lvp, li);

	for (lsp = lp->lo_status; lsp != NULL; lspprev = lsp, lsp = lsp->los_next) {
		if (lsp == lsptofree) {
			if (lspprev == NULL) {
				lp->lo_status = lsp->los_next;
			} else {
				lspprev->los_next = lsp->los_next;
			}
			TABLE_LOCK_EXIT(lp->lo_uvp, lp->lo_lvp, li);
			kmem_cache_free(lnode_status_cache, lsp);
			return;
		}
	}
	panic("tryfreelonodestatus");
	/*NOTREACHED*/
}

/*
 * Create upper node attr.
 */
int
mkuppervattr(vnode_t *lvp, vattr_t *uva, struct loinfo *li, struct cred *cr, caller_context_t *ct)
{
	int error;
	vattr_t lva;

	if ((error = VOP_GETATTR(lvp, &lva, 0, cr, ct)) != 0)
		return (error);

	uva->va_mask = AT_TYPE|AT_MODE;
	uva->va_type = lva.va_type;
	uva->va_atime = lva.va_atime;
	uva->va_mtime = lva.va_mtime;
	uva->va_ctime = lva.va_ctime;

	if (li->li_flag & LO_TRANSPARENT) {
		uva->va_mode = lva.va_mode;
		uva->va_uid = lva.va_uid;
		uva->va_gid = lva.va_gid;
	} else {
		uva->va_mode = PERMMASK & ~PTOU(curproc)->u_cmask;
		uva->va_uid = li->li_uid;
		uva->va_gid = li->li_gid;
	}

	return (error);
}

/*
 * Whiteout the lower vnode of an lo vnode.
 */
int
mkwhiteout(vnode_t *dvp, char *nm, struct cred *cr, caller_context_t *ct)
{
	int error;
	vnode_t *ldvp, *vpp;
	xvattr_t xvattr;
	xoptattr_t *xoap;

	error = ENOENT;
	ldvp = reallvp(dvp);

	if (ldvp != NULLVP) {
		error = VOP_LOOKUP(ldvp, nm, &vpp, NULL, 0, NULL, cr, ct, NULL, NULL);
		if (!error) {
			error = VOP_ACCESS(vpp, VWRITE, 0, cr, ct);
			if (!error) {
				xva_init(&xvattr);
				xoap = xva_getxoptattr(&xvattr);
				ASSERT(xoap);
				XVA_SET_REQ(&xvattr, XAT_WHITEOUT);
				xoap->xoa_whiteout = 1;

				error = VOP_SETATTR(vpp, &xvattr.xva_vattr, 0, cr, ct);
			}
			VN_RELE(vpp);
		}
	}

	return (error);
}

/*
 * Create the upper dir of an lo vnode.
 */
int
mkshadowdir(vnode_t *dvp, char *nm, vnode_t *uvp, vnode_t *lvp, struct cred *cr, caller_context_t *ct) {
	int error;
	vnode_t *udvp;
	vattr_t uva;

	if (vn_is_readonly(dvp))
		return (EROFS);

	error = EROFS;
	udvp = realuvp(dvp);

	if (udvp != NULLVP) {
		if ((error = VOP_ACCESS(udvp, VWRITE, 0, cr, ct)) != 0)
			return (error);

		if ((error = mkuppervattr(lvp, &uva, vtoli(dvp->v_vfsp), cr, ct)))
			return (error);

		if ((error = VOP_MKDIR(udvp, nm, &uva, &uvp, cr, NULL, 0, NULL)) != 0)
			return (error);
	}

    return (error);
}

/*
 * Copy the lower vnode of an lo vnode on the upper.
 */
int
upper_copyfile_core(vnode_t *uvp, vnode_t *lvp, struct cred *cr, caller_context_t *ct)
{
	int error, count;
	uio_t uio;
	iovec_t iovec;
	caddr_t mem;
	offset_t loffset, bufloffset;

	error = 0;

	mem = kmem_zalloc(MAXBSIZE, KM_SLEEP);

	uio.uio_segflg = UIO_SYSSPACE;
	uio.uio_extflg = UIO_COPY_CACHED;
	uio.uio_loffset = 0;

	while (error == 0) {
		loffset = uio.uio_loffset;

		uio.uio_iov = &iovec;
		uio.uio_iovcnt = 1;
		iovec.iov_base = mem;
		iovec.iov_len = MAXBSIZE;
		uio.uio_resid = iovec.iov_len;
		uio.uio_fmode = 0;

		if (error = VOP_READ(lvp, &uio, 0, cr, ct))
			break;
		if ((count = MAXBSIZE - uio.uio_resid) == 0)
			break;

		bufloffset = 0;
		while (bufloffset < count) {

			uio.uio_iov = &iovec;
			uio.uio_iovcnt = 1;
			iovec.iov_base = mem + bufloffset;
			iovec.iov_len = count - bufloffset;
			uio.uio_offset = loffset + bufloffset;
			uio.uio_resid = iovec.iov_len;
			uio.uio_fmode = 1;

			if (error = VOP_WRITE(uvp, &uio, 0, cr, ct))
				break;

			bufloffset += (count - bufloffset) - uio.uio_resid;
		}

		uio.uio_loffset = loffset + bufloffset;
	}

	kmem_free(mem, MAXBSIZE);

	return (error);
}

int
upper_copyfile(vnode_t *vp, struct cred *cr, caller_context_t *ct)
{
	int error;
	vnode_t *dvp, *uvp, *lvp;
	pathname_t pn_vp;
	vattr_t uva;

	lvp = reallvp(vp);

	/* Check access lower vnode */
	if ((error = VOP_ACCESS(lvp, VREAD, 0, cr, ct)) != 0)
		return (error);

	/* Get the dvp vnode */
	if ((error = pn_get(vp->v_path, UIO_SYSSPACE, &pn_vp)) != 0)
		return (error);

	if ((error = lookuppnat(&pn_vp, NULL, 1, &dvp, NULL, (vtoli(vp->v_vfsp))->li_rootvp)) != 0) {
		pn_free(&pn_vp);
		return (error);
	}

	/* Get attributes from lower vnode */
	if ((error = mkuppervattr(lvp, &uva, vtoli(vp->v_vfsp), cr, ct)))
		return (error);

	/* Create the upper vnode */
	if ((error = VOP_CREATE(realuvp(dvp), pn_vp.pn_path, &uva, EXCL, 0, &uvp, cr, 0, ct, NULL)) !=0 )
		goto out;

	/* Update the lo node */
	updatelonode(vp, uvp, vtoli(vp->v_vfsp));

	/* Open the lower vnode in read only mode */
	if ((error = VOP_OPEN(&lvp, FREAD, cr, ct)) != 0)
		goto close_uvp;

	/* Process the copyfile */
	error = upper_copyfile_core(uvp, lvp, cr, ct);

	VOP_CLOSE(lvp, 0, 0, 0, cr, ct);
close_uvp:
	VOP_CLOSE(uvp, 0, 0, 0, cr, ct);
out:
	VN_RELE(dvp);
	pn_free(&pn_vp);
	return (error);
}

#ifdef	LODEBUG
static int lofsdebug;
#endif	/* LODEBUG */

/*
 * Utilities used by both client and server
 * Standard levels:
 * 0) no debugging
 * 1) hard failures
 * 2) soft failures
 * 3) current test software
 * 4) main procedure entry points
 * 5) main procedure exit points
 * 6) utility procedure entry points
 * 7) utility procedure exit points
 * 8) obscure procedure entry points
 * 9) obscure procedure exit points
 * 10) random stuff
 * 11) all <= 1
 * 12) all <= 2
 * 13) all <= 3
 * ...
 */

#ifdef LODEBUG
/*VARARGS2*/
lo_dprint(level, str, a1, a2, a3, a4, a5, a6, a7, a8, a9)
	int level;
	char *str;
	int a1, a2, a3, a4, a5, a6, a7, a8, a9;
{

	if (lofsdebug == level || (lofsdebug > 10 && (lofsdebug - 10) >= level))
		printf(str, a1, a2, a3, a4, a5, a6, a7, a8, a9);
}
#endif
