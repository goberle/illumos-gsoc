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
 * Copyright 2009 Sun Microsystems, Inc.  All rights reserved.
 * Use is subject to license terms.
 */

/*
 * Loop-back file information structure.
 */

#ifndef _SYS_FS_LOFS_NODE_H
#define	_SYS_FS_LOFS_NODE_H

#include <sys/fs/lofs_info.h>

#ifdef	__cplusplus
extern "C" {
#endif

/*
 * The lnode is the "inode" for loop-back files.  It contains
 * all the information necessary to handle loop-back file on the
 * client side.
 */
typedef struct lnode {
	struct lnode	*lo_next;	/* link for hash chain */
	struct vnode	*lo_uvp;		/* pointer to real upper vnode */
    struct vnode    *lo_lvp;    /* pointer to real lower vnode */
	uint_t		lo_looping; 	/* looping flags (see below) */
	struct vnode	*lo_vnode;	/* place holder vnode for file */
    struct lnode_status *lo_status; /* link for status chain */
} lnode_t;

typedef struct lnode_status {
    struct  lnode_status *los_next; /* link for lnode_status chain */
    pid_t   los_pid;                /* current process ID */
    int     los_upper_opencnt;      /* open count of upper */
    int     los_lower_opencnt;      /* open count of lower */
    int     los_upper_mapcnt;       /* map count of upper */
    int     los_lower_mapcnt;       /* map count of lower */
} lnode_status_t;

/*
 * Flags used when looping has been detected.
 */
#define	LO_LOOPING	0x01	/* Looping detected */
#define	LO_AUTOLOOP	0x02	/* Autonode looping detected */

/*
 * Flag passed to makelonode().
 */
#define	LOF_FORCE	0x1	/* Force creation of new lnode */

/*
 * Convert between vnode and lnode
 */
#define	ltov(lp)	(((lp)->lo_vnode))
#define	vtol(vp)	((struct lnode *)((vp)->v_data))
#define	realuvp(vp)	(vtol(vp)->lo_uvp)
#define reallvp(vp) (vtol(vp)->lo_lvp)

#ifdef _KERNEL
extern vnode_t *makelonode(vnode_t *, vnode_t *, struct loinfo *, int);
extern void updatelonode(struct vnode *, struct vnode *, struct loinfo *);
extern void freelonode(lnode_t *);
extern void getlonodestatus(struct vnode *, struct lnode_status **, struct loinfo *);
extern void tryfreelonodestatus(struct lnode *, struct lnode_status *);
extern int mkwhiteout(vnode_t *, char *, struct cred *, caller_context_t *);
extern int mkshadowdir(vnode_t *, char *, vnode_t *, vnode_t *, struct cred *, caller_context_t *);
extern int upper_copyfile_core(vnode_t *, vnode_t *, struct cred *, caller_context_t *);
extern int upper_copyfile(vnode_t *, struct cred *, caller_context_t *);
#endif /* _KERNEL */

#ifdef	__cplusplus
}
#endif

#endif	/* _SYS_FS_LOFS_NODE_H */
