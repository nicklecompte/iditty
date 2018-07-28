/*
 * The SCREEN structure.
 */

struct FILE;

struct TERMINAL;

typedef struct TTY;

typedef unsigned char uchar;

/*
 * Used for robust ANSI parameter forward declarations:
 * int VDECL(sprintf, (char *, const char *, ...));
 *
 * NDECL() is used for functions with zero arguments;
 * FDECL() is used for functions with a fixed number of arguments;
 * VDECL() is used for functions with a variable number of arguments.
 * Separate macros are needed because ANSI will mix old-style declarations
 * with prototypes, except in the case of varargs, and the OVERLAY-specific
 * trampoli.* mechanism conflicts with the ANSI <<f(void)>> syntax.
 */

#define NDECL(f) f(void) /* overridden later if USE_TRAMPOLI set */

#define FDECL(f, p) f p

#if defined(MSDOS) || defined(USE_STDARG)
#define VDECL(f, p) f p
#else
#define VDECL(f, p) f()
#endif

#ifndef genericptr
#define genericptr char *
#endif


#ifndef genericptr_t
typedef genericptr genericptr_t; /* (void *) or (char *) */
#endif

#define INTERJECT_PANIC 0
#define INTERJECTION_TYPES (INTERJECT_PANIC + 1)
extern void FDECL(interject_assistance,
                  (int, int, genericptr_t, genericptr_t));
extern void FDECL(interject, (int));


typedef int NCURSES_SIZE_T;

// struct screen {
// 	int		_ifd;		/* input file descriptor for screen */
// 	int		_ofd;		/* output file descriptor for screen */
// //	FILE		*_ofp;		/* output file ptr for screen	    */
// 	char		*out_buffer;	/* output buffer		    */
// 	size_t		out_limit;	/* output buffer size		    */
// 	size_t		out_inuse;	/* output buffer current use	    */
// 	bool		_filtered;	/* filter() was called		    */
// 	bool		_prescreen;	/* is in prescreen phase	    */
// 	bool		_use_env;	/* LINES & COLS from environment?   */
// 	int		_checkfd;	/* filedesc for typeahead check	    */
// 	TERMINAL	*_term;		/* terminal type information	    */
// 	TTY		_saved_tty;	/* savetty/resetty information	    */
// 	NCURSES_SIZE_T	_lines;		/* screen lines			    */
// 	NCURSES_SIZE_T	_columns;	/* screen columns		    */

// 	NCURSES_SIZE_T	_lines_avail;	/* lines available for stdscr	    */
// 	NCURSES_SIZE_T	_topstolen;	/* lines stolen from top	    */

// 	int		_endwin;	/* are we out of window mode?	    */
// 	/*NCURSES_CH_T	*_current_attr;  holds current attributes set	    */
// 	int		_coloron;	/* is color enabled?		    */
// 	int		_color_defs;	/* are colors modified		    */
// 	int		_cursor;	/* visibility of the cursor	    */
// 	int		_cursrow;	/* physical cursor row		    */
// 	int		_curscol;	/* physical cursor column	    */
// 	bool		_notty;		/* true if we cannot switch non-tty */
// 	int		_nl;		/* True if NL -> CR/NL is on	    */
// 	int		_raw;		/* True if in raw mode		    */
// 	int		_cbreak;	/* 1 if in cbreak mode		    */
// 					/* > 1 if in halfdelay mode	    */
// 	int		_echo;		/* True if echo on		    */
// 	int		_use_meta;	/* use the meta key?		    */
// 	struct _SLK	*_slk;		/* ptr to soft key struct / NULL    */
// 	int		slk_format;	/* selected format for this screen  */
// 	/* cursor movement costs; units are 10ths of milliseconds */
// 	int		_char_padding;	/* cost of character put	    */
// 	int		_cr_cost;	/* cost of (carriage_return)	    */
// 	int		_cup_cost;	/* cost of (cursor_address)	    */
// 	int		_home_cost;	/* cost of (cursor_home)	    */
// 	int		_ll_cost;	/* cost of (cursor_to_ll)	    */
// 	int		_cub1_cost;	/* cost of (cursor_left)	    */
// 	int		_cuf1_cost;	/* cost of (cursor_right)	    */
// 	int		_cud1_cost;	/* cost of (cursor_down)	    */
// 	int		_cuu1_cost;	/* cost of (cursor_up)		    */
// 	int		_cub_cost;	/* cost of (parm_cursor_left)	    */
// 	int		_cuf_cost;	/* cost of (parm_cursor_right)	    */
// 	int		_cud_cost;	/* cost of (parm_cursor_down)	    */
// 	int		_cuu_cost;	/* cost of (parm_cursor_up)	    */
// 	int		_hpa_cost;	/* cost of (column_address)	    */
// 	int		_vpa_cost;	/* cost of (row_address)	    */
// 	/* used in tty_update.c, must be chars */
// 	int		_ed_cost;	/* cost of (clr_eos)		    */
// 	int		_el_cost;	/* cost of (clr_eol)		    */
// 	int		_el1_cost;	/* cost of (clr_bol)		    */
// 	int		_dch1_cost;	/* cost of (delete_character)	    */
// 	int		_ich1_cost;	/* cost of (insert_character)	    */
// 	int		_dch_cost;	/* cost of (parm_dch)		    */
// 	int		_ich_cost;	/* cost of (parm_ich)		    */
// 	int		_ech_cost;	/* cost of (erase_chars)	    */
// 	int		_rep_cost;	/* cost of (repeat_char)	    */
// 	int		_hpa_ch_cost;	/* cost of (column_address)	    */
// 	int		_cup_ch_cost;	/* cost of (cursor_address)	    */
// 	int		_cuf_ch_cost;	/* cost of (parm_cursor_right)	    */
// 	int		_inline_cost;	/* cost of inline-move		    */
// 	int		_smir_cost;	/* cost of (enter_insert_mode)	    */
// 	int		_rmir_cost;	/* cost of (exit_insert_mode)	    */
// 	int		_ip_cost;	/* cost of (insert_padding)	    */
// 	/* used in lib_mvcur.c */
// 	char *		_address_cursor;
// 	/* used in tty_update.c */
// 	int		_scrolling;	/* 1 if terminal's smart enough to  */

// 	/* used in lib_color.c */
// 	// rgb_bits_t	_direct_color;	/* RGB overrides color-table	     */
// 	// color_t		*_color_table;	/* screen's color palette	     */
// 	// int		_color_count;	/* count of colors in palette	     */
// 	// colorpair_t	*_color_pairs;	/* screen's color pair list	     */
// 	// int		_pair_count;	/* same as COLOR_PAIRS               */
// 	// int		_pair_limit;	/* actual limit of color-pairs       */
// 	// int		_pair_alloc;	/* current table-size of color-pairs */
// 	// chtype		_ok_attributes; /* valid attributes for terminal     */
// 	// chtype		_xmc_suppress;	/* attributes to suppress if xmc     */
// 	// chtype		_xmc_triggers;	/* attributes to process if xmc	     */
// 	// chtype *	_acs_map;	/* the real alternate-charset map    */
// 	// bool *		_screen_acs_map;



// 	/*
// 	 * These are the data that support the mouse interface.
// 	 */
// 	bool		_mouse_initialized;
// //	MouseType	_mouse_type;
// 	int		_maxclick;
// 	// bool		(*_mouse_event) (SCREEN *);
// 	// bool		(*_mouse_inline)(SCREEN *);
// 	// bool		(*_mouse_parse) (SCREEN *, int);
// 	// void		(*_mouse_resume)(SCREEN *);
// 	// void		(*_mouse_wrap)	(SCREEN *);
// 	int		_mouse_fd;	/* file-descriptor, if any */
// 	bool		_mouse_active;	/* true if initialized */
// //	mmask_t		_mouse_mask;	/* set via mousemask() */
// //	mmask_t		_mouse_mask2;	/* OR's in press/release bits */
// 	// mmask_t		_mouse_bstate;
// 	// MouseFormat	_mouse_format;	/* type of xterm mouse protocol */
// 	// NCURSES_CONST char *_mouse_xtermcap; /* string to enable/disable mouse */
// 	// MEVENT		_mouse_events[EV_MAX];	/* hold the last mouse event seen */
// 	// MEVENT		*_mouse_eventp;	/* next free slot in event queue */

// 	/*
// 	 * These are data that support the proper handling of the panel stack on an
// 	 * per screen basis.
// 	 */
// //	struct panelhook _panelHook;

// 	bool		_sig_winch;
// //	SCREEN		*_next_screen;

// 	/* hashes for old and new lines */
// 	unsigned long	*oldhash, *newhash;
// //	HASHMAP		*hashtab;
// 	int		hashtab_len;
// 	int		*_oldnum_list;
// 	int		_oldnum_size;

// //	NCURSES_SP_OUTC	_outch;		/* output handler if not putc */
// //	NCURSES_OUTC	jump;

// //	ripoff_t	rippedoff[N_RIPS];
// //	ripoff_t	*rsp;

// 	int		_legacy_coding;	/* see use_legacy_coding() */

// #if NCURSES_NO_PADDING
// 	bool		_no_padding;	/* flag to set if padding disabled  */
// #endif

// #if USE_HARD_TABS
// 	int		_ht_cost;	/* cost of (tab)		    */
// 	int		_cbt_cost;	/* cost of (backtab)		    */
// #endif /* USE_HARD_TABS */

// 	/* used in lib_vidattr.c */
// #if USE_ITALIC
// 	bool		_use_ritm;	/* true if we may use 'ritm'	     */
// #endif

// 	/* used in getch/twait */
// #if USE_KLIBC_KBD
// 	bool		_extended_key;	/* true if an extended key	     */
// #endif

// 	/* used in lib_color.c */
// #if NCURSES_EXT_FUNCS
// 	bool		_assumed_color; /* use assumed colors		     */
// 	bool		_default_color; /* use default colors		     */
// 	bool		_has_sgr_39_49; /* has ECMA default color support    */
// 	int		_default_fg;	/* assumed default foreground	     */
// 	int		_default_bg;	/* assumed default background	     */
// 	int		_default_pairs;	/* count pairs using default color   */
// #endif

// 	/* system-dependent mouse data */
// #if USE_GPM_SUPPORT
// 	bool		_mouse_gpm_loaded;
// 	bool		_mouse_gpm_found;
// #ifdef HAVE_LIBDL
// 	void		*_dlopen_gpm;
// 	TYPE_gpm_fd	_mouse_gpm_fd;
// 	TYPE_Gpm_Open	_mouse_Gpm_Open;
// 	TYPE_Gpm_Close	_mouse_Gpm_Close;
// 	TYPE_Gpm_GetEvent _mouse_Gpm_GetEvent;
// #endif
// 	Gpm_Connect	_mouse_gpm_connect;
// #endif /* USE_GPM_SUPPORT */

// #if USE_EMX_MOUSE
// 	int		_emxmouse_wfd;
// 	int		_emxmouse_thread;
// 	int		_emxmouse_activated;
// 	char		_emxmouse_buttons[4];
// #endif

// #if USE_SYSMOUSE
// 	MEVENT		_sysmouse_fifo[FIFO_SIZE];
// 	int		_sysmouse_head;
// 	int		_sysmouse_tail;
// 	int		_sysmouse_char_width;	/* character width */
// 	int		_sysmouse_char_height;	/* character height */
// 	int		_sysmouse_old_buttons;
// 	int		_sysmouse_new_buttons;
// #endif

// #ifdef USE_TERM_DRIVER
// 	MEVENT		_drv_mouse_fifo[FIFO_SIZE];
// 	int		_drv_mouse_head;
// 	int		_drv_mouse_tail;
// 	int		_drv_mouse_old_buttons;
// 	int		_drv_mouse_new_buttons;
// #endif
// 	/*
// 	 * This supports automatic resizing
// 	 */
// #if USE_SIZECHANGE
// 	int		(*_resize)(NCURSES_SP_DCLx int y, int x);
// 	int		(*_ungetch)(SCREEN *, int);
// #endif

// #ifdef USE_SP_WINDOWLIST
// 	WINDOWLIST*	_windowlist;
// #define WindowList(sp)  (sp)->_windowlist
// #endif

// #if USE_REENTRANT
// 	char		_ttytype[NAMESIZE];
// 	int		_ESCDELAY;
// 	int		_TABSIZE;
// 	int		_LINES;
// 	int		_COLS;
// #endif

// #if NCURSES_SP_FUNCS
// 	bool		use_tioctl;
// #endif

// 	/*
// 	 * ncurses/ncursesw are the same up to this point.
// 	 */

// // #if USE_WIDEC_SUPPORT
// // 	/* recent versions of 'screen' have partially-working support for
// // 	 * UTF-8, but do not permit ACS at the same time (see tty_update.c).
// // 	 */
// // 	bool		_screen_acs_fix;
// // 	bool		_screen_unicode;
// // #endif

// };