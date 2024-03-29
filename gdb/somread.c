/* Read HP PA/Risc object files for GDB.
   Copyright (C) 1991, 1992, 1994, 1995, 1996, 1998, 1999, 2000, 2001, 2002,
   2004, 2007, 2008, 2009, 2010, 2011 Free Software Foundation, Inc.
   Written by Fred Fish at Cygnus Support.

   This file is part of GDB.

   This program is free software; you can redistribute it and/or modify
   it under the terms of the GNU General Public License as published by
   the Free Software Foundation; either version 3 of the License, or
   (at your option) any later version.

   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.

   You should have received a copy of the GNU General Public License
   along with this program.  If not, see <http://www.gnu.org/licenses/>.  */

#include "defs.h"
#include "bfd.h"
#include <syms.h>
#include "symtab.h"
#include "symfile.h"
#include "objfiles.h"
#include "buildsym.h"
#include "stabsread.h"
#include "gdb-stabs.h"
#include "complaints.h"
#include "gdb_string.h"
#include "demangle.h"
#include "som.h"
#include "libhppa.h"
#include "psymtab.h"

#include "solib-som.h"

/* Read the symbol table of a SOM file.

   Given an open bfd, a base address to relocate symbols to, and a
   flag that specifies whether or not this bfd is for an executable
   or not (may be shared library for example), add all the global
   function and data symbols to the minimal symbol table.  */

static void
som_symtab_read (bfd *abfd, struct objfile *objfile,
		 struct section_offsets *section_offsets)
{
  struct gdbarch *gdbarch = get_objfile_arch (objfile);
  unsigned int number_of_symbols;
  int val, dynamic;
  char *stringtab;
  asection *shlib_info;
  struct symbol_dictionary_record *buf, *bufp, *endbufp;
  char *symname;
  CONST int symsize = sizeof (struct symbol_dictionary_record);
  CORE_ADDR text_offset, data_offset;


  text_offset = ANOFFSET (section_offsets, 0);
  data_offset = ANOFFSET (section_offsets, 1);

  number_of_symbols = bfd_get_symcount (abfd);

  /* Allocate a buffer to read in the debug info.
     We avoid using alloca because the memory size could be so large
     that we could hit the stack size limit.  */
  buf = xmalloc (symsize * number_of_symbols);
  make_cleanup (xfree, buf);
  bfd_seek (abfd, obj_som_sym_filepos (abfd), SEEK_SET);
  val = bfd_bread (buf, symsize * number_of_symbols, abfd);
  if (val != symsize * number_of_symbols)
    error (_("Couldn't read symbol dictionary!"));

  /* Allocate a buffer to read in the som stringtab section of
     the debugging info.  Again, we avoid using alloca because
     the data could be so large that we could potentially hit
     the stack size limitat.  */
  stringtab = xmalloc (obj_som_stringtab_size (abfd));
  make_cleanup (xfree, stringtab);
  bfd_seek (abfd, obj_som_str_filepos (abfd), SEEK_SET);
  val = bfd_bread (stringtab, obj_som_stringtab_size (abfd), abfd);
  if (val != obj_som_stringtab_size (abfd))
    error (_("Can't read in HP string table."));

  /* We need to determine if objfile is a dynamic executable (so we
     can do the right thing for ST_ENTRY vs ST_CODE symbols).

     There's nothing in the header which easily allows us to do
     this.

     This code used to rely upon the existence of a $SHLIB_INFO$
     section to make this determination.  HP claims that it is
     more accurate to check for a nonzero text offset, but they
     have not provided any information about why that test is
     more accurate.  */
  dynamic = (text_offset != 0);

  endbufp = buf + number_of_symbols;
  for (bufp = buf; bufp < endbufp; ++bufp)
    {
      enum minimal_symbol_type ms_type;

      QUIT;

      switch (bufp->symbol_scope)
	{
	case SS_UNIVERSAL:
	case SS_EXTERNAL:
	  switch (bufp->symbol_type)
	    {
	    case ST_SYM_EXT:
	    case ST_ARG_EXT:
	      continue;

	    case ST_CODE:
	    case ST_PRI_PROG:
	    case ST_SEC_PROG:
	    case ST_MILLICODE:
	      symname = bufp->name.n_strx + stringtab;
	      ms_type = mst_text;
	      bufp->symbol_value += text_offset;
	      bufp->symbol_value = gdbarch_smash_text_address
				     (gdbarch, bufp->symbol_value);
	      break;

	    case ST_ENTRY:
	      symname = bufp->name.n_strx + stringtab;
	      /* For a dynamic executable, ST_ENTRY symbols are
	         the stubs, while the ST_CODE symbol is the real
	         function.  */
	      if (dynamic)
		ms_type = mst_solib_trampoline;
	      else
		ms_type = mst_text;
	      bufp->symbol_value += text_offset;
	      bufp->symbol_value = gdbarch_smash_text_address
				     (gdbarch, bufp->symbol_value);
	      break;

	    case ST_STUB:
	      symname = bufp->name.n_strx + stringtab;
	      ms_type = mst_solib_trampoline;
	      bufp->symbol_value += text_offset;
	      bufp->symbol_value = gdbarch_smash_text_address
				     (gdbarch, bufp->symbol_value);
	      break;

	    case ST_DATA:
	      symname = bufp->name.n_strx + stringtab;
	      bufp->symbol_value += data_offset;
	      ms_type = mst_data;
	      break;
	    default:
	      continue;
	    }
	  break;

#if 0
	  /* SS_GLOBAL and SS_LOCAL are two names for the same thing (!).  */
	case SS_GLOBAL:
#endif
	case SS_LOCAL:
	  switch (bufp->symbol_type)
	    {
	    case ST_SYM_EXT:
	    case ST_ARG_EXT:
	      continue;

	    case ST_CODE:
	      symname = bufp->name.n_strx + stringtab;
	      ms_type = mst_file_text;
	      bufp->symbol_value += text_offset;
	      bufp->symbol_value = gdbarch_smash_text_address
				     (gdbarch, bufp->symbol_value);

	    check_strange_names:
	      /* Utah GCC 2.5, FSF GCC 2.6 and later generate correct local
	         label prefixes for stabs, constant data, etc.  So we need
	         only filter out L$ symbols which are left in due to
	         limitations in how GAS generates SOM relocations.

	         When linking in the HPUX C-library the HP linker has
	         the nasty habit of placing section symbols from the literal
	         subspaces in the middle of the program's text.  Filter
	         those out as best we can.  Check for first and last character
	         being '$'.

	         And finally, the newer HP compilers emit crud like $PIC_foo$N
	         in some circumstance (PIC code I guess).  It's also claimed
	         that they emit D$ symbols too.  What stupidity.  */
	      if ((symname[0] == 'L' && symname[1] == '$')
	      || (symname[0] == '$' && symname[strlen (symname) - 1] == '$')
		  || (symname[0] == 'D' && symname[1] == '$')
		  || (strncmp (symname, "L0\001", 3) == 0)
		  || (strncmp (symname, "$PIC", 4) == 0))
		continue;
	      break;

	    case ST_PRI_PROG:
	    case ST_SEC_PROG:
	    case ST_MILLICODE:
	      symname = bufp->name.n_strx + stringtab;
	      ms_type = mst_file_text;
	      bufp->symbol_value += text_offset;
	      bufp->symbol_value = gdbarch_smash_text_address
				     (gdbarch, bufp->symbol_value);
	      break;

	    case ST_ENTRY:
	      symname = bufp->name.n_strx + stringtab;
	      /* SS_LOCAL symbols in a shared library do not have
		 export stubs, so we do not have to worry about
		 using mst_file_text vs mst_solib_trampoline here like
		 we do for SS_UNIVERSAL and SS_EXTERNAL symbols above.  */
	      ms_type = mst_file_text;
	      bufp->symbol_value += text_offset;
	      bufp->symbol_value = gdbarch_smash_text_address
				     (gdbarch, bufp->symbol_value);
	      break;

	    case ST_STUB:
	      symname = bufp->name.n_strx + stringtab;
	      ms_type = mst_solib_trampoline;
	      bufp->symbol_value += text_offset;
	      bufp->symbol_value = gdbarch_smash_text_address
				     (gdbarch, bufp->symbol_value);
	      break;


	    case ST_DATA:
	      symname = bufp->name.n_strx + stringtab;
	      bufp->symbol_value += data_offset;
	      ms_type = mst_file_data;
	      goto check_strange_names;

	    default:
	      continue;
	    }
	  break;

	  /* This can happen for common symbols when -E is passed to the
	     final link.  No idea _why_ that would make the linker force
	     common symbols to have an SS_UNSAT scope, but it does.

	     This also happens for weak symbols, but their type is
	     ST_DATA.  */
	case SS_UNSAT:
	  switch (bufp->symbol_type)
	    {
	    case ST_STORAGE:
	    case ST_DATA:
	      symname = bufp->name.n_strx + stringtab;
	      bufp->symbol_value += data_offset;
	      ms_type = mst_data;
	      break;

	    default:
	      continue;
	    }
	  break;

	default:
	  continue;
	}

      if (bufp->name.n_strx > obj_som_stringtab_size (abfd))
	error (_("Invalid symbol data; bad HP string table offset: %d"),
	       bufp->name.n_strx);

      prim_record_minimal_symbol (symname, bufp->symbol_value, ms_type,
				  objfile);
    }
}

/* Scan and build partial symbols for a symbol file.
   We have been initialized by a call to som_symfile_init, which 
   currently does nothing.

   SECTION_OFFSETS is a set of offsets to apply to relocate the symbols
   in each section.  This is ignored, as it isn't needed for SOM.

   This function only does the minimum work necessary for letting the
   user "name" things symbolically; it does not read the entire symtab.
   Instead, it reads the external and static symbols and puts them in partial
   symbol tables.  When more extensive information is requested of a
   file, the corresponding partial symbol table is mutated into a full
   fledged symbol table by going back and reading the symbols
   for real.

   We look for sections with specific names, to tell us what debug
   format to look for:  FIXME!!!

   somstab_build_psymtabs() handles STABS symbols.

   Note that SOM files have a "minimal" symbol table, which is vaguely
   reminiscent of a COFF symbol table, but has only the minimal information
   necessary for linking.  We process this also, and use the information to
   build gdb's minimal symbol table.  This gives us some minimal debugging
   capability even for files compiled without -g.  */

static void
som_symfile_read (struct objfile *objfile, int symfile_flags)
{
  bfd *abfd = objfile->obfd;
  struct cleanup *back_to;

  init_minimal_symbol_collection ();
  back_to = make_cleanup_discard_minimal_symbols ();

  /* Process the normal SOM symbol table first.
     This reads in the DNTT and string table, but doesn't
     actually scan the DNTT.  It does scan the linker symbol
     table and thus build up a "minimal symbol table".  */

  som_symtab_read (abfd, objfile, objfile->section_offsets);

  /* Install any minimal symbols that have been collected as the current
     minimal symbols for this objfile.
     Further symbol-reading is done incrementally, file-by-file,
     in a step known as "psymtab-to-symtab" expansion.  hp-symtab-read.c
     contains the code to do the actual DNTT scanning and symtab building.  */
  install_minimal_symbols (objfile);
  do_cleanups (back_to);

  /* Now read information from the stabs debug sections.
     This is emitted by gcc.  */
  stabsect_build_psymtabs (objfile,
			   "$GDB_SYMBOLS$", "$GDB_STRINGS$", "$TEXT$");
}

/* Initialize anything that needs initializing when a completely new symbol
   file is specified (not just adding some symbols from another file, e.g. a
   shared library).

   We reinitialize buildsym, since we may be reading stabs from a SOM file.  */

static void
som_new_init (struct objfile *ignore)
{
  stabsread_new_init ();
  buildsym_new_init ();
}

/* Perform any local cleanups required when we are done with a particular
   objfile.  I.e, we are in the process of discarding all symbol information
   for an objfile, freeing up all memory held for it, and unlinking the
   objfile struct from the global list of known objfiles.  */

static void
som_symfile_finish (struct objfile *objfile)
{
  if (objfile->deprecated_sym_stab_info != NULL)
    {
      xfree (objfile->deprecated_sym_stab_info);
    }
}

/* SOM specific initialization routine for reading symbols.  */

static void
som_symfile_init (struct objfile *objfile)
{
  /* SOM objects may be reordered, so set OBJF_REORDERED.  If we
     find this causes a significant slowdown in gdb then we could
     set it in the debug symbol readers only when necessary.  */
  objfile->flags |= OBJF_REORDERED;
}

/* SOM specific parsing routine for section offsets.

   Plain and simple for now.  */

static void
som_symfile_offsets (struct objfile *objfile, struct section_addr_info *addrs)
{
  int i;
  CORE_ADDR text_addr;

  objfile->num_sections = bfd_count_sections (objfile->obfd);
  objfile->section_offsets = (struct section_offsets *)
    obstack_alloc (&objfile->objfile_obstack, 
		   SIZEOF_N_SECTION_OFFSETS (objfile->num_sections));

  /* FIXME: ezannoni 2000-04-20 The section names in SOM are not
     .text, .data, etc, but $TEXT$, $DATA$,...  We should initialize
     SET_OFF_* from bfd.  (See default_symfile_offsets()).  But I don't
     know the correspondence between SOM sections and GDB's idea of
     section names.  So for now we default to what is was before these
     changes.  */
  objfile->sect_index_text = 0;
  objfile->sect_index_data = 1;
  objfile->sect_index_bss = 2;
  objfile->sect_index_rodata = 3;

  /* First see if we're a shared library.  If so, get the section
     offsets from the library, else get them from addrs.  */
  if (!som_solib_section_offsets (objfile, objfile->section_offsets))
    {
      /* Note: Here is OK to compare with ".text" because this is the
         name that gdb itself gives to that section, not the SOM
         name.  */
      for (i = 0; i < addrs->num_sections && addrs->other[i].name; i++)
	if (strcmp (addrs->other[i].name, ".text") == 0)
	  break;
      text_addr = addrs->other[i].addr;

      for (i = 0; i < objfile->num_sections; i++)
	(objfile->section_offsets)->offsets[i] = text_addr;
    }
}



/* Register that we are able to handle SOM object file formats.  */

static const struct sym_fns som_sym_fns =
{
  bfd_target_som_flavour,
  som_new_init,			/* init anything gbl to entire symtab */
  som_symfile_init,		/* read initial info, setup for sym_read() */
  som_symfile_read,		/* read a symbol file into symtab */
  NULL,				/* sym_read_psymbols */
  som_symfile_finish,		/* finished with file, cleanup */
  som_symfile_offsets,		/* Translate ext. to int. relocation */
  default_symfile_segments,	/* Get segment information from a file.  */
  NULL,
  default_symfile_relocate,	/* Relocate a debug section.  */
  &psym_functions
};

void
_initialize_somread (void)
{
  add_symtab_fns (&som_sym_fns);
}
