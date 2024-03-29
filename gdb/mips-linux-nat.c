/* Native-dependent code for GNU/Linux on MIPS processors.

   Copyright (C) 2001, 2002, 2003, 2004, 2005, 2006, 2007, 2008, 2009, 2010,
   2011 Free Software Foundation, Inc.

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
#include "command.h"
#include "gdbcmd.h"
#include "gdb_assert.h"
#include "inferior.h"
#include "mips-tdep.h"
#include "target.h"
#include "regcache.h"
#include "linux-nat.h"
#include "mips-linux-tdep.h"
#include "target-descriptions.h"

#include "gdb_proc_service.h"
#include "gregset.h"

#include <sgidefs.h>
#include <sys/ptrace.h>

#include "features/mips-linux.c"
#include "features/mips64-linux.c"

#ifndef PTRACE_GET_THREAD_AREA
#define PTRACE_GET_THREAD_AREA 25
#endif

/* Assume that we have PTRACE_GETREGS et al. support.  If we do not,
   we'll clear this and use PTRACE_PEEKUSER instead.  */
static int have_ptrace_regsets = 1;

/* Whether or not to print the mirrored debug registers.  */

static int maint_show_dr;

/* Saved function pointers to fetch and store a single register using
   PTRACE_PEEKUSER and PTRACE_POKEUSER.  */

static void (*super_fetch_registers) (struct target_ops *,
				      struct regcache *, int);
static void (*super_store_registers) (struct target_ops *,
				      struct regcache *, int);

static void (*super_close) (int);

/* Map gdb internal register number to ptrace ``address''.
   These ``addresses'' are normally defined in <asm/ptrace.h>. 

   ptrace does not provide a way to read (or set) MIPS_PS_REGNUM,
   and there's no point in reading or setting MIPS_ZERO_REGNUM.
   We also can not set BADVADDR, CAUSE, or FCRIR via ptrace().  */

static CORE_ADDR
mips_linux_register_addr (struct gdbarch *gdbarch, int regno, int store)
{
  CORE_ADDR regaddr;

  if (regno < 0 || regno >= gdbarch_num_regs (gdbarch))
    error (_("Bogon register number %d."), regno);

  if (regno > MIPS_ZERO_REGNUM && regno < MIPS_ZERO_REGNUM + 32)
    regaddr = regno;
  else if ((regno >= mips_regnum (gdbarch)->fp0)
	   && (regno < mips_regnum (gdbarch)->fp0 + 32))
    regaddr = FPR_BASE + (regno - mips_regnum (gdbarch)->fp0);
  else if (regno == mips_regnum (gdbarch)->pc)
    regaddr = PC;
  else if (regno == mips_regnum (gdbarch)->cause)
    regaddr = store? (CORE_ADDR) -1 : CAUSE;
  else if (regno == mips_regnum (gdbarch)->badvaddr)
    regaddr = store? (CORE_ADDR) -1 : BADVADDR;
  else if (regno == mips_regnum (gdbarch)->lo)
    regaddr = MMLO;
  else if (regno == mips_regnum (gdbarch)->hi)
    regaddr = MMHI;
  else if (regno == mips_regnum (gdbarch)->fp_control_status)
    regaddr = FPC_CSR;
  else if (regno == mips_regnum (gdbarch)->fp_implementation_revision)
    regaddr = store? (CORE_ADDR) -1 : FPC_EIR;
  else if (mips_linux_restart_reg_p (gdbarch) && regno == MIPS_RESTART_REGNUM)
    regaddr = 0;
  else
    regaddr = (CORE_ADDR) -1;

  return regaddr;
}

static CORE_ADDR
mips64_linux_register_addr (struct gdbarch *gdbarch, int regno, int store)
{
  CORE_ADDR regaddr;

  if (regno < 0 || regno >= gdbarch_num_regs (gdbarch))
    error (_("Bogon register number %d."), regno);

  if (regno > MIPS_ZERO_REGNUM && regno < MIPS_ZERO_REGNUM + 32)
    regaddr = regno;
  else if ((regno >= mips_regnum (gdbarch)->fp0)
	   && (regno < mips_regnum (gdbarch)->fp0 + 32))
    regaddr = MIPS64_FPR_BASE + (regno - gdbarch_fp0_regnum (gdbarch));
  else if (regno == mips_regnum (gdbarch)->pc)
    regaddr = MIPS64_PC;
  else if (regno == mips_regnum (gdbarch)->cause)
    regaddr = store? (CORE_ADDR) -1 : MIPS64_CAUSE;
  else if (regno == mips_regnum (gdbarch)->badvaddr)
    regaddr = store? (CORE_ADDR) -1 : MIPS64_BADVADDR;
  else if (regno == mips_regnum (gdbarch)->lo)
    regaddr = MIPS64_MMLO;
  else if (regno == mips_regnum (gdbarch)->hi)
    regaddr = MIPS64_MMHI;
  else if (regno == mips_regnum (gdbarch)->fp_control_status)
    regaddr = MIPS64_FPC_CSR;
  else if (regno == mips_regnum (gdbarch)->fp_implementation_revision)
    regaddr = store? (CORE_ADDR) -1 : MIPS64_FPC_EIR;
  else if (mips_linux_restart_reg_p (gdbarch) && regno == MIPS_RESTART_REGNUM)
    regaddr = 0;
  else
    regaddr = (CORE_ADDR) -1;

  return regaddr;
}

/* Fetch the thread-local storage pointer for libthread_db.  */

ps_err_e
ps_get_thread_area (const struct ps_prochandle *ph,
                    lwpid_t lwpid, int idx, void **base)
{
  if (ptrace (PTRACE_GET_THREAD_AREA, lwpid, NULL, base) != 0)
    return PS_ERR;

  /* IDX is the bias from the thread pointer to the beginning of the
     thread descriptor.  It has to be subtracted due to implementation
     quirks in libthread_db.  */
  *base = (void *) ((char *)*base - idx);

  return PS_OK;
}

/* Wrapper functions.  These are only used by libthread_db.  */

void
supply_gregset (struct regcache *regcache, const gdb_gregset_t *gregsetp)
{
  if (mips_isa_regsize (get_regcache_arch (regcache)) == 4)
    mips_supply_gregset (regcache, (const mips_elf_gregset_t *) gregsetp);
  else
    mips64_supply_gregset (regcache, (const mips64_elf_gregset_t *) gregsetp);
}

void
fill_gregset (const struct regcache *regcache,
	      gdb_gregset_t *gregsetp, int regno)
{
  if (mips_isa_regsize (get_regcache_arch (regcache)) == 4)
    mips_fill_gregset (regcache, (mips_elf_gregset_t *) gregsetp, regno);
  else
    mips64_fill_gregset (regcache, (mips64_elf_gregset_t *) gregsetp, regno);
}

void
supply_fpregset (struct regcache *regcache, const gdb_fpregset_t *fpregsetp)
{
  if (mips_isa_regsize (get_regcache_arch (regcache)) == 4)
    mips_supply_fpregset (regcache, (const mips_elf_fpregset_t *) fpregsetp);
  else
    mips64_supply_fpregset (regcache,
			    (const mips64_elf_fpregset_t *) fpregsetp);
}

void
fill_fpregset (const struct regcache *regcache,
	       gdb_fpregset_t *fpregsetp, int regno)
{
  if (mips_isa_regsize (get_regcache_arch (regcache)) == 4)
    mips_fill_fpregset (regcache, (mips_elf_fpregset_t *) fpregsetp, regno);
  else
    mips64_fill_fpregset (regcache,
			  (mips64_elf_fpregset_t *) fpregsetp, regno);
}


/* Fetch REGNO (or all registers if REGNO == -1) from the target
   using PTRACE_GETREGS et al.  */

static void
mips64_linux_regsets_fetch_registers (struct regcache *regcache, int regno)
{
  struct gdbarch *gdbarch = get_regcache_arch (regcache);
  int is_fp;
  int tid;

  if (regno >= mips_regnum (gdbarch)->fp0
      && regno <= mips_regnum (gdbarch)->fp0 + 32)
    is_fp = 1;
  else if (regno == mips_regnum (gdbarch)->fp_control_status)
    is_fp = 1;
  else if (regno == mips_regnum (gdbarch)->fp_implementation_revision)
    is_fp = 1;
  else
    is_fp = 0;

  tid = ptid_get_lwp (inferior_ptid);
  if (tid == 0)
    tid = ptid_get_pid (inferior_ptid);

  if (regno == -1 || !is_fp)
    {
      mips64_elf_gregset_t regs;

      if (ptrace (PTRACE_GETREGS, tid, 0L, (PTRACE_TYPE_ARG3) &regs) == -1)
	{
	  if (errno == EIO)
	    {
	      have_ptrace_regsets = 0;
	      return;
	    }
	  perror_with_name (_("Couldn't get registers"));
	}

      mips64_supply_gregset (regcache,
			     (const mips64_elf_gregset_t *) &regs);
    }

  if (regno == -1 || is_fp)
    {
      mips64_elf_fpregset_t fp_regs;

      if (ptrace (PTRACE_GETFPREGS, tid, 0L,
		  (PTRACE_TYPE_ARG3) &fp_regs) == -1)
	{
	  if (errno == EIO)
	    {
	      have_ptrace_regsets = 0;
	      return;
	    }
	  perror_with_name (_("Couldn't get FP registers"));
	}

      mips64_supply_fpregset (regcache,
			      (const mips64_elf_fpregset_t *) &fp_regs);
    }
}

/* Store REGNO (or all registers if REGNO == -1) to the target
   using PTRACE_SETREGS et al.  */

static void
mips64_linux_regsets_store_registers (const struct regcache *regcache,
				      int regno)
{
  struct gdbarch *gdbarch = get_regcache_arch (regcache);
  int is_fp;
  int tid;

  if (regno >= mips_regnum (gdbarch)->fp0
      && regno <= mips_regnum (gdbarch)->fp0 + 32)
    is_fp = 1;
  else if (regno == mips_regnum (gdbarch)->fp_control_status)
    is_fp = 1;
  else if (regno == mips_regnum (gdbarch)->fp_implementation_revision)
    is_fp = 1;
  else
    is_fp = 0;

  tid = ptid_get_lwp (inferior_ptid);
  if (tid == 0)
    tid = ptid_get_pid (inferior_ptid);

  if (regno == -1 || !is_fp)
    {
      mips64_elf_gregset_t regs;

      if (ptrace (PTRACE_GETREGS, tid, 0L, (PTRACE_TYPE_ARG3) &regs) == -1)
	perror_with_name (_("Couldn't get registers"));

      mips64_fill_gregset (regcache, &regs, regno);

      if (ptrace (PTRACE_SETREGS, tid, 0L, (PTRACE_TYPE_ARG3) &regs) == -1)
	perror_with_name (_("Couldn't set registers"));
    }

  if (regno == -1 || is_fp)
    {
      mips64_elf_fpregset_t fp_regs;

      if (ptrace (PTRACE_GETFPREGS, tid, 0L,
		  (PTRACE_TYPE_ARG3) &fp_regs) == -1)
	perror_with_name (_("Couldn't get FP registers"));

      mips64_fill_fpregset (regcache, &fp_regs, regno);

      if (ptrace (PTRACE_SETFPREGS, tid, 0L,
		  (PTRACE_TYPE_ARG3) &fp_regs) == -1)
	perror_with_name (_("Couldn't set FP registers"));
    }
}

/* Fetch REGNO (or all registers if REGNO == -1) from the target
   using any working method.  */

static void
mips64_linux_fetch_registers (struct target_ops *ops,
			      struct regcache *regcache, int regnum)
{
  /* Unless we already know that PTRACE_GETREGS does not work, try it.  */
  if (have_ptrace_regsets)
    mips64_linux_regsets_fetch_registers (regcache, regnum);

  /* If we know, or just found out, that PTRACE_GETREGS does not work, fall
     back to PTRACE_PEEKUSER.  */
  if (!have_ptrace_regsets)
    super_fetch_registers (ops, regcache, regnum);
}

/* Store REGNO (or all registers if REGNO == -1) to the target
   using any working method.  */

static void
mips64_linux_store_registers (struct target_ops *ops,
			      struct regcache *regcache, int regnum)
{
  /* Unless we already know that PTRACE_GETREGS does not work, try it.  */
  if (have_ptrace_regsets)
    mips64_linux_regsets_store_registers (regcache, regnum);

  /* If we know, or just found out, that PTRACE_GETREGS does not work, fall
     back to PTRACE_PEEKUSER.  */
  if (!have_ptrace_regsets)
    super_store_registers (ops, regcache, regnum);
}

/* Return the address in the core dump or inferior of register
   REGNO.  */

static CORE_ADDR
mips_linux_register_u_offset (struct gdbarch *gdbarch, int regno, int store_p)
{
  if (mips_abi_regsize (gdbarch) == 8)
    return mips64_linux_register_addr (gdbarch, regno, store_p);
  else
    return mips_linux_register_addr (gdbarch, regno, store_p);
}

static const struct target_desc *
mips_linux_read_description (struct target_ops *ops)
{
  /* Report that target registers are a size we know for sure
     that we can get from ptrace.  */
  if (_MIPS_SIM == _ABIO32)
    return tdesc_mips_linux;
  else
    return tdesc_mips64_linux;
}

#ifndef PTRACE_GET_WATCH_REGS
#  define PTRACE_GET_WATCH_REGS	0xd0
#endif

#ifndef PTRACE_SET_WATCH_REGS
#  define PTRACE_SET_WATCH_REGS	0xd1
#endif

#define W_BIT 0
#define R_BIT 1
#define I_BIT 2

#define W_MASK (1 << W_BIT)
#define R_MASK (1 << R_BIT)
#define I_MASK (1 << I_BIT)

#define IRW_MASK (I_MASK | R_MASK | W_MASK)

enum pt_watch_style {
  pt_watch_style_mips32,
  pt_watch_style_mips64
};

#define MAX_DEBUG_REGISTER 8

/* A value of zero in a watchlo indicates that it is available.  */

struct mips32_watch_regs
{
  uint32_t watchlo[MAX_DEBUG_REGISTER];
  /* Lower 16 bits of watchhi.  */
  uint16_t watchhi[MAX_DEBUG_REGISTER];
  /* Valid mask and I R W bits.
   * bit 0 -- 1 if W bit is usable.
   * bit 1 -- 1 if R bit is usable.
   * bit 2 -- 1 if I bit is usable.
   * bits 3 - 11 -- Valid watchhi mask bits.
   */
  uint16_t watch_masks[MAX_DEBUG_REGISTER];
  /* The number of valid watch register pairs.  */
  uint32_t num_valid;
  /* There is confusion across gcc versions about structure alignment,
     so we force 8 byte alignment for these structures so they match
     the kernel even if it was build with a different gcc version.  */
} __attribute__ ((aligned (8)));

struct mips64_watch_regs
{
  uint64_t watchlo[MAX_DEBUG_REGISTER];
  uint16_t watchhi[MAX_DEBUG_REGISTER];
  uint16_t watch_masks[MAX_DEBUG_REGISTER];
  uint32_t num_valid;
} __attribute__ ((aligned (8)));

struct pt_watch_regs
{
  enum pt_watch_style style;
  union
  {
    struct mips32_watch_regs mips32;
    struct mips64_watch_regs mips64;
  };
};

/* -1 if the kernel and/or CPU do not support watch registers.
    1 if watch_readback is valid and we can read style, num_valid
      and the masks.
    0 if we need to read the watch_readback.  */

static int watch_readback_valid;

/* Cached watch register read values.  */

static struct pt_watch_regs watch_readback;

/* We keep list of all watchpoints we should install and calculate the
   watch register values each time the list changes.  This allows for
   easy sharing of watch registers for more than one watchpoint.  */

struct mips_watchpoint
{
  CORE_ADDR addr;
  int len;
  int type;
  struct mips_watchpoint *next;
};

static struct mips_watchpoint *current_watches;

/*  The current set of watch register values for writing the
    registers.  */

static struct pt_watch_regs watch_mirror;

/* Assuming usable watch registers, return the irw_mask.  */

static uint32_t
get_irw_mask (struct pt_watch_regs *regs, int set)
{
  switch (regs->style)
    {
    case pt_watch_style_mips32:
      return regs->mips32.watch_masks[set] & IRW_MASK;
    case pt_watch_style_mips64:
      return regs->mips64.watch_masks[set] & IRW_MASK;
    default:
      internal_error (__FILE__, __LINE__,
		      _("Unrecognized watch register style"));
    }
}

/* Assuming usable watch registers, return the reg_mask.  */

static uint32_t
get_reg_mask (struct pt_watch_regs *regs, int set)
{
  switch (regs->style)
    {
    case pt_watch_style_mips32:
      return regs->mips32.watch_masks[set] & ~IRW_MASK;
    case pt_watch_style_mips64:
      return regs->mips64.watch_masks[set] & ~IRW_MASK;
    default:
      internal_error (__FILE__, __LINE__,
		      _("Unrecognized watch register style"));
    }
}

/* Assuming usable watch registers, return the num_valid.  */

static uint32_t
get_num_valid (struct pt_watch_regs *regs)
{
  switch (regs->style)
    {
    case pt_watch_style_mips32:
      return regs->mips32.num_valid;
    case pt_watch_style_mips64:
      return regs->mips64.num_valid;
    default:
      internal_error (__FILE__, __LINE__,
		      _("Unrecognized watch register style"));
    }
}

/* Assuming usable watch registers, return the watchlo.  */

static CORE_ADDR
get_watchlo (struct pt_watch_regs *regs, int set)
{
  switch (regs->style)
    {
    case pt_watch_style_mips32:
      return regs->mips32.watchlo[set];
    case pt_watch_style_mips64:
      return regs->mips64.watchlo[set];
    default:
      internal_error (__FILE__, __LINE__,
		      _("Unrecognized watch register style"));
    }
}

/* Assuming usable watch registers, set a watchlo value.  */

static void
set_watchlo (struct pt_watch_regs *regs, int set, CORE_ADDR value)
{
  switch (regs->style)
    {
    case pt_watch_style_mips32:
      /*  The cast will never throw away bits as 64 bit addresses can
	  never be used on a 32 bit kernel.  */
      regs->mips32.watchlo[set] = (uint32_t)value;
      break;
    case pt_watch_style_mips64:
      regs->mips64.watchlo[set] = value;
      break;
    default:
      internal_error (__FILE__, __LINE__,
		      _("Unrecognized watch register style"));
    }
}

/* Assuming usable watch registers, return the watchhi.  */

static uint32_t
get_watchhi (struct pt_watch_regs *regs, int n)
{
  switch (regs->style)
    {
    case pt_watch_style_mips32:
      return regs->mips32.watchhi[n];
    case pt_watch_style_mips64:
      return regs->mips64.watchhi[n];
    default:
      internal_error (__FILE__, __LINE__,
		      _("Unrecognized watch register style"));
    }
}

/* Assuming usable watch registers, set a watchhi value.  */

static void
set_watchhi (struct pt_watch_regs *regs, int n, uint16_t value)
{
  switch (regs->style)
    {
    case pt_watch_style_mips32:
      regs->mips32.watchhi[n] = value;
      break;
    case pt_watch_style_mips64:
      regs->mips64.watchhi[n] = value;
      break;
    default:
      internal_error (__FILE__, __LINE__,
		      _("Unrecognized watch register style"));
    }
}

static void
mips_show_dr (const char *func, CORE_ADDR addr,
	      int len, enum target_hw_bp_type type)
{
  int i;

  puts_unfiltered (func);
  if (addr || len)
    printf_unfiltered (" (addr=%s, len=%d, type=%s)",
		       paddress (target_gdbarch, addr), len,
		       type == hw_write ? "data-write"
		       : (type == hw_read ? "data-read"
			  : (type == hw_access ? "data-read/write"
			     : (type == hw_execute ? "instruction-execute"
				: "??unknown??"))));
  puts_unfiltered (":\n");

  for (i = 0; i < MAX_DEBUG_REGISTER; i++)
    printf_unfiltered ("\tDR%d: lo=%s, hi=%s\n", i,
		       paddress (target_gdbarch,
				 get_watchlo (&watch_mirror, i)),
		       paddress (target_gdbarch,
				 get_watchhi (&watch_mirror, i)));
}

/* Return 1 if watch registers are usable.  Cached information is used
   unless force is true.  */

static int
mips_linux_read_watch_registers (int force)
{
  int tid;

  if (force || watch_readback_valid == 0)
    {
      tid = ptid_get_lwp (inferior_ptid);
      if (ptrace (PTRACE_GET_WATCH_REGS, tid, &watch_readback) == -1)
	{
	  watch_readback_valid = -1;
	  return 0;
	}
      switch (watch_readback.style)
	{
	case pt_watch_style_mips32:
	  if (watch_readback.mips32.num_valid == 0)
	    {
	      watch_readback_valid = -1;
	      return 0;
	    }
	  break;
	case pt_watch_style_mips64:
	  if (watch_readback.mips64.num_valid == 0)
	    {
	      watch_readback_valid = -1;
	      return 0;
	    }
	  break;
	default:
	  watch_readback_valid = -1;
	  return 0;
	}
      /* Watch registers appear to be usable.  */
      watch_readback_valid = 1;
    }
  return (watch_readback_valid == 1) ? 1 : 0;
}

/* Convert GDB's type to an IRW mask.  */

static unsigned
type_to_irw (int type)
{
  switch (type)
    {
    case hw_write:
      return W_MASK;
    case hw_read:
      return R_MASK;
    case hw_access:
      return (W_MASK | R_MASK);
    default:
      return 0;
    }
}

/* Target to_can_use_hw_breakpoint implementation.  Return 1 if we can
   handle the specified watch type.  */

static int
mips_linux_can_use_hw_breakpoint (int type, int cnt, int ot)
{
  int i;
  uint32_t wanted_mask, irw_mask;

  if (!mips_linux_read_watch_registers (0))
    return 0;

   switch (type)
    {
    case bp_hardware_watchpoint:
      wanted_mask = W_MASK;
      break;
    case bp_read_watchpoint:
      wanted_mask = R_MASK;
      break;
    case bp_access_watchpoint:
      wanted_mask = R_MASK | W_MASK;
      break;
    default:
      return 0;
    }
 
  for (i = 0; i < get_num_valid (&watch_readback) && cnt; i++)
    {
      irw_mask = get_irw_mask (&watch_readback, i);
      if ((irw_mask & wanted_mask) == wanted_mask)
	cnt--;
    }
  return (cnt == 0) ? 1 : 0;
}

/* Target to_stopped_by_watchpoint implementation.  Return 1 if
   stopped by watchpoint.  The watchhi R and W bits indicate the watch
   register triggered.  */

static int
mips_linux_stopped_by_watchpoint (void)
{
  int n;
  int num_valid;

  if (!mips_linux_read_watch_registers (1))
    return 0;

  num_valid = get_num_valid (&watch_readback);

  for (n = 0; n < MAX_DEBUG_REGISTER && n < num_valid; n++)
    if (get_watchhi (&watch_readback, n) & (R_MASK | W_MASK))
      return 1;

  return 0;
}

/* Target to_stopped_data_address implementation.  Set the address
   where the watch triggered (if known).  Return 1 if the address was
   known.  */

static int
mips_linux_stopped_data_address (struct target_ops *t, CORE_ADDR *paddr)
{
  /* On mips we don't know the low order 3 bits of the data address,
     so we must return false.  */
  return 0;
}

/* Set any low order bits in mask that are not set.  */

static CORE_ADDR
fill_mask (CORE_ADDR mask)
{
  CORE_ADDR f = 1;
  while (f && f < mask)
    {
      mask |= f;
      f <<= 1;
    }
  return mask;
}

/* Try to add a single watch to the specified registers.  Return 1 on
   success, 0 on failure.  */

static int
try_one_watch (struct pt_watch_regs *regs, CORE_ADDR addr,
	       int len, unsigned irw)
{
  CORE_ADDR base_addr, last_byte, break_addr, segment_len;
  CORE_ADDR mask_bits, t_low, t_low_end;
  uint16_t t_hi;
  int i, free_watches;
  struct pt_watch_regs regs_copy;

  if (len <= 0)
    return 0;

  last_byte = addr + len - 1;
  mask_bits = fill_mask (addr ^ last_byte) | IRW_MASK;
  base_addr = addr & ~mask_bits;

  /* Check to see if it is covered by current registers.  */
  for (i = 0; i < get_num_valid (regs); i++)
    {
      t_low = get_watchlo (regs, i);
      if (t_low != 0 && irw == ((unsigned)t_low & irw))
	{
	  t_hi = get_watchhi (regs, i) | IRW_MASK;
	  t_low &= ~(CORE_ADDR)t_hi;
	  if (addr >= t_low && last_byte <= (t_low + t_hi))
	    return 1;
	}
    }
  /* Try to find an empty register.  */
  free_watches = 0;
  for (i = 0; i < get_num_valid (regs); i++)
    {
      t_low = get_watchlo (regs, i);
      if (t_low == 0 && irw == (get_irw_mask (regs, i) & irw))
	{
	  if (mask_bits <= (get_reg_mask (regs, i) | IRW_MASK))
	    {
	      /* It fits, we'll take it.  */
	      set_watchlo (regs, i, base_addr | irw);
	      set_watchhi (regs, i, mask_bits & ~IRW_MASK);
	      return 1;
	    }
	  else
	    {
	      /* It doesn't fit, but has the proper IRW capabilities.  */
	      free_watches++;
	    }
	}
    }
  if (free_watches > 1)
    {
      /* Try to split it across several registers.  */
      regs_copy = *regs;
      for (i = 0; i < get_num_valid (&regs_copy); i++)
	{
	  t_low = get_watchlo (&regs_copy, i);
	  t_hi = get_reg_mask (&regs_copy, i) | IRW_MASK;
	  if (t_low == 0 && irw == (t_hi & irw))
	    {
	      t_low = addr & ~(CORE_ADDR)t_hi;
	      break_addr = t_low + t_hi + 1;
	      if (break_addr >= addr + len)
		segment_len = len;
	      else
		segment_len = break_addr - addr;
	      mask_bits = fill_mask (addr ^ (addr + segment_len - 1));
	      set_watchlo (&regs_copy, i, (addr & ~mask_bits) | irw);
	      set_watchhi (&regs_copy, i, mask_bits & ~IRW_MASK);
	      if (break_addr >= addr + len)
		{
		  *regs = regs_copy;
		  return 1;
		}
	      len = addr + len - break_addr;
	      addr = break_addr;
	    }
	}
    }
  /* It didn't fit anywhere, we failed.  */
  return 0;
}

/* Target to_region_ok_for_hw_watchpoint implementation.  Return 1 if
   the specified region can be covered by the watch registers.  */

static int
mips_linux_region_ok_for_hw_watchpoint (CORE_ADDR addr, int len)
{
  struct pt_watch_regs dummy_regs;
  int i;

  if (!mips_linux_read_watch_registers (0))
    return 0;

  dummy_regs = watch_readback;
  /* Clear them out.  */
  for (i = 0; i < get_num_valid (&dummy_regs); i++)
    set_watchlo (&dummy_regs, i, 0);
  return try_one_watch (&dummy_regs, addr, len, 0);
}


/* Write the mirrored watch register values for each thread.  */

static int
write_watchpoint_regs (void)
{
  struct lwp_info *lp;
  int tid;

  ALL_LWPS (lp)
    {
      tid = ptid_get_lwp (lp->ptid);
      if (ptrace (PTRACE_SET_WATCH_REGS, tid, &watch_mirror) == -1)
	perror_with_name (_("Couldn't write debug register"));
    }
  return 0;
}

/* linux_nat new_thread implementation.  Write the mirrored watch
 register values for the new thread.  */

static void
mips_linux_new_thread (ptid_t ptid)
{
  int tid;

  if (!mips_linux_read_watch_registers (0))
    return;

  tid = ptid_get_lwp (ptid);
  if (ptrace (PTRACE_SET_WATCH_REGS, tid, &watch_mirror) == -1)
    perror_with_name (_("Couldn't write debug register"));
}

/* Fill in the watch registers with the currently cached watches.  */

static void
populate_regs_from_watches (struct pt_watch_regs *regs)
{
  struct mips_watchpoint *w;
  int i;

  /* Clear them out.  */
  for (i = 0; i < get_num_valid (regs); i++)
    {
      set_watchlo (regs, i, 0);
      set_watchhi (regs, i, 0);
    }

  w = current_watches;
  while (w)
    {
      i = try_one_watch (regs, w->addr, w->len, type_to_irw (w->type));
      /* They must all fit, because we previously calculated that they
	 would.  */
      gdb_assert (i);
      w = w->next;
    }
}

/* Target to_insert_watchpoint implementation.  Try to insert a new
   watch.  Return zero on success.  */

static int
mips_linux_insert_watchpoint (CORE_ADDR addr, int len, int type,
			      struct expression *cond)
{
  struct pt_watch_regs regs;
  struct mips_watchpoint *new_watch;
  struct mips_watchpoint **pw;

  int i;
  int retval;

  if (!mips_linux_read_watch_registers (0))
    return -1;

  if (len <= 0)
    return -1;

  regs = watch_readback;
  /* Add the current watches.  */
  populate_regs_from_watches (&regs);

  /* Now try to add the new watch.  */
  if (!try_one_watch (&regs, addr, len, type_to_irw (type)))
    return -1;

  /* It fit.  Stick it on the end of the list.  */
  new_watch = (struct mips_watchpoint *)
    xmalloc (sizeof (struct mips_watchpoint));
  new_watch->addr = addr;
  new_watch->len = len;
  new_watch->type = type;
  new_watch->next = NULL;

  pw = &current_watches;
  while (*pw != NULL)
    pw = &(*pw)->next;
  *pw = new_watch;

  watch_mirror = regs;
  retval = write_watchpoint_regs ();

  if (maint_show_dr)
    mips_show_dr ("insert_watchpoint", addr, len, type);

  return retval;
}

/* Target to_remove_watchpoint implementation.  Try to remove a watch.
   Return zero on success.  */

static int
mips_linux_remove_watchpoint (CORE_ADDR addr, int len, int type,
			      struct expression *cond)
{
  int retval;
  int deleted_one;

  struct mips_watchpoint **pw;
  struct mips_watchpoint *w;

  /* Search for a known watch that matches.  Then unlink and free
     it.  */
  deleted_one = 0;
  pw = &current_watches;
  while ((w = *pw))
    {
      if (w->addr == addr && w->len == len && w->type == type)
	{
	  *pw = w->next;
	  xfree (w);
	  deleted_one = 1;
	  break;
	}
      pw = &(w->next);
    }

  if (!deleted_one)
    return -1;  /* We don't know about it, fail doing nothing.  */

  /* At this point watch_readback is known to be valid because we
     could not have added the watch without reading it.  */
  gdb_assert (watch_readback_valid == 1);

  watch_mirror = watch_readback;
  populate_regs_from_watches (&watch_mirror);

  retval = write_watchpoint_regs ();

  if (maint_show_dr)
    mips_show_dr ("remove_watchpoint", addr, len, type);

  return retval;
}

/* Target to_close implementation.  Free any watches and call the
   super implementation.  */

static void
mips_linux_close (int quitting)
{
  struct mips_watchpoint *w;
  struct mips_watchpoint *nw;

  /* Clean out the current_watches list.  */
  w = current_watches;
  while (w)
    {
      nw = w->next;
      xfree (w);
      w = nw;
    }
  current_watches = NULL;

  if (super_close)
    super_close (quitting);
}

void _initialize_mips_linux_nat (void);

void
_initialize_mips_linux_nat (void)
{
  struct target_ops *t;

  add_setshow_boolean_cmd ("show-debug-regs", class_maintenance,
			   &maint_show_dr, _("\
Set whether to show variables that mirror the mips debug registers."), _("\
Show whether to show variables that mirror the mips debug registers."), _("\
Use \"on\" to enable, \"off\" to disable.\n\
If enabled, the debug registers values are shown when GDB inserts\n\
or removes a hardware breakpoint or watchpoint, and when the inferior\n\
triggers a breakpoint or watchpoint."),
			   NULL,
			   NULL,
			   &maintenance_set_cmdlist,
			   &maintenance_show_cmdlist);

  t = linux_trad_target (mips_linux_register_u_offset);

  super_close = t->to_close;
  t->to_close = mips_linux_close;

  super_fetch_registers = t->to_fetch_registers;
  super_store_registers = t->to_store_registers;

  t->to_fetch_registers = mips64_linux_fetch_registers;
  t->to_store_registers = mips64_linux_store_registers;

  t->to_can_use_hw_breakpoint = mips_linux_can_use_hw_breakpoint;
  t->to_remove_watchpoint = mips_linux_remove_watchpoint;
  t->to_insert_watchpoint = mips_linux_insert_watchpoint;
  t->to_stopped_by_watchpoint = mips_linux_stopped_by_watchpoint;
  t->to_stopped_data_address = mips_linux_stopped_data_address;
  t->to_region_ok_for_hw_watchpoint = mips_linux_region_ok_for_hw_watchpoint;

  t->to_read_description = mips_linux_read_description;

  linux_nat_add_target (t);
  linux_nat_set_new_thread (t, mips_linux_new_thread);

  /* Initialize the standard target descriptions.  */
  initialize_tdesc_mips_linux ();
  initialize_tdesc_mips64_linux ();
}
