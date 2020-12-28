//! Functions to read and write control registers.

pub use super::model_specific::{Efer, EferFlags};

use bitflags::bitflags;

/// Various control flags modifying the basic operation of the CPU.
#[derive(Debug)]
pub struct Cr0;

bitflags! {
    /// Configuration flags of the Cr0 register.
    pub struct Cr0Flags: usize {
        /// Enables protected mode.
        const PROTECTED_MODE_ENABLE = 1;
        /// Enables monitoring of the coprocessor, typical for x87 instructions.
        ///
        /// Controls together with the `TASK_SWITCHED` flag whether a `wait` or `fwait`
        /// instruction should cause a device-not-available exception.
        const MONITOR_COPROCESSOR = 1 << 1;
        /// Force all x87 and MMX instructions to cause an exception.
        const EMULATE_COPROCESSOR = 1 << 2;
        /// Automatically set to 1 on _hardware_ task switch.
        ///
        /// This flags allows lazily saving x87/MMX/SSE instructions on hardware context switches.
        const TASK_SWITCHED = 1 << 3;
        /// Enables the native error reporting mechanism for x87 FPU errors.
        const NUMERIC_ERROR = 1 << 5;
        /// Controls whether supervisor-level writes to read-only pages are inhibited.
        ///
        /// When set, it is not possible to write to read-only pages from ring 0.
        const WRITE_PROTECT = 1 << 16;
        /// Enables automatic alignment checking.
        const ALIGNMENT_MASK = 1 << 18;
        /// Ignored. Used to control write-back/write-through cache strategy on older CPUs.
        const NOT_WRITE_THROUGH = 1 << 29;
        /// Disables internal caches (only for some cases).
        const CACHE_DISABLE = 1 << 30;
        /// Enables page translation.
        const PAGING = 1 << 31;
    }
}

/// Contains the Page Fault Linear Address (PFLA).
///
/// When page fault occurs, the CPU sets this register to the accessed address.
#[derive(Debug)]
pub struct Cr2;

/// Contains the physical address of the level 4 page table.
#[derive(Debug)]
pub struct Cr3;

bitflags! {
    /// Controls cache settings for the level 4 page table.
    pub struct Cr3Flags: usize {
        /// Use a writethrough cache policy for the P4 table (else a writeback policy is used).
        const PAGE_LEVEL_WRITETHROUGH = 1 << 3;
        /// Disable caching for the P4 table.
        const PAGE_LEVEL_CACHE_DISABLE = 1 << 4;
    }
}

/// Various control flags modifying the basic operation of the CPU while in protected mode.
///
/// Note: The documention for the individual fields is taken from the AMD64 and Intel x86_64
/// manuals.
#[derive(Debug)]
pub struct Cr4;

bitflags! {
    /// Controls cache settings for the level 4 page table.
    pub struct Cr4Flags: usize {
        /// Enables hardware-supported performance enhancements for software running in
        /// virtual-8086 mode.
        const VIRTUAL_8086_MODE_EXTENSIONS = 1;
        /// Enables support for protected-mode virtual interrupts.
        const PROTECTED_MODE_VIRTUAL_INTERRUPTS = 1 << 1;
        /// When set, only privilege-level 0 can execute the RDTSC or RDTSCP instructions.
        const TIMESTAMP_DISABLE = 1 << 2;
        /// Enables I/O breakpoint capability and enforces treatment of DR4 and DR5 registers
        /// as reserved.
        const DEBUGGING_EXTENSIONS = 1 << 3;
        /// Enables the use of 4MB physical frames; ignored in long mode.
        const PAGE_SIZE_EXTENSION = 1 << 4;
        /// Enables physical address extension and 2MB physical frames; required in long mode.
        const PHYSICAL_ADDRESS_EXTENSION = 1 << 5;
        /// Enables the machine-check exception mechanism.
        const MACHINE_CHECK_EXCEPTION = 1 << 6;
        /// Enables the global-page mechanism, which allows to make page translations global
        /// to all processes.
        const PAGE_GLOBAL = 1 << 7;
        /// Allows software running at any privilege level to use the RDPMC instruction.
        const PERFORMANCE_MONITOR_COUNTER = 1 << 8;
        /// Enable the use of legacy SSE instructions; allows using FXSAVE/FXRSTOR for saving
        /// processor state of 128-bit media instructions.
        const OSFXSR = 1 << 9;
        /// Enables the SIMD floating-point exception (#XF) for handling unmasked 256-bit and
        /// 128-bit media floating-point errors.
        const OSXMMEXCPT_ENABLE = 1 << 10;
        /// Prevents the execution of the SGDT, SIDT, SLDT, SMSW, and STR instructions by
        /// user-mode software.
        const USER_MODE_INSTRUCTION_PREVENTION = 1 << 11;
        /// Enables 5-level paging on supported CPUs.
        const L5_PAGING = 1 << 12;
        /// Enables VMX insturctions.
        const VIRTUAL_MACHINE_EXTENSIONS = 1 << 13;
        /// Enables SMX instructions.
        const SAFER_MODE_EXTENSIONS = 1 << 14;
        /// Enables software running in 64-bit mode at any privilege level to read and write
        /// the FS.base and GS.base hidden segment register state.
        const FSGSBASE = 1 << 16;
        /// Enables process-context identifiers (PCIDs).
        const PCID = 1 << 17;
        /// Enables extendet processor state management instructions, including XGETBV and XSAVE.
        const OSXSAVE = 1 << 18;
        /// Prevents the execution of instructions that reside in pages accessible by user-mode
        /// software when the processor is in supervisor-mode.
        const SUPERVISOR_MODE_EXECUTION_PROTECTION = 1 << 20;
        /// Enables restrictions for supervisor-mode software when reading data from user-mode
        /// pages.
        const SUPERVISOR_MODE_ACCESS_PREVENTION = 1 << 21;
        /// Enables 4-level paging to associate each linear address with a protection key.
        const PROTECTION_KEY = 1 << 22;
    }
}

#[cfg(feature = "instructions")]
mod x86_64 {
    use super::*;
    use crate::structures::paging::PhysFrame;
    use crate::{PhysAddr, VirtAddr};

    impl Cr0 {
        /// Read the current set of CR0 flags.
        #[inline]
        pub fn read() -> Cr0Flags {
            Cr0Flags::from_bits_truncate(Self::read_raw())
        }

        /// Read the current raw CR0 value.
        #[inline]
        pub fn read_raw() -> usize {
            let value: usize;

            #[cfg(feature = "inline_asm")]
            unsafe {
                asm!("mov {}, cr0", out(reg) value, options(nomem));
            }

            #[cfg(not(feature = "inline_asm"))]
            unsafe {
                value = crate::asm::x86_64_asm_read_cr0();
            }

            value
        }

        /// Write CR0 flags.
        ///
        /// Preserves the value of reserved fields.
        ///
        /// ## Safety
        ///
        /// This function is unsafe because it's possible to violate memory
        /// safety through it, e.g. by disabling paging.
        #[inline]
        pub unsafe fn write(flags: Cr0Flags) {
            let old_value = Self::read_raw();
            let reserved = old_value & !(Cr0Flags::all().bits());
            let new_value = reserved | flags.bits();

            Self::write_raw(new_value);
        }

        /// Write raw CR0 flags.
        ///
        /// Does _not_ preserve any values, including reserved fields.
        ///
        /// ## Safety
        ///
        /// This function is unsafe because it's possible to violate memory
        /// safety through it, e.g. by disabling paging.
        #[inline]
        pub unsafe fn write_raw(value: usize) {
            #[cfg(feature = "inline_asm")]
            asm!("mov cr0, {}", in(reg) value, options(nostack));

            #[cfg(not(feature = "inline_asm"))]
            crate::asm::x86_64_asm_write_cr0(value);
        }

        /// Updates CR0 flags.
        ///
        /// Preserves the value of reserved fields.
        ///
        /// ## Safety
        ///
        /// This function is unsafe because it's possible to violate memory
        /// safety through it, e.g. by disabling paging.
        #[inline]
        pub unsafe fn update<F>(f: F)
        where
            F: FnOnce(&mut Cr0Flags),
        {
            let mut flags = Self::read();
            f(&mut flags);
            Self::write(flags);
        }
    }

    impl Cr2 {
        /// Read the current page fault linear address from the CR2 register.
        #[inline]
        pub fn read() -> VirtAddr {
            let value: usize;

            #[cfg(feature = "inline_asm")]
            unsafe {
                asm!("mov {}, cr2", out(reg) value, options(nomem));
            }

            #[cfg(not(feature = "inline_asm"))]
            unsafe {
                value = crate::asm::x86_64_asm_read_cr2();
            }

            VirtAddr::new(value)
        }
    }

    impl Cr3 {
        /// Read the current P4 table address from the CR3 register.
        #[inline]
        pub fn read() -> (PhysFrame, Cr3Flags) {
            let value: usize;

            #[cfg(feature = "inline_asm")]
            unsafe {
                asm!("mov {}, cr3", out(reg) value, options(nomem));
            }

            #[cfg(not(feature = "inline_asm"))]
            unsafe {
                value = crate::asm::x86_64_asm_read_cr3();
            }

            let flags = Cr3Flags::from_bits_truncate(value);
            #[cfg(target_arch = "x86_64")]
            let addr = PhysAddr::new(value & 0x_000f_ffff_ffff_f000);
            #[cfg(target_arch = "x86")]
            let addr = PhysAddr::new(value & 0xffff_f000);
            let frame = PhysFrame::containing_address(addr);
            (frame, flags)
        }

        /// Write a new P4 table address into the CR3 register.
        ///
        /// ## Safety
        /// Changing the level 4 page table is unsafe, because it's possible to violate memory safety by
        /// changing the page mapping.
        #[inline]
        pub unsafe fn write(frame: PhysFrame, flags: Cr3Flags) {
            let addr = frame.start_address();
            let value = addr.as_usize() | flags.bits();

            #[cfg(feature = "inline_asm")]
            asm!("mov cr3, {}", in(reg) value, options(nostack));

            #[cfg(not(feature = "inline_asm"))]
            crate::asm::x86_64_asm_write_cr3(value)
        }
    }

    impl Cr4 {
        /// Read the current set of CR4 flags.
        #[inline]
        pub fn read() -> Cr4Flags {
            Cr4Flags::from_bits_truncate(Self::read_raw())
        }

        /// Read the current raw CR4 value.
        #[inline]
        pub fn read_raw() -> usize {
            let value: usize;

            #[cfg(feature = "inline_asm")]
            unsafe {
                asm!("mov {}, cr4", out(reg) value, options(nostack));
            }

            #[cfg(not(feature = "inline_asm"))]
            unsafe {
                value = crate::asm::x86_64_asm_read_cr4();
            }

            value
        }

        /// Write CR4 flags.
        ///
        /// Preserves the value of reserved fields.
        ///
        /// ## Safety
        ///
        /// This function is unsafe because it's possible to violate memory
        /// safety through it, e.g. by overwriting the physical address extension
        /// flag.
        #[inline]
        pub unsafe fn write(flags: Cr4Flags) {
            let old_value = Self::read_raw();
            let reserved = old_value & !(Cr4Flags::all().bits());
            let new_value = reserved | flags.bits();

            Self::write_raw(new_value);
        }

        /// Write raw CR4 flags.
        ///
        /// Does _not_ preserve any values, including reserved fields.
        ///
        /// ## Safety
        ///
        /// This function is unsafe because it's possible to violate memory
        /// safety through it, e.g. by overwriting the physical address extension
        /// flag.
        #[inline]
        pub unsafe fn write_raw(value: usize) {
            #[cfg(feature = "inline_asm")]
            asm!("mov cr4, {}", in(reg) value, options(nostack));

            #[cfg(not(feature = "inline_asm"))]
            crate::asm::x86_64_asm_write_cr4(value);
        }

        /// Updates CR4 flags.
        ///
        /// Preserves the value of reserved fields.
        /// ## Safety
        ///
        /// This function is unsafe because it's possible to violate memory
        /// safety through it, e.g. by overwriting the physical address extension
        /// flag.
        #[inline]
        pub unsafe fn update<F>(f: F)
        where
            F: FnOnce(&mut Cr4Flags),
        {
            let mut flags = Self::read();
            f(&mut flags);
            Self::write(flags);
        }
    }
}
