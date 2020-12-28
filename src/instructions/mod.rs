#![cfg(feature = "instructions")]

//! Special x86_64 instructions.

pub mod interrupts;
pub mod port;
pub mod random;
pub mod segmentation;
pub mod tables;
pub mod tlb;

/// Halts the CPU until the next interrupt arrives.
#[inline]
pub fn hlt() {
    #[cfg(feature = "inline_asm")]
    unsafe {
        asm!("hlt", options(nomem, nostack));
    }

    #[cfg(not(feature = "inline_asm"))]
    unsafe {
        crate::asm::x86_64_asm_hlt();
    }
}

/// Executes the `nop` instructions, which performs no operation (i.e. does nothing).
///
/// This operation is useful to work around the LLVM bug that endless loops are illegally
/// optimized away (see [the issue](https://github.com/rust-lang/rust/issues/28728)). By invoking this
/// instruction (which is marked as volatile), the compiler should no longer optimize the
/// endless loop away.
#[inline]
pub fn nop() {
    #[cfg(feature = "inline_asm")]
    unsafe {
        asm!("nop", options(nomem, nostack, preserves_flags));
    }

    #[cfg(not(feature = "inline_asm"))]
    unsafe {
        crate::asm::x86_64_asm_nop();
    }
}

/// Emits a '[magic breakpoint](https://wiki.osdev.org/Bochs#Magic_Breakpoint)' instruction for the [Bochs](http://bochs.sourceforge.net/) CPU
/// emulator. Make sure to set `magic_break: enabled=1` in your `.bochsrc` file.
#[cfg(feature = "inline_asm")]
#[inline]
pub fn bochs_breakpoint() {
    unsafe {
        asm!("xchgw bx, bx", options(nomem, nostack));
    }
}

/// Gets the current instruction pointer. Note that this is only approximate as it requires a few
/// instructions to execute.
#[cfg(feature = "inline_asm")]
#[inline(always)]
pub fn read_rip() -> usize {
    let rip: usize;
    unsafe {
        asm!(
            "lea {}, [rip]", out(reg) rip, options(nostack, nomem)
        );
    }
    rip
}
