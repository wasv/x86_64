//! Physical and virtual addresses manipulation

use core::fmt;
use core::ops::{Add, AddAssign, Sub, SubAssign};

use crate::structures::paging::{PageOffset, PageTableIndex};
use bit_field::BitField;

/// A canonical 64-bit virtual memory address.
///
/// This is a wrapper type around an `u64`, so it is always 8 bytes, even when compiled
/// on non 64-bit systems. The
/// [`TryFrom`](https://doc.rust-lang.org/std/convert/trait.TryFrom.html) trait can be used for performing conversions
/// between `u64` and `usize`.
///
/// On `x86_64`, only the 48 lower bits of a virtual address can be used. The top 16 bits need
/// to be copies of bit 47, i.e. the most significant bit. Addresses that fulfil this criterium
/// are called “canonical”. This type guarantees that it always represents a canonical address.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
#[repr(transparent)]
pub struct VirtAddr(usize);

/// A 64-bit physical memory address.
///
/// This is a wrapper type around an `u64`, so it is always 8 bytes, even when compiled
/// on non 64-bit systems. The
/// [`TryFrom`](https://doc.rust-lang.org/std/convert/trait.TryFrom.html) trait can be used for performing conversions
/// between `usize` and `usize`.
///
/// On `x86_64`, only the 52 lower bits of a physical address can be used. The top 12 bits need
/// to be zero. This type guarantees that it always represents a valid physical address.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
#[repr(transparent)]
pub struct PhysAddr(usize);

/// A passed `usize` was not a valid virtual address.
///
/// This means that bits 48 to 64 are not
/// a valid sign extension and are not null either. So automatic sign extension would have
/// overwritten possibly meaningful bits. This likely indicates a bug, for example an invalid
/// address calculation.
#[derive(Debug)]
pub struct VirtAddrNotValid(usize);

impl VirtAddr {
    /// Creates a new canonical virtual address.
    ///
    /// This function performs sign extension of bit 47 to make the address canonical.
    ///
    /// ## Panics
    ///
    /// This function panics if the bits in the range 48 to 64 contain data (i.e. are not null and no sign extension).
    #[inline]
    pub fn new(addr: usize) -> VirtAddr {
        Self::try_new(addr).expect(
            "address passed to VirtAddr::new must not contain any data \
             in bits 48 to 64",
        )
    }

    /// Tries to create a new canonical virtual address.
    ///
    /// This function tries to performs sign
    /// extension of bit 47 to make the address canonical. It succeeds if bits 48 to 64 are
    /// either a correct sign extension (i.e. copies of bit 47) or all null. Else, an error
    /// is returned.
    #[inline]
    #[cfg(target_arch = "x86_64")]
    pub fn try_new(addr: usize) -> Result<VirtAddr, VirtAddrNotValid> {
        match addr.get_bits(47..64) {
            0 | 0x1ffff => Ok(VirtAddr(addr)),     // address is canonical
            1 => Ok(VirtAddr::new_truncate(addr)), // address needs sign extension
            other => Err(VirtAddrNotValid(other)),
        }
    }

    /// Tries to create a new canonical virtual address.
    ///
    /// The function will always succeed on x86.
    #[inline]
    #[cfg(target_arch = "x86")]
    pub fn try_new(addr: usize) -> Result<VirtAddr, VirtAddrNotValid> {
        Ok(VirtAddr(addr))
    }

    /// Creates a new canonical virtual address, throwing out bits 48..64.
    ///
    /// This function performs sign extension of bit 47 to make the address canonical, so
    /// bits 48 to 64 are overwritten. If you want to check that these bits contain no data,
    /// use `new` or `try_new`.
    #[inline]
    #[cfg(target_arch = "x86_64")]
    pub const fn new_truncate(addr: usize) -> VirtAddr {
        // By doing the right shift as a signed operation (on a i64), it will
        // sign extend the value, repeating the leftmost bit.
        VirtAddr(((addr << 16) as isize >> 16) as usize)
    }

    /// Tries to create a new canonical virtual address.
    ///
    /// The function is identical to new on x86.
    #[inline]
    #[cfg(target_arch = "x86")]
    pub const fn new_truncate(addr: usize) -> VirtAddr {
        VirtAddr(addr)
    }

    /// Alias for [`new_truncate`][VirtAddr::new_truncate] for backwards compatibility.
    #[inline]
    #[deprecated(note = "Use new_truncate or new_unsafe instead")]
    pub const fn new_unchecked(addr: usize) -> VirtAddr {
        Self::new_truncate(addr)
    }

    /// Creates a new virtual address, without any checks.
    ///
    /// ## Safety
    ///
    /// You must make sure bits 48..64 are equal to bit 47. This is not checked.
    #[inline]
    pub const unsafe fn new_unsafe(addr: usize) -> VirtAddr {
        VirtAddr(addr)
    }

    /// Creates a virtual address that points to `0`.
    #[inline]
    pub const fn zero() -> VirtAddr {
        VirtAddr(0)
    }

    /// Converts the address to an `usize`.
    #[inline]
    pub const fn as_usize(self) -> usize {
        self.0
    }

    /// Creates a virtual address from the given pointer
    // cfg(target_pointer_width = "32") is only here for backwards
    // compatibility: Earlier versions of this crate did not have any `cfg()`
    // on this function. At least for 32- and 64-bit we know the `as u64` cast
    // doesn't truncate.
    #[cfg(any(target_pointer_width = "32", target_pointer_width = "64"))]
    #[inline]
    pub fn from_ptr<T>(ptr: *const T) -> Self {
        Self::new(ptr as usize)
    }

    /// Converts the address to a raw pointer.
    #[cfg(target_pointer_width = "64")]
    #[inline]
    pub fn as_ptr<T>(self) -> *const T {
        self.as_usize() as *const T
    }

    /// Converts the address to a mutable raw pointer.
    #[cfg(target_pointer_width = "64")]
    #[inline]
    pub fn as_mut_ptr<T>(self) -> *mut T {
        self.as_ptr::<T>() as *mut T
    }

    /// Convenience method for checking if a virtual address is null.
    #[inline]
    pub const fn is_null(self) -> bool {
        self.0 == 0
    }

    /// Aligns the virtual address upwards to the given alignment.
    ///
    /// See the `align_up` function for more information.
    #[inline]
    pub fn align_up<U>(self, align: U) -> Self
    where
        U: Into<usize>,
    {
        VirtAddr(align_up(self.0, align.into()))
    }

    /// Aligns the virtual address downwards to the given alignment.
    ///
    /// See the `align_down` function for more information.
    #[inline]
    pub fn align_down<U>(self, align: U) -> Self
    where
        U: Into<usize>,
    {
        VirtAddr(align_down(self.0, align.into()))
    }

    /// Checks whether the virtual address has the demanded alignment.
    #[inline]
    pub fn is_aligned<U>(self, align: U) -> bool
    where
        U: Into<usize>,
    {
        self.align_down(align) == self
    }

    /// Returns the 12-bit page offset of this virtual address.
    #[inline]
    pub const fn page_offset(self) -> PageOffset {
        PageOffset::new_truncate(self.0 as u16)
    }

    /// Returns the 9-bit level 1 page table index.
    #[inline]
    pub const fn p1_index(self) -> PageTableIndex {
        PageTableIndex::new_truncate((self.0 >> 12) as u16)
    }

    /// Returns the 9-bit level 2 page table index.
    #[inline]
    pub const fn p2_index(self) -> PageTableIndex {
        PageTableIndex::new_truncate((self.0 >> 12 >> 9) as u16)
    }

    /// Returns the 9-bit level 3 page table index.
    #[inline]
    pub const fn p3_index(self) -> PageTableIndex {
        PageTableIndex::new_truncate((self.0 >> 12 >> 9 >> 9) as u16)
    }

    /// Returns the 9-bit level 4 page table index.
    #[inline]
    pub const fn p4_index(self) -> PageTableIndex {
        PageTableIndex::new_truncate((self.0 >> 12 >> 9 >> 9 >> 9) as u16)
    }
}

impl fmt::Debug for VirtAddr {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "VirtAddr({:#x})", self.0)
    }
}

impl Add<usize> for VirtAddr {
    type Output = Self;
    #[inline]
    fn add(self, rhs: usize) -> Self::Output {
        VirtAddr::new(self.0 + rhs)
    }
}

impl AddAssign<usize> for VirtAddr {
    #[inline]
    fn add_assign(&mut self, rhs: usize) {
        *self = *self + rhs;
    }
}

impl Sub<usize> for VirtAddr {
    type Output = Self;
    #[inline]
    fn sub(self, rhs: usize) -> Self::Output {
        VirtAddr::new(self.0.checked_sub(rhs).unwrap())
    }
}

impl SubAssign<usize> for VirtAddr {
    #[inline]
    fn sub_assign(&mut self, rhs: usize) {
        *self = *self - rhs;
    }
}

impl Sub<VirtAddr> for VirtAddr {
    type Output = usize;
    #[inline]
    fn sub(self, rhs: VirtAddr) -> Self::Output {
        self.as_usize().checked_sub(rhs.as_usize()).unwrap()
    }
}

/// A passed `usize` was not a valid physical address.
///
/// This means that bits 52 to 64 were not all null.
#[derive(Debug)]
pub struct PhysAddrNotValid(usize);

impl PhysAddr {
    /// Creates a new physical address.
    ///
    /// ## Panics
    ///
    /// This function panics if a bit in the range 52 to 64 is set.
    #[inline]
    pub fn new(addr: usize) -> PhysAddr {
        assert_eq!(
            addr.get_bits(52..64),
            0,
            "physical addresses must not have any bits in the range 52 to 64 set"
        );
        PhysAddr(addr)
    }

    /// Creates a new physical address, throwing bits 52..64 away.
    #[inline]
    #[cfg(target_arch = "x86_64")]
    pub const fn new_truncate(addr: usize) -> PhysAddr {
        PhysAddr(addr % (1 << 52))
    }

    /// Creates a new physical address.
    ///
    /// This function is identical to new on x86.
    #[inline]
    #[cfg(target_arch = "x86")]
    pub const fn new_truncate(addr: usize) -> PhysAddr {
        PhysAddr(addr)
    }

    /// Creates a new physical address, without any checks.
    ///
    /// ## Safety
    ///
    /// You must make sure bits 52..64 are zero. This is not checked.
    #[inline]
    pub const unsafe fn new_unsafe(addr: usize) -> PhysAddr {
        PhysAddr(addr)
    }

    /// Tries to create a new physical address.
    ///
    /// Fails if any bits in the range 52 to 64 are set.
    #[inline]
    #[cfg(target_arch = "x86_64")]
    pub fn try_new(addr: usize) -> Result<PhysAddr, PhysAddrNotValid> {
        match addr.get_bits(52..64) {
            0 => Ok(PhysAddr(addr)), // address is valid
            other => Err(PhysAddrNotValid(other)),
        }
    }

    /// Tries to create a new physical address.
    ///
    /// Will always succeed on x86.
    #[inline]
    #[cfg(target_arch = "x86")]
    pub fn try_new(addr: usize) -> Result<PhysAddr, PhysAddrNotValid> {
        Ok(PhysAddr(addr)) // address is valid
    }
    /// Creates a physical address that points to `0`.
    #[inline]
    pub const fn zero() -> PhysAddr {
        PhysAddr(0)
    }

    /// Converts the address to an `usize`.
    #[inline]
    pub const fn as_usize(self) -> usize {
        self.0
    }

    /// Convenience method for checking if a physical address is null.
    #[inline]
    pub const fn is_null(self) -> bool {
        self.0 == 0
    }

    /// Aligns the physical address upwards to the given alignment.
    ///
    /// See the `align_up` function for more information.
    #[inline]
    pub fn align_up<U>(self, align: U) -> Self
    where
        U: Into<usize>,
    {
        PhysAddr(align_up(self.0, align.into()))
    }

    /// Aligns the physical address downwards to the given alignment.
    ///
    /// See the `align_down` function for more information.
    #[inline]
    pub fn align_down<U>(self, align: U) -> Self
    where
        U: Into<usize>,
    {
        PhysAddr(align_down(self.0, align.into()))
    }

    /// Checks whether the physical address has the demanded alignment.
    #[inline]
    pub fn is_aligned<U>(self, align: U) -> bool
    where
        U: Into<usize>,
    {
        self.align_down(align) == self
    }
}

impl fmt::Debug for PhysAddr {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "PhysAddr({:#x})", self.0)
    }
}

impl fmt::Binary for PhysAddr {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.0.fmt(f)
    }
}

impl fmt::LowerHex for PhysAddr {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.0.fmt(f)
    }
}

impl fmt::Octal for PhysAddr {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.0.fmt(f)
    }
}

impl fmt::UpperHex for PhysAddr {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.0.fmt(f)
    }
}

impl Add<usize> for PhysAddr {
    type Output = Self;
    #[inline]
    fn add(self, rhs: usize) -> Self::Output {
        PhysAddr::new(self.0 + rhs)
    }
}

impl AddAssign<usize> for PhysAddr {
    #[inline]
    fn add_assign(&mut self, rhs: usize) {
        *self = *self + rhs;
    }
}

impl Sub<usize> for PhysAddr {
    type Output = Self;
    #[inline]
    fn sub(self, rhs: usize) -> Self::Output {
        PhysAddr::new(self.0.checked_sub(rhs).unwrap())
    }
}

impl SubAssign<usize> for PhysAddr {
    #[inline]
    fn sub_assign(&mut self, rhs: usize) {
        *self = *self - rhs;
    }
}

impl Sub<PhysAddr> for PhysAddr {
    type Output = usize;
    #[inline]
    fn sub(self, rhs: PhysAddr) -> Self::Output {
        self.as_usize().checked_sub(rhs.as_usize()).unwrap()
    }
}

/// Align address downwards.
///
/// Returns the greatest x with alignment `align` so that x <= addr. The alignment must be
///  a power of 2.
#[inline]
pub fn align_down(addr: usize, align: usize) -> usize {
    assert!(align.is_power_of_two(), "`align` must be a power of two");
    addr & !(align - 1)
}

/// Align address upwards.
///
/// Returns the smallest x with alignment `align` so that x >= addr. The alignment must be
/// a power of 2.
#[inline]
pub fn align_up(addr: usize, align: usize) -> usize {
    assert!(align.is_power_of_two(), "`align` must be a power of two");
    let align_mask = align - 1;
    if addr & align_mask == 0 {
        addr // already aligned
    } else {
        (addr | align_mask) + 1
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    pub fn virtaddr_new_truncate() {
        assert_eq!(VirtAddr::new_truncate(0), VirtAddr(0));
        assert_eq!(VirtAddr::new_truncate(1 << 47), VirtAddr(0xfffff << 47));
        assert_eq!(VirtAddr::new_truncate(123), VirtAddr(123));
        assert_eq!(VirtAddr::new_truncate(123 << 47), VirtAddr(0xfffff << 47));
    }

    #[test]
    pub fn test_align_up() {
        // align 1
        assert_eq!(align_up(0, 1), 0);
        assert_eq!(align_up(1234, 1), 1234);
        assert_eq!(align_up(0xffff_ffff_ffff_ffff, 1), 0xffff_ffff_ffff_ffff);
        // align 2
        assert_eq!(align_up(0, 2), 0);
        assert_eq!(align_up(1233, 2), 1234);
        assert_eq!(align_up(0xffff_ffff_ffff_fffe, 2), 0xffff_ffff_ffff_fffe);
        // address 0
        assert_eq!(align_up(0, 128), 0);
        assert_eq!(align_up(0, 1), 0);
        assert_eq!(align_up(0, 2), 0);
        assert_eq!(align_up(0, 0x8000_0000_0000_0000), 0);
    }
}
