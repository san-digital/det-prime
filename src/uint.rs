use core::cmp::Ordering;
use core::fmt;

use crate::Error;

/// Stack-allocated unsigned integer with `LIMBS` 64-bit little-endian limbs.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct Uint<const LIMBS: usize>(pub [u64; LIMBS]);

pub type U128 = Uint<2>;
pub type U256 = Uint<4>;
pub type U384 = Uint<6>;
pub type U512 = Uint<8>;
pub type U1024 = Uint<16>;
pub type U2048 = Uint<32>;
pub type U4096 = Uint<64>;

impl<const LIMBS: usize> Default for Uint<LIMBS> {
    fn default() -> Self {
        Self::ZERO
    }
}

impl<const LIMBS: usize> Ord for Uint<LIMBS> {
    #[inline]
    fn cmp(&self, other: &Self) -> Ordering {
        let mut i = LIMBS;
        while i > 0 {
            i -= 1;
            match self.0[i].cmp(&other.0[i]) {
                Ordering::Equal => continue,
                ord => return ord,
            }
        }
        Ordering::Equal
    }
}

impl<const LIMBS: usize> PartialOrd for Uint<LIMBS> {
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<const LIMBS: usize> fmt::Debug for Uint<LIMBS> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "0x")?;
        if self.is_zero() {
            return write!(f, "0");
        }
        let mut started = false;
        let mut i = LIMBS;
        while i > 0 {
            i -= 1;
            let w = self.0[i];
            if !started {
                if w != 0 {
                    write!(f, "{w:x}")?;
                    started = true;
                }
            } else {
                write!(f, "{w:016x}")?;
            }
        }
        Ok(())
    }
}

impl<const LIMBS: usize> fmt::Display for Uint<LIMBS> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(self, f)
    }
}

impl<const LIMBS: usize> Uint<LIMBS> {
    pub const ZERO: Self = Self([0u64; LIMBS]);

    #[inline]
    pub const fn from_limbs(limbs: [u64; LIMBS]) -> Self {
        Self(limbs)
    }

    pub const ONE: Self = {
        let mut limbs = [0u64; LIMBS];
        if LIMBS > 0 {
            limbs[0] = 1;
        }
        Self(limbs)
    };

    pub const TWO: Self = {
        let mut limbs = [0u64; LIMBS];
        if LIMBS > 0 {
            limbs[0] = 2;
        }
        Self(limbs)
    };

    #[inline]
    pub const fn from_u64(v: u64) -> Self {
        let mut limbs = [0u64; LIMBS];
        if LIMBS > 0 {
            limbs[0] = v;
        }
        Self(limbs)
    }

    #[inline]
    pub const fn as_u64(&self) -> Option<u64> {
        if LIMBS == 0 {
            return Some(0);
        }
        let mut i = 1;
        while i < LIMBS {
            if self.0[i] != 0 {
                return None;
            }
            i += 1;
        }
        Some(self.0[0])
    }

    #[inline]
    pub const fn is_zero(&self) -> bool {
        let mut i = 0;
        while i < LIMBS {
            if self.0[i] != 0 {
                return false;
            }
            i += 1;
        }
        true
    }

    #[inline]
    pub const fn is_one(&self) -> bool {
        if LIMBS == 0 || self.0[0] != 1 {
            return false;
        }
        let mut i = 1;
        while i < LIMBS {
            if self.0[i] != 0 {
                return false;
            }
            i += 1;
        }
        true
    }

    #[inline]
    pub const fn is_even(&self) -> bool {
        if LIMBS == 0 {
            true
        } else {
            (self.0[0] & 1) == 0
        }
    }

    #[inline]
    pub const fn is_odd(&self) -> bool {
        !self.is_even()
    }

    /// Parses a big-endian byte slice into `Uint<LIMBS>`.
    pub fn from_be_bytes(bytes: &[u8]) -> Result<Self, Error> {
        let first_nz = bytes.iter().position(|&b| b != 0).unwrap_or(bytes.len());
        let sig = &bytes[first_nz..];
        if sig.len() > LIMBS * 8 {
            return Err(Error::Overflow);
        }
        let mut limbs = [0u64; LIMBS];
        for (idx, &b) in sig.iter().rev().enumerate() {
            let limb_idx = idx / 8;
            let shift = (idx % 8) * 8;
            limbs[limb_idx] |= (b as u64) << shift;
        }
        Ok(Self(limbs))
    }

    /// Writes `self` into `out` as big-endian bytes if `out` is large enough.
    pub fn write_be_bytes(&self, out: &mut [u8]) -> Result<(), Error> {
        let needed = (self.bits() as usize).div_ceil(8);
        if out.len() < needed {
            return Err(Error::Overflow);
        }
        out.fill(0);
        let len = out.len();
        for idx in 0..needed {
            let limb_idx = idx / 8;
            let shift = (idx % 8) * 8;
            out[len - 1 - idx] = ((self.0[limb_idx] >> shift) & 0xff) as u8;
        }
        Ok(())
    }

    /// Parses an ASCII hexadecimal string (with optional `0x` prefix and `_` separators).
    pub fn from_hex(s: &str) -> Result<Self, Error> {
        let raw = s
            .strip_prefix("0x")
            .or_else(|| s.strip_prefix("0X"))
            .unwrap_or(s);
        if raw.is_empty() {
            return Err(Error::InvalidInput);
        }
        let mut acc = Self::ZERO;
        let mut saw_digit = false;
        for b in raw.bytes() {
            if b == b'_' {
                continue;
            }
            let nibble = match b {
                b'0'..=b'9' => b - b'0',
                b'a'..=b'f' => b - b'a' + 10,
                b'A'..=b'F' => b - b'A' + 10,
                _ => return Err(Error::InvalidInput),
            };
            saw_digit = true;
            acc = acc
                .checked_mul_u64(16)
                .and_then(|v| v.checked_add_u64(nibble as u64))
                .ok_or(Error::Overflow)?;
        }
        if !saw_digit {
            return Err(Error::InvalidInput);
        }
        Ok(acc)
    }

    /// Parses an ASCII base-10 string (with optional `_` separators).
    pub fn from_decimal(s: &str) -> Result<Self, Error> {
        if s.is_empty() {
            return Err(Error::InvalidInput);
        }
        let mut acc = Self::ZERO;
        let mut saw_digit = false;
        for b in s.bytes() {
            if b == b'_' {
                continue;
            }
            if !b.is_ascii_digit() {
                return Err(Error::InvalidInput);
            }
            saw_digit = true;
            acc = acc
                .checked_mul_u64(10)
                .and_then(|v| v.checked_add_u64((b - b'0') as u64))
                .ok_or(Error::Overflow)?;
        }
        if !saw_digit {
            return Err(Error::InvalidInput);
        }
        Ok(acc)
    }

    /// Bit length of `self` (`0` for `ZERO`).
    #[inline]
    pub const fn bits(&self) -> u32 {
        let mut i = LIMBS;
        while i > 0 {
            i -= 1;
            let w = self.0[i];
            if w != 0 {
                return (i as u32) * 64 + (64 - w.leading_zeros());
            }
        }
        0
    }

    /// Returns bit `idx` (0-indexed from least significant bit).
    #[inline]
    pub const fn bit(&self, idx: u32) -> bool {
        let limb = (idx / 64) as usize;
        let offset = idx % 64;
        if limb >= LIMBS {
            false
        } else {
            ((self.0[limb] >> offset) & 1) != 0
        }
    }

    /// Number of trailing zero bits (`64 * LIMBS` if `self == ZERO`).
    #[inline]
    pub const fn trailing_zeros(&self) -> u32 {
        let mut i = 0;
        while i < LIMBS {
            if self.0[i] != 0 {
                return (i as u32) * 64 + self.0[i].trailing_zeros();
            }
            i += 1;
        }
        (LIMBS as u32) * 64
    }

    /// Extracts `(k, m)` for `self >= 2` such that `bits = k + 1` and `m` is the top
    /// 4 fractional bits after the leading 1 bit (`2^k <= self < 2^k * (17 + m) / 16`).
    #[inline]
    pub const fn log2_mantissa4(&self) -> (u32, u32) {
        let b = self.bits();
        if b < 2 {
            return (0, 0);
        }
        let k = b - 1;
        let mut m = 0u32;
        let mut step = 0u32;
        while step < 4 {
            m <<= 1;
            if k > step && self.bit(k - 1 - step) {
                m |= 1;
            }
            step += 1;
        }
        (k, m)
    }

    #[inline]
    pub fn carrying_add(&self, rhs: &Self) -> (Self, bool) {
        let mut out = [0u64; LIMBS];
        let mut carry = 0u128;
        for (i, dst) in out.iter_mut().enumerate() {
            let sum = (self.0[i] as u128) + (rhs.0[i] as u128) + carry;
            *dst = sum as u64;
            carry = sum >> 64;
        }
        (Self(out), carry != 0)
    }

    #[inline]
    pub fn checked_add(&self, rhs: &Self) -> Option<Self> {
        let (sum, carry) = self.carrying_add(rhs);
        if carry {
            None
        } else {
            Some(sum)
        }
    }

    #[inline]
    pub fn checked_add_u64(&self, rhs: u64) -> Option<Self> {
        if LIMBS == 0 {
            return if rhs == 0 { Some(Self::ZERO) } else { None };
        }
        let mut out = self.0;
        let mut carry = rhs as u128;
        for limb in &mut out {
            if carry == 0 {
                break;
            }
            let sum = (*limb as u128) + carry;
            *limb = sum as u64;
            carry = sum >> 64;
        }
        if carry != 0 {
            None
        } else {
            Some(Self(out))
        }
    }

    #[inline]
    pub fn borrowing_sub(&self, rhs: &Self) -> (Self, bool) {
        let mut out = [0u64; LIMBS];
        let mut borrow = 0u128;
        for (i, dst) in out.iter_mut().enumerate() {
            let a = self.0[i] as u128;
            let b = (rhs.0[i] as u128) + borrow;
            if a >= b {
                *dst = (a - b) as u64;
                borrow = 0;
            } else {
                *dst = ((1u128 << 64) + a - b) as u64;
                borrow = 1;
            }
        }
        (Self(out), borrow != 0)
    }

    #[inline]
    pub fn checked_sub(&self, rhs: &Self) -> Option<Self> {
        let (diff, borrow) = self.borrowing_sub(rhs);
        if borrow {
            None
        } else {
            Some(diff)
        }
    }

    #[inline]
    pub fn wrapping_sub(&self, rhs: &Self) -> Self {
        self.borrowing_sub(rhs).0
    }

    #[inline]
    pub fn checked_mul_u64(&self, rhs: u64) -> Option<Self> {
        let mut out = [0u64; LIMBS];
        let mut carry = 0u128;
        for (i, dst) in out.iter_mut().enumerate() {
            let prod = (self.0[i] as u128) * (rhs as u128) + carry;
            *dst = prod as u64;
            carry = prod >> 64;
        }
        if carry != 0 {
            None
        } else {
            Some(Self(out))
        }
    }

    /// Remainder `self % d` for `d > 0`.
    #[inline]
    pub fn rem_u64(&self, d: u64) -> u64 {
        debug_assert!(d != 0);
        let mut rem = 0u128;
        let d128 = d as u128;
        let mut i = LIMBS;
        while i > 0 {
            i -= 1;
            rem = ((rem << 64) | (self.0[i] as u128)) % d128;
        }
        rem as u64
    }

    /// Right-shifts `self` by `bits` positions.
    pub fn shr(&self, shift: u32) -> Self {
        let total_bits = (LIMBS as u32) * 64;
        if shift >= total_bits {
            return Self::ZERO;
        }
        let word_shift = (shift / 64) as usize;
        let bit_shift = shift % 64;
        let mut out = [0u64; LIMBS];
        for (i, dst) in out.iter_mut().enumerate().take(LIMBS - word_shift) {
            let mut v = self.0[i + word_shift] >> bit_shift;
            if bit_shift != 0 && i + word_shift + 1 < LIMBS {
                v |= self.0[i + word_shift + 1] << (64 - bit_shift);
            }
            *dst = v;
        }
        Self(out)
    }

    #[inline]
    pub fn shr1_assign(&mut self) {
        let mut carry = 0u64;
        let mut i = LIMBS;
        while i > 0 {
            i -= 1;
            let next_carry = self.0[i] << 63;
            self.0[i] = (self.0[i] >> 1) | carry;
            carry = next_carry;
        }
    }

    /// Modular addition `(a + b) mod m`, assuming `a < m` and `b < m`.
    #[inline]
    pub fn add_mod(a: &Self, b: &Self, m: &Self) -> Self {
        let (sum, carry) = a.carrying_add(b);
        if carry || &sum >= m {
            sum.wrapping_sub(m)
        } else {
            sum
        }
    }

    /// Modular subtraction `(a - b) mod m`, assuming `a < m` and `b < m`.
    #[inline]
    pub fn sub_mod(a: &Self, b: &Self, m: &Self) -> Self {
        if a >= b {
            a.wrapping_sub(b)
        } else {
            let diff = b.wrapping_sub(a);
            m.wrapping_sub(&diff)
        }
    }

    /// Binary GCD (Stein's algorithm).
    pub fn gcd(&self, other: &Self) -> Self {
        if self.is_zero() {
            return *other;
        }
        if other.is_zero() {
            return *self;
        }
        let shift = self.trailing_zeros().min(other.trailing_zeros());
        let mut u = self.shr(self.trailing_zeros());
        let mut v = other.shr(other.trailing_zeros());
        loop {
            if u > v {
                core::mem::swap(&mut u, &mut v);
            }
            v = v.wrapping_sub(&u);
            if v.is_zero() {
                // Shift `u` left by `shift`.
                return u.shl_exact(shift);
            }
            v = v.shr(v.trailing_zeros());
        }
    }

    fn shl_exact(&self, shift: u32) -> Self {
        if shift == 0 {
            return *self;
        }
        let word_shift = (shift / 64) as usize;
        let bit_shift = shift % 64;
        let mut out = [0u64; LIMBS];
        for (i, dst) in out.iter_mut().enumerate().skip(word_shift) {
            let src = i - word_shift;
            let mut v = self.0[src] << bit_shift;
            if bit_shift != 0 && src > 0 {
                v |= self.0[src - 1] >> (64 - bit_shift);
            }
            *dst = v;
        }
        Self(out)
    }
}

/// Montgomery arithmetic context for an odd modulus `m > 1`.
#[derive(Clone, Copy, Debug)]
pub struct MontCtx<const LIMBS: usize> {
    m: Uint<LIMBS>,
    mu: u64,
    r2: Uint<LIMBS>,
    one_mont: Uint<LIMBS>,
    neg_one_mont: Uint<LIMBS>,
}

impl<const LIMBS: usize> MontCtx<LIMBS> {
    /// Builds a Montgomery context for an odd modulus `m >= 3`.
    pub fn new(m: Uint<LIMBS>) -> Option<Self> {
        if LIMBS == 0 || m.is_even() || m <= Uint::ONE {
            return None;
        }
        let m0 = m.0[0];
        let mut inv = 1u64;
        for _ in 0..6 {
            inv = inv.wrapping_mul(2u64.wrapping_sub(m0.wrapping_mul(inv)));
        }
        let mu = inv.wrapping_neg();

        // Compute R mod m (`one_mont`) and R^2 mod m (`r2`) by repeated modular doubling.
        let mut r = Uint::ONE;
        for _ in 0..(64 * LIMBS) {
            r = Uint::add_mod(&r, &r, &m);
        }
        let one_mont = r;
        for _ in 0..(64 * LIMBS) {
            r = Uint::add_mod(&r, &r, &m);
        }
        let r2 = r;
        let neg_one_mont = m.wrapping_sub(&one_mont);

        Some(Self {
            m,
            mu,
            r2,
            one_mont,
            neg_one_mont,
        })
    }

    #[inline]
    pub const fn modulus(&self) -> &Uint<LIMBS> {
        &self.m
    }

    #[inline]
    pub const fn one(&self) -> Uint<LIMBS> {
        self.one_mont
    }

    #[inline]
    pub const fn neg_one(&self) -> Uint<LIMBS> {
        self.neg_one_mont
    }

    /// Converts a reduced residue `0 <= x < m` into Montgomery form `x * R mod m`.
    #[inline]
    pub fn to_mont(&self, x: &Uint<LIMBS>) -> Uint<LIMBS> {
        self.mul(x, &self.r2)
    }

    /// Converts `u64` directly into `(x mod m) * R mod m`.
    #[inline]
    pub fn u64_to_mont(&self, x: u64) -> Uint<LIMBS> {
        let mut v = Uint::<LIMBS>::from_u64(x);
        if v >= self.m {
            // Only possible when LIMBS == 1 or m fits in u64.
            if let Some(m64) = self.m.as_u64() {
                v = Uint::from_u64(x % m64);
            }
        }
        self.to_mont(&v)
    }

    /// Converts out of Montgomery form `x * R^-1 mod m`.
    #[inline]
    pub fn from_mont(&self, x: &Uint<LIMBS>) -> Uint<LIMBS> {
        self.mul(x, &Uint::ONE)
    }

    /// CIOS Montgomery multiplication `(a * b * R^-1) mod m` for `0 <= a, b < m`.
    /// Handles full-width odd moduli up to `2^(64 * LIMBS) - 1`.
    #[inline(always)]
    #[allow(clippy::needless_range_loop)]
    pub fn mul(&self, a: &Uint<LIMBS>, b: &Uint<LIMBS>) -> Uint<LIMBS> {
        let mut t = [0u64; LIMBS];
        let mut t_extra: u128 = 0;

        for i in 0..LIMBS {
            let mut carry: u128 = 0;
            let ai = a.0[i] as u128;
            for j in 0..LIMBS {
                let prod = (t[j] as u128) + ai * (b.0[j] as u128) + carry;
                t[j] = prod as u64;
                carry = prod >> 64;
            }
            let sum_hi = t_extra + carry;

            let q = t[0].wrapping_mul(self.mu) as u128;
            let prod0 = (t[0] as u128) + q * (self.m.0[0] as u128);
            let mut carry2: u128 = prod0 >> 64;
            for j in 1..LIMBS {
                let prod = (t[j] as u128) + q * (self.m.0[j] as u128) + carry2;
                t[j - 1] = prod as u64;
                carry2 = prod >> 64;
            }
            let top = sum_hi + carry2;
            t[LIMBS - 1] = top as u64;
            t_extra = top >> 64;
        }

        let res = Uint(t);
        if t_extra != 0 || res >= self.m {
            res.wrapping_sub(&self.m)
        } else {
            res
        }
    }

    #[inline(always)]
    pub fn sqr(&self, a: &Uint<LIMBS>) -> Uint<LIMBS> {
        self.mul(a, a)
    }

    /// Modular exponentiation `base^exp` in Montgomery domain using a 4-bit sliding odd window.
    pub fn pow(&self, base_mont: &Uint<LIMBS>, exp: &Uint<LIMBS>) -> Uint<LIMBS> {
        let top = exp.bits();
        if top == 0 {
            return self.one_mont;
        }
        if top < 16 {
            let mut result = *base_mont;
            let mut i = top - 1;
            while i > 0 {
                i -= 1;
                result = self.sqr(&result);
                if exp.bit(i) {
                    result = self.mul(&result, base_mont);
                }
            }
            return result;
        }

        let b2 = self.sqr(base_mont);
        let mut odd = [*base_mont; 8];
        let mut k = 1usize;
        while k < 8 {
            odd[k] = self.mul(&odd[k - 1], &b2);
            k += 1;
        }

        let mut result = self.one_mont;
        let mut started = false;
        let mut i = top;
        while i > 0 {
            if !exp.bit(i - 1) {
                result = self.sqr(&result);
                i -= 1;
            } else {
                let win_len = if i >= 4 { 4 } else { i };
                let mut w = 0u32;
                let mut bit_off = 0u32;
                while bit_off < win_len {
                    w = (w << 1) | (exp.bit(i - 1 - bit_off) as u32);
                    bit_off += 1;
                }
                let tz = w.trailing_zeros();
                let eff_len = win_len - tz;
                let odd_val = w >> tz;
                if !started {
                    result = odd[(odd_val >> 1) as usize];
                    started = true;
                } else {
                    for _ in 0..eff_len {
                        result = self.sqr(&result);
                    }
                    result = self.mul(&result, &odd[(odd_val >> 1) as usize]);
                }
                i -= eff_len;
            }
        }
        result
    }
}
