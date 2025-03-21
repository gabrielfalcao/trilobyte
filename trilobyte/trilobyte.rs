use crate::errors::TriloByteParseError;

/// `TriloByte` is a data-structure representing `3` bits, primarily
/// designed for representing masks and the `3` role permissions of
/// unix files (user, group and other).
///
/// For example, a unix file with mode `007` can be represented with
/// `3` trilobytes:
///
/// ```
/// use trilobyte::TriloByte;
///
/// let trilobytes = [
///     TriloByte(false, false, false),
///     TriloByte(false, false, false),
///     TriloByte(true, true, true),
/// ];
/// let mode = trilobytes.iter().map(|t| t.to_string_octal()).collect::<String>();
/// assert_eq!(mode, "007");
/// ```
///

#[derive(Clone, PartialEq, Eq, Hash, Copy)]
pub struct TriloByte(pub bool, pub bool, pub bool);

/// `high_water_mark_u8_to_trilobyte` reduces [`u8`] to `3` bits so as to fit in one [`TriloByte`].
pub fn high_water_mark_u8_to_trilobyte(val: u8) -> u8 {
    if val <= 0b111 {
        return val;
    } else {
        high_water_mark_u8_to_trilobyte(val - 0b1000)
    }
}

impl TriloByte {
    pub const MAX: u8 = 7;
    pub const MIN: u8 = 0;

    /// `from_u8` creates a new [`TriloByte`] from a [`u8`], returns
    /// [`TriloByteParseError`] if the [`u8`] value is greater than
    /// `7`, unlike [`from_u8_highwatermark`](#method.from_u8_highwatermark).
    ///
    /// Example:
    /// ```
    /// use trilobyte::TriloByte;
    ///
    /// let trilobyte = TriloByte::from_u8(3).unwrap();
    /// assert_eq!(trilobyte.to_string(), "011");
    /// ```
    pub fn from_u8(val: u8) -> Result<TriloByte, TriloByteParseError> {
        if val > Self::MAX {
            return Err(TriloByteParseError(format!("{} higher than {}", val, Self::MAX), val));
        }
        Ok(TriloByte::from_u8_highwatermark(val))
    }

    /// `from_u8_highwatermark` creates a new [`TriloByte`] from a
    /// [`u8`] shrinking it down to `3` bits if the given [`u8`] value
    /// is greater than `7` (i.e.: `0b111`)
    ///
    /// Example:
    /// ```
    /// use trilobyte::TriloByte;
    ///
    /// let trilobyte = TriloByte::from_u8_highwatermark(4);
    /// assert_eq!(trilobyte.to_string(), "100");
    /// ```
    pub fn from_u8_highwatermark(val: u8) -> TriloByte {
        let val = high_water_mark_u8_to_trilobyte(val);
        TriloByte(
            (val >> 0b010 & !0b110) == 0b1,
            (val >> 0b001 & !0b010) == 0b1,
            (val >> 0b000 & !0b110) == 0b1,
        )
    }

    /// `to_array` returns [`array`] of length `3` where each u8 is either 0 or 1.
    /// `from_u8_highwatermark` creates a new [`TriloByte`] from a
    /// [`u8`] shrinking it down to `3` bits if the given [`u8`] value
    /// is greater than `7` (i.e.: `0b111`)
    ///
    /// Example:
    /// ```
    /// use trilobyte::TriloByte;
    ///
    /// let trilobyte = TriloByte(false, true, true);
    /// assert_eq!(trilobyte.to_array(), [0, 1, 1]);
    /// ```
    pub fn to_array(self) -> [u8; 3] {
        [self.0 as u8, self.1 as u8, self.2 as u8]
    }

    /// `to_tuple` returns [`tuple`] of length `3` where each u8 is either 0 or 1.
    ///
    /// Example:
    /// ```
    /// use trilobyte::TriloByte;
    ///
    /// let trilobyte = TriloByte(false, true, false);
    /// assert_eq!(trilobyte.to_tuple(), (0, 1, 0));
    /// ```
    pub fn to_tuple(self) -> (u8, u8, u8) {
        self.to_array().into()
    }

    /// `into_string` returns [`String`] representing the [`TriloByte`] as `3` sequential bits.
    ///
    /// Example:
    /// ```
    /// use trilobyte::TriloByte;
    ///
    /// let trilobyte = TriloByte::from(5);
    /// assert_eq!(trilobyte.into_string(), "101");
    /// ```
    pub fn into_string(self) -> String {
        self.to_array().iter().map(|b| b.to_string()).collect()
    }

    /// `into_u32` returns a value [`u32`] represented by a [`TriloByte`].
    ///
    /// Example:
    /// ```
    /// use trilobyte::TriloByte;
    ///
    /// let trilobyte = TriloByte::from(7);
    /// assert_eq!(trilobyte.into_u32(), 7);
    /// ```
    pub fn into_u32(self) -> u32 {
        u32::from_str_radix(&self.into_string(), 2).unwrap()
    }

    /// `into_u8` returns a value [`u8`] represented by a [`TriloByte`].
    ///
    /// Example:
    /// ```
    /// use trilobyte::TriloByte;
    ///
    /// let trilobyte = TriloByte::from(7);
    /// assert_eq!(trilobyte.into_u8(), 7);
    /// ```
    pub fn into_u8(self) -> u8 {
        u8::from_str_radix(&self.into_string(), 2).unwrap()
    }

    /// `to_string_octal` returns [`String`] representing the [`TriloByte`] as octal number.
    ///
    /// Example:
    /// ```
    /// use trilobyte::TriloByte;
    ///
    /// let trilobyte = TriloByte::from(5);
    /// assert_eq!(trilobyte.to_string_octal(), "5");
    /// ```
    pub fn to_string_octal(self) -> String {
        self.into_u8().to_string()
    }

    /// `rewrite_from` rewrites a [`TriloByte`] with the values of another [`TriloByte`]
    ///
    /// Example:
    /// ```
    /// use trilobyte::TriloByte;
    ///
    /// let mut trilobyte = TriloByte(true, false, true);
    /// assert_eq!(trilobyte.to_string(), "101");
    /// trilobyte.rewrite_from(&TriloByte(false, true, false));
    /// assert_eq!(trilobyte.to_string(), "010");
    /// ```
    pub fn rewrite_from(&mut self, other: &Self) {
        self.0 = other.0;
        self.1 = other.1;
        self.2 = other.2;
    }
}

impl std::cmp::PartialOrd for TriloByte {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        self.into_u8().partial_cmp(&other.into_u8())
    }
}
impl std::cmp::Ord for TriloByte {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.into_u8().cmp(&other.into_u8())
    }
}
impl From<u8> for TriloByte {
    fn from(val: u8) -> TriloByte {
        TriloByte::from_u8_highwatermark(val)
    }
}
impl Into<String> for TriloByte {
    fn into(self) -> String {
        self.into_string()
    }
}

impl Into<u32> for TriloByte {
    fn into(self) -> u32 {
        self.into_u32()
    }
}
impl Into<u8> for TriloByte {
    fn into(self) -> u8 {
        self.into_u8()
    }
}

impl std::fmt::Display for TriloByte {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{}", self.into_string())
    }
}

impl std::fmt::Debug for TriloByte {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "TriloByte[{}]", self.into_string())
    }
}

impl std::ops::Not for TriloByte {
    type Output = TriloByte;

    fn not(self) -> TriloByte {
        TriloByte::from(!self.into_u8())
    }
}

impl std::ops::BitAnd for TriloByte {
    type Output = TriloByte;

    fn bitand(self, rhs: TriloByte) -> TriloByte {
        TriloByte::from(self.into_u8() & rhs.into_u8())
    }
}

impl std::ops::BitOr for TriloByte {
    type Output = TriloByte;

    fn bitor(self, rhs: TriloByte) -> TriloByte {
        TriloByte::from(self.into_u8() | rhs.into_u8())
    }
}

impl std::ops::BitXor for TriloByte {
    type Output = TriloByte;

    fn bitxor(self, rhs: TriloByte) -> TriloByte {
        TriloByte::from(self.into_u8() ^ rhs.into_u8())
    }
}

impl std::ops::Shr for TriloByte {
    type Output = TriloByte;

    fn shr(self, rhs: TriloByte) -> TriloByte {
        TriloByte::from(self.into_u8() >> rhs.into_u8())
    }
}

impl std::ops::Shl for TriloByte {
    type Output = TriloByte;

    fn shl(self, rhs: TriloByte) -> TriloByte {
        TriloByte::from(self.into_u8() << rhs.into_u8())
    }
}

impl std::ops::BitAndAssign for TriloByte {
    fn bitand_assign(&mut self, rhs: TriloByte) {
        self.rewrite_from(&(*self & rhs));
    }
}

impl std::ops::BitOrAssign for TriloByte {
    fn bitor_assign(&mut self, rhs: TriloByte) {
        self.rewrite_from(&(*self | rhs));
    }
}

impl std::ops::BitXorAssign for TriloByte {
    fn bitxor_assign(&mut self, rhs: TriloByte) {
        self.rewrite_from(&(*self ^ rhs));
    }
}

impl std::ops::ShrAssign for TriloByte {
    fn shr_assign(&mut self, rhs: TriloByte) {
        self.rewrite_from(&(*self >> rhs));
    }
}

impl std::ops::ShlAssign for TriloByte {
    fn shl_assign(&mut self, rhs: TriloByte) {
        self.rewrite_from(&(*self << rhs));
    }
}

#[cfg(test)]
mod test_high_water_mark_u8_to_trilobyte {
    use crate::{assert_bits_eq, high_water_mark_u8_to_trilobyte};

    #[test]
    fn test_high_water_mark_u8_to_trilobyte() {
        assert_bits_eq!(high_water_mark_u8_to_trilobyte(0b1001), 0b001);
        assert_bits_eq!(high_water_mark_u8_to_trilobyte(0b1010), 0b010);

        assert_bits_eq!(high_water_mark_u8_to_trilobyte(0b11111001), 0b001);
        assert_bits_eq!(high_water_mark_u8_to_trilobyte(0b11111010), 0b010);
        assert_bits_eq!(high_water_mark_u8_to_trilobyte(0b11111100), 0b100);
        assert_bits_eq!(high_water_mark_u8_to_trilobyte(0b11111101), 0b101);
        assert_bits_eq!(high_water_mark_u8_to_trilobyte(0b11111110), 0b110);
        assert_bits_eq!(high_water_mark_u8_to_trilobyte(0b11111111), 0b111);
    }
}

#[cfg(test)]
mod test_trilobyte {
    use crate::{TriloByte, TriloByteParseError};

    #[test]
    fn test_from_u8() {
        assert_eq!(TriloByte::from_u8(0b111), Ok(TriloByte(true, true, true)));
        assert_eq!(TriloByte::from_u8(0b110), Ok(TriloByte(true, true, false)));
        assert_eq!(TriloByte::from_u8(0b101), Ok(TriloByte(true, false, true)));
        assert_eq!(TriloByte::from_u8(0b100), Ok(TriloByte(true, false, false)));
        assert_eq!(TriloByte::from_u8(0b011), Ok(TriloByte(false, true, true)));
        assert_eq!(TriloByte::from_u8(0b010), Ok(TriloByte(false, true, false)));
        assert_eq!(TriloByte::from_u8(0b001), Ok(TriloByte(false, false, true)));
        assert_eq!(TriloByte::from_u8(0b000), Ok(TriloByte(false, false, false)));
        assert_eq!(
            TriloByte::from_u8(0x008),
            Err(TriloByteParseError("8 higher than 7".to_string(), 0b1000))
        );
    }

    #[test]
    fn test_trait_from_u8() {
        assert_eq!(TriloByte::from_u8(0b111).unwrap(), TriloByte(true, true, true));
        assert_eq!(TriloByte::from_u8(0b110).unwrap(), TriloByte(true, true, false));
        assert_eq!(TriloByte::from_u8(0b101).unwrap(), TriloByte(true, false, true));
        assert_eq!(TriloByte::from_u8(0b100).unwrap(), TriloByte(true, false, false));
        assert_eq!(TriloByte::from_u8(0b011).unwrap(), TriloByte(false, true, true));
        assert_eq!(TriloByte::from_u8(0b010).unwrap(), TriloByte(false, true, false));
        assert_eq!(TriloByte::from_u8(0b001).unwrap(), TriloByte(false, false, true));
        assert_eq!(TriloByte::from_u8(0b000).unwrap(), TriloByte(false, false, false));
    }

    #[test]
    fn test_to_array() {
        assert_eq!(TriloByte(true, true, true).to_array(), [1, 1, 1]);
        assert_eq!(TriloByte(true, true, false).to_array(), [1, 1, 0]);
        assert_eq!(TriloByte(true, false, true).to_array(), [1, 0, 1]);
        assert_eq!(TriloByte(true, false, false).to_array(), [1, 0, 0]);
        assert_eq!(TriloByte(false, true, true).to_array(), [0, 1, 1]);
        assert_eq!(TriloByte(false, true, false).to_array(), [0, 1, 0]);
        assert_eq!(TriloByte(false, false, true).to_array(), [0, 0, 1]);
        assert_eq!(TriloByte(false, false, false).to_array(), [0, 0, 0]);
    }

    #[test]
    fn test_to_tuple() {
        assert_eq!(TriloByte(true, true, true).to_tuple(), (1, 1, 1));
        assert_eq!(TriloByte(true, true, false).to_tuple(), (1, 1, 0));
        assert_eq!(TriloByte(true, false, true).to_tuple(), (1, 0, 1));
        assert_eq!(TriloByte(true, false, false).to_tuple(), (1, 0, 0));
        assert_eq!(TriloByte(false, true, true).to_tuple(), (0, 1, 1));
        assert_eq!(TriloByte(false, true, false).to_tuple(), (0, 1, 0));
        assert_eq!(TriloByte(false, false, true).to_tuple(), (0, 0, 1));
        assert_eq!(TriloByte(false, false, false).to_tuple(), (0, 0, 0));
    }
    #[test]
    fn test_to_string() {
        assert_eq!(TriloByte(true, true, true).to_string(), "111");
        assert_eq!(TriloByte(true, true, false).to_string(), "110");
        assert_eq!(TriloByte(true, false, true).to_string(), "101");
        assert_eq!(TriloByte(true, false, false).to_string(), "100");
        assert_eq!(TriloByte(false, true, true).to_string(), "011");
        assert_eq!(TriloByte(false, true, false).to_string(), "010");
        assert_eq!(TriloByte(false, false, true).to_string(), "001");
        assert_eq!(TriloByte(false, false, false).to_string(), "000");
    }
    #[test]
    fn test_from_u8_highwatermark() {
        assert_eq!(TriloByte::from_u8_highwatermark(0b001), TriloByte(false, false, true));

        assert_eq!(TriloByte::from_u8_highwatermark(0b11111001), TriloByte(false, false, true));

        assert_eq!(TriloByte::from_u8_highwatermark(0b111), TriloByte(true, true, true));

        assert_eq!(TriloByte::from_u8_highwatermark(0b10000111), TriloByte(true, true, true));
        assert_eq!(TriloByte::from_u8_highwatermark(0b10000000), TriloByte(false, false, false));
        assert_eq!(TriloByte::from_u8_highwatermark(0b10000100), TriloByte(true, false, false));
        assert_eq!(TriloByte::from_u8_highwatermark(0b10000110), TriloByte(true, true, false));
        assert_eq!(TriloByte::from_u8_highwatermark(0b10000111), TriloByte(true, true, true));
        assert_eq!(TriloByte::from_u8_highwatermark(0b11001000), TriloByte(false, false, false));
        assert_eq!(TriloByte::from_u8_highwatermark(0b11001001), TriloByte(false, false, true));
        assert_eq!(TriloByte::from_u8_highwatermark(0b11001010), TriloByte(false, true, false));
        assert_eq!(TriloByte::from_u8_highwatermark(0b11001100), TriloByte(true, false, false));
        assert_eq!(TriloByte::from_u8_highwatermark(0b11011001), TriloByte(false, false, true));
        assert_eq!(TriloByte::from_u8_highwatermark(0b11011010), TriloByte(false, true, false));
        assert_eq!(TriloByte::from_u8_highwatermark(0b11011100), TriloByte(true, false, false));
        assert_eq!(TriloByte::from_u8_highwatermark(0b11111001), TriloByte(false, false, true));
        assert_eq!(TriloByte::from_u8_highwatermark(0b11111010), TriloByte(false, true, false));
        assert_eq!(TriloByte::from_u8_highwatermark(0b11111100), TriloByte(true, false, false));
    }

    #[test]
    fn test_into_u32() {
        assert_eq!(TriloByte::from(0b111).into_u32(), 7);
        assert_eq!(TriloByte::from(0b110).into_u32(), 6);
        assert_eq!(TriloByte::from(0b101).into_u32(), 5);
        assert_eq!(TriloByte::from(0b100).into_u32(), 4);
        assert_eq!(TriloByte::from(0b011).into_u32(), 3);
        assert_eq!(TriloByte::from(0b010).into_u32(), 2);
        assert_eq!(TriloByte::from(0b001).into_u32(), 1);
        assert_eq!(TriloByte::from(0b000).into_u32(), 0);
        assert_eq!(Into::<u32>::into(TriloByte::from(0b111)), 7);
        assert_eq!(Into::<u32>::into(TriloByte::from(0b110)), 6);
        assert_eq!(Into::<u32>::into(TriloByte::from(0b101)), 5);
        assert_eq!(Into::<u32>::into(TriloByte::from(0b100)), 4);
        assert_eq!(Into::<u32>::into(TriloByte::from(0b011)), 3);
        assert_eq!(Into::<u32>::into(TriloByte::from(0b010)), 2);
        assert_eq!(Into::<u32>::into(TriloByte::from(0b001)), 1);
        assert_eq!(Into::<u32>::into(TriloByte::from(0b000)), 0);
    }
    #[test]
    fn test_into_u8() {
        assert_eq!(TriloByte::from(0b111).into_u8(), 7);
        assert_eq!(TriloByte::from(0b110).into_u8(), 6);
        assert_eq!(TriloByte::from(0b101).into_u8(), 5);
        assert_eq!(TriloByte::from(0b100).into_u8(), 4);
        assert_eq!(TriloByte::from(0b011).into_u8(), 3);
        assert_eq!(TriloByte::from(0b010).into_u8(), 2);
        assert_eq!(TriloByte::from(0b001).into_u8(), 1);
        assert_eq!(TriloByte::from(0b000).into_u8(), 0);

        assert_eq!(Into::<u8>::into(TriloByte::from(0b111)), 7);
        assert_eq!(Into::<u8>::into(TriloByte::from(0b110)), 6);
        assert_eq!(Into::<u8>::into(TriloByte::from(0b101)), 5);
        assert_eq!(Into::<u8>::into(TriloByte::from(0b100)), 4);
        assert_eq!(Into::<u8>::into(TriloByte::from(0b011)), 3);
        assert_eq!(Into::<u8>::into(TriloByte::from(0b010)), 2);
        assert_eq!(Into::<u8>::into(TriloByte::from(0b001)), 1);
        assert_eq!(Into::<u8>::into(TriloByte::from(0b000)), 0);
    }
    #[test]
    fn test_to_string_octal() {
        assert_eq!(TriloByte::from(0b111).to_string_octal(), "7");
        assert_eq!(TriloByte::from(0b110).to_string_octal(), "6");
        assert_eq!(TriloByte::from(0b101).to_string_octal(), "5");
        assert_eq!(TriloByte::from(0b100).to_string_octal(), "4");
        assert_eq!(TriloByte::from(0b011).to_string_octal(), "3");
        assert_eq!(TriloByte::from(0b010).to_string_octal(), "2");
        assert_eq!(TriloByte::from(0b001).to_string_octal(), "1");
        assert_eq!(TriloByte::from(0b000).to_string_octal(), "0");
    }
    #[test]
    fn test_order() {
        let unsorted = vec![
            TriloByte::from(0b111),
            TriloByte::from(0b101),
            TriloByte::from(0b100),
            TriloByte::from(0b011),
            TriloByte::from(0b110),
            TriloByte::from(0b001),
            TriloByte::from(0b010),
            TriloByte::from(0b000),
        ];
        let sorted = vec![
            TriloByte::from(0b000),
            TriloByte::from(0b001),
            TriloByte::from(0b010),
            TriloByte::from(0b011),
            TriloByte::from(0b100),
            TriloByte::from(0b101),
            TriloByte::from(0b110),
            TriloByte::from(0b111),
        ];
        let mut result = unsorted.clone();
        result.sort();
        assert_eq!(result, sorted);
    }
    #[test]
    fn test_xor() {
        assert_eq!(TriloByte::from(0b111) ^ TriloByte::from(0b111), TriloByte::from(0b000));
        assert_eq!(TriloByte::from(0b111) ^ TriloByte::from(0b010), TriloByte::from(0b101));
        assert_eq!(TriloByte::from(0b011) ^ TriloByte::from(0b110), TriloByte::from(0b101));
    }

    #[test]
    fn test_trilobyte_and() {
        assert_eq!(TriloByte::from(0b101) & TriloByte::from(0b101), TriloByte::from(0b101));
    }

    #[test]
    fn test_trilobyte_or() {
        assert_eq!(TriloByte::from(0) | TriloByte::from(1), TriloByte::from(1));
        assert_eq!(TriloByte::from(1) | TriloByte::from(0), TriloByte::from(1));
    }

    #[test]
    fn test_trilobyte_shr() {
        assert_eq!(TriloByte::from(0b101) >> TriloByte::from(1), TriloByte::from(0b10));
    }

    #[test]
    fn test_trilobyte_shl() {
        assert_eq!(TriloByte::from(0b1) << TriloByte::from(2), TriloByte::from(0b100));
    }

    #[test]
    fn test_trilobyte_xor() {
        assert_eq!(TriloByte::from(0b100) ^ TriloByte::from(0b001), TriloByte::from(0b101));
    }

    #[test]
    fn test_rewrite_from() {
        let mut trilobyte = TriloByte::from(0b100);
        trilobyte.rewrite_from(&TriloByte::from(0b101));
        assert_eq!(trilobyte, TriloByte::from(0b101));
    }

    #[test]
    fn test_trilobyte_and_assign() {
        let mut value = TriloByte::from(0b101);
        value &= TriloByte::from(0b101);
        assert_eq!(value, TriloByte::from(0b101));
    }

    #[test]
    fn test_trilobyte_or_assign() {
        let mut value = TriloByte::from(0);
        value |= TriloByte::from(1);
        assert_eq!(value, TriloByte::from(1));
    }

    #[test]
    fn test_trilobyte_shr_assign() {
        let mut value = TriloByte::from(0b101);
        value >>= TriloByte::from(1);
        assert_eq!(value, TriloByte::from(0b10));
    }

    #[test]
    fn test_trilobyte_shl_assign() {
        let mut value = TriloByte::from(0b1);
        value <<= TriloByte::from(2);
        assert_eq!(value, TriloByte::from(0b100));
    }

    #[test]
    fn test_trilobyte_xor_assign() {
        let mut value = TriloByte::from(0b100);
        value ^= TriloByte::from(0b001);
        assert_eq!(value, TriloByte::from(0b101));
    }
}
