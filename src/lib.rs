#![cfg_attr(not(test), no_std)]

use core::ops::{Add, Not, Sub};

// [l4, l3, l2, l1]
// l1 = least significant limb
// l4 = most significant limb
#[repr(C)]
#[derive(Eq, PartialEq, PartialOrd, Debug, Copy, Clone)]
pub struct U256([u64; 4]);

impl U256 {
    pub const MAX: U256 = U256([u64::MAX, u64::MAX, u64::MAX, u64::MAX]);
    pub const ZERO: U256 = U256([0x00, 0x00, 0x00, 0x00]);
    pub const ONE: U256 = U256([0x00, 0x00, 0x00, 0x01]);

    pub fn new() -> U256 {
        U256::ZERO
    }

    pub fn from_digits(value: [u64; 4]) -> U256 {
        let mut v = U256::new();
        let U256(ref mut this) = v;

        for i in 0..4 {
            this[i] = value[i];
        }
        v
    }

    fn char_to_value(c: char) -> u8 {
        match c {
            '0' => 0x00,
            '1' => 0x01,
            '2' => 0x02,
            '3' => 0x03,
            '4' => 0x04,
            '5' => 0x05,
            '6' => 0x06,
            '7' => 0x07,
            '8' => 0x08,
            '9' => 0x09,
            'a' => 0x0A,
            'b' => 0x0B,
            'c' => 0x0C,
            'd' => 0x0D,
            'e' => 0x0E,
            'f' => 0x0F,
            'A' => 0x0A,
            'B' => 0x0B,
            'C' => 0x0C,
            'D' => 0x0D,
            'E' => 0x0E,
            'F' => 0x0F,
            _ => panic!("invalid hex digit"),
        }
    }

    pub fn from_hex_string(hex_string: &str) -> U256 {
        let l = hex_string.len();
        if l == 0 {
            panic!("invalid empty string");
        }

        if l > 64 {
            panic!("invalid hex string length");
        }

        let mut value = U256::new();
        let U256(ref mut this) = value;

        let mut chars = hex_string.chars().rev();

        let mut pos_inside_limb: usize = 0;
        let mut limb: usize = 3;

        while let Some(c) = chars.next() {
            let val = U256::char_to_value(c);
            let val64 = (val as u64) << (pos_inside_limb * 4);

            this[limb] |= val64;

            pos_inside_limb += 1;

            if pos_inside_limb == 16 {
                pos_inside_limb = 0;
                limb -= 1;
            }
        }

        value
    }

    pub fn overflowing_add(self, other: U256) -> (U256, bool) {
        let U256(ref left) = self;
        let U256(ref right) = other;

        let mut ret = U256::ZERO;
        let U256(ref mut result) = ret;

        let mut carry: u64 = 0;
        for i in (0..4).rev() {
            let (value, carry1) = left[i].overflowing_add(right[i]);
            let (value, carry2) = value.overflowing_add(carry);

            result[i] = value;
            carry = if carry1 || carry2 { 1 } else { 0 }
        }

        (ret, carry > 0)
    }
}

impl Add for U256 {
    type Output = Self;

    fn add(self, other: Self) -> Self {
        let (o, v) = self.overflowing_add(other);
        if v {
            panic!("overflow");
        }
        o
    }
}

impl Sub for U256 {
    type Output = Self;

    //    #[inline]
    fn sub(self, other: Self) -> Self {
        if self == other {
            return U256::ZERO;
        }

        if self < other {
            panic!("underflow");
        }

        let not_other = !other;
        let (value, _o) = self.overflowing_add(not_other);

        let (value_plus_one, _o) = value.overflowing_add(U256::ONE);

        value_plus_one
    }
}

impl Not for U256 {
    type Output = Self;

    fn not(self) -> Self {
        let U256(ref this) = self;

        let mut r = U256::new();
        let U256(ref mut ret) = r;

        for i in (0..4).rev() {
            ret[i] = !this[i];
        }
        r
    }
}

#[cfg(test)]
mod tests {

    use proptest::prelude::*;
    use rug::{integer::Order, Integer};

    use super::U256;

    impl Arbitrary for U256 {
        type Parameters = ();
        type Strategy = BoxedStrategy<Self>;

        fn arbitrary_with(_: Self::Parameters) -> Self::Strategy {
            let strategy = (0..4).prop_map(|_| {
                let digits = [
                    rand::random(),
                    rand::random(),
                    rand::random(),
                    rand::random(),
                ];
                U256::from_digits(digits)
            });
            strategy.boxed()
        }
    }

    #[test]
    fn add_1() {
        let a = U256([0, 0, 0, 0]);
        let b = U256([0, 0, 0, 0]);

        assert_eq!(a + b, U256([0, 0, 0, 0]));
    }

    #[test]
    fn add_2() {
        let a = U256([1, 0, 0, 0]);
        let b = U256([0, 0, 0, 1]);

        assert_eq!(a + b, U256([1, 0, 0, 1]));
    }

    #[test]
    fn add_3() {
        let a = U256([0, 0, 0, 0xFFFFFFFFFFFFFFFF]);
        let b = U256([0, 0, 0, 1]);

        assert_eq!(a + b, U256([0, 0, 1, 0]));
    }

    #[test]
    fn add_4() {
        let a = U256([0, 0, 0xFFFFFFFFFFFFFFFF, 0]);
        let b = U256([0, 0, 1, 0]);

        assert_eq!(a + b, U256([0, 1, 0, 0]));
    }

    #[test]
    fn add_5() {
        let a = U256([0, 0xFFFFFFFFFFFFFFFF, 0, 0]);
        let b = U256([0, 1, 0, 0]);

        assert_eq!(a + b, U256([1, 0, 0, 0]));
    }

    #[test]
    fn add_6() {
        let a = U256([
            0xFFFFFFFFFFFFFFFE,
            0xFFFFFFFFFFFFFFFF,
            0xFFFFFFFFFFFFFFFF,
            0xFFFFFFFFFFFFFFFF,
        ]);
        let b = U256([0, 0, 0, 1]);

        assert_eq!(a + b, U256([0xFFFFFFFFFFFFFFFF, 0, 0, 0]));
    }

    #[test]
    fn add_7() {
        let a = U256([
            0,
            0xFFFFFFFFFFFFFFFF,
            0xFFFFFFFFFFFFFFFF,
            0xFFFFFFFFFFFFFFFF,
        ]);
        let b = U256([0, 0, 0, 1]);

        assert_eq!(a + b, U256([1, 0, 0, 0]));
    }

    #[test]
    #[should_panic(expected = "overflow")]
    fn add_with_overflow() {
        let a = U256([0xFFFFFFFFFFFFFFFF, 0, 0, 0]);
        let b = U256([1, 0, 0, 0]);

        let _c = a + b;
    }

    const NUM_CASES: u32 = 100;

    proptest! {
        #![proptest_config(ProptestConfig::with_cases(NUM_CASES))]

        #[test]
        fn u256_addition_is_commutative(a in any::<U256>(), b in any::<U256>()) {
            let (sum1, ov1) = a.overflowing_add(b);
            let (sum2, ov2) = b.overflowing_add(a);
            assert_eq!(ov1, ov2);
            assert_eq!(sum1, sum2);

            let big_int_expected_sum = to_big_integer(sum1);

            let big_int_a = to_big_integer(a);
            let big_int_b = to_big_integer(b);
            let big_int_sum = big_int_a + big_int_b;

            if ov1 {
                assert!(big_int_sum > big_int_expected_sum)
            }
            else {
                assert_eq!(big_int_sum, big_int_expected_sum);
            }
        }
    }

    fn to_big_integer(u: U256) -> Integer {
        Integer::from_digits(&u.0, Order::Msf)
    }

    proptest! {
        #![proptest_config(ProptestConfig::with_cases(NUM_CASES))]

        #[test]
        fn u256_add(a in any::<U256>(), b in any::<U256>()) {

            let (sum, overflow) = a.overflowing_add(b);

            let big_int_a = to_big_integer(a);
            let big_int_b = to_big_integer(b);
            let big_int_sum = big_int_a + big_int_b;

            if overflow {
                let max = to_big_integer(U256::MAX);
                assert!(big_int_sum > max)
            }
            else {
                let big_int_expected_sum = to_big_integer(sum);
                assert_eq!(big_int_sum, big_int_expected_sum);
            }
        }
    }

    #[test]
    fn sub_1() {
        let a = U256([0, 0, 0, 0]);
        let b = U256([0, 0, 0, 0]);

        assert_eq!(a - b, U256([0, 0, 0, 0]));
    }

    #[test]
    fn sub_2() {
        let a = U256([0, 0, 0, 2]);
        let b = U256([0, 0, 0, 1]);

        assert_eq!(a - b, U256([0, 0, 0, 1]));
    }

    #[test]
    fn sub_3() {
        let a = U256([0xFFFFFFFFFFFFFFFF, 0, 0, 0]);
        let b = U256([0, 0, 0, 1]);

        assert_eq!(
            a - b,
            U256([
                0xFFFFFFFFFFFFFFFE,
                0xFFFFFFFFFFFFFFFF,
                0xFFFFFFFFFFFFFFFF,
                0xFFFFFFFFFFFFFFFF
            ])
        );
    }

    #[test]
    fn sub_4() {
        let a = U256([
            0xFFFFFFFFFFFFFFFF,
            0xFFFFFFFFFFFFFFFF,
            0xFFFFFFFFFFFFFFFF,
            0xFFFFFFFFFFFFFFFF,
        ]);
        let b = U256([1, 0, 0, 1]);

        assert_eq!(
            a - b,
            U256([
                0xFFFFFFFFFFFFFFFE,
                0xFFFFFFFFFFFFFFFF,
                0xFFFFFFFFFFFFFFFF,
                0xFFFFFFFFFFFFFFFE
            ])
        );
    }

    #[test]
    #[should_panic(expected = "underflow")]
    fn sub_6() {
        let a = U256([0, 0, 0, 1]);
        let b = U256([0, 0, 0, 2]);
        let _c = a - b;
    }

    proptest! {
        #![proptest_config(ProptestConfig::with_cases(NUM_CASES))]

        #[test]
        #[should_panic(expected = "underflow")]
        fn u256_sub_overflow(a in any::<U256>(), b in any::<U256>()) {
            if a < b {
                let _c = a - b;
            }
        }
    }

    proptest! {
        #![proptest_config(ProptestConfig::with_cases(NUM_CASES))]

        #[test]
        fn u256_sub_equals(a in any::<U256>()) {
            assert_eq!(a -a, U256::ZERO);
        }
    }

    proptest! {
        #![proptest_config(ProptestConfig::with_cases(NUM_CASES))]

        #[test]
        fn u256_sub(a in any::<U256>(), b in any::<U256>()) {

            if a > b {
                let sub = a - b;

                let big_int_a = to_big_integer(a);
                let big_int_b = to_big_integer(b);
                let big_int_sub = big_int_a - big_int_b;

                let big_int_expected_sub = to_big_integer(sub);
                assert_eq!(big_int_sub, big_int_expected_sub);
            }
        }
    }

    #[test]
    #[should_panic(expected = "invalid hex digit")]
    fn from_hex_invalid_1() {
        U256::from_hex_string("v");
    }

    #[test]
    #[should_panic(expected = "invalid hex digit")]
    fn from_hex_invalid_2() {
        U256::from_hex_string("FvF");
    }

    #[test]
    #[should_panic(expected = "invalid hex string length")]
    fn from_hex_invalid_length() {
        let _v = U256::from_hex_string(
            "FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF1",
        );
    }

    #[test]
    #[should_panic(expected = "invalid empty string")]
    fn from_hex_invalid_length_empty_string() {
        let _v = U256::from_hex_string("");
    }

    #[test]
    fn from_hex_1() {
        let v = U256::from_hex_string("FF");
        assert_eq!(v, U256([0, 0, 0, 0xFF]));
    }

    fn value_to_char(v: u8) -> char {
        match v {
            0x00 => '0',
            0x01 => '1',
            0x02 => '2',
            0x03 => '3',
            0x04 => '4',
            0x05 => '5',
            0x06 => '6',
            0x07 => '7',
            0x08 => '8',
            0x09 => '9',
            0x0A => 'a',
            0x0B => 'b',
            0x0C => 'c',
            0x0D => 'd',
            0x0E => 'e',
            0x0F => 'f',
            _ => panic!("invalid value for hex"),
        }
    }

    #[derive(Debug)]
    struct HexString(String);

    impl Arbitrary for HexString {
        type Parameters = ();
        type Strategy = BoxedStrategy<Self>;

        fn arbitrary_with(_: Self::Parameters) -> Self::Strategy {
            let strategy = (0..1).prop_map(|_| {
                let len = (rand::random::<usize>() % 63) + 1;

                let mut s = String::with_capacity(len);
                for _ in 0..len {
                    let c = value_to_char(rand::random::<u8>() % 16);
                    s.push(c);
                }

                s = s.trim_start_matches('0').to_string();

                if s.is_empty() {
                    s = "0".to_string();
                }

                HexString(s)
            });
            strategy.boxed()
        }
    }

    proptest! {
        #![proptest_config(ProptestConfig::with_cases(NUM_CASES))]

        #[test]
        fn u256_from_hex_string(s in any::<HexString>()) {
            let value = U256::from_hex_string(&s.0);

            let big_int_value = to_big_integer(value);
            assert_eq!(big_int_value.to_string_radix(16), s.0);
        }
    }
}
