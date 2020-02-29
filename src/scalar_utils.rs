extern crate byteorder;
extern crate rand;
extern crate curve25519_dalek;

use rand::SeedableRng;
use rand::rngs::OsRng;
use self::byteorder::{ByteOrder, LittleEndian};
use curve25519_dalek::scalar::Scalar;
use std::fmt;

pub type ScalarBytes = [u8; 32];

/// Get a bit array of this scalar, LSB is first element of this array
#[derive(Clone)]
pub struct ScalarBits {
    pub bit_array: Vec<u8>
}

impl fmt::Debug for ScalarBits {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}", self.bit_array)
    }
}

impl ScalarBits {
    pub fn from_scalar(scalar: &Scalar, process_bits: usize) -> Self {
        let s = scalar.reduce();
        Self {
            bit_array: get_bits(&s, process_bits)
        }
    }

    /*pub fn from_scalar_dont_reduce(scalar: &Scalar) -> Self {
        //let s = scalar.reduce();
        let b = get_bits(scalar);
        for i in TreeDepth..256 {
            assert_eq!(b[i], 0);
        }

        let mut reduced_bits = [0; TreeDepth];
        for i in 0..TreeDepth {
            reduced_bits[i] = b[i];
        }
        Self {
            bit_array: reduced_bits
        }
    }*/

    pub fn to_scalar(&self) -> Scalar {
        /*let mut bytes: [u8; 32] = [0; 32];
        let powers_of_2: [u8; 8] = [1, 2, 4, 8, 16, 32, 64, 128];
        let mut i = 0;
        let mut current_byte = 0u8;
        for b in self.bit_array.iter() {
            if *b == 1 {
                current_byte += powers_of_2[i % 8];
            }
            i += 1;
            if (i % 8) == 0 {
                bytes[(i / 8) -1] = current_byte;
                current_byte = 0;
            }
        }
        bytes[31] = current_byte;
        Scalar::from_bits(bytes).reduce()*/
        self.to_non_reduced_scalar().reduce()
    }

    pub fn to_non_reduced_scalar(&self) -> Scalar {
        let mut bytes: [u8; 32] = [0; 32];
        let powers_of_2: [u8; 8] = [1, 2, 4, 8, 16, 32, 64, 128];
        let mut i = 0;
        let mut current_byte = 0u8;
        for b in self.bit_array.iter() {
            if *b == 1 {
                current_byte += powers_of_2[i % 8];
            }
            i += 1;
            if (i % 8) == 0 {
                bytes[(i / 8) - 1] = current_byte;
                current_byte = 0;
            }
        }
        bytes[31] = current_byte;
        Scalar::from_bits(bytes)
    }

    /// Shift left by 1 bit
    pub fn shl(&mut self) {
        for i in (1..self.bit_array.len()).rev() {
            self.bit_array[i] = self.bit_array[i-1];
        }
        self.bit_array[0] = 0;
    }

    /// Shift right by 1 bit
    pub fn shr(&mut self) {
        let size = self.bit_array.len();
        for i in 1..size {
            self.bit_array[i-1] = self.bit_array[i];
        }
        self.bit_array[size-1] = 0;
    }

    /// Return a new bit-array shifted to the left with 1 bit
    pub fn new_left_shifted(&self) -> Self {
        // Not using the above method `shl` to avoid copying
        let size = self.bit_array.len();
        let mut new_array = vec![0; size];
        for i in (1..size).rev() {
            new_array[i] = self.bit_array[i-1];
        }
        new_array[0] = 0;
        Self {
            bit_array: new_array
        }
    }

    /// Return a new bit-array shifted to the right with 1 bit
    pub fn new_right_shifted(&self) -> Self {
        // Not using the above method `shr` to avoid copying
        let size = self.bit_array.len();
        let mut new_array = vec![0; size];
        for i in 1..size {
            new_array[i-1] = self.bit_array[i];
        }
        new_array[size-1] = 0;
        Self {
            bit_array: new_array
        }
    }

    /// Check if most significant bit is set
    pub fn is_msb_set(&self) -> bool {
        self.bit_array[self.bit_array.len()-1] == 1
    }

    /// Check if least significant bit is set
    pub fn is_lsb_set(&self) -> bool {
        self.bit_array[0] == 1
    }
}

pub fn get_bits(scalar: &Scalar, process_bits: usize) -> Vec<u8> {
    let mut bits = vec![0u8; process_bits];
    let bytes = scalar.as_bytes();
    for i in 0..process_bits {
        // As i runs from 0..256, the bottom 3 bits index the bit,
        // while the upper bits index the byte.
        bits[i] = ((bytes[i>>3] >> (i&7)) & 1u8) as u8;
    }
    bits
}

pub fn scalar_to_u64_array(scalar: &Scalar) -> [u64; 4] {
    let bytes = scalar.to_bytes();
    let mut result = [0; 4];
    LittleEndian::read_u64_into(&bytes, &mut result);
    result
}

pub fn u64_array_to_scalar(array: &[u64; 4]) -> Scalar {
    let mut result: [u8; 32] = [0; 32];
    LittleEndian::write_u64_into(array, &mut result);
    let s = Scalar::from_bits(result);
    s.reduce()
}

/// Get a base 4 representation of the given `scalar`. Only process `limit_bytes` of the scalar
pub fn get_base_4_repr(scalar: &Scalar, limit_bytes: usize) -> Vec<u8> {
    let d = limit_bytes * 4;    // number of base 4 digits
    let n = limit_bytes * 8;    // number of bits to process
    let mut base_4 = vec![0u8; d];
    // Keep only the number of bits needed.
    let mut bits = get_bits(scalar, n).to_vec();
    bits.reverse();
    for i in (0..bits.len()-1).step_by(2) {
        base_4[i / 2] = match (bits[i], bits[i+1]) {
            (0, 0) => 0,
            (0, 1) => 1,
            (1, 0) => 2,
            _ => 3
        }
    }
    base_4
}


/// Following code for handling Hex is taken from https://play.rust-lang.org/?version=stable&mode=debug&edition=2015&gist=e241493d100ecaadac3c99f37d0f766f
use std::num::ParseIntError;

pub fn decode_hex(s: &str) -> Result<Vec<u8>, DecodeHexError> {
    let s = if s[0..2] == *"0x" || s[0..2] == *"0X" {
        match s.char_indices().skip(2).next() {
            Some((pos, _)) => &s[pos..],
            None => "",
        }
    } else { s };
    if s.len() % 2 != 0 {
        Err(DecodeHexError::OddLength)
    } else {
        (0..s.len())
            .step_by(2)
            .map(|i| u8::from_str_radix(&s[i..i + 2], 16).map_err(|e| e.into()))
            .collect()
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DecodeHexError {
    OddLength,
    ParseInt(ParseIntError),
}

impl From<ParseIntError> for DecodeHexError {
    fn from(e: ParseIntError) -> Self {
        DecodeHexError::ParseInt(e)
    }
}

impl fmt::Display for DecodeHexError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            DecodeHexError::OddLength => "input string has an odd number of bytes".fmt(f),
            DecodeHexError::ParseInt(e) => e.fmt(f),
        }
    }
}

impl std::error::Error for DecodeHexError {}

pub fn get_scalar_from_hex(hex_str: &str) -> Result<Scalar, DecodeHexError> {
    let bytes = decode_hex(hex_str)?;
    let mut result: [u8; 32] = [0; 32];
    result.copy_from_slice(&bytes);
    Ok(Scalar::from_bytes_mod_order(result))
}

#[cfg(test)]
mod tests {
    use super::*;
    use curve25519_dalek::constants::BASEPOINT_ORDER;
    use crate::gadget_vsmt_2::TreeDepth;

    #[test]
    fn test_shl_shr() {
        let mut csprng: OsRng = OsRng::default();
        for _ in 0..100 {
            let r: Scalar = Scalar::random(&mut csprng);
            let mut b_arr = ScalarBits::from_scalar(&r, TreeDepth);
            assert_eq!(r, b_arr.to_scalar());
            //assert_eq!(b_arr, ScalarBits::from_scalar(&b_arr.to_scalar()));
        }

        /*let mut one = ScalarBitArray::from_scalar(&Scalar::one());
        println!("{:?}", one.to_scalar());
        for i in 0..TreeDepth {
            one.shl();
            println!("i={}, {:?}", i, one.to_scalar());
        }*/
    }

    #[test]
    fn test_scalar_to_u64_array() {
        for n in vec![32, 255, 127, 488, 256, 257].iter() {
            let s = Scalar::from(*n as u64);
            let u = scalar_to_u64_array(&s);
            let e = u64_array_to_scalar(&u);
            assert_eq!(e, s);
            /*println!("{:?}", u);
            println!("{:?}", e);*/
        }

        let o = BASEPOINT_ORDER - Scalar::one();
        let u = scalar_to_u64_array(&o);
        let e = u64_array_to_scalar(&u);
        assert_eq!(e, o);

        {
            let u: [u64; 4] = [0, 0, 0, 1762596304162127872];
            let s = u64_array_to_scalar(&u);
            println!("s={:?}", s);
            let b = ScalarBits::from_scalar(&s, TreeDepth);
            println!("b={:?}", b);
            let s1 = b.to_scalar();
            println!("s1={:?}", s1);
            let u1 = scalar_to_u64_array(&s1);
            println!("u1={:?}", u1);
        }
    }

    #[test]
    fn test_scalar_to_base_4_array() {
        println!("{:?}", get_base_4_repr(&Scalar::from(18u64), 32));
        println!("{:?}", get_base_4_repr(&Scalar::from(1u64), 32));
        println!("{:?}", get_base_4_repr(&Scalar::from(0u64), 32));
        println!("{:?}", get_base_4_repr(&Scalar::from(2u64), 32));
        println!("{:?}", get_base_4_repr(&Scalar::from(3u64), 32));
        println!("{:?}", get_base_4_repr(&Scalar::from(4u64), 32));
        println!("{:?}", get_base_4_repr(&Scalar::from(5u64), 32));
        println!("{:?}", get_base_4_repr(&Scalar::from(6u64), 32));
    }

    #[test]
    fn test_invert() {
        let x = Scalar::zero();
        println!("Inverse {:?}", x.invert());
    }
}

