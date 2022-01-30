use std::ops;
// use std::mem;
use num_traits::{One, Zero};
use std::sync::Arc;
use std::thread;
use std::u32;
use std::u64;
use rayon::prelude::*;

#[derive(Debug, Clone)]
pub struct BigInt {
  digits: Vec<u64>,
}

impl BigInt {
  pub fn new(digits: Vec<u64>) -> BigInt {
    return BigInt { digits };
  }

  pub fn size(&self) -> usize {
    return self.digits.len();
  }

  fn resize(&mut self, new_len: usize, val: u64) {
    return self.digits.resize(new_len, val);
  }

  pub fn print_digits(&self) {
    println!("{:?}", self.digits)
  }

  fn concurrent_slow_mul(lhs: BigInt, rhs: BigInt) -> BigInt {
    let mut result = BigInt::new(vec![0]);
  
    let mut transient_mul_vec_iter: Vec<BigInt> = rhs
      .digits
      .into_par_iter()
      .map(|digit_b| (&lhs * digit_b))
      .collect();
  
    for (i, num) in transient_mul_vec_iter.iter_mut().enumerate() {
      *num <<= i;
      if result.size() < num.size() {
        result.resize(num.size(), 0);
      }
      result += &num;
    }
  
    return result;
  }
}

impl Zero for BigInt {
  fn zero() -> BigInt {
    BigInt { digits: vec![0] }
  }
  fn is_zero(&self) -> bool {
    return (self.size() == 1) && (self.digits[0] == 0);
  }
}

impl One for BigInt {
  fn one() -> BigInt {
    BigInt { digits: vec![1] }
  }
}

impl ops::ShlAssign<usize> for BigInt {
  fn shl_assign(&mut self, rhs: usize) {
    self.digits.reserve(rhs);
    for _i in 0..rhs {
      self.digits.insert(0, 0);
    }
  }
}
impl<'a> ops::AddAssign<&'a BigInt> for BigInt {
  fn add_assign(&mut self, rhs: &Self) {
    let mut carry: bool = false;
    let (self_lo, self_hi) = self.digits.split_at_mut(rhs.size());
    for (a, b) in self_lo.iter_mut().zip(rhs.digits.iter()) {
      let (half_sum, carry0) = a.overflowing_add(*b);
      let (sum, carry1) = half_sum.overflowing_add(carry as u64);
      carry = carry0 || carry1;
      *a = sum;
    }

    if carry {
      for a in self_hi {
        carry = *a == u64::MAX;
        if carry {
          *a = 0;
        } else {
          *a += 1;
          break;
        }
      }
      if carry {
        self.digits.push(1);
      }
    }
  }
}

impl ops::Add for &BigInt {
  type Output = BigInt;

  fn add(self, rhs: Self) -> BigInt {
    let mut c = self.clone();
    c += &rhs;
    return c;
  }
}

impl ops::Add for BigInt {
  type Output = BigInt;

  fn add(self, rhs: Self) -> BigInt {
    let mut c = self.clone();
    c += &rhs;
    return c;
  }
}

impl ops::Mul for BigInt {
  type Output = BigInt;

  fn mul(self, rhs: Self) -> BigInt {
    let mut c = self.clone();
    c *= rhs;
    return c;
  }
}

impl ops::Mul for &BigInt {
  type Output = BigInt;

  fn mul(self, rhs: Self) -> BigInt {
    let mut c = self.clone();
    c *= rhs;
    return c;
  }
}

impl ops::MulAssign<&BigInt> for BigInt{
  fn mul_assign(&mut self, rhs: &Self) {
    let self_copy = self.clone();

    let mut transient_mul_vec_iter: Vec<BigInt> = rhs
      .digits
      .iter()
      .map(|digit_b| (&self_copy * *digit_b))
      .collect();

    for (i, num) in transient_mul_vec_iter.iter_mut().enumerate() {
      *num <<= i;
      if self.size() < num.size() {
        self.resize(num.size(), 0);
      }
      *self += &num;
    }
  }
}

impl ops::MulAssign for BigInt {
  fn mul_assign(&mut self, rhs: Self) {
    let self_copy = self.clone();

    let mut transient_mul_vec_iter: Vec<BigInt> = rhs
      .digits
      .into_iter()
      .map(|digit_b| (&self_copy * digit_b))
      .collect();

    for (i, num) in transient_mul_vec_iter.iter_mut().enumerate() {
      *num <<= i;
      if self.size() < num.size() {
        self.resize(num.size(), 0);
      }
      *self += &num;
    }
  }
}

impl ops::MulAssign<u64> for BigInt {
  fn mul_assign(&mut self, rhs: u64) {
    let mut carry = 0;
    for digit in self.digits.iter_mut() {
      let (prod, carry0) = widening_mul(*digit, rhs);
      let (ans, carry1) = prod.overflowing_add(carry as u64);
      carry = carry0 + (carry1 as u64);
      *digit = ans;
    }
    if carry > 0 {
      self.digits.push(carry)
    }
  }
}

impl ops::Mul<u64> for &BigInt {
  type Output = BigInt;
  fn mul(self, rhs: u64) -> BigInt {
    let mut c = BigInt::new(self.digits.clone());
    c *= rhs;
    return c;
  }
}

// fn slow_mul(lhs: BigInt, rhs: BigInt) -> BigInt {
//   let mut result = BigInt::new(vec![0]);

//   let transient_mul_vec_iter: Vec<BigInt> = rhs.digits.into_iter().map(|digit_b| (&lhs * digit_b)).collect();

//   let mut shift_zeros = BigInt::one();
//   let big_int_ten = BigInt::new(vec![0,1]);
//   for num in transient_mul_vec_iter.iter_mut() {
//     num = num * shift_zeros;
//     shift_zeros = shift_zeros * big_int_ten;
//     if result.size() >= num.size(){
//       result += &num;
//     }else {
//       result = num + result;
//     }
//   }

//   return result;
// }



fn full_adder(a: u64, b: u64, c: u64) -> (u64, bool, bool) {
  let (half_sum, carry1) = a.overflowing_add(b);
  let p = half_sum == u64::MAX;
  let (sum, carry2) = half_sum.overflowing_add(c);
  return (sum, carry1 || carry2, p);
}

fn ripple_carry_adder(lhs: &BigInt, rhs: &BigInt) -> BigInt {
  debug_assert!(lhs.size() >= rhs.size());
  let mut carry: bool = false;
  let mut output = BigInt::new(Vec::with_capacity(lhs.size()));
  let (self_lo, self_hi) = lhs.digits.split_at(rhs.size());

  for i in 0..self_lo.len() {
    let (half_sum, carry0) = lhs.digits[i].overflowing_add(rhs.digits[i]);
    let (sum, carry1) = half_sum.overflowing_add(carry as u64);
    carry = carry0 || carry1;
    output.digits[i] = sum;
  }

  if carry {
    for i in self_lo.len()..self_hi.len() {
      carry = lhs.digits[i] == u64::MAX;
      if carry {
        output.digits[i] = 0;
      } else {
        output.digits[i] += 1;
        break;
      }
    }
    if carry {
      output.digits.push(1);
    }
  }

  return output;
}

fn widening_mul(a: u64, b: u64) -> (u64, u64) {
  let hi = |x: u64| x >> 32;

  let lo = |x: u64| ((u32::MAX) as u64) & x;
  let mut x = lo(a) * lo(b);
  let s0 = lo(x);
  x = hi(a) * lo(b) + hi(x);
  let mut s1 = lo(x);
  let mut s2 = hi(x);
  x = s1 + lo(a) * hi(b);
  s1 = lo(x);

  x = s2 + hi(a) * hi(b) + hi(x);
  s2 = lo(x);
  let s3 = hi(x);

  let result = s1 << 32 | s0;
  let carry = s3 << 32 | s2;
  return (result, carry);
}

// fn faster_add(&mut self, rhs: BigInt) -> BigInt {
//     let n = self.size(); // Number of digits
//     // Resize a to hold answer
//     if n < rhs.size() {
//         self.resize(rhs.size(), 0);
//         n = rhs.size();
//     }
//     let m = f64::sqrt((n as f64) / 2.0) as u64; // block size
//     // Add every digit of this and rhs, and carry the overflow to the next digit
//     if m > 20 {
//         let a = self.digits.chunks_mut(m as usize);
//         let b = rhs.digits.chunks(m as usize);
//         let carry_set = BitVec::from_elem(m as usize, false);
//         let mut carry: u64 = 0;
//         let mut p = false;
//         for i in 0..n   {

//             for (a_digit, b_digit) in a..zip(b_block) {
//                 let (sum, c, p0) = fullAdder(*a_digit, *b_digit, carry);
//                 *a_digit = sum;
//                 carry = c;
//                 p = p && p;
//             }
//             let carry_out = if p {carry_in. } else carry;

//         }

//     }

//     return compact(*this);
// }
