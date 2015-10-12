//! Runtime-checked non-NaN floating point numbers with total ordering.

extern crate num;
extern crate quickcheck;

use std::ops::Deref;
use std::cmp::Ordering;
use std::borrow::Borrow;

use num::{Float, NumCast, ToPrimitive, FromPrimitive, Bounded};
use quickcheck::{Arbitrary, Gen};

fn map_nan<T: Float>(n: T) -> Option<Real<T>> {
    if n.is_nan() {
        None
    } else {
        Some(Real(n))
    }
}

pub type Real32 = Real<f32>;
pub type Real64 = Real<f64>;

/// Runtime-checked non-NaN floating point numbers with total ordering.
///
/// Useful for putting floats in data structures that require a total ordering
/// (i.e. situations where NaN would not be valid anyway).
/// 
/// Note that both negative and positive infinity are considered real values.
///
/// # Examples
/// 
/// ```
/// use real::Real;
/// use std::collections::binary_heap::BinaryHeap;
/// 
/// let mut heap = BinaryHeap::new();
/// heap.push(Real::new(1.3));
/// heap.push(Real::new(2.9));
/// heap.push(Real::new(6.0));
/// 
/// assert!(heap.pop().unwrap() == Real::new(6.0));
/// assert!(heap.pop().unwrap() == Real::new(2.9));
/// assert!(heap.pop().unwrap() == Real::new(1.3));
/// ```
///
#[derive(Copy, Clone, PartialEq, Hash, Default, Debug)]
pub struct Real<T>(T);

impl<T: Float> Real<T> {
    /// Creates a new real value
    ///
    /// # Panics
    /// Panics if value is NaN
    pub fn new(inner: T) -> Real<T> {
        Real::try_new(inner).expect("Unexpected NaN")
    }

    /// Creates a new real value if non-NaN.
    /// Returns `None` if inner is NaN.
    pub fn try_new(inner: T) -> Option<Real<T>> {
        map_nan(inner)
    }

    /// Copies the inner float value out of the real
    pub fn inner(self) -> T {
        self.0
    }

    /// Returns a reference to the inner float value
    pub fn inner_ref(&self) -> &T {
        &self.0
    }
}

impl<T: Float> Eq for Real<T> { }

impl<T: Float> Ord for Real<T> {
    fn cmp(&self, other: &Real<T>) -> Ordering {
        if self.0 < other.0 { Ordering::Less }
        else if self.0 > other.0 { Ordering::Greater }
        else { Ordering::Equal }
    }
}

impl<T: Float> PartialOrd for Real<T> {
    fn partial_cmp(&self, other: &Real<T>) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<T: Float> PartialOrd<T> for Real<T> {
    fn partial_cmp(&self, other: &T) -> Option<Ordering> {
        self.0.partial_cmp(other)
    }
}

impl<T: Float> PartialEq<T> for Real<T> {
    fn eq(&self, other: &T) -> bool {
        self.0.eq(other)
    }

    fn ne(&self, other: &T) -> bool {
        self.0.ne(other)
    }
}

impl<T: Float + NumCast> NumCast for Real<T> {
    fn from<U: ToPrimitive>(n: U) -> Option<Real<T>> {
        NumCast::from(n).and_then(map_nan)
    }
}

impl<T: Bounded> Bounded for Real<T> {
    fn min_value() -> Real<T> {
        Real(T::min_value())
    }

    fn max_value() -> Real<T> {
        Real(T::max_value())
    }
}

impl<T: ToPrimitive> ToPrimitive for Real<T> {
    fn to_isize(&self) -> Option<isize> { self.0.to_isize() }
    fn to_i8   (&self) -> Option<i8>    { self.0.to_i8()    }
    fn to_i16  (&self) -> Option<i16>   { self.0.to_i16()   }
    fn to_i32  (&self) -> Option<i32>   { self.0.to_i32()   }
    fn to_i64  (&self) -> Option<i64>   { self.0.to_i64()   }
    fn to_usize(&self) -> Option<usize> { self.0.to_usize() }
    fn to_u8   (&self) -> Option<u8>    { self.0.to_u8()    }
    fn to_u16  (&self) -> Option<u16>   { self.0.to_u16()   }
    fn to_u32  (&self) -> Option<u32>   { self.0.to_u32()   }
    fn to_u64  (&self) -> Option<u64>   { self.0.to_u64()   }
    fn to_f32  (&self) -> Option<f32>   { self.0.to_f32()   }
    fn to_f64  (&self) -> Option<f64>   { self.0.to_f64()   }
}

impl<T: Float + FromPrimitive> FromPrimitive for Real<T> {
    fn from_isize(n: isize) -> Option<Real<T>> { FromPrimitive::from_isize(n).and_then(map_nan) }
    fn from_i8   (n: i8)    -> Option<Real<T>> { FromPrimitive::from_i8   (n).and_then(map_nan) }
    fn from_i16  (n: i16)   -> Option<Real<T>> { FromPrimitive::from_i16  (n).and_then(map_nan) }
    fn from_i32  (n: i32)   -> Option<Real<T>> { FromPrimitive::from_i32  (n).and_then(map_nan) }
    fn from_i64  (n: i64)   -> Option<Real<T>> { FromPrimitive::from_i64  (n).and_then(map_nan) }
    fn from_usize(n: usize) -> Option<Real<T>> { FromPrimitive::from_usize(n).and_then(map_nan) }
    fn from_u8   (n: u8)    -> Option<Real<T>> { FromPrimitive::from_u8   (n).and_then(map_nan) }
    fn from_u16  (n: u16)   -> Option<Real<T>> { FromPrimitive::from_u16  (n).and_then(map_nan) }
    fn from_u32  (n: u32)   -> Option<Real<T>> { FromPrimitive::from_u32  (n).and_then(map_nan) }
    fn from_u64  (n: u64)   -> Option<Real<T>> { FromPrimitive::from_u64  (n).and_then(map_nan) }
    fn from_f32  (n: f32)   -> Option<Real<T>> { FromPrimitive::from_f32  (n).and_then(map_nan) }
    fn from_f64  (n: f64)   -> Option<Real<T>> { FromPrimitive::from_f64  (n).and_then(map_nan) }
}

impl<T> Deref for Real<T> {
    type Target = T;

    fn deref(&self) -> &T {
        &self.0
    }
}

impl<T: Float> Borrow<T> for Real<T> {
    fn borrow(&self) -> &T {
        &self.0
    }
}

impl<T: Arbitrary + Float> Arbitrary for Real<T> {
    fn arbitrary<G: Gen>(g: &mut G) -> Real<T> {
        let mut ar = T::arbitrary(g);
        while ar.is_nan() {
            ar = T::arbitrary(g);
        }
        Real(ar)
    }

    fn shrink(&self) -> Box<Iterator<Item=Self>> {
        Box::new(self.0.shrink().map(|x| Real(x)))
    }
}

#[cfg(test)]
mod test {
    use std::f32;
    use super::Real;
    use num::traits::FromPrimitive;

    #[test]
    fn valid() {
        let v = 0.16f32;
        let real: Real<f32> = Real::from_f32(v).unwrap();
        assert!(*real == v);
    }

    #[test]
    fn invalid() {
        let real: Option<Real<f32>> = Real::from_f32(f32::NAN);
        assert!(real == None);
    }
}
