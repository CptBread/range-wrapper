use num_traits::ops::{
	wrapping::{WrappingAdd, WrappingSub},
	overflowing::OverflowingSub,
};
use num_traits::identities::One;
use num_traits::cast::{ToPrimitive, FromPrimitive, AsPrimitive};
use num_traits::bounds::Bounded;
use std::ops::{Range, RangeInclusive, Sub};
use std::iter::DoubleEndedIterator;
use std::fmt::Debug;

#[derive(Clone, Default, PartialEq, Eq, Hash, Debug)]
pub struct RangeWrapping<T> {
	pub start: T,
	pub end: T,
	// After writing everything I realized why RangeInclusive needs to exist as a seperate struct... I.e. RangeInclusive can represent one more value then Range can.
	inclusive_hack: bool,
}

impl<T> RangeWrapping<T> {
	pub fn will_wrap(&self) -> bool 
		where T: PartialOrd + Bounded
	{
		self.start_end_wrap() && self.end != T::min_value()
	}

	// will return true even if the range actually doesn't wrap but only if the end is MIN
	fn start_end_wrap(&self) -> bool 
		where T: PartialOrd + Bounded
	{
		self.start > self.end || self.inclusive_hack && self.start == self.end
	}

	pub fn contains<U>(&self, item: &U) -> bool
		where T: PartialOrd + Bounded + PartialOrd<U> + WrappingSub + One, U: ?Sized + PartialOrd<T>
	{
		if self.start_end_wrap() {
			// If we are wrapping then only one of these needs to be true
			self.start <= *item || *item < self.end
		}
		else {
			self.start <= *item && *item < self.end
		}
	}
}

impl<T> std::iter::FusedIterator for RangeWrapping<T>
	where T: WrappingAdd + WrappingSub + OverflowingSub + Sub<Output = T> + One + Copy + Eq + Ord + ToPrimitive + Bounded + FromPrimitive + AsPrimitive<usize>
{}

// Can't do exact size fo anythign above 16 bit types becuase we also support inclusive ranges... Has the same issues as RangeInclusive does with u16 and i16(i.e. it doesn't take into consideration the platform usize size).
impl ExactSizeIterator for RangeWrapping<u8> {}
impl ExactSizeIterator for RangeWrapping<u16> {}
impl ExactSizeIterator for RangeWrapping<i8> {}
impl ExactSizeIterator for RangeWrapping<i16> {}

impl<T> DoubleEndedIterator for RangeWrapping<T>
	where T: WrappingAdd + WrappingSub + OverflowingSub + Sub<Output = T> + One + Copy + Eq + Ord + ToPrimitive + Bounded + FromPrimitive + AsPrimitive<usize>
{
	fn next_back(&mut self) -> Option<T> {
		if !self.inclusive_hack && self.start == self.end {
			None
		}
		else {
			self.inclusive_hack = false;
			self.end = self.end.wrapping_sub(&T::one());
			Some(self.end)
		}
	}
}

impl<T> Iterator for RangeWrapping<T>
	where T: WrappingAdd + WrappingSub + OverflowingSub + Sub<Output = T> + One + Copy + Eq + Ord + ToPrimitive + Bounded + FromPrimitive + AsPrimitive<usize>
{
	type Item = T;

	#[inline]
	fn next(&mut self) -> Option<T> {
		if !self.inclusive_hack && self.start == self.end {
			None
		}
		else {
			self.inclusive_hack = false;
			let res = self.start;
			self.start = res.wrapping_add(&T::one());
			Some(res)
		}
	}

	fn size_hint(&self) -> (usize, Option<usize>) {
		if self.start == self.end && self.inclusive_hack {
			let max = T::max_value().to_usize().and_then(|max| max.checked_add(1));
			return (max.unwrap_or(usize::MAX), max);
		}
		if self.start <= self.end {
			let (size, over) = self.end.overflowing_sub(&self.start);
			let size = if over {
				// We overflowed. If our max value is larger then usize then our diff should be above usize limits
				if T::max_value().to_usize().is_none() {
					None
				}
				// Otherwise we should be able to 
				else {
					Some(self.end.as_().wrapping_sub(self.start.as_()))
				}
			}
			else {
				size.to_usize()
			};
			(size.unwrap_or(usize::MAX), size)
		}
		else {
			let diff = self.end.wrapping_sub(&self.start).to_usize();
			(diff.unwrap_or(usize::MAX), diff)
		}
	}

	fn nth(&mut self, n: usize) -> Option<T> {
		let (_, size) = self.size_hint();
		self.inclusive_hack = false;
		// Size should only be none if the size is beyond usize::MAX, meaning it should be safe to unwrap from a usize(as it can only be beyond(or equal) usize::MAX if it can contain a usize safely)
		if size.map_or(true, |size| n < size) {
			let res = self.start.wrapping_add(&T::from_usize(n).unwrap());
			self.start = res.wrapping_add(&T::one());
			Some(res)
		}
		else {
			self.start = self.end;
			None
		}
	}

	#[inline]
	fn last(mut self) -> Option<T> {
		self.next_back()
	}

	fn min(self) -> Option<T> {
		if self.start == self.end {
			if self.inclusive_hack {
				Some(T::min_value())
			}
			else {
				None
			}
		}
		else if self.end != T::min_value() && self.start > self.end {
			// Wrapping around so should be min_value
			Some(T::min_value())
		}
		else {
			Some(self.start)
		}
	}

	fn max(self) -> Option<T> {
		if self.start == self.end {
			if self.inclusive_hack {
				Some(T::max_value())
			}
			else {
				None
			}
		}
		else if self.start > self.end {
			// Wrapping around so should be max_value
			Some(T::max_value())
		}
		else {
			Some(self.end.sub(T::one()))
		}
	}
}

impl<T> From<Range<T>> for RangeWrapping<T>
{
	fn from(range: Range<T>) -> Self {
		RangeWrapping{
			start: range.start,
			end: range.end,
			inclusive_hack: false,
		}
	}
}

impl<T> From<RangeInclusive<T>> for RangeWrapping<T>
	where T: WrappingAdd + One + Clone
{
	fn from(range: RangeInclusive<T>) -> Self {
		RangeWrapping{
			start: range.start().clone(),
			end: range.end().wrapping_add(&T::one()),
			inclusive_hack: true,
		}
	}
}

#[cfg(test)]
mod tests {
	use crate::*;
	#[test]
	fn test_wrapping() {
		let mut range = RangeWrapping {
			start: u16::MAX,
			end: 1,
			inclusive_hack: false,
		};
		assert_eq!(range.next(), Some(u16::MAX));
		assert_eq!(range.next(), Some(0));
		assert_eq!(range.next(), None);
	}

	#[test]
	fn test_from_range() {
		let mut range = RangeWrapping::from(u16::MAX..1);
		assert_eq!(range.next(), Some(u16::MAX));
		assert_eq!(range.next(), Some(0));
		assert_eq!(range.next(), None);
	}

	#[test]
	fn test_from_inclusive_range() {
		let mut range = RangeWrapping::from(u16::MAX..=1);
		assert_eq!(range.next(), Some(u16::MAX));
		assert_eq!(range.next(), Some(0));
		assert_eq!(range.next(), Some(1));
		assert_eq!(range.next(), None);

		let mut range =  RangeWrapping::from(0..=u16::MAX);
		assert_eq!(range.next(), Some(0));
	}

	#[test]
	fn test_no_wrapping() {
		let mut range = RangeWrapping::from(1..3);
		assert_eq!(range.next(), Some(1));
		assert_eq!(range.next(), Some(2));
		assert_eq!(range.next(), None);
	}

	fn ok_hint(size: usize) -> (usize, Option<usize>) {
		(size, Some(size))
	}

	#[test]
	fn test_size_hint() {
		let mut range = RangeWrapping::from(u32::MAX..2);
		assert_eq!(range.size_hint(), ok_hint(3));
		range.next();
		assert_eq!(range.size_hint(), ok_hint(2));
		range.next();
		assert_eq!(range.size_hint(), ok_hint(1));
		range.next();
		assert_eq!(range.size_hint(), ok_hint(0));
		assert_eq!(range.next(), None);

		assert_eq!(RangeWrapping::from(0..usize::MAX).size_hint(), ok_hint(usize::MAX));
		// Ensure we work the same as inclusive range size_hints in the non wrapping case
		assert_eq!(RangeWrapping::from(0..=usize::MAX).size_hint(), (0..=usize::MAX).size_hint());
		assert_eq!(RangeWrapping::from(0..=u32::MAX).size_hint(), ok_hint(u32::MAX as usize + 1));
	}

	#[test]
	fn test_signed_size_hint() {
		let mut range = RangeWrapping::from(i32::MAX..(i32::MIN + 2));
		assert_eq!(range.size_hint(), ok_hint(3));
		range.next();
		assert_eq!(range.size_hint(), ok_hint(2));
		range.next();
		assert_eq!(range.size_hint(), ok_hint(1));
		range.next();
		assert_eq!(range.size_hint(), ok_hint(0));
		assert_eq!(range.next(), None);

		// Wrapping size hint
		assert_eq!(RangeWrapping::from(
			-1..i32::MAX).size_hint(),
			(i32::MAX as usize + 1, Some(i32::MAX as usize + 1))
		);

		assert_eq!(RangeWrapping::from(i32::MIN..i32::MAX).size_hint(), (i32::MIN..i32::MAX).size_hint());
	}

	#[test]
	fn test_max() {
		assert_eq!(RangeWrapping::from(0..u32::MAX).max(), Some(u32::MAX - 1));
		assert_eq!(RangeWrapping::from(1..0).max(), Some(u32::MAX));
		assert_eq!(RangeWrapping::from(1..=10).max(), Some(10));
		assert_eq!(RangeWrapping::from(1..10).max(), Some(9));
		assert_eq!(RangeWrapping::from(i32::MIN..i32::MAX).max(), Some(i32::MAX - 1));
		assert_eq!(RangeWrapping::from(u32::MAX..u32::MIN).max(), Some(u32::MAX));
	}

	#[test]
	fn test_min() {
		assert_eq!(RangeWrapping::from(0..u32::MAX).min(), Some(0));
		assert_eq!(RangeWrapping::from(1..0u32).min(), Some(1));
		assert_eq!(RangeWrapping::from(1..0i32).min(), Some(i32::MIN));
		assert_eq!(RangeWrapping::from(1..10).min(), Some(1));
		assert_eq!(RangeWrapping::from(1..0i32).min(), Some(i32::MIN));
		assert_eq!(RangeWrapping::from(i32::MIN..i32::MAX).min(), Some(i32::MIN));
		assert_eq!(RangeWrapping::from(u32::MAX..u32::MIN).min(), Some(u32::MAX));
	}

	#[test]
	fn test_back() {
		let mut range = RangeWrapping::from(u16::MAX..2);
		assert_eq!(range.next_back(), Some(1));
		assert_eq!(range.next_back(), Some(0));
		assert_eq!(range.next_back(), Some(u16::MAX));
		assert_eq!(range.next_back(), None);
	}

	#[test]
	fn test_nth() {
		let mut range = RangeWrapping::from(u16::MAX..2);
		assert_eq!(range.clone().nth(0), Some(u16::MAX));
		assert_eq!(range.clone().nth(1), Some(0));
		assert_eq!(range.clone().nth(2), Some(1));
		assert_eq!(range.clone().nth(3), None);

		assert_eq!(range.nth(0), Some(u16::MAX));
		assert_eq!(range.clone().nth(0), Some(0));
		assert_eq!(range.clone().nth(1), Some(1));
		assert_eq!(range.clone().nth(2), None);
	}

	#[test]
	fn test_128() {
		assert_eq!(RangeWrapping::from(0..std::i128::MAX).size_hint(), (usize::MAX, None));
		assert_eq!(RangeWrapping::from(0..10).size_hint(), (10, Some(10)));

		// Wrapping size hint
		assert_eq!(RangeWrapping::from(
			-1..std::i128::MAX).size_hint(),
			(usize::MAX, None)
		);

		let range = RangeWrapping::from(-200..std::i128::MIN);
		assert_eq!(range.clone().nth(0), Some(-200));
		assert_eq!(range.clone().nth(200), Some(0));
		assert_eq!(range.clone().nth(usize::MAX), Some((-200i128) + usize::MAX as i128));
		assert_eq!(RangeWrapping::from(0..std::u128::MAX).nth(usize::MAX), Some(usize::MAX as u128));
	}

	#[test]
	fn test_inclusive_hack() {
		assert_eq!(RangeWrapping::from(0..=usize::MAX).nth(usize::MAX), Some(usize::MAX));
		assert_eq!((0..=usize::MAX).size_hint(), (usize::MAX, None));
		assert_eq!(RangeWrapping::from(0..=usize::MAX).size_hint(), (usize::MAX, None));
		assert_eq!(RangeWrapping::from(1..=0usize).size_hint(), (usize::MAX, None));
		assert_eq!(RangeWrapping::from(1..=0u32).size_hint(), ok_hint(u32::MAX as usize + 1));
		// assert_eq!(RangeWrapping::from(1..=0i32).size_hint(), ok_hint(u32::MAX as usize + 1));
		assert_eq!(RangeWrapping::from(usize::MAX..=usize::MAX).next(), Some(usize::MAX));
		assert_eq!(RangeWrapping::from(0..=1).next_back(), Some(1));
		assert_eq!(RangeWrapping::from(isize::MAX..=isize::MIN).next_back(), Some(isize::MIN));
		assert_eq!(RangeWrapping::from(5u8..=4u8).nth(u8::MAX.into()), Some(4u8));
		assert_eq!(RangeWrapping::from(5u8..=4u8).rev().nth(u8::MAX.into()), Some(5u8));
		assert_eq!(RangeWrapping::from(5u8..=4u8).rev().nth(u8::MAX as usize + 1), None);
	}

	#[test]
	fn test_will_wrap() {
		assert_eq!(RangeWrapping::from(0..=usize::MAX).will_wrap(), false);
		assert_eq!(RangeWrapping::from(0..usize::MAX).will_wrap(), false);
		assert_eq!(RangeWrapping::from(1..0).will_wrap(), true);
		assert_eq!(RangeWrapping::from(1..=0).will_wrap(), true);
		assert_eq!(RangeWrapping::from(1..=0).will_wrap(), true);
		assert_eq!(RangeWrapping::from(0..0).will_wrap(), false);
		assert_eq!(RangeWrapping::from(0..=0).will_wrap(), false);
	}

	#[test]
	fn test_contains() {
		assert_eq!(RangeWrapping::from(0..=usize::MAX).contains(&0), true);
		assert_eq!(RangeWrapping::from(0..=usize::MAX).contains(&1), true);
		assert_eq!(RangeWrapping::from(0..=usize::MAX).contains(&usize::MAX), true);
		assert_eq!(RangeWrapping::from(0..usize::MAX).contains(&usize::MAX), false);
		assert_eq!(RangeWrapping::from(10..4).contains(&usize::MAX), true);
		assert_eq!(RangeWrapping::from(10..4).contains(&10), true);
		assert_eq!(RangeWrapping::from(10..4).contains(&1), true);
		assert_eq!(RangeWrapping::from(10..4).contains(&4), false);
		assert_eq!(RangeWrapping::from(10..4).contains(&5), false);
	}
}
