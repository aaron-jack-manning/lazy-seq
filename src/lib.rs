//! # Lazy Seq
//!
//! `lazy_seq` is a crate containing tools for lazily evaluated
//! collections, specifically Seq which is a collection of lazily
//! evaluated functions, and Lazy, which is the primitive used for lazy
//! evaluation.

/// Stores an operation which can be evaluated when required.
pub struct Lazy<T> {
    f : Option<Box<dyn FnOnce() -> T>>,
    val : Option<T>,
}

impl<T> Lazy<T> {
    /// Constructs a new `Lazy<T>` from a closure implementing `FnOnce() -> T`. 
    pub fn new<F : FnOnce() -> T + 'static>(f : F) -> Lazy<T> {
        Lazy {
            f : Some(Box::new(f)),
            val : None, 
        }
    }

    /// Forces evaluation of the underlying function.
    pub fn force(&mut self) {
        if self.f.is_some() {
            let mut f = None;
            std::mem::swap(&mut f, &mut self.f);

            let f = f.unwrap();
            let result = (f)();
            self.val = Some(result);
        }
    }

    /// Forces evaluation of the underlying function and returns the inside value, consuming
    /// the `Lazy<T>`.
    pub fn into_inner(mut self) -> T {
        self.force();
        let Lazy { f : _ , val } = self;
        val.unwrap()
    }

    /// Returns an immutable reference to the result of the function.
    pub fn as_ref(&mut self) -> &T {
        self.force();
        self.val.as_ref().unwrap()
    }
}

impl<T> AsMut<T> for Lazy<T> {
    /// Returns a mutable reference to the result of the function.
    fn as_mut(&mut self) -> &mut T {
        self.force();
        self.val.as_mut().unwrap()
    }
}

impl<T> Default for Lazy<T>
    where T : Default {
    fn default() -> Self {
        Lazy {
            f : None,
            val : Some(T::default())
        }
    }
}

/// A lazily evaluated sequence of functions.
pub struct Seq<T>(Vec<Lazy<T>>);

impl<T> Seq<T> {
    /// Constructs a new, empty `Seq<T>`.
    pub fn new() -> Seq<T> {
        Seq(Vec::new())
    }

    /// Returns `true` if the sequence contains no elements.
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    // Returns the number of elements the sequence can hold without reallocating.
    pub fn capacity(&self) -> usize {
        self.0.capacity()
    }

    /// Returns the number of elements in the sequence, also referred to as its ‘length’.
    pub fn len(&self) -> usize {
        self.0.len()
    }

    /// Constructs a new, empty `Seq<T>` with the specified capacity.
    pub fn with_capacity(capacity : usize) -> Seq<T> {
        Seq(Vec::with_capacity(capacity))
    }

    /// Appends the provided function to the back of the collection.
    pub fn push<F : FnOnce() -> T + 'static>(&mut self, value : F) {
        self.0.push(Lazy::new(value))
    }

    /// Forces evaluation of the last function in the sequence, returning the result.
    pub fn pop(&mut self) -> Option<T> {
        let lazy = self.0.pop();
        lazy.map(|l| l.into_inner())
    }

    /// Evaluates all unevaluated functions within the Seq.
    pub fn force_all(&mut self) {
        for i in 0..self.0.len() {
            self.0[i].force()
        }
    }

    /// Converts a `Seq<T>` to a `Vec<T>` by forcing evaluation of all functions.
    pub fn to_vec(self) -> Vec<T> {
        let Seq(vec) = self;

        vec
        .into_iter()
        .map(|x| x.into_inner())
        .collect()
    }

    /// Converts a `Seq<T>` to a `Vec<Lazy<T>>` without evaluating any additional
    /// functions.
    pub fn to_lazy_vec(self) -> Vec<Lazy<T>> {
        let Seq(vec) = self;
        vec
    }

    /// Gets an immutable reference to the value at the specified index.
    pub fn get(&mut self, index : usize) -> Option<&T> {
        self.0.get_mut(index).map(|l| { l.force(); l.as_ref() })
    }

    /// Gets a mutable reference to the value at the specified index.
    pub fn get_mut(&mut self, index : usize) -> Option<&mut T> {
        self.0.get_mut(index).map(|l| { l.force(); l.as_mut() })
    }
}

impl<T> From<Vec<Box<dyn FnOnce() -> T>>> for Seq<T> {
    fn from(vec : Vec<Box<dyn FnOnce() -> T>>) -> Self {
        Seq(
            vec
            .into_iter()
            .map(|b| Lazy { f : Some(b), val : None })
            .collect()
        )
    }
}

impl<T> From<Vec<T>> for Seq<T> {
    fn from(vec : Vec<T>) -> Self {
        Seq(
            vec
            .into_iter()
            .map(|v| Lazy { f : None, val : Some(v) })
            .collect()
        )
    }
}

impl<T> Default for Seq<T> {
    fn default() -> Self {
        Self::new()
    }
}

/// Constructs a Seq from a literal in a similar way that vec! does for Vec.
#[macro_export]
macro_rules! seq {
    () => (
        lazy_seq::Seq::new()
    );
    ($elem:expr; $n:expr) => (
        {
            let mut seq = Seq::with_capacity($n);
            for _ in 0..$n {
                seq.push($elem);
            }
            seq
        }
    );
    ($($x:expr),+ $(,)?) => (
        {
            let mut seq = Seq::new();
            $(seq.push($x);)*
            seq
        }
    );
}

#[cfg(test)]
mod tests {
    use std::rc::Rc;
    use std::cell::RefCell;
    use crate::{Lazy, Seq, seq};
    #[test]
    pub fn lazy_correct() {
        let counter = Rc::new(RefCell::new(0));
        let counter_new = counter.clone();
        let mut lazy = Lazy::new(
            move || {
                *counter_new.borrow_mut() += 1;
                5 + 5
            });
        let result = lazy.as_ref();
        assert_eq!(10, *result);
    }

    #[test]
    pub fn seq_correct() {

        let counter = Rc::new(RefCell::new(0));
        let counter_new = counter.clone();

        let mut seq = seq![
            || { 0 }; 9
        ];

        assert_eq!(9, seq.len());

        seq.push(move || {
            *counter_new.borrow_mut() += 1;
            println!("{:?}", counter_new);
            5 + 5
        });

        assert_eq!(10, seq.len());

        assert_eq!(0, *counter.borrow());

        let _ = seq.get(9).unwrap();

        assert_eq!(1, *counter.borrow());

        seq.force_all();
        let result = seq.pop();
        assert_eq!(9, seq.len());
        assert_eq!(1, *counter.borrow());
        assert_eq!(10, result.unwrap());
    }
}
