//! Implements a last-in-first-out data structure.

pub struct Stack<T>(Vec<T>);

impl<T> Stack<T> {
    /// Initiates an empty stack
    ///
    /// # Example
    /// ```
    /// # use colliflower::Stack;
    /// let stack: Stack<i32> = Stack::empty();
    ///
    /// assert_eq!(stack.depth(), 0);
    /// ```
    pub fn empty() -> Self { Self(vec![]) }

    /// Initiates an empty stack with space to push `capacity` elements.
    ///
    /// # Example
    /// ```
    /// # use colliflower::Stack;
    /// let stack: Stack<i32> = Stack::with_capacity(10);
    ///
    /// assert_eq!(stack.depth(), 0);
    /// assert_eq!(stack.capacity(), 10);
    /// ```
    pub fn with_capacity(capacity: usize) -> Self {
        Self(Vec::with_capacity(capacity))
    }

    /// The number of elements that can be pushed onto the stack before resizing.
    ///
    /// ```
    /// # use colliflower::Stack;
    /// let stack: Stack<i32> = Stack::empty();
    ///
    /// assert_eq!(stack.capacity(), 0);
    ///
    /// let mut stack: Stack<i32> = Stack::with_capacity(10);
    ///
    /// assert_eq!(stack.capacity(), 10);
    ///
    /// stack.npush(0..=10);
    ///
    /// assert!(stack.capacity() > 10);
    /// ```
    pub fn capacity(&self) -> usize { self.0.capacity() }

    /// Empties a stack
    ///
    /// # Example
    /// ```
    /// # use colliflower::Stack;
    /// let mut stack: Stack<i32> = Stack::from(vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9]);
    ///
    /// assert_eq!(stack.depth(), 10);
    ///
    /// stack.clear();
    ///
    /// assert_eq!(stack.depth(), 0);
    /// ```
    pub fn clear(&mut self) { self.0.clear() }

    /// The number of elements that can be pushed onto the stack before resizing.
    ///
    /// ```
    /// # use colliflower::Stack;
    /// let stack: Stack<i32> = Stack::empty();
    ///
    /// assert_eq!(stack.depth(), 0);
    ///
    /// let mut stack: Stack<i32> = Stack::with_capacity(10);
    ///
    /// assert_eq!(stack.depth(), 0);
    ///
    /// stack.npush(0..10);
    ///
    /// assert_eq!(stack.depth(), 10);
    /// ```
    pub fn depth(&self) -> usize { self.0.len() }

    /// Manipulates the stack one element below the top.
    ///
    /// When the stack is empty, `f` manipulates it as such.
    ///
    /// # Example
    /// ```
    /// # use colliflower::Stack;
    /// let mut stack: Stack<i32> = Stack::from(vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9]);
    ///
    /// stack.dip(|s| {
    ///     s.pop().map(|b|
    ///         s.pop().map(|a|
    ///             s.push(a + b)
    ///         )
    ///     );
    /// });
    ///
    /// assert_eq!(stack.pop(), Some(9));
    /// assert_eq!(stack.pop(), Some(15)); // 7 + 8
    /// assert_eq!(stack.pop(), Some(6));
    /// ```
    pub fn dip<F: FnMut(&mut Stack<T>)>(&mut self, mut f: F) {
        let last = self.0.pop();

        f(self);

        if let Some(last) = last { self.0.push(last); }
    }

    /// Removes the top element if one exists.
    ///
    /// # Example
    /// ```
    /// # use colliflower::Stack;
    /// let mut stack: Stack<i32> = Stack::empty();
    ///
    /// stack.drop(); // nothing happens
    ///
    /// stack.push(1);
    ///
    /// assert_eq!(stack.depth(), 1);
    ///
    /// stack.drop();
    ///
    /// assert_eq!(stack.depth(), 0);
    /// ```
    pub fn drop(&mut self) { self.0.pop(); }

    /// Whether a stack has any elements.
    ///
    /// ```
    /// # use colliflower::Stack;
    /// let stack: Stack<i32> = Stack::empty();
    ///
    /// assert!(stack.is_empty());
    ///
    /// let mut stack: Stack<i32> = Stack::with_capacity(10);
    ///
    /// assert!(stack.is_empty());
    ///
    /// stack.push(0);
    ///
    /// assert!(!stack.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool { self.0.is_empty() }

    pub fn iter(&self) -> impl Iterator<Item=&T> + '_ { self.0.iter().rev() }

    pub fn iter_rev(&self) -> impl Iterator<Item=&T> + '_ { self.0.iter() }

    /// Manipulates the stack `count` elements below the top.
    ///
    /// `ndip(1, f) === dip(f)`
    ///
    /// # Example
    /// ```
    /// # use colliflower::Stack;
    /// let mut stack: Stack<i32> = Stack::from(vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9]);
    ///
    /// stack.ndip(4, |s| {
    ///     s.pop().map(|b|
    ///         s.pop().map(|a|
    ///             s.push(a + b)
    ///         )
    ///     );
    /// });
    ///
    /// assert_eq!(stack.pop(), Some(9));
    /// assert_eq!(stack.pop(), Some(8));
    /// assert_eq!(stack.pop(), Some(7));
    /// assert_eq!(stack.pop(), Some(6));
    /// assert_eq!(stack.pop(), Some(9)); // 4 + 5
    /// ```
    pub fn ndip<F: FnMut(&mut Stack<T>)>(&mut self, count: usize, mut f: F) {
        let n = self.0.len();
        let count = if count > n { n } else { count };
        let popped = self.0.drain((n - count)..).collect::<Vec<_>>();

        f(self);

        self.0.extend(popped);
    }

    /// Removes the top element if one exists.
    ///
    /// # Example
    /// ```
    /// # use colliflower::Stack;
    /// let mut stack: Stack<i32> = Stack::empty();
    ///
    /// stack.drop(); // nothing happens
    ///
    /// stack.push(1);
    ///
    /// assert_eq!(stack.depth(), 1);
    ///
    /// stack.drop();
    ///
    /// assert_eq!(stack.depth(), 0);
    /// ```
    pub fn ndrop(&mut self, count: usize) {
        let n = self.0.len();
        let count = if count > n { 0 } else { n - count };
        self.0.truncate(count);
    }

    /// Drops the element one down from the top.
    ///
    /// Nothing happens if less than two elements are on the stack.
    ///
    /// # Example
    /// ```
    /// # use colliflower::Stack;
    /// let mut stack: Stack<i32> = Stack::empty();
    ///
    /// stack.nip();
    ///
    /// stack.push(0);
    ///
    /// stack.nip();
    ///
    /// assert_eq!(stack.peek(), Some(&0));
    ///
    /// stack.push(1);
    ///
    /// assert_eq!(stack.depth(), 2);
    /// assert_eq!(stack.peek(), Some(&1));
    ///
    /// stack.nip();
    ///
    /// assert_eq!(stack.depth(), 1);
    /// assert_eq!(stack.peek(), Some(&1));
    /// ```
    pub fn nip(&mut self) {
        match self.0.len() {
            0 | 1 => (),
            n => {
                self.0.swap_remove(n - 2);
            }
        }
    }

    /// Drops `count` elements one element down from the top.
    ///
    /// Every element but the top element is dropped if the stack has less than `count + 1`
    /// elements.
    ///
    ///
    /// # Example
    /// ```
    /// # use colliflower::Stack;
    /// let mut stack: Stack<i32> = Stack::empty();
    ///
    /// stack.nnip(4);
    ///
    /// assert!(stack.is_empty());
    ///
    /// stack.push(0);
    ///
    /// stack.nnip(4);
    ///
    /// assert_eq!(stack.peek(), Some(&0));
    ///
    /// stack.npush(1..4);
    ///
    /// assert_eq!(stack.depth(), 4);
    /// assert_eq!(stack.peek(), Some(&3));
    ///
    /// stack.nnip(4);
    ///
    /// assert_eq!(stack.depth(), 1);
    /// assert_eq!(stack.peek(), Some(&3));
    ///
    /// stack.npush(4..8);
    ///
    /// assert_eq!(stack.depth(), 5);
    /// assert_eq!(stack.peek(), Some(&7));
    ///
    /// stack.nnip(4);
    ///
    /// assert_eq!(stack.depth(), 1);
    /// assert_eq!(stack.peek(), Some(&7));
    /// ```
    pub fn nnip(&mut self, count: usize) {
        let n = self.0.len();

        if count == 0 || n < 2 { return; }

        let count = if count >= n { n - 1 } else { count };

        self.0.swap_remove(n - count - 1);
        self.0.truncate(1);
    }

    /// Removes and returns the `count` elements at the top of the stack.
    ///
    /// The returned order is the order in which the elements were popped off of
    /// the stack.
    ///
    /// If less than `count` elements are on the stack, the entire stack is drained.
    ///
    /// # Example
    /// ```
    /// # use colliflower::Stack;
    /// let mut stack: Stack<i32> = Stack::empty();
    ///
    /// assert_eq!(stack.npop(4), vec![]);
    ///
    /// stack.push(0);
    ///
    /// assert_eq!(stack.npop(4), vec![0]);
    /// assert!(stack.is_empty());
    ///
    /// stack.npush(0..5);
    ///
    /// assert_eq!(stack.npop(4), vec![4, 3, 2, 1]);
    /// assert_eq!(stack.peek(), Some(&0));
    /// ```
    pub fn npop(&mut self, count: usize) -> Vec<T> {
        let n = self.0.len();
        let count = if count > n { 0 } else { n - count };

        self.0.drain(count..).rev().collect::<Vec<_>>()
    }

    /// Pushes an iterator of elements onto the stack with the last element at the top.
    ///
    /// # Example
    /// ```
    /// # use colliflower::Stack;
    /// let mut stack: Stack<i32> = Stack::from(vec![0, 1, 2, 3, 4]);
    ///
    /// assert_eq!(stack.depth(), 5);
    /// assert_eq!(stack.peek(), Some(&4));
    ///
    /// stack.npush(5..10);
    ///
    /// assert_eq!(stack.depth(), 10);
    /// assert_eq!(stack.peek(), Some(&9));
    /// ```
    pub fn npush<I: IntoIterator<Item=T>>(&mut self, values: I) { self.0.extend(values); }

    /// Rotates the top `count` elements to the left by `distance`.
    ///
    /// # Example
    /// ```
    /// # use colliflower::Stack;
    /// let mut stack = Stack::from(vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9]);
    ///
    /// stack.nroll(7, 3);
    ///
    /// assert_eq!(stack.npop(7), vec![5, 4, 3, 9, 8, 7, 6]);
    /// ```
    pub fn nroll(&mut self, count: usize, distance: usize) {
        match self.0.len() {
            n if n < count => panic!("expected {} operands", n),
            n if n == count => self.unroll(distance),
            1 => (),
            n => {
                let distance = distance % count;

                if distance == 0 { return; }

                let left_slice_start = n - count;
                let right_slice_start = left_slice_start + distance;

                self.0[left_slice_start..right_slice_start].reverse();
                self.0[right_slice_start..].reverse();
                self.0[left_slice_start..].reverse();
            }
        }
    }

    /// Rotates the top `count` elements to the right by `distance`.
    ///
    /// # Example
    /// ```
    /// # use colliflower::Stack;
    /// let mut stack = Stack::from(vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9]);
    ///
    /// stack.nunroll(7, 3);
    ///
    /// assert_eq!(stack.npop(7), vec![6, 5, 4, 3, 9, 8, 7]);
    /// ```
    pub fn nunroll(&mut self, count: usize, distance: usize) {
        match self.0.len() {
            n if n < count => panic!("expected {} operands", n),
            n if n == count => self.unroll(distance),
            1 => (),
            n => {
                let distance = distance % count;

                if distance == 0 { return; }

                let left_slice_start = n - count;
                let right_slice_start = n - distance;

                self.0[right_slice_start..].reverse();
                self.0[left_slice_start..right_slice_start].reverse();
                self.0[left_slice_start..].reverse();
            }
        }
    }

    /// Returns a reference to the elment at the top of the stack.
    ///
    /// # Example
    /// ```
    /// # use colliflower::Stack;
    /// let mut stack: Stack<i32> = Stack::empty();
    ///
    /// assert_eq!(stack.peek(), None);
    ///
    /// stack.push(0);
    ///
    /// assert_eq!(stack.peek(), Some(&0));
    /// ```
    pub fn peek(&self) -> Option<&T> { self.0.last() }

    /// Removes and returns the elment at the top of the stack.
    ///
    /// # Example
    /// ```
    /// # use colliflower::Stack;
    /// let mut stack: Stack<i32> = Stack::empty();
    ///
    /// assert_eq!(stack.pop(), None);
    ///
    /// stack.push(0);
    ///
    /// assert_eq!(stack.pop(), Some(0));
    /// ```
    pub fn pop(&mut self) -> Option<T> { self.0.pop() }

    /// Pushes an element onto the stack.
    ///
    /// # Example
    /// ```
    /// # use colliflower::Stack;
    /// let mut stack: Stack<i32> = Stack::empty();
    ///
    /// assert_eq!(stack.depth(), 0);
    /// assert_eq!(stack.peek(), None);
    ///
    /// stack.push(0);
    ///
    /// assert_eq!(stack.depth(), 1);
    /// assert_eq!(stack.peek(), Some(&0));
    /// ```
    pub fn push(&mut self, value: T) { self.0.push(value) ; }

    /// Rotates the entire stack to the left by `distance`.
    ///
    /// # Example
    /// ```
    /// # use colliflower::Stack;
    /// let mut stack = Stack::from(vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9]);
    ///
    /// stack.roll(3);
    ///
    /// assert_eq!(stack.npop(10), vec![2, 1, 0, 9, 8, 7, 6, 5, 4, 3]);
    /// ```
    pub fn roll(&mut self, distance: usize) {
        match self.0.len() {
            0 | 1 => (),
            n => {
                let distance = distance % n;

                if distance == 0 { return; }

                self.0[..distance].reverse();
                self.0[distance..].reverse();
                self.0.reverse();
            }
        }
    }

    /// Swaps the two elements one down from the top.
    ///
    /// Nothing happens if less than two elements are on the stack.
    ///
    /// # Example
    /// ```
    /// # use colliflower::Stack;
    /// let mut stack: Stack<i32> = Stack::empty();
    ///
    /// stack.swap();
    /// stack.push(0);
    /// stack.swap();
    ///
    /// assert_eq!(stack.peek(), Some(&0));
    ///
    /// stack.push(1);
    /// stack.swap();
    ///
    /// assert_eq!(stack.peek(), Some(&0));
    /// ```
    pub fn swap(&mut self) {
        match self.0.len() {
            0 | 1 => (),
            n => self.0.swap(n - 1, n - 2)
        }
    }

    /// Swaps the two elements one down from the top.
    ///
    /// Nothing happens if less than three elements are on the stack.
    ///
    /// # Example
    /// ```
    /// # use colliflower::Stack;
    /// let mut stack: Stack<i32> = Stack::empty();
    ///
    /// stack.swapd();
    /// stack.push(0);
    /// stack.swapd();
    ///
    /// assert_eq!(stack.peek(), Some(&0));
    ///
    /// stack.npush(1..4);
    /// stack.swapd();
    ///
    /// assert_eq!(stack.pop(), Some(3));
    /// assert_eq!(stack.pop(), Some(1));
    /// assert_eq!(stack.pop(), Some(2));
    /// ```
    pub fn swapd(&mut self) {
        match self.0.len() {
            0 | 1 | 2 => (),
            n => self.0.swap(n - 3, n - 2)
        }
    }

    /// Rotates the entire stack to the right by `distance`.
    ///
    /// # Example
    /// ```
    /// # use colliflower::Stack;
    /// let mut stack = Stack::from(vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9]);
    ///
    /// stack.unroll(3);
    ///
    /// assert_eq!(stack.npop(10), vec![6, 5, 4, 3, 2, 1, 0, 9, 8, 7]);
    /// ```
    pub fn unroll(&mut self, distance: usize) {
        match self.0.len() {
            0 | 1 => (),
            n => {
                let distance = distance % n;

                if distance == 0 { return; }

                self.0[(n - distance)..].reverse();
                self.0[..(n - distance)].reverse();
                self.0.reverse();
            }
        }
    }
}

impl<T: Clone> Stack<T> {
    /// Duplicates the element at the top of the stack.
    ///
    /// Nothing happens if the stack is empty.
    ///
    /// # Example
    /// ```
    /// # use colliflower::Stack;
    /// let mut stack: Stack<i32> = Stack::empty();
    ///
    /// stack.dup();
    ///
    /// assert_eq!(stack.depth(), 0);
    ///
    /// stack.push(0);
    /// stack.dup();
    ///
    /// assert_eq!(stack.depth(), 2);
    /// assert_eq!(stack.peek(), Some(&0));
    /// ```
    pub fn dup(&mut self) {
        match self.0.len() {
            0 => (),
            n => {
                let last = self.0[n - 1].clone();
                self.0.push(last);
            }
        }
    }

    /// Duplicates the element one down from the top of the stack then swaps the top two elements.
    ///
    /// Nothing happens if the stack has less than two elements.
    ///
    /// ```plaintext
    /// dupd === swap dup nroll(3, 1) === over swap
    ///
    /// ...             -- [x, y, z]
    /// over            -- [x, y, z, y]
    /// swap            -- [x, y, y, z]
    /// ```
    ///
    /// # Example
    /// ```
    /// # use colliflower::Stack;
    /// let mut stack: Stack<i32> = Stack::empty();
    ///
    /// stack.dupd();
    ///
    /// assert!(stack.is_empty());
    ///
    /// stack.push(0);
    /// stack.dupd();
    ///
    /// assert_eq!(stack.depth(), 1);
    /// assert_eq!(stack.peek(), Some(&0));
    ///
    /// stack.push(1);
    /// stack.dupd();
    ///
    /// assert_eq!(stack.depth(), 3);
    /// assert_eq!(stack.pop(), Some(1));
    /// assert_eq!(stack.peek(), Some(&0));
    /// ```
    pub fn dupd(&mut self) {
        match self.0.len() {
            0 | 1 => (),
            n => {
                let second = self.0[n - 2].clone();
                self.0.push(second);
                self.0.swap(n - 1, n);
            }
        }
    }

    /// Duplicates the element at the top of the stack `count` times.
    ///
    /// Nothing happens if the stack is empty.
    ///
    /// # Example
    /// ```
    /// # use colliflower::Stack;
    /// let mut stack: Stack<i32> = Stack::empty();
    ///
    /// stack.dupn(4);
    ///
    /// assert_eq!(stack.depth(), 0);
    ///
    /// stack.push(0);
    /// stack.dupn(4);
    ///
    /// assert_eq!(stack.depth(), 5);
    /// assert_eq!(stack.peek(), Some(&0));
    /// ```
    pub fn dupn(&mut self, count: usize) {
        match self.0.len() {
            0 => (),
            n => {
                let last = self.0[n - 1].clone();
                self.0.resize(n + count, last);
            }
        }
    }

    /// Duplicates the top `count` elements of the stack.
    ///
    /// Nothing happens if the stack is empty. The whole stack is cloned if less than `count`
    /// elements are in the stack.
    ///
    /// # Example
    /// ```
    /// # use colliflower::Stack;
    /// let mut stack: Stack<i32> = Stack::empty();
    ///
    /// stack.ndup(4);
    ///
    /// assert_eq!(stack.depth(), 0);
    ///
    /// stack.push(0);
    /// stack.ndup(4);
    ///
    /// assert_eq!(stack.depth(), 2);
    /// assert_eq!(stack.pop(), Some(0));
    ///
    /// stack.npush(1..5);
    ///
    /// assert_eq!(stack.depth(), 5);
    ///
    /// stack.ndup(4);
    ///
    /// assert_eq!(stack.depth(), 9);
    /// assert_eq!(stack.pop(), Some(4));
    /// assert_eq!(stack.pop(), Some(3));
    /// assert_eq!(stack.pop(), Some(2));
    /// assert_eq!(stack.pop(), Some(1));
    /// ```
    pub fn ndup(&mut self, count: usize) {
        let n = self.0.len();

        if n == 0 { return; }

        let start = if count > n { 0 } else { n - count };
        self.0.reserve(n - start);

        for i in start..n {
            self.0.push(self.0[i].clone());
        }
    }

    /// Duplicates the element one down from the top.
    ///
    /// Nothing happens if less than two elements are on the stack.
    ///
    /// ```plaintext
    /// over === swap dup nunroll(3, 1)
    ///
    /// ...             -- [x, y, z]
    /// swap            -- [x, z, y]
    /// dup             -- [x, z, y, y]
    /// nunroll(3, 1)   -- [x, y, z, y]
    /// ```
    ///
    /// # Example
    /// ```
    /// # use colliflower::Stack;
    /// let mut stack: Stack<i32> = Stack::empty();
    ///
    /// stack.over();
    ///
    /// assert!(stack.is_empty());
    ///
    /// stack.push(0);
    /// stack.over();
    ///
    /// assert_eq!(stack.peek(), Some(&0));
    ///
    /// stack.push(1);
    /// stack.over();
    ///
    /// assert_eq!(stack.depth(), 3);
    /// assert_eq!(stack.pop(), Some(0));
    /// assert_eq!(stack.peek(), Some(&1));
    /// ```
    pub fn over(&mut self) {
        match self.0.len() {
            0 | 1 => (),
            n => {
                let second = self.0[n - 2].clone();
                self.0.push(second);
            }
        }
    }
}

impl<T> From<Vec<T>> for Stack<T> {
    /// Creates a stack from a vector of elements with the last element on top.
    ///
    /// # Example
    /// ```
    /// # use colliflower::Stack;
    /// let mut stack: Stack<i32> = Stack::from(vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9]);
    ///
    /// assert_eq!(stack.peek(), Some(&9));
    /// ```
    fn from(vec: Vec<T>) -> Self { Self(vec) }
}

impl<const N: usize, T> From<[T; N]> for Stack<T> {
    /// Creates a stack from a vector of elements with the last element on top.
    ///
    /// # Example
    /// ```
    /// # use colliflower::Stack;
    /// let mut stack: Stack<i32> = Stack::from(vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9]);
    ///
    /// assert_eq!(stack.peek(), Some(&9));
    /// ```
    fn from(array: [T; N]) -> Self { Self(Vec::from(array)) }
}

impl<T: Clone> From<&[T]> for Stack<T> {
    /// Creates a stack from a slice of clone-able elements with the last element on top.
    ///
    /// # Example
    /// ```
    /// # use colliflower::Stack;
    /// let elements = vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9];
    /// let mut stack: Stack<i32> = Stack::from(elements.as_slice());
    ///
    /// assert_eq!(stack.peek(), Some(&9));
    /// ```
    fn from(slice: &[T]) -> Self { Self::from(slice.to_vec()) }
}

impl<T> FromIterator<T> for Stack<T> {
    /// Creates a stack from an iterator of elements with the last element on top.
    ///
    /// # Example
    /// ```
    /// # use colliflower::Stack;
    /// let mut stack: Stack<i32> = Stack::from_iter(0..10);
    ///
    /// assert_eq!(stack.peek(), Some(&9));
    /// ```
    fn from_iter<I: IntoIterator<Item=T>>(iter: I) -> Self { Self(Vec::from_iter(iter)) }
}

impl<T> IntoIterator for Stack<T> {
    type Item = T;
    type IntoIter = std::iter::Rev<std::vec::IntoIter<T>>;

    /// An iterator over elements of the stack
    ///
    /// # Example
    /// ```
    /// # use colliflower::Stack;
    fn into_iter(self) -> Self::IntoIter { self.0.into_iter().rev() }
}