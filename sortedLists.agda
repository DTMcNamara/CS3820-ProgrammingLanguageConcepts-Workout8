module sortedLists where

open import lib

{- we use internal verification to define a datatype of sorted lists
   of natural numbers, where typing ensures that the lists are truly
   sorted in non-decreasing order.

   A list of type (sortedList n) is sorted and guaranteed to have 
   all its data greater than or equal to n; so n is a lower bound
   on the data in the list.  Keeping this lower bound explicit in
   the type enables us to require a proof of a constant-time check,
   namely d ≤ n, when insert d into a list with lower-bound n.  For
   cons nodes, we allow the lower-bound to be less than the head of
   the list.  This is needed for merge below.

   There are three constructors:

   -- nil, as usual (empty list)
   -- cons, as usual (build a new list from head and tail)
   -- weaken, decrease the lower bound (this was missing in my first
      attempt, which led to nasty problems in the case of merge below)

 -}

data sortedList : ℕ → Set where
  nil : ∀ (n : ℕ) → sortedList n  -- empty lists can have any lower bound you like
  cons : ∀ (d : ℕ) → -- the head of the list
           {n : ℕ} → -- the lower-bound for the tail
           sortedList n → -- the tail of the list, with lower bound n on its data
           d ≤ n ≡ tt → {- proof that d is less than or equal to that lower bound, and
                           hence less than or equal to all data in the tail -}
           sortedList d -- d is the lower bound for the new list created by the cons
  weaken : ∀ (n : ℕ) {n' : ℕ} → sortedList n' → n ≤ n' ≡ tt → sortedList n

-- fill in the holes below, just to help you get a feel for how the sortedList datatype works
-- [5 points]
simple : sortedList 1
simple = weaken 1 (cons 2 (nil 3) refl)refl

{- glb stands for greatest lower bound.  min d n is the greatest 
   lower bound of d and n, in the sense that if any other d' is a lower bound 
   of both d and n, then it is also a lower bound of min d n.  (Ideas from 
   basic lattice theory.) 

   To prove this, you will run into a mess if you case split on d', d, or n.
   Instead, you should consider cases for whether or not d < n.  You can use
   "with" for this, as discussed in Section 4.3.3 (page 86) of the book. 
   -}
-- [10 points]
glb : ∀ d' d n → d' ≤ d ≡ tt → d' ≤ n ≡ tt → d' ≤ min d n ≡ tt
glb d' d n x y with keep (d < n)
... | tt , p rewrite p = x
... | ff , p rewrite p = y
{- insert d xs should insert d into xs as the right position to keep the list
   sorted.  

   So you will case split on xs (the sortedList), and in the cons case, 
   consider whether the data you are inserting is ≤ the data at the head of the
   list.

   I found I needed to use the "with keep" idiom; see Section 4.3.3 (page 90).

   Another hint: I also needed a few theorems from nat-thms.agda in the IAL: 

     <≤, min-mono2, <ff

  Note that you can pattern match on implicit arguments, for example for a cons, like this:

  (cons d' {n} xs x)

  The {n} is used to match on that implicit lower-bound for the sortedList xs.

  [15 points]
-}

insert : ∀ (d : ℕ) → {n : ℕ} → sortedList n → sortedList (min d n)
insert d (nil n) with keep ( d < n )
... | tt , p rewrite p = cons d (nil n) (<≤ {d} p)
... | ff , p rewrite p = weaken n (cons d (nil d) (≤-refl d)) (<ff {d} p)

insert d (cons d1 {n} xs x) with keep ( d < d1 )
... | tt , p rewrite p = cons d ( cons d1 {n} xs x ) ( <≤ {d} {d1} p ) 
... | ff , p rewrite p  = cons d1 (nil d) (<ff {d} {d1} p )

insert d (weaken d1 {n} xs x) with keep ( d < d1 )
... | tt , p rewrite p =  cons d ( weaken d1 xs x ) ( <≤ {d} p )
... | ff , p rewrite p = weaken d1 (insert d xs) (glb d1 d n (<ff {d} p) x)
{- Write code to merge two sorted lists.

   I found I needed these lemmas from the IAL:

   min-<1, min-<2, <ff, <≤

   Additionally, I found I could save myself some cases by considering these cases for two input lists:

     nil and ys

     xs and nil

     weaken and ys

     xs and weaken

     cons and cons

   This is just five cases, instead of the nine that would be required if you considered the three
   cases for the first list simultaneously with the three for the second (3 * 3 gives 9 cases).
   You will see light gray highlighting on the patterns in the cases if you do this, but that
   is ok (it is just Agda warning you that you are not breaking out all the cases explicitly).

   [20 points]
-}
merge : ∀ {n : ℕ} → sortedList n → {m : ℕ} → sortedList m → sortedList (min n m)
merge (nil d) (nil d1) with keep ( d < d1 )
... | tt , p rewrite p = weaken d (nil d1) (<≤ {d} p)
... | ff , p rewrite p = weaken d1 (nil d) (<ff {d} p)
merge (nil d) (cons d1 d1s pd1) with keep ( d < d1 )
... | tt , p rewrite p = weaken d (cons d1 d1s pd1 ) ( <≤ {d} p)
... | ff , p rewrite p = cons d1 d1s pd1
merge ( nil d ) ( weaken d1 d1s pd1 ) with keep ( d < d1 )
... | tt , p rewrite p = weaken d ( weaken d1 d1s pd1 ) ( <≤ {d} p )
... | ff , p rewrite p = weaken d1 d1s pd1
merge ( cons d ds pd ) ( nil d1 ) with keep ( d < d1 )
... | tt , p rewrite p = cons d ds pd
... | ff , p rewrite p = weaken d1 ( cons d ds pd ) ( <ff {d} p )
merge ( cons d {dn} ds pd ) ( cons d1 {d1n} d1s pd1 ) with keep ( d < d1 )
... | tt , p rewrite p = cons d ( merge ds ( cons d1 d1s pd1 ) ) ( glb d dn d1 pd ( <≤ {d} p ) )
... | ff , p rewrite p = cons d1 ( merge d1s ( cons d ds pd) ) ( glb d1 d1n d pd1 ( <ff {d} p ) ) 
merge ( cons d {dn} ds pd ) ( weaken d1 {d1n} d1s pd1 ) with keep ( d < d1 )
... | tt , p rewrite p = cons d ( merge ds ( weaken d1 d1s pd1 ) ) ( glb d dn d1 pd ( <≤ {d} p ) )
... | ff , p rewrite p = weaken d1 ( merge d1s ( cons d ds pd ) ) ( glb d1 d1n d pd1 ( <ff {d} p ) )
merge ( weaken d ds pd ) ( nil d1 ) with keep ( d < d1 )
... | tt , p rewrite p = weaken d ds pd
... | ff , p rewrite p = weaken d1 ( weaken d ds pd ) ( <ff {d} p )
merge ( weaken d {dn} ds pd ) ( cons d1 {d1n} d1s pd1 ) with keep ( d < d1 )
... | tt , p rewrite p = weaken d ( merge ds ( cons d1 d1s pd1 ) ) ( glb d dn d1 pd ( <≤ {d} p ) )
... | ff , p rewrite p = cons d1 ( merge d1s ( weaken d ds pd ) ) ( glb d1 d1n d pd1 ( <ff {d} p ) )
merge ( weaken d {dn} ds pd ) ( weaken d1 {d1n} d1s pd1 ) with keep ( d < d1 )
... | tt , p rewrite p = weaken d ( merge ds ( weaken d1 d1s pd1 ) ) ( glb d dn d1 pd ( <≤ {d} p ) )
... | ff , p rewrite p = weaken d1 ( merge d1s ( weaken d ds pd ) ) ( glb d1 d1n d pd1 ( <ff {d} p ) )
