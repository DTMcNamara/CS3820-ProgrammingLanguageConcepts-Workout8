module gc where

open import lib

-- we will model addresses in memory as just natural numbers
Address : Set
Address = ℕ

-- a value of type (Bounded n) is an address a together with a proof that a is less than n
Bounded : Address → Set
Bounded n = Σ Address (λ a → a < n ≡ tt)

-- a (Cell a) models an addressable cell of memory
data Cell(bound : Address) : Set where
  Scalar : ℕ → Cell bound -- this represents a cell with no outgoing pointers, just a natural number value
  Pointers : ∀ (p1 p2 : Bounded bound) → Cell bound -- this cell has exactly two outgoing pointers

{- a (well-formed) memory is a vector of m cells, where all pointers in those cells are bounded by n.
   This is just a way of expressing that the memory does not have any pointers heading off to some
   illegal locations (outside the allocated memory). -}
Memory : Address → Set
Memory m = 𝕍 (Cell m) m

-- return a list of natural numbers from n-1 down to 0. [5 points]
nats : ∀(n : ℕ) → 𝕍 ℕ n
nats zero = []
nats (suc n) = n :: (nats n)

-- when the definition of nats is correct, the highlighting will disappear from refl below:
test-nats : nats 3 ≡ 2 :: 1 :: 0 :: []
test-nats = refl

{- (outgoingPointers m mem b) returns the list of outgoing pointers at the location
   given by b in the Memory m.  This is either empty (for Scalar) or a list of length
   two (for Pointers).

   Hint: there is already a function in vector.agda in the IAL that can find the Cell
   for you from mem and b. 

   [10 points] -}
outgoingPointers : ∀ (m : Address) → Memory m → Bounded m → 𝕃 (Bounded m)
outgoingPointers n mem (j , k) with (nth𝕍 j k mem)
... | Scalar c = []
... | Pointers x y = x :: y :: []

{- (doMark u unmarked m b) is supposed to return (just v) if the address
   given by b is a member of unmarked, and v is the result of removing that
   address from unmarked.  If the address given by b is not in unmarked,
   then return none. This function simulates marking a cell by removing
   it (if it is there) from the vector of unmarked cells.  Because the
   length of the vector decreases, we can recurse in markh on the result
   if we need to. 

   [17 points]
-}
doMark : ∀(u : ℕ)(unmarked : 𝕍 Address (suc u)) → (m : Address) → Bounded m → maybe (𝕍 Address u)
doMark u ( x :: unmarked ) m ( a , b ) with ( a =ℕ x )
... | tt = just unmarked
doMark 0 ( x :: [] ) m ( a , b ) | ff = nothing
doMark ( suc u ) ( x :: x1 :: unmarked ) m ( a , b ) | ff with ( doMark u ( x1 :: unmarked ) m ( a , b ) )
... | nothing = nothing
... | just unmarked1 = just ( x :: unmarked1 )

{- given a list of unmarked addresses and a Memory m, and a worklist of addresses,  return the 
   list of all unmarked addresses that are not reachable in the memory from an address in the
   worklist.  So this is basically implementing mark and sweep gc, where addresses are considered
   marked if they do not appear in unmarked, and you use outgoingPointers to update the worklist
   when it is time to recurse. 

   [18 points] 
-}
markh : ∀(u : ℕ)(unmarked : 𝕍 Address u) → (m : Address) → Memory m → (worklist : 𝕃 (Bounded m)) → 𝕃 Address
markh u [] m x worklist = []
markh u unmarked m x [] = 𝕍-to-𝕃 unmarked
markh ( suc u ) unmarked m x ( x1 :: worklist ) with ( doMark u unmarked m x1 )
... | nothing = markh ( suc u ) unmarked m x worklist
... | just something = markh u something m x ( worklist ++ ( outgoingPointers m x x1 ) )

{- the final mark-and-sweep function, which just takes in a memory and list of roots, and
   returns the addresses not reachable in that memory from one of the roots. -}
mark : ∀(m : Address) → Memory m → (roots : 𝕃 (Bounded m)) → 𝕃 Address
mark m memory roots = markh m (nats m) m memory roots

----------------------------------------------------------------------
-- a test case:

test-memory : Memory 3
test-memory = Pointers (0 , refl) (2 , refl) :: Pointers (0 , refl) (2 , refl) :: Pointers (0 , refl) (0 , refl) :: []

test-roots : 𝕃 (Bounded 3)
test-roots = [ (0 , refl) ]

-- the addresses not reachable from address 0 by following pointers in test-memory
test-garbage : 𝕃 Address
test-garbage = mark 3 test-memory test-roots

-- if the implementation above is correct, highlighting on refl below will disappear
test-check : test-garbage ≡ 1 :: []
test-check = refl
