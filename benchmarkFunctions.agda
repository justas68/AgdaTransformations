module benchmarkFunctions where

open import Agda.Builtin.Bool
open import Agda.Builtin.Equality
open import Agda.Builtin.Nat public

_>_ : Nat -> Nat -> Bool
0 > m = false
n > 0 = true
(suc n) > (suc m) = n > m

_eq_ : Nat -> Nat -> Bool
0 eq 0 = true
0 eq m = false
n eq 0 = false
(suc n) eq (suc m) = n eq m

_! : Nat -> Nat
0 ! = 1
(suc n) ! = (suc n) * (n !)

data List (A : Set) : Set where
  empty  : List A
  append : A → List A → List A
{-# BUILTIN LIST List #-}

data Vec (A : Set) : Nat -> Set where
  emptyV : Vec A zero
  appendV : {n : Nat} -> A -> Vec A n -> Vec A (suc n)

isPrime : Nat -> Bool
isPrime 0 = false
isPrime 1 = false
isPrime n with dividersCount n n
  where
  dividersCount : Nat -> Nat -> Nat
  dividersCount 0 _ = 0
  dividersCount _ 0 = 0
  dividersCount (suc n) m with mod-helper 0 n m n
  dividersCount (suc n) m | 0 = suc (dividersCount n m)
  dividersCount (suc n) m | _ = dividersCount n m
isPrime n | 2 = true
isPrime n | _ = false  

countPrimes : Nat -> Nat
countPrimes 0 = 0
countPrimes (suc n) with isPrime (suc n)
countPrimes (suc n) | false = countPrimes n
countPrimes (suc n) | true = suc (countPrimes n)

{-# TERMINATING #-}
bubblesortiter : ∀ {n} -> Vec Nat n -> Vec Nat n
bubblesortiter (appendV x (appendV y xs)) with  x > y
bubblesortiter (appendV x (appendV y xs)) | true  = appendV y (bubblesortiter (appendV x xs))
bubblesortiter (appendV x (appendV y xs)) | false  = appendV x (bubblesortiter (appendV y xs))
bubblesortiter x = x


{-# TERMINATING #-}
bubblesort' : ∀ {n} -> Vec Nat n -> Nat -> Vec Nat n
bubblesort' {n} xs i  with n eq i
bubblesort' {n} xs i | true = xs
bubblesort' {n} xs i | false = bubblesort' (bubblesortiter xs) (suc i)
 
bubblesort : ∀ {n} -> Vec Nat n -> Vec Nat n
bubblesort xs = bubblesort' xs 0

testList : Vec Nat 6
testList = appendV 21 (appendV 3 (appendV 5 (appendV 7 (appendV 99 (appendV 1 emptyV)))))

testListSorted : Vec Nat 6
testListSorted = appendV 1 (appendV 3 (appendV 5 (appendV 7 (appendV 21 (appendV 99 emptyV)))))

testListIsSorted : testListSorted ≡ (bubblesort testList)
testListIsSorted = refl