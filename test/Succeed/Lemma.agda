-- This tests translation between Lemma postcondition on insertion sort (on the Nat type).

module Lemma where

open import Haskell.Prelude
open import Agda.Builtin.Equality
open import Haskell.Extra.Refinement

-- ============================================================================
-- SETUP 
-- ============================================================================

insert : Nat → List Nat → List Nat
insert x []       = x ∷ []
insert x (y ∷ ys) = if x <= y then x ∷ y ∷ ys else y ∷ insert x ys

{-# COMPILE AGDA2HS insert #-}

sort : List Nat → List Nat
sort []       = []
sort (x ∷ xs) = insert x (sort xs)

{-# COMPILE AGDA2HS sort #-}

isSorted : List Nat → Bool
isSorted []           = True
isSorted (x ∷ [])     = True
isSorted (x ∷ y ∷ xs) = (x <= y) && isSorted (y ∷ xs)

{-# COMPILE AGDA2HS isSorted #-}

data Sorted : List Nat → Set where
  sorted-nil  : Sorted []
  sorted-one  : ∀ {x} → Sorted (x ∷ [])
  sorted-cons : ∀ {x y xs} → IsTrue (x <= y)
              → Sorted (y ∷ xs) → Sorted (x ∷ y ∷ xs)


-- ============================================================================
-- FORM 1: LEMMAS
-- ============================================================================

postulate

  -- 1a: Bool predicate
  @0 sortIsSortedLemma : ∀ (xs : List Nat) → isSorted (sort xs) ≡ True

  -- 1b: Equality
  @0 sortLengthLemma : ∀ (xs : List Nat) → length (sort xs) ≡ length xs

  -- 1c: Inductive predicate
  @0 sortSortedLemma : ∀ (xs : List Nat) → Sorted (sort xs)

  -- 1d: Conjunction
  -- qc translation: prop_sortCorrectLemma xs = isSorted (sort xs) === True .&&. length (sort xs) === length xs
  @0 sortCorrectLemma : ∀ (xs : List Nat)
    → isSorted (sort xs) ≡ True × length (sort xs) ≡ length xs

  -- 1e: Misc
  @0 sortIdempotentLemma : ∀ (xs : List Nat) → sort (sort xs) ≡ sort xs

  -- 1f: IsTrue encoding
  @0 sortIsSortedIsTrue : ∀ (xs : List Nat) → IsTrue (isSorted (sort xs))

{-# COMPILE AGDA2HS sortIsSortedLemma property #-}
{-# COMPILE AGDA2HS sortLengthLemma property #-}
{-# COMPILE AGDA2HS sortSortedLemma property #-}
{-# COMPILE AGDA2HS sortCorrectLemma property #-}
{-# COMPILE AGDA2HS sortIdempotentLemma property #-}
{-# COMPILE AGDA2HS sortIsSortedIsTrue property #-}
