-- This tests translation between Lemma postcondition on insertion sort (on the Nat type).

module GenericLemma where

open import Haskell.Prelude
open import Agda.Builtin.Equality
open import Haskell.Extra.Refinement
open import Haskell.Extra.Dec  -- THIS IS NECESSARY FOR THE TEST TO COMPILE - we need to bring decider instances into the context.

-- ============================================================================
-- SETUP 
-- ============================================================================

insert : ⦃ Ord a ⦄ → a → List a → List a
insert x []       = x ∷ []
insert x (y ∷ ys) = if x <= y then x ∷ y ∷ ys else y ∷ insert x ys

{-# COMPILE AGDA2HS insert #-}

sort : ⦃ Ord a ⦄ → List a → List a
sort []       = []
sort (x ∷ xs) = insert x (sort xs)

{-# COMPILE AGDA2HS sort #-}

isSorted : ⦃ Ord a ⦄ → List a → Bool
isSorted []           = True
isSorted (x ∷ [])     = True
isSorted (x ∷ y ∷ xs) = (x <= y) && isSorted (y ∷ xs)

{-# COMPILE AGDA2HS isSorted #-}

data Sorted {a : Type} ⦃ _ : Ord a ⦄ : List a → Set where
  sorted-nil  : Sorted []
  sorted-one  : ∀ {x} → Sorted (x ∷ [])
  sorted-cons : ∀ {x y xs} → IsTrue (x <= y)
              → Sorted (y ∷ xs) → Sorted (x ∷ y ∷ xs)


instance
  iDecSorted : {a : Type} → {xs : List a} → Dec (Sorted xs)
  iDecSorted {[]} = True ⟨ sorted-nil ⟩
  iDecSorted {x ∷ []} = True ⟨ sorted-one ⟩
  iDecSorted {x ∷ y ∷ xs} = mapDec
    (λ where (p , q) → sorted-cons p q)
    (λ where (sorted-cons p q) → p , q)
    iDecPair

{-# COMPILE AGDA2HS iDecSorted #-}

-- ============================================================================
-- FORM 1: LEMMAS
-- ============================================================================

postulate

-- 1a: Bool predicate
@0 sortIsSortedLemma : {a : Type} → ⦃ Ord a ⦄ → ∀ (xs : List a) → isSorted (sort xs) ≡ True

-- 1b: Equality
@0 sortLengthLemma : {a : Type} → ⦃ Ord a ⦄ → ∀ (xs : List a) → length (sort xs) ≡ length xs

-- 1c: Inductive predicate
@0 sortSortedLemma : {a : Type} → ⦃ Ord a ⦄ → ∀ (xs : List a) → Sorted (sort xs)

-- 1d: Conjunction
@0 sortCorrectLemma : {a : Type} → ⦃ Ord a ⦄ → ∀ (xs : List a)
  → isSorted (sort xs) ≡ True × length (sort xs) ≡ length xs

-- 1e: Misc
@0 sortIdempotentLemma : {a : Type} → ⦃ Ord a ⦄ → ∀ (xs : List a) → sort (sort xs) ≡ sort xs

{-# COMPILE AGDA2HS sortIsSortedLemma property #-}
{-# COMPILE AGDA2HS sortLengthLemma property #-}
{-# COMPILE AGDA2HS sortSortedLemma property #-}
{-# COMPILE AGDA2HS sortCorrectLemma property #-}
{-# COMPILE AGDA2HS sortIdempotentLemma property #-}
