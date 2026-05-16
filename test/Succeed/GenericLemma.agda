module GenericLemma where

open import Haskell.Prelude
open import Agda.Builtin.Equality
open import Haskell.Extra.Dec
open import Haskell.Law

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

myZip : List a → List b → List (a × b)
myZip []       _        = []
myZip _        []       = []
myZip (x ∷ xs) (y ∷ ys) = (x , y) ∷ myZip xs ys

{-# COMPILE AGDA2HS myZip #-}

-- ============================================================================
-- LEMMAS
-- ============================================================================

postulate
  @0 sortIsSortedIsTrue : ⦃ iOrd : Ord a ⦄ → ∀ (xs : List a)
    → IsTrue (isSorted ⦃ iOrd ⦄ (sort ⦃ iOrd ⦄ xs))

  @0 sortIdempotentLemma : ⦃ iOrd : Ord a ⦄ → @0 ⦃ IsLawfulEq a ⦄
    → ∀ (xs : List a) → sort ⦃ iOrd ⦄ (sort ⦃ iOrd ⦄ xs) ≡ sort ⦃ iOrd ⦄ xs

  @0 zipLengthLemma : ∀ (xs : List a) (ys : List b)
    → length (myZip xs ys) ≡ min (length xs) (length ys)

{-# COMPILE AGDA2HS sortIsSortedIsTrue property #-}
{-# COMPILE AGDA2HS sortIdempotentLemma property #-}
{-# COMPILE AGDA2HS zipLengthLemma property #-}
