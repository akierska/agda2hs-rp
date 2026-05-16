module Haskell.Extra.Dec.Instances where

open import Haskell.Prelude
open import Haskell.Prim
open import Haskell.Extra.Dec.Def
open import Haskell.Extra.Refinement
open import Haskell.Law                public

instance
  iDecIsTrue : {b : Bool} → Dec (IsTrue b)
  iDecIsTrue {False} = False ⟨ (λ ()) ⟩
  iDecIsTrue {True}  = True  ⟨ IsTrue.itsTrue ⟩
  {-# COMPILE AGDA2HS iDecIsTrue transparent #-}

  iDecIsFalse : {b : Bool} → Dec (IsFalse b)
  iDecIsFalse {b} = mapDec isTrueNotIsFalse isFalseIsTrueNot (iDecIsTrue {not b})
    where
      @0 isTrueNotIsFalse : {b : Bool} → IsTrue (not b) → IsFalse b
      isTrueNotIsFalse {False} IsTrue.itsTrue = IsFalse.itsFalse

      @0 isFalseIsTrueNot : {b : Bool} → IsFalse b → IsTrue (not b)
      isFalseIsTrueNot {False} IsFalse.itsFalse = IsTrue.itsTrue
  {-# COMPILE AGDA2HS iDecIsFalse inline #-}

  iDecPair : {{Dec a}} → {{Dec b}} → Dec (a × b)
  iDecPair ⦃ b1 ⟨ r1 ⟩ ⦄ ⦃ b2 ⟨ r2 ⟩ ⦄ = (b1 && b2) ⟨ ×-reflects-&& r1 r2 ⟩
    where
      @0 ×-reflects-&& : ∀ {b1 b2 p q} → Reflects p b1 → Reflects q b2 → Reflects (p × q) (b1 && b2)
      ×-reflects-&& {False} {_}     r1 r2 = r1 ∘ fst
      ×-reflects-&& {True}  {False} r1 r2 = r2 ∘ snd
      ×-reflects-&& {True}  {True}  r1 r2 = r1 , r2
  {-# COMPILE AGDA2HS iDecPair inline #-}

  iDecEither : {{Dec a}} → {{Dec b}} → Dec (Either a b)
  iDecEither ⦃ b1 ⟨ r1 ⟩ ⦄ ⦃ b2 ⟨ r2 ⟩ ⦄ = (b1 || b2) ⟨ Either-reflects-|| r1 r2 ⟩
    where
      @0 Either-reflects-|| : ∀ {b1 b2 p q} → Reflects p b1 → Reflects q b2 → Reflects (Either p q) (b1 || b2)
      Either-reflects-|| {False} {False} r1 r2 = either r1 r2
      Either-reflects-|| {False} {True}  r1 r2 = Right r2
      Either-reflects-|| {True}  {_}     r1 r2 = Left r1
  {-# COMPILE AGDA2HS iDecEither inline #-}

  iDecEquiv : {a : Set} → {{_ : Eq a}} {{_ : IsLawfulEq a}} → {x y : a} →  Dec(x ≡ y)
  iDecEquiv {_} {x} {y} = x ≟ y
  {-# COMPILE AGDA2HS iDecEquiv inline #-}
