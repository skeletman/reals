{-# OPTIONS --cubical --warning=noNoEquivWhenSplitting #-}
module Relation.Binary.Apartness.Properties where

open import Cubical.Foundations.Prelude

open import Relation.Binary.Apartness.Base
open import Cubical.Relation.Binary.Base
open BinaryRelation renaming (isEquivRel to IsEquivalenceRel)
open import Cubical.Relation.Nullary.Base 
open import Cubical.Data.Empty.Base renaming (rec to rec⊥)
open import Cubical.Data.Sum.Base renaming (rec to rec⊎)

private
  variable
    ℓ ℓ' : Level
    A : Type ℓ
    _#_ : Rel A A ℓ'
    a b c : A

≡preserves#c : a ≡ b → a # c → b # c
≡preserves#c {_#_ = _#_} {c = c} eq ap = transport (cong (λ x → x # c) eq) ap

apartnessRel→EquivRel : IsApartnessRel _#_ → IsEquivalenceRel (λ a b → ¬ (a # b))
apartnessRel→EquivRel (isapartnessrel isSym₁ isIrrefl isCotrans) = 
  equivRel 
    isIrrefl 
    (λ a b z z₁ → z (isSym₁ z₁)) 
    λ a b c ¬a#b ¬b#c a#c → rec⊎ ¬a#b ¬b#c (isCotrans a#c b)
