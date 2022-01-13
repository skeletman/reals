{-# OPTIONS --cubical --warning=noNoEquivWhenSplitting #-}
module Relation.Binary.Apartness.Properties where

open import Cubical.Foundations.Prelude

open import Relation.Binary.Apartness.Base
open import Cubical.Relation.Binary.Base using (Rel)

private
  variable
    ℓ ℓ' : Level
    A : Type ℓ
    _∥_ : Rel A A ℓ'
    a b c : A

≡preserves∥c : a ≡ b → a ∥ c → b ∥ c
≡preserves∥c {_∥_ = _∥_} {c = c} eq ap = transport (cong (λ x → x ∥ c) eq) ap

