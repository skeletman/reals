{-# OPTIONS --cubical --warning=noNoEquivWhenSplitting #-}
module Algebra.ApartnessField.Base where


open import Cubical.Foundations.Prelude

open import Cubical.Relation.Binary.Base
open import Relation.Binary.Apartness

open import Cubical.Algebra.CommRing

private
  variable
    ℓ ℓ' : Level

record IsApartnessField {F : Type ℓ} (_∥_ : Rel F F ℓ') (0f 1f : F) (_+_ _∙_ : F → F → F) (-_ : F → F) (/ : (x : F) → x ∥ 0f → F) : Type (ℓ-max ℓ ℓ') where
    constructor isapartnessfield
    field
        +-∙IsCommRing : IsCommRing 0f 1f _+_ _∙_ -_
        apartIsApartnessRel : IsApartnessRel _∥_
        0∥1 : 0f ∥ 1f
        /∙Inverse : (x : F) → (a : x ∥ 0f) → x ∙ (/ x a) ≡ 1f
        /Preserves∥0 : {x : F} → (a : x ∥ 0f) → (/ x a) ∥ 0f
        ∙Preserves∥0 : {x y : F} → x ∥ 0f → y ∥ 0f → (x ∙ y) ∥ 0f
        -Preserves∥ : {x y : F} → x ∥ y → (- x) ∥ (- y)
