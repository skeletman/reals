{-# OPTIONS --cubical --warning=noNoEquivWhenSplitting #-}
module Algebra.TightApartnessField.Base where


open import Cubical.Foundations.Prelude

open import Algebra.ApartnessField

open import Cubical.Relation.Binary.Base
open import Relation.Binary.Definitions

private
  variable
    ℓ ℓ' : Level

record IsTightApartnessField {F : Type ℓ} (_∥_ : Rel F F ℓ') (0f 1f : F) (_+_ _∙_ : F → F → F) (-_ : F → F) (/ : (x : F) → x ∥ 0f → F) : Type (ℓ-max ℓ ℓ') where
    constructor istightapartnessfield
    field
        isApartnessField : IsApartnessField _∥_ 0f 1f _+_ _∙_ -_ /
        ∥IsTight : IsTight _∥_