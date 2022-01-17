{-# OPTIONS --cubical --warning=noNoEquivWhenSplitting #-}
module Algebra.ConstructiveField.Base where


open import Cubical.Foundations.Prelude

open import Cubical.Relation.Binary.Base
open import Relation.Binary.Apartness
open import Relation.Binary.Definitions

open import Cubical.Algebra.CommRing

private
  variable
    ℓ ℓ' : Level

record IsConstructiveField {F : Type ℓ} (_#_ : Rel F F ℓ') (0f 1f : F) (_+_ _∙_ : F → F → F) (-_ : F → F) (/ : (x : F) → x # 0f → F) : Type (ℓ-max ℓ ℓ') where
    constructor isconstructivefield
    field
        isCommRing : IsCommRing 0f 1f _+_ _∙_ -_
        apartIsTightApartnessRel : IsTightApartnessRel _#_
        divIsPartialInverseToMult : (x : F) → (a : x # 0f) → x ∙ (/ x a) ≡ 1f
        addIsApartExtensional : _+_ Is _#_ Extensional
