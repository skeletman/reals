{-# OPTIONS --cubical --warning=noNoEquivWhenSplitting #-}
module Algebra.PseudoOrderedField.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Relation.Binary.Base
open import Relation.Binary.Definitions
open import Relation.Binary.Apartness
open import Relation.Binary.PseudoOrder
open import Algebra.ConstructiveField

private
    variable
        ℓ ℓ' : Level

record IsPseudoOrderedField {F : Type ℓ} (_<_ : Rel F F ℓ') (0f 1f : F) (_+_ _∙_ : F → F → F) (- : F → F) (/ : (x : F) → <→# _<_ x 0f → F) : Type (ℓ-max ℓ ℓ') where
    constructor ispseudoorderedfield
    field
        isConstructiveField : IsConstructiveField (<→# _<_) 0f 1f _+_ _∙_ - /
        isPseudoOrder : IsPseudoOrder _<_
        addIsOrderExtensional : _+_ Is _<_ Extensional
        multiplicationByPositivePreservesOrder : ∀ {a b c} → 0f < a → b < c  → (a ∙ b) < (a ∙ c)
