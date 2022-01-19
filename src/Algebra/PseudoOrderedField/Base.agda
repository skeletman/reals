{-# OPTIONS --cubical --warning=noNoEquivWhenSplitting #-}
module Algebra.PseudoOrderedField.Base where

open import Cubical.Foundations.Prelude
open import Cubical.HITs.Rationals.QuoQ
    renaming
        (
            _+_ to _+ℚ_;
            -_ to -ℚ;
            _-_ to _-ℚ_
        )
open import Cubical.HITs.SetQuotients
    renaming
        (
            rec to recQuo
        )
open import Cubical.Data.Int.MoreInts.QuoInt
    renaming 
        (
            _+_ to _+ℤ_;
            -_ to -ℤ_;
            rec to recℤ
        )
open import Cubical.Data.NatPlusOne
open import Cubical.Data.Nat
    renaming 
        (
            _+_ to _+ℕ_
        )
open import Cubical.Data.Sigma
open import Cubical.Data.Sum
open import Cubical.Relation.Binary.Base
open import Relation.Binary.Definitions
open import Relation.Binary.Apartness
open import Relation.Binary.PseudoOrder
open import Algebra.ConstructiveField

private
    variable
        ℓ ℓ' ℓ'' : Level

record IsPseudoOrderedField {F : Type ℓ} (_<_ : Rel F F ℓ') (0f 1f : F) (_+_ _∙_ : F → F → F) (- : F → F) (/ : (x : F) → <→# _<_ x 0f → F) : Type (ℓ-max ℓ ℓ') where
    constructor ispseudoorderedfield
    field
        isConstructiveField : IsConstructiveField (<→# _<_) 0f 1f _+_ _∙_ - /
        isPseudoOrder : IsPseudoOrder _<_
        addIsOrderExtensional : _+_ Is _<_ Extensional
        multiplicationByPositivePreservesOrder : ∀ {a b c} → 0f < a → b < c  → (a ∙ b) < (a ∙ c)

    open IsConstructiveField isConstructiveField public

    open IsPseudoOrder isPseudoOrder public
        renaming
            (
                isAsym to <isAsym;
                isConnex to <isConnex;
                isCotrans to <isCotrans;
                isIrrefl to <isIrrefl;
                isTrans to <isTrans
            )