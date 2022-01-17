{-# OPTIONS --cubical --warning=noNoEquivWhenSplitting #-}
module Algebra.PseudoOrderedField.Properties where

open import Cubical.Foundations.Prelude
    renaming
        (
            _∙_ to trans
        )
open import Cubical.HITs.Rationals.SigmaQ
open import Cubical.HITs.SetQuotients
open import Cubical.Relation.Binary.Base
open import Cubical.Data.Int.MoreInts.QuoInt
    renaming 
        (
            _+_ to _+ℤ_;
            -_ to -ℤ_
        )
open import Cubical.Data.NatPlusOne
open import Cubical.Data.Nat
    renaming 
        (
            _+_ to _+ℕ_
        )
open import Cubical.Data.Nat.Coprime
open import Algebra.PseudoOrderedField.Base
open import Relation.Binary.Definitions
open import Relation.Binary.Apartness
open import Relation.Binary.PseudoOrder

private
    variable
        ℓ ℓ' : Level
        F : Type ℓ 
        _<_ : Rel F F ℓ'
        0f 1f : F 
        _+_ _∙_ : F → F → F 
        - : F → F 
        