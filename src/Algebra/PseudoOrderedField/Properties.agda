{-# OPTIONS --cubical --warning=noNoEquivWhenSplitting #-}
module Algebra.PseudoOrderedField.Properties where

open import Cubical.Foundations.Prelude
    renaming
        (
            _∙_ to trans
        )
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
open import Cubical.Relation.Binary.Base
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
open import Cubical.Data.Nat.Coprime
open import Cubical.Data.Sigma
open import Cubical.Data.Sum
open import Cubical.Data.Empty renaming (rec to rec⊥)
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Ring
open import Algebra.Ring.Properties
open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.Group
open import Algebra.Group.Properties
open import Cubical.Algebra.Monoid
open import Cubical.Algebra.Semigroup
open import Algebra.PseudoOrderedField.Base
open import Algebra.ConstructiveField
open import Relation.Binary.Definitions
open import Relation.Binary.Apartness
open import Relation.Binary.PseudoOrder

private
    variable
        ℓ ℓ' ℓ'' : Level
        F : Type ℓ 
        _<_ : Rel F F ℓ'
        0f 1f : F 
        _+_ _∙_ : F → F → F 
        - : F → F 


addIsOrderCompatible : {/ : (x : F) → <→# _<_ x 0f → F} → IsPseudoOrderedField _<_ 0f 1f _+_ _∙_ (-) (/) → _+_ Is _<_ Compatible
addIsOrderCompatible {_<_ = _<_} {0f = 0f} {1f = 1f} {_+_ = _+_} {_∙_ = _∙_}  { - = - } {/ = /} (ispseudoorderedfield (isconstructivefield isCommRing multInverseImpliesApartness apartIsTightApartnessRel divIsPartialInverseToMult addIsApartExtensional) (ispseudoorder isAsym isCotrans isConnex) addIsOrderExtensional multiplicationByPositivePreservesOrder) {x} {y} x<y z = 
    let isPOF : IsPseudoOrderedField _<_ 0f 1f _+_ _∙_ (-) (/)
        isPOF = (ispseudoorderedfield (isconstructivefield isCommRing multInverseImpliesApartness apartIsTightApartnessRel divIsPartialInverseToMult addIsApartExtensional) (ispseudoorder isAsym isCotrans isConnex) addIsOrderExtensional multiplicationByPositivePreservesOrder) 
        isCF : IsConstructiveField (<→# _<_) 0f 1f _+_ _∙_ (-) (/)
        isCF = (isconstructivefield isCommRing multInverseImpliesApartness apartIsTightApartnessRel divIsPartialInverseToMult addIsApartExtensional)
    in rec (λ z → z) (λ y+z<x+z → rec (λ y<x → rec⊥ (isAsym x y (x<y , y<x))) (λ z<z →  rec⊥ (isAsym z z (z<z , z<z))) (addIsOrderExtensional y+z<x+z)) (addIsApartCompatible isCF (inl x<y) z)

0<1 : {/ : (x : F) → <→# _<_ x 0f → F} → IsPseudoOrderedField _<_ 0f 1f _+_ _∙_ (-) (/) → 0f < 1f
0<1 {_<_ = _<_} {0f = 0f} {1f = 1f} {_+_ = _+_} {_∙_ = _∙_} { - = - } {/ = /} (ispseudoorderedfield (isconstructivefield (iscommring (isring (isabgroup (isgroup (ismonoid isSemigroup identity) inverse) comm) ·IsMonoid dist) ·Comm) multInverseImpliesApartness apartIsTightApartnessRel divIsPartialInverseToMult addIsApartExtensional) isPseudoOrder addIsOrderExtensional multiplicationByPositivePreservesOrder) = 
    let isPOF : IsPseudoOrderedField _<_ 0f 1f _+_ _∙_ (-) (/)
        isPOF = (ispseudoorderedfield (isconstructivefield (iscommring (isring (isabgroup (isgroup (ismonoid isSemigroup identity) inverse) comm) ·IsMonoid dist) ·Comm) multInverseImpliesApartness apartIsTightApartnessRel divIsPartialInverseToMult addIsApartExtensional) isPseudoOrder addIsOrderExtensional multiplicationByPositivePreservesOrder)
        isCF : IsConstructiveField (<→# _<_) 0f 1f _+_ _∙_ (-) (/)
        isCF = isconstructivefield (iscommring (isring (isabgroup (isgroup (ismonoid isSemigroup identity) inverse) comm) ·IsMonoid dist) ·Comm) multInverseImpliesApartness apartIsTightApartnessRel divIsPartialInverseToMult addIsApartExtensional
        isRing : IsRing 0f 1f _+_ _∙_ -
        isRing = isring (isabgroup (isgroup (ismonoid isSemigroup identity) inverse) comm) ·IsMonoid dist
        isGroup : IsGroup 0f _+_ -
        isGroup = isgroup (ismonoid isSemigroup identity) inverse
    in rec (λ -1<0 → transport (cong₂ (λ a b → a < b) (snd (inverse 1f)) (snd (identity 1f))) (addIsOrderCompatible isPOF -1<0 1f)) (λ 0<-1 → transport (cong₂ (λ a b → a < b) (zeroAbsorbsR isRing (- 1f)) (trans (sym (-x≡-1x isRing (- 1f))) (-[-x]≡x isGroup 1f))) (multiplicationByPositivePreservesOrder 0<-1 0<-1)) (-1#0 isCF)