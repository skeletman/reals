{-# OPTIONS --cubical --warning=noNoEquivWhenSplitting #-}
module Algebra.ConstructiveField.Properties where


open import Cubical.Foundations.Prelude renaming (_∙_ to trans)

open import Cubical.Data.Sigma
open import Cubical.Data.Sum renaming (rec to rec⊎)
open import Cubical.Data.Empty renaming (rec to rec⊥)

open import Cubical.Relation.Binary.Base
open import Relation.Binary.Apartness
open import Relation.Binary.Definitions

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Ring
open import Algebra.Ring.Properties
open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.Group
open import Algebra.Group.Properties
open import Cubical.Algebra.Monoid
open import Cubical.Algebra.Semigroup
open import Algebra.ConstructiveField.Base

private
    variable
        ℓ ℓ' : Level
        F : Type ℓ
        _#_ : Rel F F ℓ'
        0f 1f : F 
        _+_ _∙_ : F → F → F
        - : F → F

1#0 : {/ : (x : F) → x # 0f → F } → IsConstructiveField _#_ 0f 1f _+_ _∙_ - / → 1f # 0f 
1#0 {1f = 1f} (isconstructivefield (iscommring (isring _ (ismonoid _ identity) _) _) multInverseImpliesApartness _ _ _) = multInverseImpliesApartness 1f (1f , fst (identity 1f))

-1#0 : {/ : (x : F) → x # 0f → F } → IsConstructiveField _#_ 0f 1f _+_ _∙_ - / → - 1f # 0f 
-1#0 {0f = 0f} {1f = 1f} {_+_ = _+_} {_∙_ = _∙_} { - = - } (isconstructivefield (iscommring (isring (isabgroup isGroup comm) (ismonoid isSemigroup identity) ∙isMonoid) _) multInverseImpliesApartness _ _ _) = 
    let isRing : IsRing 0f 1f _+_ _∙_ -
        isRing = isring (isabgroup isGroup comm) (ismonoid isSemigroup identity) ∙isMonoid
    in multInverseImpliesApartness (- 1f) (- 1f , trans (-x∙y≡-[x∙y] isRing 1f (- 1f)) (trans (cong (λ a → - a) (snd (identity (- 1f)))) (-[-x]≡x isGroup 1f)))

addIsApartCompatible : {/ : (x : F) → x # 0f → F } → IsConstructiveField _#_ 0f 1f _+_ _∙_ - / → _+_ Is _#_ Compatible
addIsApartCompatible {_#_ = _#_} {_+_ = _+_} { - = - } (isconstructivefield (iscommring (isring (isabgroup isGroup comm) ·IsMonoid dist) ·Comm) multInverseImpliesApartness (istightapartnessrel (isapartnessrel isSym isIrrefl isCotrans) isTight) divIsPartialInverseToMult addIsApartExtensional) {x} {y} x#y z = rec⊎ (λ z → z) (λ -z#-z → rec⊥ (isIrrefl (- z) -z#-z)) (addIsApartExtensional (transport (sym (cong₂ (λ a b → a # b) (x+z-z≡x isGroup x z) (x+z-z≡x isGroup y z))) x#y)) 

multIsApartExtensional : {/ : (x : F) → x # 0f → F } → IsConstructiveField _#_ 0f 1f _+_ _∙_ - / → _∙_ Is _#_ Extensional
multIsApartExtensional {_#_ = _#_} {0f = 0f} {1f = 1f} {_+_ = _+_} {_∙_ = _∙_} { - = - } {/ = /} (isconstructivefield (iscommring (isring (isabgroup (isgroup (ismonoid +isSemigroup +identity) inverse) comm) (ismonoid ∙isSemigroup ∙identity) dist) ·Comm) multInverseImpliesApartness (istightapartnessrel (isapartnessrel isSym isIrrefl isCotrans) isTight) divIsPartialInverseToMult addIsApartExtensional) {w} {x} {y} {z} wx#yz = 
    let cf : IsConstructiveField _#_ 0f 1f _+_ _∙_ (-) (/)
        cf = isconstructivefield (iscommring (isring (isabgroup (isgroup (ismonoid +isSemigroup +identity) inverse) comm) (ismonoid ∙isSemigroup ∙identity) dist) ·Comm) multInverseImpliesApartness (istightapartnessrel (isapartnessrel isSym isIrrefl isCotrans) isTight) divIsPartialInverseToMult addIsApartExtensional
        gp :  IsGroup 0f _+_ -
        gp = isgroup (ismonoid +isSemigroup +identity) inverse
        ring : IsRing 0f 1f _+_ _∙_ -
        ring = isring (isabgroup (isgroup (ismonoid +isSemigroup +identity) inverse) comm) (ismonoid ∙isSemigroup ∙identity) dist
    in rec⊎ 
        (λ wx#wz → inr 
            let w[x-z]#0 : (w ∙ (x + - z)) # 0f
                w[x-z]#0 = transport (cong₂ (λ a b → a # b) (trans (cong (λ a → (w ∙ x) + a) (sym (x∙-y≡-[x∙y] ring w z))) (sym (fst (dist w x (- z))))) (fst (inverse (w ∙ z)))) (addIsApartCompatible cf wx#wz (- (w ∙ z)))
            in (transport 
                (cong₂ 
                    (λ a b → a # b) 
                    (x-z+z≡x gp x z) 
                    (snd (+identity z))
                ) 
                (addIsApartCompatible cf (multInverseImpliesApartness (x + - z) (w ∙ (/ (w ∙ (x + - z)) w[x-z]#0) ,  trans (IsSemigroup.assoc ∙isSemigroup (x + - z) w (/ (w ∙ (x + - z)) w[x-z]#0)) (trans (cong (λ a → a ∙ (/ (w ∙ (x + - z)) w[x-z]#0)) (·Comm (x + - z) w)) (divIsPartialInverseToMult (w ∙ (x + - z)) w[x-z]#0)))) z))) 
        (λ wz#yz → inl
            let [w-y]z#0 : ((w + - y) ∙ z) # 0f
                [w-y]z#0 = (transport (cong₂ (λ a b → a # b) (trans (cong (λ a → (w ∙ z) + a) (sym (-x∙y≡-[x∙y] ring y z))) (sym( snd (dist w (- y) z)))) (fst (inverse (y ∙ z)))) (addIsApartCompatible cf wz#yz (- (y ∙ z))))
            in (transport (cong₂ (λ a b → a # b) (x-z+z≡x gp w y) (snd (+identity y))) (addIsApartCompatible cf (multInverseImpliesApartness (w + (- y)) ((z ∙ (/  ((w + - y) ∙ z) [w-y]z#0)) , trans (IsSemigroup.assoc ∙isSemigroup (w + - y) z (/ ((w + - y) ∙ z) [w-y]z#0)) (divIsPartialInverseToMult ((w + - y) ∙ z) [w-y]z#0))) y))) 
        (isCotrans wx#yz ((w ∙ z))) 



