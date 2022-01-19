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
open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.Group
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
       
private
    x-z+z≡x : IsGroup 0f _+_ - → ∀ x z → (x + - z) + z ≡ x
    x-z+z≡x {_+_ = _+_} { - = - } (isgroup (ismonoid isSemigroup identity) inverse) x z = trans (sym (IsSemigroup.assoc isSemigroup x (- z) z )) (trans (cong (λ a → x + a) (snd (inverse z))) (fst (identity x)))

    x+z-z≡x : IsGroup 0f _+_ - → ∀ x z → (x + z) + - z ≡ x
    x+z-z≡x {_+_ = _+_} { - = - } (isgroup (ismonoid isSemigroup identity) inverse) x z = trans (sym (IsSemigroup.assoc isSemigroup x z (- z) )) ((trans (cong (λ a → x + a) (fst (inverse z))) (fst (identity x))))
    
    zeroAbsorbsL : IsRing 0f 1f _+_ _∙_ - → ∀ x → 0f ∙ x ≡ 0f 
    zeroAbsorbsL {0f = 0f} {1f = 1f} {_+_ = _+_} {_∙_ = _∙_} { - = - } (isring (isabgroup (isgroup (ismonoid +isSemigroup +identity) inverse) comm) (ismonoid isSemigroup ∙identity) dist) x = 
        trans 
            (sym (fst (+identity (0f ∙ x)))) 
            (transport 
                (cong 
                    (λ a → ((0f ∙ x) + a) ≡ 0f) 
                    (fst (inverse (0f ∙ x)))
                ) 
                (transport 
                    (cong 
                        (λ a → a ≡ 0f) 
                        (sym (IsSemigroup.assoc +isSemigroup (0f ∙ x) (0f ∙ x) (- (0f ∙ x)))) 
                    ) 
                    (transport 
                        (cong 
                            (λ a → (a + - (0f ∙ x)) ≡ 0f) 
                            (snd (dist 0f 0f x))
                        ) 
                        (transport 
                            (cong 
                                (λ a → ((a ∙ x) + - (0f ∙ x)) ≡ 0f) 
                                (sym (fst (+identity 0f)))
                            ) 
                            (fst (inverse (0f ∙ x)))
                        )
                    )
                )
            )

    zeroAbsorbsR : IsRing 0f 1f _+_ _∙_ - → ∀ x → x ∙ 0f ≡ 0f 
    zeroAbsorbsR {0f = 0f} {1f = 1f} {_+_ = _+_} {_∙_ = _∙_} { - = - } (isring (isabgroup (isgroup (ismonoid +isSemigroup +identity) inverse) comm) (ismonoid isSemigroup ∙identity) dist) x = trans 
            (sym (fst (+identity (x ∙ 0f)))) 
            (trans 
                (cong (λ a → (x ∙ 0f) + a) (sym (fst (inverse (x ∙ 0f))))) 
                (trans 
                    (IsSemigroup.assoc +isSemigroup (x ∙ 0f) (x ∙ 0f) (- (x ∙ 0f))) 
                    (trans 
                        (cong (λ a → a + - (x ∙ 0f)) (sym (fst (dist x 0f 0f))) ) 
                        (trans 
                            (cong (λ a → (x ∙ a) + - (x ∙ 0f)) (fst (+identity 0f))) 
                            (fst (inverse (x ∙ 0f)))
                        )
                    )
                )
            )

    -x≡-1x : IsRing 0f 1f _+_ _∙_ - → ∀ x → - x ≡ (- 1f) ∙ x
    -x≡-1x {0f = 0f} {1f = 1f} {_+_ = _+_} {_∙_ = _∙_} { - = - } (isring (isabgroup (isgroup (ismonoid +isSemigroup +identity) inverse) comm) (ismonoid ∙isSemigroup ∙identity) dist) x = 
        let isRing : IsRing 0f 1f _+_ _∙_ -
            isRing = isring (isabgroup (isgroup (ismonoid +isSemigroup +identity) inverse) comm) (ismonoid ∙isSemigroup ∙identity) dist
        in trans 
            (trans 
                (sym (snd (+identity (- x))))  
                (cong 
                    (λ a → a + (- x)) 
                    (trans 
                        (sym (zeroAbsorbsL isRing x)) 
                        (transport 
                            (cong₂ 
                                (λ a b →  a ∙ x ≡ (- 1f ∙ x) + b) 
                                (snd (inverse (1f))) 
                                (snd (∙identity x))
                            ) 
                            (snd (dist (- 1f) (1f) x))
                        )
                    )
                )
            )  
            (trans 
                (sym (IsSemigroup.assoc +isSemigroup (- 1f ∙ x) x (- x))) 
                (trans 
                    (cong (λ a → (- 1f ∙ x) + a) (fst (inverse x))) 
                    (fst (+identity (- 1f ∙ x)))
                )
            )

    -x≡x[-1] : IsRing 0f 1f _+_ _∙_ - → ∀ x → - x ≡ x ∙ (- 1f)
    -x≡x[-1] {0f = 0f} {1f = 1f} {_+_ = _+_} {_∙_ = _∙_} { - = - } (isring (isabgroup (isgroup (ismonoid +isSemigroup +identity) inverse) comm) (ismonoid ∙isSemigroup ∙identity) dist) x =
        let isRing : IsRing 0f 1f _+_ _∙_ -
            isRing = isring (isabgroup (isgroup (ismonoid +isSemigroup +identity) inverse) comm) (ismonoid ∙isSemigroup ∙identity) dist
        in trans 
            (trans 
                (sym (snd (+identity (- x)))) 
                (cong 
                    (λ a → a + (- x)) 
                    (trans 
                        (sym (zeroAbsorbsR isRing x)) 
                        (transport 
                            (cong₂ 
                                (λ a b →  x ∙ a ≡ (x ∙ (- 1f)) + b) 
                                (snd (inverse (1f))) 
                                (fst (∙identity x))
                            ) 
                            (fst (dist x (- 1f) 1f))
                        )
                    )
                )
            ) 
            (trans 
                (sym (IsSemigroup.assoc +isSemigroup (x ∙ - 1f) x (- x))) 
                (trans 
                    (cong (λ a → (x ∙ - 1f) + a) (fst (inverse x))) 
                    (fst (+identity (x ∙ - 1f)))
                )
            )

    -x∙y≡-[x∙y] : IsRing 0f 1f _+_ _∙_ - → ∀ x y → (- x) ∙ y ≡ - (x ∙ y)
    -x∙y≡-[x∙y] {0f = 0f} {1f = 1f} {_+_ = _+_} {_∙_ = _∙_} { - = - } (isring (isabgroup (isgroup (ismonoid +isSemigroup +identity) inverse) comm) (ismonoid ∙isSemigroup ∙identity) dist) x y = 
        let isRing : IsRing 0f 1f _+_ _∙_ -
            isRing = (isring (isabgroup (isgroup (ismonoid +isSemigroup +identity) inverse) comm) (ismonoid ∙isSemigroup ∙identity) dist)
        in trans (cong (λ a → a ∙ y) (-x≡-1x isRing x)) (trans (sym (IsSemigroup.assoc ∙isSemigroup (- 1f) x y)) (sym (-x≡-1x isRing (x ∙ y)))) 

    x∙-y≡-[x∙y] : IsRing 0f 1f _+_ _∙_ - → ∀ x y → x ∙ (- y) ≡ - (x ∙ y)
    x∙-y≡-[x∙y] {0f = 0f} {1f = 1f} {_+_ = _+_} {_∙_ = _∙_} { - = - } (isring (isabgroup (isgroup (ismonoid +isSemigroup +identity) inverse) comm) (ismonoid ∙isSemigroup ∙identity) dist) x y = 
        let isRing : IsRing 0f 1f _+_ _∙_ -
            isRing = (isring (isabgroup (isgroup (ismonoid +isSemigroup +identity) inverse) comm) (ismonoid ∙isSemigroup ∙identity) dist)
        in trans (cong (λ a → x ∙ a) (-x≡x[-1] isRing y)) (trans (IsSemigroup.assoc ∙isSemigroup x y (- 1f)) (sym (-x≡x[-1] isRing (x ∙ y))))
    
    -[-x]≡x : IsGroup 0f _+_ - → ∀ x → - (- x) ≡ x
    -[-x]≡x {0f = 0f} {_+_ = _+_} { - = - } (isgroup (ismonoid +isSemigroup +identity) inverse) x = trans (sym (x-z+z≡x (isgroup (ismonoid +isSemigroup +identity) inverse) (- (- x)) x)) (trans (cong (λ a → a + x) (snd (inverse (- x)))) (snd (+identity x)))


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



