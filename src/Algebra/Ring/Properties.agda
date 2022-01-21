{-# OPTIONS --cubical --warning=noNoEquivWhenSplitting #-}
module Algebra.Ring.Properties where

open import Cubical.Foundations.Prelude
    renaming (_∙_ to trans)
open import Cubical.Algebra.Ring
open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.Group
open import Cubical.Algebra.Monoid
open import Cubical.Algebra.Semigroup

private
    variable
        ℓ : Level
        F : Type ℓ 
        0f 1f : F 
        _+_ _∙_ : F → F → F 
        - : F → F 

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