{-# OPTIONS --cubical --warning=noNoEquivWhenSplitting #-}
module Algebra.PseudoOrderedField.QInitialObject where

open import Cubical.Foundations.Prelude
    renaming
        (
            _∙_ to trans
        )
open import Cubical.Foundations.Transport

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
            _·_ to _·ℤ_;
            rec to recℤ;
            elim to indℤ;
            ·-comm to ·ℤ-comm
        )
open import Cubical.Data.NatPlusOne
open import Cubical.Data.Nat
    renaming 
        (
            _+_ to _+ℕ_;
            _·_ to _·ℕ_;
            elim to indℕ
        )
open import Cubical.Data.Sigma
open import Cubical.Data.Sum
open import Cubical.Data.Bool

open import Cubical.Relation.Binary.Base
open import Relation.Binary.Definitions
open import Relation.Binary.Apartness
open import Relation.Binary.PseudoOrder

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Ring
open import Algebra.Ring.Properties
open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.Group hiding (ℤ)
open import Algebra.Group.Properties
open import Cubical.Algebra.Monoid
open import Cubical.Algebra.Semigroup
open import Algebra.ConstructiveField
open import Algebra.PseudoOrderedField.Base
open import Algebra.PseudoOrderedField.Properties

private
    variable
        ℓ ℓ' ℓ'' : Level

private
    _∘_ : ∀ {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''} → (B → C) → (A → B) → A → C
    (f ∘ g) x = f (g x)

    altRecℤ : {C : Type ℓ} → (ℕ → C) → (ℕ₊₁ → C) → ℤ → C
    altRecℤ fpos fnegsuc = recℤ fpos (indℕ (fpos 0) (λ n _ → fnegsuc (1+ n))) refl

    altIndℤ : (C : ℤ → Type ℓ) → ((n : ℕ) → C (pos n)) → ((n : ℕ₊₁) → C (neg (ℕ₊₁→ℕ n))) → (n : ℤ) → C n 
    altIndℤ C fpos fnegsuc = indℤ C fpos (indℕ (transport (cong (λ x → C x) posneg) (fpos 0)) (λ n _ → fnegsuc (1+ n))) λ i → transp (λ j → (C (posneg (i ∧ j)))) (~ i) (fpos 0)

ℕ→F : ∀ {F : Type ℓ} (0f 1f : F) (_+_ : F → F → F) → ℕ → F
ℕ→F 0f 1f _+_ = indℕ 0f (λ _ x → 1f + x )

-ℕ→F : ∀ {F : Type ℓ} (0f 1f : F) (_+_ : F → F → F) (- : F → F) → ℕ → F
-ℕ→F 0f 1f _+_ - = indℕ 0f (λ _ x → (- 1f) + x )

ℕ→Fpreserves+ : {F : Type ℓ} {_<_ : Rel F F ℓ'} {0f 1f : F} {_+_ _∙_ : F → F → F} { - : F → F} {/ : (x : F) → <→# _<_ x 0f → F} → IsPseudoOrderedField _<_ 0f 1f _+_ _∙_ (-) (/) → (a b : ℕ) → ℕ→F 0f 1f _+_ (a +ℕ b) ≡ (ℕ→F 0f 1f _+_ a) + (ℕ→F 0f 1f _+_ b)
ℕ→Fpreserves+ {0f = 0f} {1f = 1f} {_+_ = _+_} pof zero b = sym (IsPseudoOrderedField.+Lid pof (indℕ 0f (λ n → _+_ 1f) b))
ℕ→Fpreserves+ {0f = 0f} {1f = 1f} {_+_ = _+_} pof (suc a) b = trans (cong (λ x → 1f + x) (ℕ→Fpreserves+ pof a b)) (IsPseudoOrderedField.+Assoc pof 1f (indℕ 0f (λ n → _+_ 1f) a) (indℕ 0f (λ n → _+_ 1f) b))

-ℕ→F≡-[ℕ→F] : {F : Type ℓ} {_<_ : Rel F F ℓ'} {0f 1f : F} {_+_ _∙_ : F → F → F} { - : F → F} {/ : (x : F) → <→# _<_ x 0f → F} → IsPseudoOrderedField _<_ 0f 1f _+_ _∙_ (-) (/) → ∀ n → -ℕ→F 0f 1f _+_ - n ≡ - (ℕ→F 0f 1f _+_ n)
-ℕ→F≡-[ℕ→F] {0f = 0f} {1f = 1f} {_+_ = _+_} { - = - } pof zero = trans (sym (IsPseudoOrderedField.+Rinv pof 0f)) (IsPseudoOrderedField.+Lid pof (- 0f))
-ℕ→F≡-[ℕ→F] {0f = 0f} {1f = 1f} {_+_ = _+_} {_∙_ = _∙_} { - = - } pof (suc n) = trans (trans (trans (cong (λ x → - 1f + x) (trans (-ℕ→F≡-[ℕ→F] pof n) (-x≡-1x (IsPseudoOrderedField.isRing pof) (indℕ 0f (λ n → _+_ 1f) n)))) (cong (λ x → x + (- 1f ∙ indℕ 0f (λ _ → _+_ 1f) n)) (sym (IsPseudoOrderedField.·Rid pof (- 1f))))) (sym (IsPseudoOrderedField.·Rdist+ pof (- 1f) 1f (indℕ 0f (λ n → _+_ 1f) n)))) (sym (-x≡-1x (IsPseudoOrderedField.isRing pof) (1f + indℕ 0f (λ n → _+_ 1f) n)))

ℕ→Fpreserves· : {F : Type ℓ} {_<_ : Rel F F ℓ'} {0f 1f : F} {_+_ _∙_ : F → F → F} { - : F → F} {/ : (x : F) → <→# _<_ x 0f → F} → IsPseudoOrderedField _<_ 0f 1f _+_ _∙_ (-) (/) → (a b : ℕ) → ℕ→F 0f 1f _+_ (a ·ℕ b) ≡ (ℕ→F 0f 1f _+_ a) ∙ (ℕ→F 0f 1f _+_ b)
ℕ→Fpreserves· {0f = 0f} {1f = 1f} {_+_ = _+_} {_∙_ = _∙_} pof a zero = trans (cong (λ x → ℕ→F 0f 1f _+_ x) (sym (0≡m·0 a))) (sym (zeroAbsorbsR (IsPseudoOrderedField.isRing pof) (indℕ 0f (λ n → _+_ 1f) a)))
ℕ→Fpreserves· {0f = 0f} {1f = 1f} {_+_ = _+_} {_∙_ = _∙_} pof a (suc b) = trans (cong (λ x → ℕ→F 0f 1f _+_ x) (·-suc a b)) (trans (trans (trans (ℕ→Fpreserves+ pof a (a ·ℕ b)) (cong (λ x → indℕ 0f (λ n → _+_ 1f) a + x) (ℕ→Fpreserves· pof a b))) (cong (λ x → x + (indℕ 0f (λ n → _+_ 1f) a ∙ indℕ 0f (λ n → _+_ 1f) b)) (sym (IsPseudoOrderedField.·Rid pof (indℕ 0f (λ n → _+_ 1f) a))))) (sym (IsPseudoOrderedField.·Rdist+ pof (indℕ 0f (λ n → _+_ 1f) a) 1f (indℕ 0f (λ n → _+_ 1f) b))))

ℤ→F : ∀ {F : Type ℓ} (0f 1f : F) (_+_  : F → F → F) (- : F → F) → ℤ → F
ℤ→F 0f 1f _+_ - a = recℤ (ℕ→F 0f 1f _+_) (-ℕ→F 0f 1f _+_ -) refl a

ℤ→Fpreserves· :  {F : Type ℓ} {_<_ : Rel F F ℓ'} {0f 1f : F} {_+_ _∙_ : F → F → F} { - : F → F} {/ : (x : F) → <→# _<_ x 0f → F} → IsPseudoOrderedField _<_ 0f 1f _+_ _∙_ (-) (/) → (a b : ℤ) → ℤ→F 0f 1f _+_ - (a ·ℤ b) ≡ (ℤ→F 0f 1f _+_ - a) ∙ (ℤ→F 0f 1f _+_ - b)
ℤ→Fpreserves· {_<_ = _<_} {0f = 0f} {1f = 1f} {_+_ = _+_} {_∙_ = _∙_} { - = - } {/ = /} pof a b = 
    altIndℤ 
        (λ m → ℤ→F 0f 1f _+_ - (m ·ℤ b) ≡ (ℤ→F 0f 1f _+_ - m ∙ ℤ→F 0f 1f _+_ - b)) 
        (λ m → altIndℤ 
            (λ n → ℤ→F 0f 1f _+_ - (pos m ·ℤ n) ≡ (ℤ→F 0f 1f _+_ - (pos m) ∙ ℤ→F 0f 1f _+_ - n)) 
            (λ n → trans 
                (cong₂ (λ x y → recℤ (indℕ 0f (λ _ → _+_ 1f)) (indℕ 0f (λ _ → _+_ (- 1f))) (λ _ → 0f) (signed (x ⊕ y) (m ·ℕ n))) (sign-pos m) (sign-pos n)) 
                (ℕ→Fpreserves· pof m n)
            ) 
            (λ n → trans 
                (cong (ℤ→F 0f 1f _+_ -) (trans (·ℤ-comm (pos m) (neg (ℕ₊₁→ℕ n))) (·-signed-pos (ℕ₊₁→ℕ n) m)))
                (trans 
                    (-ℕ→F≡-[ℕ→F] pof ((ℕ₊₁→ℕ n) ·ℕ m)) 
                    (trans 
                        (trans 
                            (trans 
                                (trans 
                                    (cong (λ x → - x) (ℕ→Fpreserves· pof (ℕ₊₁→ℕ n) m)) 
                                    (-x≡-1x (IsPseudoOrderedField.isRing pof) (indℕ 0f (λ _ → _+_ 1f) (ℕ₊₁→ℕ n) ∙ indℕ 0f (λ _ → _+_ 1f) m))
                                ) 
                                (IsPseudoOrderedField.·Assoc pof  (- 1f) ( ℕ→F 0f 1f _+_ (ℕ₊₁→ℕ n)) ( ℕ→F 0f 1f _+_ m))
                            ) 
                            (IsPseudoOrderedField.·Comm pof (- 1f ∙ ℕ→F 0f 1f _+_ (ℕ₊₁→ℕ n)) (ℕ→F 0f 1f _+_ m))
                        ) 
                        (cong (λ x → (ℕ→F 0f 1f _+_ m) ∙ x) (sym (trans (-ℕ→F≡-[ℕ→F] pof (ℕ₊₁→ℕ n)) (-x≡-1x (IsPseudoOrderedField.isRing pof) (ℕ→F 0f 1f _+_ (ℕ₊₁→ℕ n))))))
                    )
                )
            ) 
            b
        ) 
        (λ m → altIndℤ 
            (λ n → ℤ→F 0f 1f _+_ - (neg (ℕ₊₁→ℕ m) ·ℤ n) ≡ (ℤ→F 0f 1f _+_ - (neg (ℕ₊₁→ℕ m)) ∙ ℤ→F 0f 1f _+_ - n)) 
            (λ n → trans 
                (cong (λ x → recℤ (indℕ 0f (λ _ → _+_ 1f)) (indℕ 0f (λ _ → _+_ (- 1f))) (λ _ → 0f) (signed (not x) (n +ℕ ℕ₊₁.n m ·ℕ n))) (sign-pos n))
                (trans 
                    ((-ℕ→F≡-[ℕ→F] pof ((ℕ₊₁→ℕ m) ·ℕ n))) 
                    (trans 
                        (trans 
                            (trans 
                                (cong (λ x → - x) (ℕ→Fpreserves· pof (ℕ₊₁→ℕ m) n)) 
                                (-x≡-1x (IsPseudoOrderedField.isRing pof) (indℕ 0f (λ _ → _+_ 1f) (ℕ₊₁→ℕ m) ∙ indℕ 0f (λ _ → _+_ 1f) n))
                            ) 
                            (IsPseudoOrderedField.·Assoc pof  (- 1f) ( ℕ→F 0f 1f _+_ (ℕ₊₁→ℕ m)) ( ℕ→F 0f 1f _+_ n))
                        ) 
                        (cong (λ x → x ∙ (ℕ→F 0f 1f _+_ n)) (sym (trans (-ℕ→F≡-[ℕ→F] pof (ℕ₊₁→ℕ m)) (-x≡-1x (IsPseudoOrderedField.isRing pof) (ℕ→F 0f 1f _+_ (ℕ₊₁→ℕ m))))))
                    )
                )
            ) 
            (λ n → trans 
                (ℕ→Fpreserves· pof (ℕ₊₁→ℕ m) (ℕ₊₁→ℕ n)) 
                (trans 
                    (trans 
                        (trans 
                            (trans 
                                (trans 
                                    (sym (IsPseudoOrderedField.·Lid pof (ℕ→F 0f 1f _+_ (ℕ₊₁→ℕ m) ∙ ℕ→F 0f 1f _+_ (ℕ₊₁→ℕ n)))) 
                                    (cong (λ x → x ∙ (ℕ→F 0f 1f _+_ (ℕ₊₁→ℕ m) ∙ ℕ→F 0f 1f _+_ (ℕ₊₁→ℕ n))) 
                                        (trans 
                                            (sym (-[-x]≡x (IsPseudoOrderedField.+IsGroup pof) 1f)) 
                                            (-x≡-1x (IsPseudoOrderedField.isRing pof) (- 1f))
                                        )
                                    )
                                ) 
                                (IsPseudoOrderedField.·Assoc pof (- 1f ∙ - 1f) (ℕ→F 0f 1f _+_ (ℕ₊₁→ℕ m)) (ℕ→F 0f 1f _+_ (ℕ₊₁→ℕ n)))
                            ) 
                            (cong (λ x → x ∙ ℕ→F 0f 1f _+_ (ℕ₊₁→ℕ n)) (trans (sym (IsPseudoOrderedField.·Assoc pof (- 1f) (- 1f) (ℕ→F 0f 1f _+_ (ℕ₊₁→ℕ m))))  (IsPseudoOrderedField.·Comm pof (- 1f) (- 1f ∙ ℕ→F 0f 1f _+_ (ℕ₊₁→ℕ m)))))
                        ) 
                        (sym (IsPseudoOrderedField.·Assoc pof (- 1f ∙ ℕ→F 0f 1f _+_ (ℕ₊₁→ℕ m)) (- 1f) (ℕ→F 0f 1f _+_ (ℕ₊₁→ℕ n))))
                    ) 
                    (cong₂ (λ x y → x ∙ y) 
                        (sym (trans (-ℕ→F≡-[ℕ→F] pof (ℕ₊₁→ℕ m)) (-x≡-1x (IsPseudoOrderedField.isRing pof) (ℕ→F 0f 1f _+_ (ℕ₊₁→ℕ m)))))
                        (sym (trans (-ℕ→F≡-[ℕ→F] pof (ℕ₊₁→ℕ n)) (-x≡-1x (IsPseudoOrderedField.isRing pof) (ℕ→F 0f 1f _+_ (ℕ₊₁→ℕ n)))))
                    )
                )
            )
            b 
        )
        a

ℚ' : Type₀
ℚ' = ℤ × ℕ₊₁

n+1#0 : {F : Type ℓ} {_<_ : Rel F F ℓ'} {0f 1f : F} {_+_ _∙_ : F → F → F} { - : F → F} {/ : (x : F) → <→# _<_ x 0f → F} → IsPseudoOrderedField _<_ 0f 1f _+_ _∙_ (-) (/)   → ∀ d → <→# _<_ (ℕ→F 0f 1f _+_ (ℕ₊₁→ℕ d)) 0f 
n+1#0 {_<_ = _<_} {0f = 0f} {1f = 1f} {_+_ = _+_} {_∙_ = _∙_} { - = - } {/ = /} pof den = (inr (indℕ (transport (cong (λ a → 0f < a) (sym (IsPseudoOrderedField.+Rid pof 1f))) (0<1 pof)) (λ m 0<1+m → IsPseudoOrderedField.<isTrans pof (0<1 pof) (transport ((cong₂ λ a b → a < b) (IsPseudoOrderedField.+Lid pof 1f) (IsPseudoOrderedField.+Comm pof (1f + indℕ 0f (λ _ → _+_ 1f) m) 1f)) (addIsOrderCompatible pof 0<1+m 1f))) (ℕ₊₁.n den)))

ℚ'→F : ∀ {F : Type ℓ} {_<_ : Rel F F ℓ'} {0f 1f : F} {_+_ _∙_ : F → F → F} { - : F → F} {/ : (x : F) → <→# _<_ x 0f → F} → IsPseudoOrderedField _<_ 0f 1f _+_ _∙_ (-) (/) → ℚ' → F
ℚ'→F {_<_ = _<_} {0f = 0f} {1f = 1f} {_+_ = _+_} {_∙_ = _∙_} { - = - } {/ = /} pof (num , den) = (ℤ→F 0f 1f _+_ - num) ∙ / (ℕ→F 0f 1f _+_ (ℕ₊₁→ℕ den)) (n+1#0 pof den)

ℚ→FwellDefined :  ∀ {F : Type ℓ} {_<_ : Rel F F ℓ'} {0f 1f : F} {_+_ _∙_ : F → F → F} { - : F → F} {/ : (x : F) → <→# _<_ x 0f → F} → (pof : IsPseudoOrderedField _<_ 0f 1f _+_ _∙_ (-) (/)) → (a b : ℚ') → a ∼ b → ℚ'→F pof a ≡ ℚ'→F pof b
ℚ→FwellDefined {_<_ = _<_} {0f = 0f} {1f = 1f} {_+_ = _+_} {_∙_ = _∙_} { - = - } {/ = /} pof (numa , dena) (numb , denb) a∼b = transport (cong₂ (λ x y → x ≡ y) (trans ((sym (IsPseudoOrderedField.·Assoc pof (ℤ→F 0f 1f _+_ - (numa ·ℤ ℕ₊₁→ℤ denb)) (/ (ℕ→F 0f 1f _+_ (ℕ₊₁→ℕ dena)) (n+1#0 pof dena)) (/ (ℕ→F 0f 1f _+_ (ℕ₊₁→ℕ denb)) (n+1#0 pof denb))))) (trans ((cong (λ a → ℤ→F 0f 1f _+_ - (numa ·ℤ ℕ₊₁→ℤ denb) ∙ a) (IsPseudoOrderedField.·Comm pof (/ (ℕ→F 0f 1f _+_ (ℕ₊₁→ℕ dena)) (n+1#0 pof dena)) (/ (ℕ→F 0f 1f _+_ (ℕ₊₁→ℕ denb)) (n+1#0 pof denb))))) (trans (IsPseudoOrderedField.·Assoc pof (ℤ→F 0f 1f _+_ - (numa ·ℤ ℕ₊₁→ℤ denb)) (/ (ℕ→F 0f 1f _+_ (ℕ₊₁→ℕ denb)) (n+1#0 pof denb)) (/ (ℕ→F 0f 1f _+_ (ℕ₊₁→ℕ dena)) (n+1#0 pof dena))) (cong (λ x → x ∙ / (ℕ→F 0f 1f _+_ (ℕ₊₁→ℕ dena)) (n+1#0 pof dena)) (trans (trans (trans (cong (λ x → x ∙ / (ℕ→F 0f 1f _+_ (ℕ₊₁→ℕ denb)) (n+1#0 pof denb)) (ℤ→Fpreserves· pof numa (ℕ₊₁→ℤ denb))) (sym (IsPseudoOrderedField.·Assoc pof (ℤ→F 0f 1f _+_ - numa) (ℕ→F 0f 1f _+_ (ℕ₊₁→ℕ denb)) (/ (ℕ→F 0f 1f _+_ (ℕ₊₁→ℕ denb)) (n+1#0 pof denb))))) (cong (λ x → (ℤ→F 0f 1f _+_ - numa) ∙ x) (IsPseudoOrderedField.divIsPartialInverseToMult pof (ℕ→F 0f 1f _+_ (ℕ₊₁→ℕ denb)) (n+1#0 pof denb)))) (IsPseudoOrderedField.·Rid pof (ℤ→F 0f 1f _+_ - numa))))))) (cong (λ x → x ∙ / (ℕ→F 0f 1f _+_ (ℕ₊₁→ℕ denb)) (n+1#0 pof denb)) (trans (trans (cong (λ x → x ∙ / (ℕ→F 0f 1f _+_ (ℕ₊₁→ℕ dena)) (n+1#0 pof dena)) (ℤ→Fpreserves· pof numb (ℕ₊₁→ℤ dena))) (sym (IsPseudoOrderedField.·Assoc pof (ℤ→F 0f 1f _+_ - numb) (ℕ→F 0f 1f _+_ (ℕ₊₁→ℕ dena)) (/ (ℕ→F 0f 1f _+_ (ℕ₊₁→ℕ dena)) (n+1#0 pof dena))))) (trans (cong (λ x → (ℤ→F 0f 1f _+_ - numb) ∙ x)  (IsPseudoOrderedField.divIsPartialInverseToMult pof (ℕ→F 0f 1f _+_ (ℕ₊₁→ℕ dena)) (n+1#0 pof dena))) (IsPseudoOrderedField.·Rid pof (ℤ→F 0f 1f _+_ - numb)))))) (cong (λ x → (x ∙ / (ℕ→F 0f 1f _+_ (ℕ₊₁→ℕ dena)) (n+1#0 pof dena)) ∙ / (ℕ→F 0f 1f _+_ (ℕ₊₁→ℕ denb)) (n+1#0 pof denb)) (cong (ℤ→F 0f 1f _+_ -) a∼b))

ℚ→F : ∀ {ℓ} {ℓ'} {F : Type ℓ} {_<_ : Rel F F ℓ'} {0f 1f : F} {_+_ _∙_ : F → F → F} { - : F → F} {/ : (x : F) → <→# _<_ x 0f → F} → isSet F → IsPseudoOrderedField _<_ 0f 1f _+_ _∙_ (-) (/) → ℚ → F 
ℚ→F {ℓ} {ℓ'} {F} {_<_} {0f} {1f} {_+_} {_∙_} { - } {/} isset pof = recQuo {R = _∼_} isset (ℚ'→F pof) (ℚ→FwellDefined pof)      