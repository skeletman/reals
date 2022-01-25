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
            rec to recQuo;
            elim to indQuo
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
open import Cubical.Data.Nat.Order
    renaming
        (
            _<_ to _<ℕ_
        )
open import Cubical.Data.Sigma
open import Cubical.Data.Sum
open import Cubical.Data.Bool
    hiding (_≟_)
open import Cubical.Data.Empty
    renaming
        (
            rec to rec⊥
        )

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

ℕ→Fpreserves< : {F : Type ℓ} {_<_ : Rel F F ℓ'} {0f 1f : F} {_+_ _∙_ : F → F → F} { - : F → F} {/ : (x : F) → <→# _<_ x 0f → F} → IsPseudoOrderedField _<_ 0f 1f _+_ _∙_ (-) (/) → {a b : ℕ} → a <ℕ b → ℕ→F 0f 1f _+_ a < ℕ→F 0f 1f _+_ b
ℕ→Fpreserves< {_<_ = _<_} {0f = 0f} {1f = 1f} {_+_ = _+_} {_∙_ = _∙_} pof {a} {b} a<b = transport (cong (λ x →  ℕ→F 0f 1f _+_ a < ℕ→F 0f 1f _+_ x) (snd a<b)) (lemma (fst a<b) a)
    where
    lemma : (a b : ℕ) → ℕ→F 0f 1f _+_ b < ℕ→F 0f 1f _+_ (a +ℕ (suc b))
    lemma zero b = transport (cong (λ x → x < (1f + indℕ 0f (λ _ → _+_ 1f) b)) (IsPseudoOrderedField.+Lid pof (ℕ→F 0f 1f _+_ b))) (addIsOrderCompatible pof (0<1 pof) (ℕ→F 0f 1f _+_ b))
    lemma (suc a) b = IsPseudoOrderedField.<isTrans pof (lemma a b) (transport (cong (λ x → x < (1f + indℕ 0f (λ _ → _+_ 1f) (a +ℕ suc b))) (IsPseudoOrderedField.+Lid pof (ℕ→F 0f 1f _+_ (a +ℕ suc b)))) (addIsOrderCompatible pof (0<1 pof) (ℕ→F 0f 1f _+_ (a +ℕ suc b))))

ℕ→Finj : {F : Type ℓ} {_<_ : Rel F F ℓ'} {0f 1f : F} {_+_ _∙_ : F → F → F} { - : F → F} {/ : (x : F) → <→# _<_ x 0f → F} → IsPseudoOrderedField _<_ 0f 1f _+_ _∙_ (-) (/) → ∀ {a b} → ℕ→F 0f 1f _+_ a ≡ ℕ→F 0f 1f _+_ b → a ≡ b
ℕ→Finj {_<_ = _<_} {0f = 0f} {1f = 1f} {_+_ = _+_} {_∙_ = _∙_} pof {a} {b} = lemma (a ≟ b)
    where
    lemma : ∀ {m n} → Trichotomy m n → ℕ→F 0f 1f _+_ m ≡ ℕ→F 0f 1f _+_ n → m ≡ n
    lemma {m} {n} (lt m<n) fa≡fb = rec⊥ (IsPseudoOrderedField.<isIrrefl pof (ℕ→F 0f 1f _+_ m) (transport (cong (λ x → ℕ→F 0f 1f _+_ m < x) (sym fa≡fb)) (ℕ→Fpreserves<  pof m<n)))
    lemma {m} {n} (eq m≡n) fa≡fb = m≡n
    lemma {m} {n} (gt n<m) fa≡fb = rec⊥ (IsPseudoOrderedField.<isIrrefl pof (ℕ→F 0f 1f _+_ m) (transport (cong (λ x → x < ℕ→F 0f 1f _+_ m) (sym fa≡fb)) (ℕ→Fpreserves< pof n<m)))


ℤ→F : ∀ {F : Type ℓ} (0f 1f : F) (_+_  : F → F → F) (- : F → F) → ℤ → F
ℤ→F 0f 1f _+_ - a = recℤ (ℕ→F 0f 1f _+_) (-ℕ→F 0f 1f _+_ -) refl a

ℤ→Finj : {F : Type ℓ} {_<_ : Rel F F ℓ'} {0f 1f : F} {_+_ _∙_ : F → F → F} { - : F → F} {/ : (x : F) → <→# _<_ x 0f → F} → IsPseudoOrderedField _<_ 0f 1f _+_ _∙_ (-) (/) → ∀ {a b} → ℤ→F 0f 1f _+_ - a ≡ ℤ→F 0f 1f _+_ - b → a ≡ b
ℤ→Finj {_<_ = _<_} {0f = 0f} {1f = 1f} {_+_ = _+_} {_∙_ = _∙_} { - = - } pof {a} {b} = altIndℤ (λ m → (ℤ→F 0f 1f _+_ - m ≡ ℤ→F 0f 1f _+_ - b → m ≡ b)) (λ m → altIndℤ (λ n → (ℤ→F 0f 1f _+_ - (pos m) ≡ ℤ→F 0f 1f _+_ - n → (pos m) ≡ n)) (λ n → λ fm≡fn → cong pos (ℕ→Finj pof fm≡fn)) (λ n → λ fm≡f[-n] → rec⊥ (IsPseudoOrderedField.<isIrrefl pof (ℤ→F 0f 1f _+_ - (pos m)) (transport (cong (λ x → x < ℤ→F 0f 1f _+_ - (pos m)) (sym fm≡f[-n])) (lemma m n)))) b) (λ m → altIndℤ (λ n → (ℤ→F 0f 1f _+_ - (neg (ℕ₊₁→ℕ m)) ≡ ℤ→F 0f 1f _+_ - n → (neg (ℕ₊₁→ℕ m)) ≡ n)) (λ n f[-m]≡fn → rec⊥ (IsPseudoOrderedField.<isIrrefl pof (ℤ→F 0f 1f _+_ - (pos n)) (transport (cong (λ x → x < ℤ→F 0f 1f _+_ - (pos n)) f[-m]≡fn) (lemma n m)))) (λ n f[-m]≡f[-n] → cong neg (ℕ→Finj pof (transport (cong₂ (λ x y → x ≡ y) (-[-x]≡x (IsPseudoOrderedField.+IsGroup pof) (ℕ→F 0f 1f _+_ (ℕ₊₁→ℕ m))) (-[-x]≡x (IsPseudoOrderedField.+IsGroup pof) (ℕ→F 0f 1f _+_ (ℕ₊₁→ℕ n)))) (cong - (transport (cong₂ (λ x y →  x ≡ y) (-ℕ→F≡-[ℕ→F] pof (ℕ₊₁→ℕ m)) (-ℕ→F≡-[ℕ→F] pof (ℕ₊₁→ℕ n))) f[-m]≡f[-n]))))) b) a
    where
    lemma : (m : ℕ) → (n : ℕ₊₁) → ℤ→F 0f 1f _+_ - (neg (ℕ₊₁→ℕ n)) < ℤ→F 0f 1f _+_ - (pos m)
    lemma zero one = transport (cong (λ x → x < 0f) (sym (IsPseudoOrderedField.+Rid pof (- 1f)))) (-1<0 pof)
    lemma zero (2+ n) = IsPseudoOrderedField.<isTrans pof (transport (cong (λ x → ℤ→F 0f 1f _+_ - (neg (ℕ₊₁→ℕ (2+ n))) < x) (IsPseudoOrderedField.+Lid pof (ℤ→F 0f 1f _+_ - (neg (ℕ₊₁→ℕ (1+ n))))))  (addIsOrderCompatible pof (-1<0 pof) (- 1f + indℕ 0f (λ n → _+_ (- 1f)) n))) (lemma zero (1+ n))
    lemma (suc m) n = IsPseudoOrderedField.<isTrans pof (lemma m n) (transport (cong (λ x → x < (1f + (ℤ→F 0f 1f _+_ - (pos m)))) (IsPseudoOrderedField.+Lid pof (ℤ→F 0f 1f _+_ - (pos m)))) (addIsOrderCompatible pof (0<1 pof) (ℤ→F 0f 1f _+_ - (pos m))))

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

ℚ→F : ∀ {ℓ} {ℓ'} {F : Type ℓ} {_<_ : Rel F F ℓ'} {0f 1f : F} {_+_ _∙_ : F → F → F} { - : F → F} {/ : (x : F) → <→# _<_ x 0f → F} → IsPseudoOrderedField _<_ 0f 1f _+_ _∙_ (-) (/) → ℚ → F 
ℚ→F {ℓ} {ℓ'} {F} {_<_} {0f} {1f} {_+_} {_∙_} { - } {/} pof = recQuo {R = _∼_} (IsPseudoOrderedField.is-set pof) (ℚ'→F pof) (ℚ→FwellDefined pof)



ℚ→Finj : {F : Type ℓ} {_<_ : Rel F F ℓ'} {0f 1f : F} {_+_ _∙_ : F → F → F} { - : F → F} {/ : (x : F) → <→# _<_ x 0f → F} → (pof : IsPseudoOrderedField _<_ 0f 1f _+_ _∙_ (-) (/)) → ∀ {x y : ℚ} → ℚ→F pof x ≡ ℚ→F pof y → x ≡ y
ℚ→Finj {F = F} {_<_ = _<_} {0f = 0f} {1f = 1f} {_+_ = _+_} {_∙_ = _∙_} { - = - } {/ = /} pof {x} {y} fa≡fb =  (elimProp2 {P = λ x1 y1 → (x1 ≡ x → y1 ≡ y → x ≡ y)} (λ x₁ y₁ f g → funExt λ x₁≡x → funExt λ y₁≡y → isSetℚ x y (f x₁≡x y₁≡y) (g x₁≡x y₁≡y)) λ a b [a]≡x [b]≡y → trans (trans (sym [a]≡x) (eq/ a b (lemma a b (transport (cong₂ (λ x₁ y₁ → ℚ→F pof x₁ ≡ ℚ→F pof y₁) (sym [a]≡x) (sym [b]≡y)) fa≡fb)))) [b]≡y) x y refl refl
    where 
    lemma1 : ((numa , dena) (numb , denb) : ℚ') → ℚ'→F pof (numa , dena) ≡ ℚ'→F pof (numb , denb) → ((ℤ→F 0f 1f _+_ - numa) ∙ ℕ→F 0f 1f _+_ (ℕ₊₁→ℕ denb)) ≡ ((ℤ→F 0f 1f _+_ - numb) ∙ ℕ→F 0f 1f _+_ (ℕ₊₁→ℕ dena))
    lemma1 (numa , dena) (numb , denb) fa≡fb = transport (cong₂ (λ x y → (x ∙ ℕ→F 0f 1f _+_ (ℕ₊₁→ℕ denb)) ≡ (y ∙ ℕ→F 0f 1f _+_ (ℕ₊₁→ℕ dena))) (trans (sym (IsPseudoOrderedField.·Assoc pof (ℤ→F 0f 1f _+_ - numa) (/ (ℕ→F 0f 1f _+_ (ℕ₊₁→ℕ dena)) (n+1#0 pof dena)) (ℕ→F 0f 1f _+_ (ℕ₊₁→ℕ dena)))) (trans (cong (λ x → (ℤ→F 0f 1f _+_ - numa ∙ x)) (trans (IsPseudoOrderedField.·Comm pof (/ (ℕ→F 0f 1f _+_ (ℕ₊₁→ℕ dena)) (n+1#0 pof dena)) (ℕ→F 0f 1f _+_ (ℕ₊₁→ℕ dena))) (IsPseudoOrderedField.divIsPartialInverseToMult pof (ℕ→F 0f 1f _+_ (ℕ₊₁→ℕ dena)) (n+1#0 pof dena)))) (IsPseudoOrderedField.·Rid pof (ℤ→F 0f 1f _+_ - numa)))) (trans (sym (IsPseudoOrderedField.·Assoc pof (ℤ→F 0f 1f _+_ - numb) (/ (ℕ→F 0f 1f _+_ (ℕ₊₁→ℕ denb)) (n+1#0 pof denb)) (ℕ→F 0f 1f _+_ (ℕ₊₁→ℕ denb)))) (trans (cong (λ x → (ℤ→F 0f 1f _+_ - numb ∙ x)) (trans (IsPseudoOrderedField.·Comm pof (/ (ℕ→F 0f 1f _+_ (ℕ₊₁→ℕ denb)) (n+1#0 pof denb)) (ℕ→F 0f 1f _+_ (ℕ₊₁→ℕ denb))) (IsPseudoOrderedField.divIsPartialInverseToMult pof (ℕ→F 0f 1f _+_ (ℕ₊₁→ℕ denb)) (n+1#0 pof denb)))) (IsPseudoOrderedField.·Rid pof (ℤ→F 0f 1f _+_ - numb))))) (transport (cong₂ (λ x y → x ≡ y) (IsPseudoOrderedField.·Assoc pof (ℚ'→F pof (numa , dena)) (ℕ→F 0f 1f _+_ (ℕ₊₁→ℕ dena)) (ℕ→F 0f 1f _+_ (ℕ₊₁→ℕ denb))) (IsPseudoOrderedField.·Assoc pof (ℚ'→F pof (numb , denb)) (ℕ→F 0f 1f _+_ (ℕ₊₁→ℕ denb)) (ℕ→F 0f 1f _+_ (ℕ₊₁→ℕ dena)))) (cong₂ (λ x y → x ∙ y) fa≡fb (IsPseudoOrderedField.·Comm pof (ℕ→F 0f 1f _+_ (ℕ₊₁→ℕ dena)) (ℕ→F 0f 1f _+_ (ℕ₊₁→ℕ denb)))))
    lemma : (a b : ℚ') → ℚ'→F pof a ≡ ℚ'→F pof b → a ∼ b
    lemma a b fa≡fb = ℤ→Finj pof (transport (cong₂ (λ x y → x ≡ y) (sym (ℤ→Fpreserves· pof (fst a) (ℕ₊₁→ℤ (snd b)))) (sym (ℤ→Fpreserves· pof (fst b) (ℕ₊₁→ℤ (snd a))))) (lemma1 a b fa≡fb))

-- transport (cong₂ (λ x y → x ≡ y) (IsPseudoOrderedField.·Assoc pof (ℚ'→F pof (numa , dena)) (ℕ→F 0f 1f _+_ (ℕ₊₁→ℕ dena)) (ℕ→F 0f 1f _+_ (ℕ₊₁→ℕ denb))) (IsPseudoOrderedField.·Assoc pof (ℚ'→F pof (numb , denb)) (ℕ→F 0f 1f _+_ (ℕ₊₁→ℕ denb)) (ℕ→F 0f 1f _+_ (ℕ₊₁→ℕ dena)))) (cong₂ (λ x y → x ∙ y) fa≡fb (IsPseudoOrderedField.·Comm pof (ℕ→F 0f 1f _+_ (ℕ₊₁→ℕ dena)) (ℕ→F 0f 1f _+_ (ℕ₊₁→ℕ denb))))

-- cong (λ x → (ℤ→F 0f 1f _+_ - numa ∙ x))  