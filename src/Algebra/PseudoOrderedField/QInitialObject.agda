{-# OPTIONS --cubical --warning=noNoEquivWhenSplitting #-}
module Algebra.PseudoOrderedField.QInitialObject where

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

open import Cubical.Data.Int.MoreInts.QuoInt
    renaming 
        (
            _+_ to _+ℤ_;
            -_ to -ℤ_;
            _·_ to _·ℤ_;
            rec to recℤ
        )
open import Cubical.Data.NatPlusOne
open import Cubical.Data.Nat
    renaming 
        (
            _+_ to _+ℕ_;
            _·_ to _·ℕ_
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
open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.Group hiding (ℤ)
open import Cubical.Algebra.Monoid
open import Algebra.ConstructiveField
open import Algebra.PseudoOrderedField.Base
open import Algebra.PseudoOrderedField.Properties

private
    variable
        ℓ ℓ' ℓ'' : Level

private
    _∘_ : ∀ {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''} → (B → C) → (A → B) → A → C
    (f ∘ g) x = f (g x)

    recℕ : {C : Type ℓ} → C → (ℕ → C → C) → ℕ → C
    recℕ x f zero = x
    recℕ x f (suc n) = f n (recℕ x f n) 

    indℕ : {C : ℕ → Type ℓ} → C zero → ((m : ℕ) → C m → C (suc m)) → (n : ℕ) → C n
    indℕ x f zero = x
    indℕ x f (suc n) = f n (indℕ x f n)

ℕ→F : ∀ {F : Type ℓ} (0f 1f : F) (_+_ : F → F → F) → ℕ → F
ℕ→F 0f 1f _+_ = recℕ 0f (λ _ x → 1f + x )

-ℕ→F : ∀ {F : Type ℓ} (0f 1f : F) (_+_ : F → F → F) (- : F → F) → ℕ → F
-ℕ→F 0f 1f _+_ - = recℕ 0f (λ _ x → (- 1f) + x )

ℤ→F : ∀ {F : Type ℓ} (0f 1f : F) (_+_  : F → F → F) (- : F → F) → ℤ → F
ℤ→F 0f 1f _+_ - a = recℤ (ℕ→F 0f 1f _+_) (-ℕ→F 0f 1f _+_ -) refl a

ℚ' : Type₀
ℚ' = ℤ × ℕ₊₁

n+1#0 : {F : Type ℓ} {_<_ : Rel F F ℓ'} {0f 1f : F} {_+_ _∙_ : F → F → F} { - : F → F} {/ : (x : F) → <→# _<_ x 0f → F} → IsPseudoOrderedField _<_ 0f 1f _+_ _∙_ (-) (/)   → ∀ d → <→# _<_ (ℕ→F 0f 1f _+_ (ℕ₊₁→ℕ d)) 0f 
n+1#0 {_<_ = _<_} {0f = 0f} {1f = 1f} {_+_ = _+_} {_∙_ = _∙_} { - = - } {/ = /} pof den = (inr (indℕ (transport (cong (λ a → 0f < a) (sym (IsPseudoOrderedField.+Rid pof 1f))) (0<1 pof)) (λ m 0<1+m → IsPseudoOrderedField.<isTrans pof (0<1 pof) (transport ((cong₂ λ a b → a < b) (IsPseudoOrderedField.+Lid pof 1f) (IsPseudoOrderedField.+Comm pof (1f + recℕ 0f (λ _ → _+_ 1f) m) 1f)) (addIsOrderCompatible pof 0<1+m 1f))) (ℕ₊₁.n den)))

ℚ'→F : ∀ {F : Type ℓ} {_<_ : Rel F F ℓ'} {0f 1f : F} {_+_ _∙_ : F → F → F} { - : F → F} {/ : (x : F) → <→# _<_ x 0f → F} → IsPseudoOrderedField _<_ 0f 1f _+_ _∙_ (-) (/) → ℚ' → F
ℚ'→F {_<_ = _<_} {0f = 0f} {1f = 1f} {_+_ = _+_} {_∙_ = _∙_} { - = - } {/ = /} pof (num , den) = (ℤ→F 0f 1f _+_ - num) ∙ / (ℕ→F 0f 1f _+_ (ℕ₊₁→ℕ den)) (n+1#0 pof den)

ℚ→FwellDefined :  ∀ {F : Type ℓ} {_<_ : Rel F F ℓ'} {0f 1f : F} {_+_ _∙_ : F → F → F} { - : F → F} {/ : (x : F) → <→# _<_ x 0f → F} → (pof : IsPseudoOrderedField _<_ 0f 1f _+_ _∙_ (-) (/)) → (a b : ℚ') → a ∼ b → ℚ'→F pof a ≡ ℚ'→F pof b
ℚ→FwellDefined {_<_ = _<_} {0f = 0f} {1f = 1f} {_+_ = _+_} {_∙_ = _∙_} { - = - } {/ = /} pof (numa , dena) (numb , denb) a∼b = transport (cong₂ (λ x y → x ≡ y) (trans ((sym (IsPseudoOrderedField.·Assoc pof (ℤ→F 0f 1f _+_ - (numa ·ℤ ℕ₊₁→ℤ denb)) (/ (ℕ→F 0f 1f _+_ (ℕ₊₁→ℕ dena)) (n+1#0 pof dena)) (/ (ℕ→F 0f 1f _+_ (ℕ₊₁→ℕ denb)) (n+1#0 pof denb))))) {!   !}) {!   !}) (cong (λ x → (x ∙ / (ℕ→F 0f 1f _+_ (ℕ₊₁→ℕ dena)) (n+1#0 pof dena)) ∙ / (ℕ→F 0f 1f _+_ (ℕ₊₁→ℕ denb)) (n+1#0 pof denb)) (cong (ℤ→F 0f 1f _+_ -) a∼b))

ℚ→F : ∀ {ℓ} {ℓ'} {F : Type ℓ} {_<_ : Rel F F ℓ'} {0f 1f : F} {_+_ _∙_ : F → F → F} { - : F → F} {/ : (x : F) → <→# _<_ x 0f → F} → isSet F → IsPseudoOrderedField _<_ 0f 1f _+_ _∙_ (-) (/) → ℚ → F 
ℚ→F {ℓ} {ℓ'} {F} {_<_} {0f} {1f} {_+_} {_∙_} { - } {/} isset pof = recQuo {R = _∼_} isset (ℚ'→F pof) (ℚ→FwellDefined pof) 