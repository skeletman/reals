{-# OPTIONS --cubical --warning=noNoEquivWhenSplitting #-}
module Relation.Binary.Definitions where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Sum.Base renaming (_⊎_ to infixr 4 _⊎_)
open import Cubical.Relation.Nullary.Base using (¬_)
open import Cubical.Relation.Binary.Base
open BinaryRelation
    using ()
    renaming 
    (
        isRefl to IsRefl;
        isSym to IsSym;
        isAntisym to IsAntisym;
        isTrans to IsTrans
    ) 
    public

private
    variable
        ℓ ℓ' : Level

IsIrrefl : {A : Type ℓ} → (R : Rel A A ℓ') → Type (ℓ-max ℓ ℓ')
IsIrrefl R = ∀ {a} → ¬(R a a)

IsCotrans : {A : Type ℓ} → (R : Rel A A ℓ') → Type (ℓ-max ℓ ℓ')
IsCotrans R = ∀ {a b} → R a b → (∀ x → (R a x) ⊎ (R x b))

IsTight : {A : Type ℓ} → (R : Rel A A ℓ') → Type (ℓ-max ℓ ℓ')
IsTight R = ∀ {a b} → ¬ (R a b) → a ≡ b

IsCotight : {A : Type ℓ} → (R : Rel A A ℓ') → Type (ℓ-max ℓ ℓ')
IsCotight R = ∀ {a b} → a ≡ b → ¬ (R a b) 

Irrefl→Cotight : {A : Type ℓ} → {R : Rel A A ℓ'} → IsIrrefl R → IsCotight R
Irrefl→Cotight {R = R} isIrrefl {a = a} a≡b  = transport (cong (λ x → ¬ R a x) a≡b) isIrrefl

Cotight→Irrefl : {A : Type ℓ} → {R : Rel A A ℓ'} → IsCotight R → IsIrrefl R 
Cotight→Irrefl isCotight  = isCotight refl

IsDedekindComplete : ∀ (A : Type ℓ) (_≤_ : Rel A A ℓ') (ℓ'' : Level) → Type (ℓ-max (ℓ-max ℓ ℓ') (ℓ-suc ℓ''))
IsDedekindComplete A _≤_ ℓ'' = (p : A → Type ℓ'') → ∃ A (λ m → ((x : A) → p x → x ≤ m )) → ∃ A (λ sup → ( ((x : A) → p x → x ≤ sup) × ((m x : A) → (p x → x ≤ m) → sup ≤ m) ) ) 
