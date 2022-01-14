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
        isRefl to IsRefl
    ) 
    public

private
    variable
        ℓ ℓ' : Level

{-
IsRefl : {A : Type ℓ} → (R : Rel A A ℓ') → Type (ℓ-max ℓ ℓ')
IsRefl R = ∀ a → R a a
-}

IsSym : {A : Type ℓ} → (R : Rel A A ℓ') → Type (ℓ-max ℓ ℓ')
IsSym R = ∀ {a b} → R a b → R b a

IsAntisym : {A : Type ℓ} → (R : Rel A A ℓ') → Type (ℓ-max ℓ ℓ')
IsAntisym R =  ∀ {a b} → R a b → R b a → a ≡ b

IsTrans : {A : Type ℓ} → (R : Rel A A ℓ') → Type (ℓ-max ℓ ℓ')
IsTrans R =  ∀ {a b c}  → R a b → R b c → R a c

IsIrrefl : {A : Type ℓ} → (R : Rel A A ℓ') → Type (ℓ-max ℓ ℓ')
IsIrrefl R = ∀ a → ¬(R a a)

IsCotrans : {A : Type ℓ} → (R : Rel A A ℓ') → Type (ℓ-max ℓ ℓ')
IsCotrans R = ∀ {a b} → R a b → (∀ x → (R a x) ⊎ (R x b))

IsTight : {A : Type ℓ} → (R : Rel A A ℓ') → Type (ℓ-max ℓ ℓ')
IsTight R = ∀ {a b} → ¬ (R a b) → a ≡ b

IsTotal : {A : Type ℓ} → (R : Rel A A ℓ') → Type (ℓ-max ℓ ℓ')
IsTotal R = ∀ a b → R a b ⊎ R b a

IsConnected : {A : Type ℓ} → (R : Rel A A ℓ') → Type (ℓ-max ℓ ℓ')
IsConnected R = ∀ {a b} → ¬ (a ≡ b) → R a b ⊎ R b a 

IsConnectedProperly : {A : Type ℓ} → (R : Rel A A ℓ') → Type (ℓ-max ℓ ℓ')
IsConnectedProperly R = ∀ a b → (R a b ⊎ R b a) ⊎ (a ≡ b)

HasExcludedMiddle₂ : {A : Type ℓ} → (R : Rel A A ℓ') → Type (ℓ-max ℓ ℓ')
HasExcludedMiddle₂ R = ∀ a b → (R a b) ⊎ (¬ R a b)

IsDedekindComplete : ∀ (A : Type ℓ) (_≤_ : Rel A A ℓ') (ℓ'' : Level) → Type (ℓ-max (ℓ-max ℓ ℓ') (ℓ-suc ℓ''))
IsDedekindComplete A _≤_ ℓ'' = (p : A → Type ℓ'') → ∃ A (λ m → ((x : A) → p x → x ≤ m )) → ∃ A (λ sup → ( ((x : A) → p x → x ≤ sup) × ((m x : A) → (p x → x ≤ m) → sup ≤ m) ) ) 
