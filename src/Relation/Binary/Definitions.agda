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
        ℓ ℓ' ℓ'' ℓ''' : Level

-- On a binary relation

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

IsAsym : {A : Type ℓ} → (R : Rel A A ℓ') → Type (ℓ-max ℓ ℓ')
IsAsym R = ∀ a b → ¬ (R a b × R b a)

IsCotrans : {A : Type ℓ} → (R : Rel A A ℓ') → Type (ℓ-max ℓ ℓ')
IsCotrans R = ∀ {a b} → R a b → (∀ x → (R a x) ⊎ (R x b))

IsTight : {A : Type ℓ} → (R : Rel A A ℓ') → Type (ℓ-max ℓ ℓ')
IsTight R = ∀ {a b} → ¬ (R a b) → a ≡ b

IsTotal : {A : Type ℓ} → (R : Rel A A ℓ') → Type (ℓ-max ℓ ℓ')
IsTotal R = ∀ a b → R a b ⊎ R b a

IsConnected : {A : Type ℓ} → (R : Rel A A ℓ') → Type (ℓ-max ℓ ℓ')
IsConnected R = ∀ {a b} → ¬ (a ≡ b) → R a b ⊎ R b a 

IsConnex : {A : Type ℓ} → (R : Rel A A ℓ') → Type (ℓ-max ℓ ℓ')
IsConnex R = ∀ {a b} → ¬ (R a b ⊎ R b a) → a ≡ b

IsConnectedProperly : {A : Type ℓ} → (R : Rel A A ℓ') → Type (ℓ-max ℓ ℓ')
IsConnectedProperly R = ∀ a b → (R a b ⊎ R b a) ⊎ (a ≡ b)

IsApartnessConnected : {A : Type ℓ} → (_#_ : Rel A A ℓ'') (R : Rel A A ℓ') → Type (ℓ-max ℓ (ℓ-max ℓ'' ℓ'))
IsApartnessConnected _#_ R = ∀ {a b} → a # b → R a b ⊎ R b a

HasExcludedMiddle₂ : {A : Type ℓ} → (R : Rel A A ℓ') → Type (ℓ-max ℓ ℓ')
HasExcludedMiddle₂ R = ∀ a b → (R a b) ⊎ (¬ R a b)

-- On a binary relation and binary function

_Is_Extensional : {A : Type ℓ} → (A → A → A) → (Rel A A ℓ') → Type (ℓ-max ℓ ℓ')
_+_ Is _#_ Extensional = ∀ {w x y z} → (w + x) # (y + z) → (w # y) ⊎ (x # z)  

_Is_Compatible : {A : Type ℓ} → (A → A → A) → (Rel A A ℓ') → Type (ℓ-max ℓ ℓ')
_+_ Is _#_ Compatible = ∀ {x y} → x # y → ∀ z → (x + z) # (y + z)

-- Dedekind Completeness

IsDedekindComplete : ∀  {A : Type ℓ} (_≤_ : Rel A A ℓ') (sup : (p : A → Type ℓ'') → ∃ A (λ m → ((x : A) → p x → x ≤ m )) → A) → Type (ℓ-max (ℓ-max ℓ ℓ') (ℓ-suc ℓ''))
IsDedekindComplete {ℓ'' = ℓ''} {A} _≤_ sup = (p : A → Type ℓ'') → (upperbd : ∃ A (λ m → ((x : A) → p x → x ≤ m ))) → ((x : A) → p x → x ≤ (sup p upperbd)) × ({m x : A} → (p x → x ≤ m) → (sup p upperbd) ≤ m)

IsAlmostDedekindComplete :  ∀  {A : Type ℓ} (_<_ : Rel A A ℓ') (_#_ : Rel A A ℓ''') (sup : (p : A → Type ℓ'') → ∃ A (λ m → ((x : A) → x # m → p x → x < m )) → A) → Type (ℓ-max (ℓ-max ℓ ℓ') (ℓ-max (ℓ-suc ℓ'') ℓ'''))
IsAlmostDedekindComplete {ℓ'' = ℓ''} {A} _<_ _#_ sup = (p : A → Type ℓ'') → (almostupperbd : ∃ A (λ m → ((x : A) → x # m → p x → x < m ))) → ((x : A) → x # (sup p almostupperbd) → p x → x < (sup p almostupperbd)) × ({m x : A} → (x # m → p x → x < m) → (sup p almostupperbd) < m)

{-
IsDedekindComplete : ∀ (A : Type ℓ) (_≤_ : Rel A A ℓ') (ℓ'' : Level) → Type (ℓ-max (ℓ-max ℓ ℓ') (ℓ-suc ℓ''))
IsDedekindComplete A _≤_ ℓ'' = (p : A → Type ℓ'') → ∃ A (λ m → ((x : A) → p x → x ≤ m )) → ∃ A (λ sup → ( ((x : A) → p x → x ≤ sup) × ((m x : A) → (p x → x ≤ m) → sup ≤ m) ) ) 
-}
 