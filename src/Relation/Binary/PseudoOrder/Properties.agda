{-# OPTIONS --cubical --warning=noNoEquivWhenSplitting #-}
module Relation.Binary.PseudoOrder.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sum.Base renaming (_⊎_ to infixr 4 _⊎_; rec to rec⊎)
open import Cubical.Data.Empty.Base renaming (rec to rec⊥)
open import Cubical.Relation.Binary.Base
open import Relation.Binary.Definitions
open import Relation.Binary.Apartness
open import Relation.Binary.PseudoOrder.Base

private
    variable
        ℓ ℓ' : Level
        A : Type ℓ

pseudoOrder→tightApartness : (_<_ : Rel A A ℓ') → IsPseudoOrder _<_ → IsTightApartnessRel (<→# _<_)
pseudoOrder→tightApartness _<_ (ispseudoorder isAsym isCotrans isConnex) = 
    istightapartnessrel 
        (isapartnessrel 
            (λ a<>b → rec⊎ (λ a<b → inr a<b) (λ b<a → inl b<a) a<>b) 
            (λ a a<>a → rec⊎ (λ z → isAsym a a (z , z)) (λ z → isAsym a a (z , z)) a<>a) 
            λ a<>b x → rec⊎ 
                (λ a<b  → rec⊎ (λ a<x → inl (inl a<x)) (λ x<b → inr (inl x<b)) (isCotrans a<b x)) 
                (λ b<a → rec⊎ (λ b<x → inr (inr b<x)) (λ x<a → inl (inr x<a)) (isCotrans b<a x)) 
                a<>b
        ) 
        isConnex