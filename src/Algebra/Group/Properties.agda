{-# OPTIONS --cubical --warning=noNoEquivWhenSplitting #-}
module Algebra.Group.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Algebra.Monoid
open import Cubical.Algebra.Group
open import Cubical.Data.Sigma

private
    variable
        ℓ : Level
        G : Type ℓ
        e : G 
        _*_ : G → G → G
        i : G → G
        
ie≡e : IsGroup e _*_ i → i e ≡ e
ie≡e {e = e} {i = i} (isgroup (ismonoid isSemigroup identity) inverse) = sym (fst (identity (i e))) ∙ snd (inverse e)
