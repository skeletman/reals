{-# OPTIONS --cubical --warning=noNoEquivWhenSplitting #-}
module Algebra.AbGroup.Properties where

open import Cubical.Foundations.Prelude using (Level; Type; ℓ-max; _≡_)
open import Cubical.Algebra.AbGroup

private
    variable
        ℓ : Level
        G : Type ℓ
        0g : G 
        _+_ : G → G → G
        - : G → G
        
        
