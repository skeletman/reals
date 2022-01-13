{-# OPTIONS --cubical --warning=noNoEquivWhenSplitting #-}
module Algebra.Ring.Properties where

open import Cubical.Foundations.Prelude using (Level; Type; ℓ-max; _≡_)
open import Cubical.Algebra.Ring

private
    variable
        ℓ : Level
        R : Type ℓ
        0r 1r : R 
        _+_ _∙_ : R → R → R
        - : R → R
        
        
