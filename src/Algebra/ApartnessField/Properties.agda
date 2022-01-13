{-# OPTIONS --cubical --warning=noNoEquivWhenSplitting #-}
module Algebra.ApartnessField.Properties where

open import Cubical.Foundations.Prelude renaming (_∙_ to trans)

open import Cubical.Relation.Nullary.Base using (¬_)
open import Cubical.Relation.Binary.Base using (Rel)
open import Relation.Binary.Apartness
open import Relation.Binary.Definitions

open import Algebra.ApartnessField.Base
open import Algebra.Group.Properties
open import Cubical.Algebra.Group
open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Ring

open import Cubical.Data.Sum.Base renaming (_⊎_ to infixr 4 _⊎_)
open import Cubical.Data.Empty.Base using (⊥)

private
  variable
    ℓ ℓ' : Level
    F : Type ℓ
    _∥_ : Rel F F ℓ'
    0f 1f : F
    _+_ _∙_ : F → F → F
    -_ : F → F


0∥-1 : {/ : (x : F) → x ∥ 0f → F} → IsApartnessField _∥_ 0f 1f _+_ _∙_ -_ / 
  → 0f ∥ (- 1f)
0∥-1 {_∥_ = _∥_} (isapartnessfield (iscommring (isring (isabgroup isGroup _) _ _) _) _ 0∥1 _ _ _ -Preserves∥) 
  = ≡preserves∥c {_∥_ = _∥_} (ie≡e isGroup) (-Preserves∥ 0∥1) 

