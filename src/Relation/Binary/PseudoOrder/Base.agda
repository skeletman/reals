{-# OPTIONS --cubical --warning=noNoEquivWhenSplitting #-}
module Relation.Binary.PseudoOrder.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sum.Base renaming (_⊎_ to infixr 4 _⊎_)
open import Cubical.Relation.Binary.Base
open import Relation.Binary.Definitions

private
    variable
        ℓ ℓ' : Level

record IsPseudoOrder {A : Type ℓ} (_<_ : Rel A A ℓ') : Type (ℓ-max ℓ ℓ') where
    constructor ispseudoorder
    field
        isAsym : IsAsym _<_
        isCotrans : IsCotrans _<_ 
        isConnex : IsConnex _<_

<→# : {A : Type ℓ} → (_<_ : Rel A A ℓ') → Rel A A ℓ'
<→# _<_ a b = (a < b) ⊎ (b < a)
