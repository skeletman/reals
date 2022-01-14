{-# OPTIONS --cubical --warning=noNoEquivWhenSplitting #-}
module Relation.Binary.TotalOrder.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Sum.Base renaming (_⊎_ to infixr 4 _⊎_)
open import Cubical.Relation.Nullary.Base using (¬_)
open import Cubical.Relation.Binary.Base
open import Relation.Binary.Definitions

private
    variable
        ℓ ℓ' : Level

record IsTotalOrder {A : Type ℓ} (_≤_ : Rel A A ℓ') : Type (ℓ-max ℓ ℓ') where
    constructor istotalorder
    field 
        isRefl : IsRefl _≤_
        isTrans : IsTrans _≤_
        isAntisym : IsAntisym _≤_
        isTotal : IsTotal _≤_

record IsWeakStrictTotalOrder {A : Type ℓ} (_<_ : Rel A A ℓ') : Type (ℓ-max ℓ ℓ') where
    constructor isweakstricttotalorder
    field
        isIrrefl : IsIrrefl _<_
        isTrans : IsTrans _<_
        isConnected : IsConnected _<_

record IsStrongStrictTotalOrder {A : Type ℓ} (_<_ : Rel A A ℓ') : Type (ℓ-max ℓ ℓ') where
    constructor isstrongstricttotalorder
    field
        isIrrefl : IsIrrefl _<_
        isTrans : IsTrans _<_
        isConnectedProperly : IsConnectedProperly _<_

record IsTotalOrderWithExcludedMiddle {A : Type ℓ} (_≤_ : Rel A A ℓ') : Type (ℓ-max ℓ ℓ') where
    constructor istotalorderwithexcludedmiddle
    field 
        isRefl : IsRefl _≤_
        isTrans : IsTrans _≤_
        isAntisym : IsAntisym _≤_
        isTotal : IsTotal _≤_
        hasExcludedMiddle : HasExcludedMiddle₂ _≤_

record IsStrictTotalOrderWithExcludedMiddle {A : Type ℓ} (_<_ : Rel A A ℓ') : Type (ℓ-max ℓ ℓ') where
    constructor isstricttotalorderwithexcludedmiddle
    field
        isIrrefl : IsIrrefl _<_
        isTrans : IsTrans _<_
        isConnected : IsConnected _<_
        hasExcludedMiddle : HasExcludedMiddle₂ _<_

strictify : {A : Type ℓ} → Rel A A ℓ' → Rel A A (ℓ-max ℓ ℓ')
strictify _≤_ a b = (a ≤ b) × (¬ (a ≡ b))

nonstrictify : {A : Type ℓ} → Rel A A ℓ' → Rel A A (ℓ-max ℓ ℓ')
nonstrictify _<_ a b = (a < b) ⊎ (a ≡ b)