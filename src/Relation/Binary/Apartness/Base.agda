{-# OPTIONS --cubical --warning=noNoEquivWhenSplitting #-}
module Relation.Binary.Apartness.Base where 

open import Cubical.Foundations.Prelude

open import Cubical.Relation.Binary.Base using (Rel)
open import Relation.Binary.Definitions

private
  variable
    ℓ ℓ' : Level


record IsApartnessRel {A : Type ℓ} (R : Rel A A ℓ') : Type (ℓ-max ℓ ℓ') where
    constructor isapartnessrel
    field
        isSym : IsSym R
        isIrrefl : IsIrrefl R
        isCotrans : IsCotrans R


record IsTightApartnessRel {A : Type ℓ} (R : Rel A A ℓ') : Type (ℓ-max ℓ ℓ') where
    constructor istightapartnessrel
    field
        isApartnessRel : IsApartnessRel R
        isTight : IsTight R

    open IsApartnessRel isApartnessRel public