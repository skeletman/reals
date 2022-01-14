{-# OPTIONS --cubical --warning=noNoEquivWhenSplitting #-}
module Relation.Binary.TotalOrder.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Sum.Base renaming (_⊎_ to infixr 4 _⊎_; rec to rec⊎)
open import Cubical.Data.Empty.Base renaming (rec to rec⊥)
open import Cubical.Relation.Nullary.Base using (¬_)
open import Cubical.Relation.Binary.Base
open import Relation.Binary.Definitions
open import Relation.Binary.TotalOrder.Base

private
    variable
        ℓ ℓ' : Level
        A : Type ℓ
        < ≤ : Rel A A ℓ'

totalOrder→weakStrictTotalOrder : IsTotalOrder ≤ → IsWeakStrictTotalOrder (strictify ≤)
totalOrder→weakStrictTotalOrder {≤ = ≤} (istotalorder isRefl isTrans isAntisym isTotal) = 
    isweakstricttotalorder 
        (λ a a<a → snd a<a refl) 
        (λ {a} {b} {c} a<b b<c → 
            isTrans (fst a<b) (fst b<c) 
            , 
            λ a≡c → (snd a<b) 
                (
                    isAntisym 
                        (fst a<b) 
                        (isTrans 
                            (fst b<c) 
                            (transport (cong (λ x → ≤ x a) a≡c) (isRefl a))
                        )
                )
        )
        λ {a} {b} ¬a≡b → rec⊎ (λ a≤b → inl (a≤b , ¬a≡b)) (λ b≤a → inr (b≤a , λ b≡a → ¬a≡b (sym b≡a))) (isTotal a b)

strongStrictTotalOrder→totalOrder : IsStrongStrictTotalOrder < → IsTotalOrder (nonstrictify <)
strongStrictTotalOrder→totalOrder {< = <} (isstrongstricttotalorder isIrrefl isTrans isConnectedProperly) = 
    istotalorder 
        (λ a → inr refl) 
        (λ {a = a} {c = c} a≤b b≤c → 
            rec⊎ 
                (λ a<b → inl (rec⊎ 
                    (λ b<c → isTrans a<b b<c) 
                    (λ b≡c → transport (cong (λ x → < a x) b≡c) a<b)
                    b≤c
                )) 
                (λ a≡b → rec⊎ 
                    (λ b<c → inl (transport (cong (λ x → < x c) (sym a≡b)) b<c)) 
                    (λ b≡c → inr (a≡b ∙ b≡c)) b≤c
                ) 
                a≤b
        ) 
        (λ {a = a} a≤b b≤a → rec⊎ (rec⊎ (λ b<a a<b → rec⊥ ((isIrrefl a) (isTrans a<b b<a))) (λ b≡a _ → sym b≡a) b≤a) (λ z → z) a≤b) 
        λ a b → rec⊎ (λ a<b⊎b<a → rec⊎ (λ a<b → inl (inl a<b)) (λ b<a → inr (inl b<a)) a<b⊎b<a) (λ a≡b → inl (inr a≡b)) (isConnectedProperly a b) 

strongStrictTotalOrder→strictTotalOrderWithExcludedMiddle : IsStrongStrictTotalOrder < → IsStrictTotalOrderWithExcludedMiddle <
strongStrictTotalOrder→strictTotalOrderWithExcludedMiddle {< = <} (isstrongstricttotalorder isIrrefl isTrans isConnectedProperly) = 
    isstricttotalorderwithexcludedmiddle 
        isIrrefl 
        isTrans 
        (λ {a} {b} ¬a≡b → rec⊎ (λ z → z) (λ a≡b → rec⊥ (¬a≡b a≡b)) (isConnectedProperly a b)) 
        λ a b → rec⊎ 
            (λ a<>b → rec⊎ 
                (λ a<b → inl a<b) 
                (λ b<a → inr λ a<b → isIrrefl a (isTrans a<b b<a)) 
                a<>b
            ) 
            (λ a≡b →  inr (transport (cong (λ x → ¬ < a x) a≡b) (isIrrefl a))) 
            (isConnectedProperly a b)  


strongStrictTotalOrder→totalOrderWithExcludedMiddle : IsStrongStrictTotalOrder < → IsTotalOrderWithExcludedMiddle (nonstrictify <)
strongStrictTotalOrder→totalOrderWithExcludedMiddle {< = <} (isstrongstricttotalorder isIrrefl isTrans isConnectedProperly) = 
    istotalorderwithexcludedmiddle
        (λ a → inr refl) 
        (λ {a = a} {c = c} a≤b b≤c → 
            rec⊎ 
                (λ a<b → inl (rec⊎ 
                    (λ b<c → isTrans a<b b<c) 
                    (λ b≡c → transport (cong (λ x → < a x) b≡c) a<b)
                    b≤c
                )) 
                (λ a≡b → rec⊎ 
                    (λ b<c → inl (transport (cong (λ x → < x c) (sym a≡b)) b<c)) 
                    (λ b≡c → inr (a≡b ∙ b≡c)) b≤c
                ) 
                a≤b
        ) 
        (λ {a = a} a≤b b≤a → rec⊎ (rec⊎ (λ b<a a<b → rec⊥ ((isIrrefl a) (isTrans a<b b<a))) (λ b≡a _ → sym b≡a) b≤a) (λ z → z) a≤b) 
        (λ a b → rec⊎ (λ a<b⊎b<a → rec⊎ (λ a<b → inl (inl a<b)) (λ b<a → inr (inl b<a)) a<b⊎b<a) (λ a≡b → inl (inr a≡b)) (isConnectedProperly a b) )
        λ a b → rec⊎ 
            (λ a<>b → rec⊎ 
                (λ a<b → inl (inl a<b)) 
                (λ b<a → inr λ a≤b → rec⊎ 
                    (λ a<b → isIrrefl a (isTrans a<b b<a)) 
                    (λ a≡b → isIrrefl a (transport (cong (λ x → < x a) (sym a≡b)) b<a)) 
                    a≤b
                ) 
                a<>b
            ) 
            (λ a≡b → inl (inr a≡b)) 
            (isConnectedProperly a b)
