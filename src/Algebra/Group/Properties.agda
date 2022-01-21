{-# OPTIONS --cubical --warning=noNoEquivWhenSplitting #-}
module Algebra.Group.Properties where

open import Cubical.Foundations.Prelude renaming (_∙_ to trans)
open import Cubical.Algebra.Group
open import Cubical.Algebra.Monoid
open import Cubical.Algebra.Semigroup
open import Cubical.Data.Sigma

private
    variable
        ℓ : Level
        G : Type ℓ
        e : G 
        _*_ _+_ : G → G → G
        i - : G → G
        
ie≡e : IsGroup e _*_ i → i e ≡ e
ie≡e {e = e} {i = i} (isgroup (ismonoid isSemigroup identity) inverse) = trans (sym (fst (identity (i e)))) (snd (inverse e))

x-z+z≡x : IsGroup e _+_ - → ∀ x z → (x + - z) + z ≡ x
x-z+z≡x {_+_ = _+_} { - = - } (isgroup (ismonoid isSemigroup identity) inverse) x z = trans (sym (IsSemigroup.assoc isSemigroup x (- z) z )) (trans (cong (λ a → x + a) (snd (inverse z))) (fst (identity x)))

x+z-z≡x : IsGroup e _+_ - → ∀ x z → (x + z) + - z ≡ x
x+z-z≡x {_+_ = _+_} { - = - } (isgroup (ismonoid isSemigroup identity) inverse) x z = trans (sym (IsSemigroup.assoc isSemigroup x z (- z) )) ((trans (cong (λ a → x + a) (fst (inverse z))) (fst (identity x))))

-[-x]≡x : IsGroup e _+_ - → ∀ x → - (- x) ≡ x
-[-x]≡x {e = e} {_+_ = _+_} { - = - } (isgroup (ismonoid +isSemigroup +identity) inverse) x = trans (sym (x-z+z≡x (isgroup (ismonoid +isSemigroup +identity) inverse) (- (- x)) x)) (trans (cong (λ a → a + x) (snd (inverse (- x)))) (snd (+identity x)))
