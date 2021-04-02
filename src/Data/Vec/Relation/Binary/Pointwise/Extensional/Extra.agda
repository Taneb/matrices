{-# OPTIONS --safe --without-K #-}
-- I think I could get this into stdlib, as Data.Vec.Relation.Binary.Pointwise.Extensional.Properties or something
-- It should a counterpart to everything in Data.Vec.Properties that has an _≡_ on its left had side
-- As well as congruence properties which are unnecessary with _≡_
module Data.Vec.Relation.Binary.Pointwise.Extensional.Extra where

open import Algebra.Definitions
open import Data.Nat.Base using (ℕ)
open import Data.Vec.Base
open import Data.Vec.Properties hiding (zipWith-assoc; zipWith-comm; zipWith-identityˡ; zipWith-identityʳ)
open import Data.Vec.Relation.Binary.Pointwise.Extensional
open import Level
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as ≡

private
  variable
    a ℓ : Level
    A : Set a
    n : ℕ

module _ {_∼_ : Rel A ℓ} {f : A → A → A} where
  zipWith-cong₂ : Congruent₂ _∼_ f → Congruent₂ (Pointwise _∼_) (zipWith {n = n} f)
  zipWith-cong₂ cong {u} {v} {x} {y} ps qs = ext λ i → 
    subst₂ _∼_
      (≡.sym (lookup-zipWith f i u x))
      (≡.sym (lookup-zipWith f i v y))
      (cong (Pointwise.app ps i) (Pointwise.app qs i))

  zipWith-assoc : Associative _∼_ f → Associative (Pointwise _∼_) (zipWith {n = n} f)
  zipWith-assoc assoc xs ys zs = ext λ i →
    subst₂ _∼_
      (≡.sym (≡.trans (lookup-zipWith f i (zipWith f xs ys) zs) (cong (λ v → f v (lookup zs i)) (lookup-zipWith f i xs ys))))
      (≡.sym (≡.trans (lookup-zipWith f i xs (zipWith f ys zs)) (cong (λ v → f (lookup xs i) v) (lookup-zipWith f i ys zs))))
      (assoc (lookup xs i) (lookup ys i) (lookup zs i))

  zipWith-comm : Commutative _∼_ f → Commutative (Pointwise _∼_) (zipWith {n = n} f)
  zipWith-comm comm xs ys = ext λ i →
    subst₂ _∼_
      (≡.sym (lookup-zipWith f i xs ys))
      (≡.sym (lookup-zipWith f i ys xs))
      (comm (lookup xs i) (lookup ys i))

module _ {_∼_ : Rel A ℓ} {f : A → A → A} {e : A} where
  zipWith-identityˡ : LeftIdentity _∼_ e f → LeftIdentity (Pointwise _∼_) (replicate e) (zipWith {n = n} f)
  zipWith-identityˡ identityˡ xs = ext λ i →
    subst (_∼ lookup xs i)
      (≡.sym (≡.trans (lookup-zipWith f i (replicate e) xs) (≡.cong (λ v → f v (lookup xs i)) (lookup-replicate i e))))
      (identityˡ (lookup xs i))

  zipWith-identityʳ : RightIdentity _∼_ e f → RightIdentity (Pointwise _∼_) (replicate e) (zipWith {n = n} f)
  zipWith-identityʳ identityʳ xs = ext λ i →
    subst (_∼ lookup xs i)
      (≡.sym (≡.trans (lookup-zipWith f i xs (replicate e)) (≡.cong (λ v → f (lookup xs i) v) (lookup-replicate i e))))
      (identityʳ (lookup xs i))
