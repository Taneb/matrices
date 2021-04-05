{-# OPTIONS --safe --without-K #-}
open import Algebra.Bundles

module Matrix {c} {ℓ} (ℛ : Semiring c ℓ) where

open Semiring ℛ renaming (Carrier to R)

open import Algebra.Core
import Algebra.Definitions
open import Algebra.Properties.Semiring.Sum ℛ
import Algebra.Structures
open import Data.Bool.Base using (if_then_else_)
open import Data.Fin.Base using (Fin)
open import Data.Fin.Properties using (_≟_)
open import Data.Nat.Base using (ℕ)
open import Data.Product
open import Data.Vec.Functional
open import Data.Vec.Functional.Relation.Binary.Pointwise as PW using (Pointwise)
import Data.Vec.Functional.Relation.Binary.Pointwise.Properties as PW
open import Function.Base using (_∘_)
open import Relation.Nullary using (does)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)
import Relation.Binary.Reasoning.Setoid as Setoid-Reasoning

Matrix : ℕ → ℕ → Set c
Matrix m n = Vector (Vector R n) m

_≋_ : ∀ {m n} → Rel (Matrix m n) ℓ
_≋_ = Pointwise (Pointwise _≈_)

≋-isEquivalence : ∀ {m n} → IsEquivalence (_≋_ {m} {n})
≋-isEquivalence {m} {n} = PW.isEquivalence (PW.isEquivalence isEquivalence n) m

0M : ∀ {m n} → Matrix m n
0M = replicate (replicate 0#)

1M : ∀ {m} → Matrix m m
1M i j = if does (i ≟ j) then 1# else 0#

-- Addition
------------------------------------------------------------------------

_+M_ : ∀ {m n} → Op₂ (Matrix m n)
_+M_ = zipWith (zipWith _+_)

module _ {m n} where
  open Algebra.Definitions (_≋_ {m} {n})
  open Algebra.Structures (_≋_ {m} {n})

  +M-cong : Congruent₂ _+M_
  +M-cong p q i j = +-cong (p i j) (q i j)

  +M-assoc : Associative _+M_
  +M-assoc M N O i j  = +-assoc (M i j) (N i j) (O i j)

  +M-comm : Commutative _+M_
  +M-comm M N i j = +-comm (M i j) (N i j)

  +M-identityˡ : LeftIdentity 0M _+M_
  +M-identityˡ M i j = +-identityˡ (M i j)

  +M-identityʳ : RightIdentity 0M _+M_
  +M-identityʳ M i j = +-identityʳ (M i j)

  +M-identity : Identity 0M _+M_
  +M-identity = +M-identityˡ , +M-identityʳ

  -- Structures
  ----------------------------------------------------------------------

  +M-isMagma : IsMagma _+M_
  +M-isMagma = record
    { isEquivalence = ≋-isEquivalence
    ; ∙-cong = +M-cong
    }

  +M-isSemigroup : IsSemigroup _+M_
  +M-isSemigroup = record
    { isMagma = +M-isMagma
    ; assoc = +M-assoc
    }

  +M-isCommutativeSemigroup : IsCommutativeSemigroup _+M_
  +M-isCommutativeSemigroup = record
    { isSemigroup = +M-isSemigroup
    ; comm = +M-comm
    }

  +M-0M-isMonoid : IsMonoid _+M_ 0M
  +M-0M-isMonoid = record
    { isSemigroup = +M-isSemigroup
    ; identity = +M-identity
    }

  +M-0M-isCommutativeMonoid : IsCommutativeMonoid _+M_ 0M
  +M-0M-isCommutativeMonoid = record
    { isMonoid = +M-0M-isMonoid
    ; comm = +M-comm
    }

  -- Bundles
  ----------------------------------------------------------------------

  +M-magma : Magma c ℓ
  +M-magma = record { isMagma = +M-isMagma }

  +M-semigroup : Semigroup c ℓ
  +M-semigroup = record { isSemigroup = +M-isSemigroup }

  +M-commutativeSemigroup : CommutativeSemigroup c ℓ
  +M-commutativeSemigroup = record { isCommutativeSemigroup = +M-isCommutativeSemigroup }

  +M-0M-monoid : Monoid c ℓ
  +M-0M-monoid = record { isMonoid = +M-0M-isMonoid }

  +M-0M-commutativeMonoid : Monoid c ℓ
  +M-0M-commutativeMonoid = record { isMonoid = +M-0M-isMonoid }

-- Multiplication
------------------------------------------------------------------------

-- NOTE: this uses the obvious O(n³) algorithm
-- Faster algorithms generally don't work on arbitrary semirings
_*M_ : ∀ {m n o} → Matrix n o → Matrix m n → Matrix m o
M *M N = λ i k → ∑[ j < _ ] (M j k * N i j)

-- due to the dimension-changing nature of _*M_ we can't use the
-- standard type definitions in the Algebra heirarchy. I'm going to
-- use those names, but aim for types that would let me make this a
-- Category in the agda-categories library with minimal effort

*M-cong : ∀ {n m o} {M M′ : Matrix m o} {N N′ : Matrix n m} → M ≋ M′ → N ≋ N′ → (M *M N) ≋ (M′ *M N′)
*M-cong {M = M} {M′} {N} {N′} M≋M′ N≋N′ i k = sum-cong-≋ (λ j → *-cong (M≋M′ j k) (N≋N′ i j))

*M-assoc : ∀ {m n o p} (M : Matrix o p) (N : Matrix n o) (O : Matrix m n) → ((M *M N) *M O) ≋ (M *M (N *M O))
*M-assoc M N O i l = begin
  ((M *M N) *M O) i l ≡⟨⟩
  ∑[ j < _ ] (∑[ k < _ ] (M k l * N j k) * O i j) ≈⟨ sum-cong-≋ (λ j → sum-distribʳ (O i j) λ k → M k l * N j k) ⟩
  ∑[ j < _ ] ∑[ k < _ ] ((M k l * N j k) * O i j) ≈⟨ sum-cong-≋ (λ j → sum-cong-≋ λ k → *-assoc (M k l) (N j k) (O i j)) ⟩
  ∑[ j < _ ] ∑[ k < _ ] (M k l * (N j k * O i j)) ≈⟨ ∑-comm (λ j k → M k l * (N j k * O i j)) ⟩
  ∑[ k < _ ] ∑[ j < _ ] (M k l * (N j k * O i j)) ≈˘⟨ sum-cong-≋ (λ k → sum-distribˡ (M k l) λ j → N j k * O i j) ⟩
  ∑[ k < _ ] (M k l * ∑[ j < _ ] (N j k * O i j)) ≡⟨⟩
  (M *M (N *M O)) i l ∎
  where open Setoid-Reasoning setoid

private
  module _ where
    open Setoid-Reasoning setoid

    -- a pair of lemmas for identity proofs
    -- the sum of a vector of interesting values multiplies pointwise by a
    -- one-hot vector is the value of the interesting vector at the hot point

    *M-identityˡ-lemma : ∀ {m} (M : Fin m → R) (y : Fin m) → ∑[ j < _ ] ((if does (j ≟ y) then 1# else 0#) * M j) ≈ M y
    *M-identityˡ-lemma {ℕ.suc m} M Fin.zero = begin
      ∑[ j < ℕ.suc m ] ((if does (j ≟ Fin.zero) then 1# else 0#) * M j)
        ≈⟨ +-cong (*-identityˡ (M Fin.zero)) (trans (sum-cong-≋ λ j → zeroˡ (M (Fin.suc j))) (sum-replicate-zero m)) ⟩
      M Fin.zero + 0#
        ≈⟨ +-identityʳ (M Fin.zero) ⟩
      M Fin.zero
        ∎
    *M-identityˡ-lemma {ℕ.suc m} M (Fin.suc y) = begin
      ∑[ j < ℕ.suc m ] ((if does (j ≟ Fin.suc y) then 1# else 0#) * M j)
        ≈⟨ +-cong (zeroˡ (M Fin.zero)) (*M-identityˡ-lemma (M ∘ Fin.suc) y) ⟩
      0# + M (Fin.suc y)
        ≈⟨ +-identityˡ (M (Fin.suc y)) ⟩
      M (Fin.suc y)
        ∎

    *M-identityʳ-lemma : ∀ {m} (M : Fin m → R) (x : Fin m) → ∑[ j < _ ] (M j * (if does (x ≟ j) then 1# else 0#)) ≈ M x
    *M-identityʳ-lemma {ℕ.suc m} M Fin.zero = begin
      ∑[ j < ℕ.suc m ] (M j * (if does (Fin.zero ≟ j) then 1# else 0#))
        ≈⟨ +-cong (*-identityʳ (M Fin.zero)) (trans (sum-cong-≋ λ j → zeroʳ (M (Fin.suc j))) (sum-replicate-zero m)) ⟩
      M Fin.zero + 0#
        ≈⟨ +-identityʳ (M Fin.zero) ⟩
      M Fin.zero
        ∎
    *M-identityʳ-lemma {ℕ.suc m} M (Fin.suc x) = begin
      ∑[ j < ℕ.suc m ] (M j * (if does (Fin.suc x ≟ j) then 1# else 0#))
        ≈⟨ +-cong (zeroʳ (M Fin.zero)) (*M-identityʳ-lemma (M ∘ Fin.suc) x) ⟩
      0# + M (Fin.suc x)
        ≈⟨ +-identityˡ (M (Fin.suc x)) ⟩
      M (Fin.suc x)
        ∎

*M-identityˡ : ∀ {m n} (M : Matrix m n) → (1M *M M) ≋ M
*M-identityˡ M i j = *M-identityˡ-lemma (M i) j

*M-identityʳ : ∀ {m n} (M : Matrix m n) → (M *M 1M) ≋ M
*M-identityʳ M i j = *M-identityʳ-lemma (λ i′ → M i′ j) i

*M-distribˡ-+M : ∀ {m n o} (M : Matrix n o) (N O : Matrix m n) → (M *M (N +M O)) ≋ ((M *M N) +M (M *M O))
*M-distribˡ-+M M N O i k = begin
  (M *M (N +M O)) i k ≡⟨⟩
  ∑[ j < _ ] (M j k * (N i j + O i j)) ≈⟨ sum-cong-≋ (λ j → distribˡ (M j k) (N i j) (O i j)) ⟩
  ∑[ j < _ ] ((M j k * N i j) + (M j k * O i j)) ≈⟨ ∑-distrib-+ (λ j → M j k * N i j) (λ j → M j k * O i j) ⟩
  ((M *M N) +M (M *M O)) i k ∎
  where open Setoid-Reasoning setoid

*M-distribʳ-+M : ∀ {m n o} (M : Matrix m n) (N O : Matrix n o) → ((N +M O) *M M) ≋ ((N *M M) +M (O *M M))
*M-distribʳ-+M M N O i k = begin
  ((N +M O) *M M) i k ≡⟨⟩
  ∑[ j < _ ] ((N j k + O j k) * M i j) ≈⟨ sum-cong-≋ (λ j → distribʳ (M i j) (N j k) (O j k)) ⟩
  ∑[ j < _ ] ((N j k * M i j) + (O j k * M i j)) ≈⟨ ∑-distrib-+ (λ j → N j k * M i j) (λ j → O j k * M i j) ⟩
  ((N *M M) +M (O *M M)) i k ∎
  where open Setoid-Reasoning setoid

*M-zeroˡ : ∀ {m n o} (M : Matrix m n) → (0M {n} {o} *M M) ≋ 0M
*M-zeroˡ {n = n} M i k = begin
  (0M *M M) i k ≈⟨ sum-cong-≋ (λ j → zeroˡ (M i j)) ⟩
  ∑[ j < n ] 0# ≈⟨ sum-replicate-zero n ⟩
  0M i k ∎
  where open Setoid-Reasoning setoid

*M-zeroʳ : ∀ {m n o} (M : Matrix n o) → (M *M 0M {m} {n}) ≋ 0M
*M-zeroʳ {n = n} M i k = begin
  (M *M 0M) i k ≈⟨ sum-cong-≋ (λ j → zeroʳ (M j k)) ⟩
  ∑[ j < n ] 0# ≈⟨ sum-replicate-zero n ⟩
  0M i k ∎
  where open Setoid-Reasoning setoid
