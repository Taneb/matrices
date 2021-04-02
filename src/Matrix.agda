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
open import Data.Vec.Base
open import Data.Vec.Properties
open import Data.Vec.Relation.Binary.Pointwise.Extensional as PW using (Pointwise)
import Data.Vec.Relation.Binary.Pointwise.Extensional.Extra as PW
open import Function.Base using (_∘_)
open import Level
open import Relation.Nullary
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)
import Relation.Binary.Reasoning.Setoid as Setoid-Reasoning

Matrix : ℕ → ℕ → Set c
Matrix m n = Vec (Vec R n) m

_≋_ : ∀ {m n} → Rel (Matrix m n) (c ⊔ ℓ)
_≋_ = Pointwise (Pointwise _≈_)

≋-isEquivalence : ∀ {m n} → IsEquivalence (_≋_ {m} {n})
≋-isEquivalence = PW.isEquivalence (PW.isEquivalence isEquivalence)

0M : ∀ {m n} → Matrix m n
0M = replicate (replicate 0#)

1M : ∀ {m} → Matrix m m
1M = tabulate λ j → tabulate λ k → if does (j ≟ k) then 1# else 0#

-- Addition
------------------------------------------------------------------------

_+M_ : ∀ {m n} → Op₂ (Matrix m n)
_+M_ = zipWith (zipWith _+_)

module _ {m n} where
  open Algebra.Definitions (_≋_ {m} {n})
  open Algebra.Structures (_≋_ {m} {n})

  +M-cong : Congruent₂ _+M_
  +M-cong = PW.zipWith-cong₂ (PW.zipWith-cong₂ +-cong)

  +M-assoc : Associative _+M_
  +M-assoc = PW.zipWith-assoc (PW.zipWith-assoc +-assoc)

  +M-comm : Commutative _+M_
  +M-comm = PW.zipWith-comm (PW.zipWith-comm +-comm)

  +M-identityˡ : LeftIdentity 0M _+M_
  +M-identityˡ = PW.zipWith-identityˡ (PW.zipWith-identityˡ +-identityˡ)

  +M-identityʳ : RightIdentity 0M _+M_
  +M-identityʳ = PW.zipWith-identityʳ (PW.zipWith-identityʳ +-identityʳ)

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

  +M-magma : Magma c (c ⊔ ℓ)
  +M-magma = record { isMagma = +M-isMagma }

  +M-semigroup : Semigroup c (c ⊔ ℓ)
  +M-semigroup = record { isSemigroup = +M-isSemigroup }

  +M-commutativeSemigroup : CommutativeSemigroup c (c ⊔ ℓ)
  +M-commutativeSemigroup = record { isCommutativeSemigroup = +M-isCommutativeSemigroup }

  +M-0M-monoid : Monoid c (c ⊔ ℓ)
  +M-0M-monoid = record { isMonoid = +M-0M-isMonoid }

  +M-0M-commutativeMonoid : Monoid c (c ⊔ ℓ)
  +M-0M-commutativeMonoid = record { isMonoid = +M-0M-isMonoid }

-- Multiplication
------------------------------------------------------------------------

-- NOTE: this uses the obvious O(n³) algorithm
-- Faster algorithms generally don't work on arbitrary semirings
_*M_ : ∀ {m n o} → Matrix n o → Matrix m n → Matrix m o
M *M N = tabulate λ i → tabulate λ k → ∑[ j < _ ] (lookup (lookup M j) k * lookup (lookup N i) j)

-- due to the dimension-changing nature of _*M_ we can't use the
-- standard type definitions in the Algebra heirarchy. I'm going to
-- use those names, but aim for types that would let me make this a
-- Category in the agda-categories library with minimal effort

lookup²∘tabulate² : ∀ {a} {A : Set a} {m n} (f : Fin m → Fin n → A) (i : Fin m) (j : Fin n) →
                    lookup (lookup (tabulate λ i′ → tabulate (f i′)) i) j ≡ f i j
lookup²∘tabulate² f i j = begin
  lookup (lookup (tabulate λ i′ → tabulate (f i′)) i) j ≡⟨ ≡.cong (λ m → lookup m j) (lookup∘tabulate (λ i′ → tabulate (f i′)) i) ⟩
  lookup (tabulate (f i)) j ≡⟨ lookup∘tabulate (f i) j ⟩
  f i j ∎
  where open ≡.≡-Reasoning

*M-cong : ∀ {n m o} {M M′ : Matrix m o} {N N′ : Matrix n m} → M ≋ M′ → N ≋ N′ → (M *M N) ≋ (M′ *M N′)
*M-cong {M = M} {M′} {N} {N′} M≋M′ N≋N′ = PW.ext λ x → PW.ext λ y → begin
  lookup (lookup (M *M N) x) y
    ≡⟨⟩
  lookup (lookup (tabulate λ i → tabulate λ k → ∑[ j < _ ] (lookup (lookup M j) k * lookup (lookup N i) j)) x) y
    ≡⟨ ≡.cong (λ m → lookup m y) (lookup∘tabulate _ x) ⟩
  lookup (tabulate λ k → ∑[ j < _ ] (lookup (lookup M j) k * lookup (lookup N x) j)) y
    ≡⟨ lookup∘tabulate _ y ⟩
  ∑[ j < _ ] (lookup (lookup M j) y * lookup (lookup N x) j)
    ≈⟨ sum-cong-≋ (λ j → *-cong (PW.Pointwise.app (PW.Pointwise.app M≋M′ j) y) (PW.Pointwise.app (PW.Pointwise.app N≋N′ x) j)) ⟩
  ∑[ j < _ ] (lookup (lookup M′ j) y * lookup (lookup N′ x) j)
    ≡˘⟨ lookup∘tabulate _ y ⟩
  lookup (tabulate λ k → ∑[ j < _ ] (lookup (lookup M′ j) k * lookup (lookup N′ x) j)) y
    ≡˘⟨ ≡.cong (λ m → lookup m y) (lookup∘tabulate _ x) ⟩
  lookup (lookup (tabulate λ i → tabulate λ k → ∑[ j < _ ] (lookup (lookup M′ j) k * lookup (lookup N′ i) j)) x) y
    ≡⟨⟩
  lookup (lookup (M′ *M N′) x) y ∎
  where open Setoid-Reasoning setoid

*M-assoc : ∀ {m n o p} (M : Matrix o p) (N : Matrix n o) (O : Matrix m n) → ((M *M N) *M O) ≋ (M *M (N *M O))
*M-assoc M N O = PW.ext λ x → PW.ext λ y → begin
  lookup (lookup ((M *M N) *M O) x) y ≡⟨⟩
  lookup (lookup (tabulate λ i → tabulate λ l → ∑[ j < _ ] (lookup (lookup (M *M N) j) l * lookup (lookup O i) j)) x) y ≡⟨ lookup²∘tabulate² _ x y ⟩
  ∑[ j < _ ] (lookup (lookup (M *M N) j) y * lookup (lookup O x) j) ≡⟨⟩
  ∑[ j < _ ] (lookup (lookup (tabulate λ a → tabulate λ b → ∑[ k < _ ] (lookup (lookup M k) b * lookup (lookup N a) k)) j) y * lookup (lookup O x) j) ≡⟨ sum-cong-≗ (λ j → ≡.cong (_* lookup (lookup O x) j) (lookup²∘tabulate² _ j y)) ⟩
  ∑[ j < _ ] (∑[ k < _ ] (lookup (lookup M k) y * lookup (lookup N j) k) * lookup (lookup O x) j) ≈⟨ (sum-cong-≋ (λ j → sum-distribʳ (lookup (lookup O x) j) λ k → lookup (lookup M k) y * lookup (lookup N j) k)) ⟩
  ∑[ j < _ ] ∑[ k < _ ] ((lookup (lookup M k) y * lookup (lookup N j) k) * lookup (lookup O x) j) ≈⟨ (sum-cong-≋ λ j → sum-cong-≋ λ k → *-assoc (lookup (lookup M k) y) (lookup (lookup N j) k) (lookup (lookup O x) j)) ⟩
  ∑[ j < _ ] ∑[ k < _ ] (lookup (lookup M k) y * (lookup (lookup N j) k * lookup (lookup O x) j)) ≈⟨ (∑-comm λ j k → lookup (lookup M k) y * (lookup (lookup N j) k * lookup (lookup O x) j)) ⟩
  ∑[ k < _ ] ∑[ j < _ ] (lookup (lookup M k) y * (lookup (lookup N j) k * lookup (lookup O x) j)) ≈˘⟨ (sum-cong-≋ λ k → sum-distribˡ (lookup (lookup M k) y) λ j → lookup (lookup N j) k * lookup (lookup O x) j) ⟩
  ∑[ k < _ ] (lookup (lookup M k) y * (∑[ j < _ ] (lookup (lookup N j) k *  lookup (lookup O x) j))) ≡˘⟨ (sum-cong-≗ λ k → ≡.cong (lookup (lookup M k) y *_) (lookup²∘tabulate² _ x k)) ⟩
  ∑[ k < _ ] (lookup (lookup M k) y * lookup (lookup (tabulate λ a → tabulate λ b → ∑[ j < _ ] (lookup (lookup N j) b * lookup (lookup O a) j)) x) k) ≡⟨⟩
  ∑[ k < _ ] (lookup (lookup M k) y * lookup (lookup (N *M O) x) k) ≡˘⟨ lookup²∘tabulate² _ x y ⟩
  lookup (lookup (tabulate λ i → tabulate λ l → ∑[ k < _ ] (lookup (lookup M k) l * lookup (lookup (N *M O) i) k)) x) y ≡⟨⟩
  lookup (lookup (M *M (N *M O)) x) y ∎
  where open Setoid-Reasoning setoid

private
  module _ where
    open Setoid-Reasoning setoid

    *M-identityˡ-lemma : ∀ {m} (M : Fin m → R) (y : Fin m) → ∑[ j < _ ] ((if does (j ≟ y) then 1# else 0#) * M j) ≈ M y
    *M-identityˡ-lemma {ℕ.suc m} M Fin.zero = begin
      ∑[ j < ℕ.suc m ] ((if does (j ≟ Fin.zero) then 1# else 0#) * M j) ≡⟨⟩
      1# * M Fin.zero + ∑[ j < m ] (0# * M (Fin.suc j)) ≈⟨ +-cong (*-identityˡ (M Fin.zero)) (trans (sum-cong-≋ λ j → zeroˡ (M (Fin.suc j))) (sum-replicate-zero m)) ⟩
      M Fin.zero + 0# ≈⟨ +-identityʳ (M Fin.zero) ⟩
      M Fin.zero ∎
    *M-identityˡ-lemma {ℕ.suc m} M (Fin.suc y) = begin
      ∑[ j < ℕ.suc m ] ((if does (j ≟ Fin.suc y) then 1# else 0#) * M j) ≡⟨⟩
      0# * M Fin.zero + ∑[ j < m ] ((if does (Fin.suc j ≟ Fin.suc y) then 1# else 0#) * M (Fin.suc j)) ≈⟨ +-cong (zeroˡ (M Fin.zero)) (*M-identityˡ-lemma (M ∘ Fin.suc) y) ⟩
      0# + M (Fin.suc y) ≈⟨ +-identityˡ (M (Fin.suc y)) ⟩
      M (Fin.suc y) ∎

    *M-identityʳ-lemma : ∀ {m} (M : Fin m → R) (x : Fin m) → ∑[ j < _ ] (M j * (if does (x ≟ j) then 1# else 0#)) ≈ M x
    *M-identityʳ-lemma {ℕ.suc m} M Fin.zero = begin
      ∑[ j < ℕ.suc m ] (M j * (if does (Fin.zero ≟ j) then 1# else 0#)) ≡⟨⟩
      M Fin.zero * 1# + ∑[ j < m ] (M (Fin.suc j) * 0#) ≈⟨ +-cong (*-identityʳ (M Fin.zero)) (trans (sum-cong-≋ λ j → zeroʳ (M (Fin.suc j))) (sum-replicate-zero m)) ⟩
      M Fin.zero + 0# ≈⟨ +-identityʳ (M Fin.zero) ⟩
      M Fin.zero ∎
    *M-identityʳ-lemma {ℕ.suc m} M (Fin.suc x) = begin
      ∑[ j < ℕ.suc m ] (M j * (if does (Fin.suc x ≟ j) then 1# else 0#)) ≡⟨⟩
      M Fin.zero * 0# + ∑[ j < m ] (M (Fin.suc j) * (if does (Fin.suc x ≟ Fin.suc j) then 1# else 0#)) ≈⟨ +-cong (zeroʳ (M Fin.zero)) (*M-identityʳ-lemma (M ∘ Fin.suc) x) ⟩
      0# + M (Fin.suc x) ≈⟨ +-identityˡ (M (Fin.suc x)) ⟩
      M (Fin.suc x) ∎

*M-identityˡ : ∀ {m n} (M : Matrix m n) → (1M *M M) ≋ M
*M-identityˡ M = PW.ext λ x → PW.ext λ y → begin
  lookup (lookup (1M *M M) x) y ≡⟨⟩
  lookup (lookup (tabulate λ i → tabulate λ k → ∑[ j < _ ] (lookup (lookup 1M j) k * lookup (lookup M i) j)) x) y ≡⟨ lookup²∘tabulate² _ x y ⟩
  ∑[ j < _ ] (lookup (lookup 1M j) y * lookup (lookup M x) j) ≡⟨⟩
  ∑[ j < _ ] (lookup (lookup (tabulate λ a → tabulate λ b → if does (a ≟ b) then 1# else 0#) j) y * lookup (lookup M x) j) ≡⟨ (sum-cong-≗ λ j → ≡.cong (_* lookup (lookup M x) j) (lookup²∘tabulate² _ j y)) ⟩
  ∑[ j < _ ] ((if does (j ≟ y) then 1# else 0#) * lookup (lookup M x) j) ≈⟨ *M-identityˡ-lemma (lookup (lookup M x)) y ⟩
  lookup (lookup M x) y ∎
  where open Setoid-Reasoning setoid

*M-identityʳ : ∀ {m n} (M : Matrix m n) → (M *M 1M) ≋ M
*M-identityʳ M = PW.ext λ x → PW.ext λ y → begin
  lookup (lookup (M *M 1M) x) y ≡⟨⟩
  lookup (lookup (tabulate λ i → tabulate λ k → ∑[ j < _ ] (lookup (lookup M j) k * lookup (lookup 1M i) j)) x) y ≡⟨ lookup²∘tabulate² _ x y ⟩
  ∑[ j < _ ] (lookup (lookup M j) y * lookup (lookup 1M x) j) ≡⟨⟩
  ∑[ j < _ ] (lookup (lookup M j) y * lookup (lookup (tabulate λ a → tabulate λ b → if does (a ≟ b) then 1# else 0#) x) j) ≡⟨ (sum-cong-≗ λ j → ≡.cong (lookup (lookup M j) y *_) (lookup²∘tabulate² _ x j)) ⟩
  ∑[ j < _ ] (lookup (lookup M j) y * (if does (x ≟ j) then 1# else 0#)) ≈⟨ *M-identityʳ-lemma (λ j → lookup (lookup M j) y) x ⟩
  lookup (lookup M x) y ∎
  where open Setoid-Reasoning setoid
