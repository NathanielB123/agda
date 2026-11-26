{-# OPTIONS --local-rewriting --smart-with --prop --show-irrelevant #-}

open import Agda.Builtin.Equality
import Agda.Builtin.Equality.Rewrite

infix 4 _≡ᴾ_
data _≡ᴾ_ {ℓ} {A : Set ℓ} (x : A) : A → Prop ℓ where
  refl : x ≡ᴾ x

postulate
  ↑≡ : ∀ {ℓ} {A : Set ℓ} (x y : A) → x ≡ᴾ y → x ≡ y

module _ (Ob : Set) (Hom : Ob → Ob → Set)
         (id : ∀ {x} → Hom x x)
         (_⨾_ : ∀ {x y z} → Hom y x → Hom z y → Hom z x)
 where

  record Psh : Set₁ where
    field
      El   : Ob → Set
      _⟨_⟩ : ∀ {W V} → El W → Hom V W → El V
      ⟨id⟩ : ∀ {W} x → x ⟨ id {W} ⟩ ≡ᴾ x

  module _ (Γ : Psh) (X : Set) (open Psh Γ) where
    ID : Psh
    ID .Psh.El   W   = El W
    ID .Psh._⟨_⟩ ρ φ
      = ρ ⟨ φ ⟩
    ID .Psh.⟨id⟩ ρ
      rewrite ↑≡ (ρ ⟨ id ⟩) ρ (⟨id⟩ ρ)
      = refl
