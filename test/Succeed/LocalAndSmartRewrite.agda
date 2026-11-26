{-# OPTIONS --local-rewriting --smart-with #-}

open import Agda.Builtin.Equality
import Agda.Builtin.Equality.Rewrite

record PreSemigroup : Set₁ where
  field
    El  : Set
    _◆_ : El → El → El

module _ (S : PreSemigroup) (let module S = PreSemigroup S)
         (@rewrite eq : ∀ {x y z} → (x S.◆ y) S.◆ z ≡ x S.◆ (y S.◆ z))
         where

  record Semigroupᴰ : Set₁ where
    field
      Elᴰ : S.El → Set
      _◆ᴰ_ : ∀ {x y} → Elᴰ x → Elᴰ y → Elᴰ (x S.◆ y)
      ◆◆ᴰ : ∀ {x y z} (xᴰ : Elᴰ x) (yᴰ : Elᴰ y) (zᴰ : Elᴰ z)
          → (xᴰ ◆ᴰ yᴰ) ◆ᴰ zᴰ ≡ xᴰ ◆ᴰ (yᴰ ◆ᴰ zᴰ)
  open Semigroupᴰ

  module _ (Sᴰ : Semigroupᴰ) (let module Sᴰ = Semigroupᴰ Sᴰ) where
    ◆◆◆ᴰ : ∀ {x y z w}
             (xᴰ : Sᴰ.Elᴰ x) (yᴰ : Sᴰ.Elᴰ y) (zᴰ : Sᴰ.Elᴰ z) (wᴰ : Sᴰ.Elᴰ w)
        → ((xᴰ Sᴰ.◆ᴰ yᴰ) Sᴰ.◆ᴰ zᴰ) Sᴰ.◆ᴰ wᴰ ≡ xᴰ Sᴰ.◆ᴰ (yᴰ Sᴰ.◆ᴰ (zᴰ Sᴰ.◆ᴰ wᴰ))
    ◆◆◆ᴰ xᴰ yᴰ zᴰ wᴰ
      rewrite Sᴰ.◆◆ᴰ xᴰ yᴰ (zᴰ Sᴰ.◆ᴰ wᴰ)
      rewrite Sᴰ.◆◆ᴰ (xᴰ Sᴰ.◆ᴰ yᴰ) zᴰ wᴰ
      = refl
