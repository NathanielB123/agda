{-# OPTIONS --local-rewriting --smart-with --show-implicit #-}

open import Agda.Builtin.Equality
import Agda.Builtin.Equality.Rewrite
open import Agda.Builtin.Sigma

module LocalAndSmartRewrite2 where

module _ (Ob : Set) (Hom : Ob → Ob → Set)
         (id : ∀ {x} → Hom x x)
         (_⨾_ : ∀ {x y z} → Hom y x → Hom z y → Hom z x)
         (@rewrite ⨾⨾  : ∀ {W V U T} {f : Hom V W} {g : Hom U V} {h : Hom T U}
                       → (f ⨾ g) ⨾ h ≡ f ⨾ (g ⨾ h))
  where

  variable
    W V U : Ob
    φ ψ : Hom _ _

  record Ctx : Set₁ where
    field
      El   : Ob → Set
      -- "Restriction"
      _⟨_⟩ : El W → Hom V W → El V
      -- Laws
      ⟨id⟩ : ∀ x → x ⟨ id {W} ⟩ ≡ x
  open Ctx

  module _ (Γ : Ctx)
           (Δ : Ctx)
           (let module Γ = Ctx Γ)
           (let module Δ = Ctx Δ) where
    _*_ : Ctx
    _*_ .El   W         = Σ (Γ.El W) λ _ → Δ.El W
    _*_ ._⟨_⟩ (ρ , γ) φ = (ρ Γ.⟨ φ ⟩ , γ Δ.⟨ φ ⟩)
    _*_ .⟨id⟩ (ρ , γ)
      rewrite Γ.⟨id⟩ ρ
      rewrite Δ.⟨id⟩ γ
      = refl
