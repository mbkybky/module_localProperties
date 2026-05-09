/-
Copyright (c) 2024 Sihan Su. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sihan Su, Yongle Hu, Yi Song
-/
module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.Algebra.Module.LocalizedModule.Away
public import Mathlib.Algebra.Module.LocalizedModule.Submodule
public import Mathlib.RingTheory.Localization.Finiteness

open Submodule IsLocalizedModule LocalizedModule Ideal IsLocalization TensorProduct

public section

universe u v

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M] (s : Finset R)

lemma Submodule.of_localizationSpan_finite' {N : Submodule R M} (hs : Ideal.span (s : Set R) = ⊤)
    {Mₚ : ∀ (_ : s), Type*} [∀ (g : s), AddCommMonoid (Mₚ g)] [∀ (g : s), Module R (Mₚ g)]
    {Rₚ : ∀ (_ : s), Type u} [∀ (g : s), CommRing (Rₚ g)] [∀ (g : s), Algebra R (Rₚ g)]
    [∀ (g : s), IsLocalization.Away g.val (Rₚ g)]
    [∀ (g : s), Module (Rₚ g) (Mₚ g)] [∀ (g : s), IsScalarTower R (Rₚ g) (Mₚ g)]
    (ϕ : ∀ (g : s), M →ₗ[R] Mₚ g) [∀ (g : s), IsLocalizedModule (Submonoid.powers g.val) (ϕ g)]
    (H : ∀ (g : s), (N.localized' (Rₚ g) (Submonoid.powers g.1) (ϕ g)).FG) :
    N.FG := by
  simp [← Module.Finite.iff_fg, Module.Finite.of_localizationSpan_finite' s hs
    (fun g ↦ N.toLocalized' (Rₚ g) (Submonoid.powers g.1) (ϕ g))
    (fun g ↦ Module.Finite.iff_fg.mpr (H g))]

lemma Submodule.of_localizationSpan_finite {N : Submodule R M}
    (hs : Ideal.span (s : Set R) = ⊤) (H : ∀ (g : s), (localized (Submonoid.powers g.1) N).FG) :
    N.FG :=
  N.of_localizationSpan_finite' s hs (Rₚ := fun g ↦ Localization (Submonoid.powers g.1))
    (fun g ↦ LocalizedModule.mkLinearMap (Submonoid.powers g.1) M)
    (fun g ↦ by simp_all only [Subtype.forall])

theorem Module.FinitePresentation.of_localizationSpan_finite' (hs : Ideal.span (s : Set R) = ⊤)
    {Mₚ : ∀ (_ : s), Type*} [∀ (g : s), AddCommGroup (Mₚ g)] [∀ (g : s), Module R (Mₚ g)]
    {Rₚ : ∀ (_ : s), Type u} [∀ (g : s), CommRing (Rₚ g)] [∀ (g : s), Algebra R (Rₚ g)]
    [∀ (g : s), IsLocalization.Away g.val (Rₚ g)]
    [∀ (g : s), Module (Rₚ g) (Mₚ g)] [∀ (g : s), IsScalarTower R (Rₚ g) (Mₚ g)]
    (ϕ : ∀ (g : s), M →ₗ[R] Mₚ g) [∀ (g : s), IsLocalizedModule (Submonoid.powers g.val) (ϕ g)]
    (h : ∀ (g : s), Module.FinitePresentation (Rₚ g) (Mₚ g)) :
    Module.FinitePresentation R M := by
  have : Module.Finite R M :=
    Module.Finite.of_localizationSpan_finite' (Rₚ := Rₚ) s hs ϕ (fun g ↦ inferInstance)
  obtain ⟨n, f, fsurj⟩ := Module.Finite.exists_fin' R M
  rw [← Module.FinitePresentation.fg_ker_iff f fsurj]
  refine f.ker.of_localizationSpan_finite' s hs (Rₚ := Rₚ)
    (fun g ↦ TensorProduct.mk R (Rₚ g) (Fin n → R) 1) (fun g ↦ ?_)
  rw [LinearMap.localized'_ker_eq_ker_localizedMap (Rₚ g) (Submonoid.powers g.1) _ (ϕ g) f]
  apply Module.FinitePresentation.fg_ker
  rw [← LinearMap.range_eq_top] at fsurj ⊢
  simp [← LinearMap.localized'_range_eq_range_localizedMap (Rₚ g), fsurj]

lemma Module.FinitePresentation.of_localizationSpan_finite (hs : span (s : Set R) = ⊤)
    (h : ∀ g : s, Module.FinitePresentation (Localization.Away g.1) (LocalizedModule.Away g.1 M)) :
      Module.FinitePresentation R M :=
  of_localizationSpan_finite' s hs (fun g ↦ LocalizedModule.mkLinearMap (Submonoid.powers g.1) M) h

lemma IsNoetherian.of_localization_finitespan (hs : span (s : Set R) = ⊤)
    (h : ∀ g : s, IsNoetherian (Localization.Away g.1) (LocalizedModule.Away g.1 M)) :
    IsNoetherian R M :=
  ⟨fun _ ↦ Submodule.of_localizationSpan_finite s hs <| fun g ↦ (h g).noetherian _⟩

lemma IsNoetherianRing.of_localization_finitespan
    (hs : span (s : Set R) = ⊤) (h : ∀ g : s, IsNoetherianRing (Localization.Away g.1)) :
    IsNoetherianRing R :=
  ⟨fun _ ↦ Ideal.fg_of_localizationSpan _ hs <| fun g ↦ (h g).noetherian _⟩

namespace Submodule

variable {R M M' : Type*} (R' : Type*) [CommRing R] [CommRing R'] [Algebra R R']
    [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M'] [Module R' M']
    [IsScalarTower R R' M']
    (S : Submonoid R) [IsLocalization S R']
    (f : M →ₗ[R] M') [IsLocalizedModule S f]
    {p q : Submodule R M}

lemma localized'_of_finite (h : p.FG) : (localized' R' S f p).FG := by
  rw [fg_def] at h ⊢
  rcases h with ⟨s, hfin, hspan⟩
  exact ⟨f '' s, Set.Finite.image f hfin, by rw [← hspan, localized'_span]⟩

lemma localized_of_finite (h : p.FG) : (localized S p).FG := localized'_of_finite _ _ _ h

end Submodule
