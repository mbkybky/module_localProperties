/-
Copyright (c) 2024 Yi Song. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yi Song, Yongle Hu, Sihan Su
-/
module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.Algebra.Module.LocalizedModule.Away
public import Mathlib.Algebra.Module.LocalizedModule.Submodule
public import Mathlib.RingTheory.Localization.Finiteness

open Submodule IsLocalizedModule LocalizedModule Ideal IsLocalization TensorProduct

public section

universe u v w t

variable {R : Type u} [CommRing R] {M : Type w} [AddCommGroup M] [Module R M] (s : Finset R)

lemma Submodule.of_localizationSpan_finite {N : Submodule R M}
    (spn : Ideal.span (s : Set R) = ⊤) (H : ∀ (g : s), (localized (Submonoid.powers g.1) N).FG) :
    N.FG := by
  apply Module.Finite.iff_fg.mp (Module.Finite.of_localizationSpan_finite s spn (fun g ↦ ?_))
  have := Module.Finite.iff_fg.mpr (H g)
  exact Module.Finite.equiv (N.localizedEquiv _)

theorem Module.FinitePresentation.of_localizationSpan_finite' (s : Finset R)
    (spn : Ideal.span (s : Set R) = ⊤)
    {Mₚ : ∀ (_ : s), Type*} [∀ (g : s), AddCommMonoid (Mₚ g)] [∀ (g : s), Module R (Mₚ g)]
    {Rₚ : ∀ (_ : s), Type u} [∀ (g : s), CommRing (Rₚ g)] [∀ (g : s), Algebra R (Rₚ g)]
    [∀ (g : s), IsLocalization.Away g.val (Rₚ g)]
    [∀ (g : s), Module (Rₚ g) (Mₚ g)] [∀ (g : s), IsScalarTower R (Rₚ g) (Mₚ g)]
    (ϕ : ∀ (g : s), M →ₗ[R] Mₚ g) [∀ (g : s), IsLocalizedModule (Submonoid.powers g.val) (ϕ g)]
    (H : ∀ (g : s), Module.FinitePresentation (Rₚ g) (Mₚ g)) :
    Module.FinitePresentation R M := by
  letI : Module.Finite R M :=
    Module.Finite.of_localizationSpan_finite' (Rₚ := Rₚ) s spn ϕ (fun g ↦ inferInstance)
  obtain ⟨n, f, fsur⟩ := Module.Finite.exists_fin' R M
  rw [← Module.FinitePresentation.fg_ker_iff f fsur]
  refine f.ker.of_localizationSpan_finite s spn (fun g => ?_)
  set f' := IsLocalizedModule.mapExtendScalars
    (Submonoid.powers g.1) (TensorProduct.mk R (Rₚ g) (Fin n → R) 1) (ϕ g) (Rₚ g) f
  sorry

lemma Module.FinitePresentation.of_localizationSpan_finite (spn : span (s : Set R) = ⊤)
    (h : ∀ r : s, Module.FinitePresentation (Localization.Away r.1) (LocalizedModule.Away r.1 M)) :
      Module.FinitePresentation R M := by
  have : Module.Finite R M := Module.Finite.of_localizationSpan_finite s spn (fun _ ↦ inferInstance)
  obtain ⟨n, f, fsur⟩ := Module.Finite.exists_fin' R M
  rw [← Module.FinitePresentation.fg_ker_iff f fsur]
  refine f.ker.of_localizationSpan_finite s spn (fun g => ?_)
  set f' := map (Submonoid.powers g.1) f
  have : Module.Finite (Localization.Away g.1) (LocalizedModule (Submonoid.powers g.1) (Fin n → R))
    := Module.Finite.of_isLocalizedModule (Submonoid.powers g.1) (mkLinearMap _ (Fin n → R))
  have h : localized (Submonoid.powers g.1) f.ker = f'.ker :=
    LinearMap.localized'_ker_eq_ker_localizedMap _ _ _ _ f
  rw [h]
  apply Module.FinitePresentation.fg_ker f'
  have h : (localized (Submonoid.powers g.1) f.range) = f'.range :=
    LinearMap.localized'_range_eq_range_localizedMap _ _ _ _ f
  rw [← LinearMap.range_eq_top, ← h, LinearMap.range_eq_top.mpr fsur]
  ext
  exact ⟨by simp, fun _ ↦ by simp⟩
/-
theorem Module.FinitePresentation.of_localizationSpan_finite' (spn : Ideal.span (s : Set R) = ⊤)
    {Mₚ : ∀ (_ : s), Type*} [∀ (g : s), AddCommGroup (Mₚ g)] [∀ (g : s), Module R (Mₚ g)]
    {Rₚ : ∀ (_ : s), Type u} [∀ (g : s), CommRing (Rₚ g)] [∀ (g : s), Algebra R (Rₚ g)]
    [∀ (g : s), IsLocalization.Away g.val (Rₚ g)]
    [∀ (g : s), Module (Rₚ g) (Mₚ g)] [∀ (g : s), IsScalarTower R (Rₚ g) (Mₚ g)]
    (f : ∀ (g : s), M →ₗ[R] Mₚ g) [∀ (g : s), IsLocalizedModule (Submonoid.powers g.val) (f g)]
    (H : ∀ (g : s), Module.FinitePresentation (Rₚ g) (Mₚ g)) :
    Module.FinitePresentation R M := by
  refine of_localizationSpan_finite s spn (fun g ↦ ?_)
  have := H g
  apply Module.FinitePresentation.of_equiv (M := Mₚ g)
 -/
lemma isNoetherian_of_localization_finitespan {R M : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] (s : Finset R) (spn : span (s : Set R) = ⊤)
    (h : ∀ r : s, IsNoetherian (Localization.Away r.1) (LocalizedModule.Away r.1 M)) :
    IsNoetherian R M :=
  isNoetherian_def.mpr <| fun _ => Submodule.of_localizationSpan_finite s spn <|
  fun r => isNoetherian_def.mp (h r) <| _

lemma isNoetherianRing_of_localization_finitespan {R : Type*} [CommRing R](s : Finset R)
    (spn : span (s : Set R) = ⊤) (h : ∀ r : s, IsNoetherianRing (Localization.Away r.1)) :
    IsNoetherianRing R :=
  (isNoetherianRing_iff_ideal_fg _).mpr <| fun _ => Ideal.fg_of_localizationSpan _ spn <|
    fun r => (isNoetherianRing_iff_ideal_fg _).mp (h r) <| _

namespace Submodule

variable {R M S_M : Type*} (S_R : Type*) [CommRing R] [CommRing S_R] [Algebra R S_R]
    [AddCommGroup M] [Module R M] [AddCommGroup S_M] [Module R S_M] [Module S_R S_M]
    [IsScalarTower R S_R S_M]
    (S : Submonoid R) [IsLocalization S S_R]
    (f : M →ₗ[R] S_M) [IsLocalizedModule S f]
    {p q : Submodule R M}

lemma localized'_of_finite (h : p.FG) : (localized' S_R S f p).FG := by
  rw [fg_def] at h ⊢
  rcases h with ⟨s, hfin, hspan⟩
  use f '' s
  constructor
  · exact Set.Finite.image f hfin
  · rw [← hspan, localized'_span]

lemma localized_of_finite (h : p.FG) : (localized S p).FG := localized'_of_finite _ _ _ h

end Submodule
