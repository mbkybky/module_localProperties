/-
Copyright (c) 2024 Yi Song. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yi Song, Yongle Hu, Sihan Su
-/
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.RingTheory.Localization.Finiteness
import Mathlib.RingTheory.Localization.Away.AdjoinRoot
import Mathlib.Algebra.Module.LocalizedModule

import ModuleLocalProperties.Basic

open Submodule IsLocalizedModule LocalizedModule Ideal IsLocalization

noncomputable def LinearEquiv.extendScalarsOfIsLocalization {R M N : Type*} [CommSemiring R]
    (S : Submonoid R) (A : Type*) [CommSemiring A] [Algebra R A] [IsLocalization S A]
    [AddCommMonoid M] [Module R M] [Module A M] [IsScalarTower R A M] [AddCommMonoid N]
    [Module R N] [Module A N] [IsScalarTower R A N] (f : M ≃ₗ[R] N) : M ≃ₗ[A] N :=
  LinearEquiv.ofBijective (f.toLinearMap.extendScalarsOfIsLocalization S A)
  (Function.bijective_iff_has_inverse.mpr ⟨f.symm, Function.leftInverse_iff_comp.mpr
  ((symm_comp_eq id f).mpr rfl), Function.rightInverse_iff_comp.mpr ((comp_symm_eq id f).mpr rfl)⟩)

noncomputable def submodule_localization_equiv {R M : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] (N : Submodule R M) (S : Submonoid R) :
    (localized S N) ≃ₗ[Localization S] LocalizedModule S N :=
  (iso S (Submodule.toLocalized S N)).symm.extendScalarsOfIsLocalization S (Localization S)

lemma submodule.of_localizationSpan_finite {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (N : Submodule R M) (s : Finset R) (spn : span (s : Set R) = ⊤)
    (H : ∀ (g : s), (localized (Submonoid.powers g.1) N).FG) : N.FG := by
  apply Module.Finite.iff_fg.mp (Module.Finite.of_localizationSpan_finite s spn ?_)
  intro g
  letI := Module.Finite.iff_fg.mpr (H g)
  exact Module.Finite.equiv (submodule_localization_equiv N _)

lemma finitepresented_of_localization_fintespan {R M : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] (s : Finset R) (spn : span (s : Set R) = ⊤) (h : ∀ r : s,
    Module.FinitePresentation (Localization.Away r.1) (LocalizedModule.Away r.1 M)) :
      Module.FinitePresentation R M := by
  letI : Module.Finite R M := Module.Finite.of_localizationSpan_finite s spn
    (fun g ↦ instFiniteOfFinitePresentation _ _)
  obtain ⟨n, f, fsur⟩ := Module.Finite.exists_fin' R M
  apply (Module.FinitePresentation.fg_ker_iff f fsur).mp
  letI : Module R (LinearMap.ker f) := by exact (LinearMap.ker f).module'
  apply submodule.of_localizationSpan_finite (LinearMap.ker f) s spn
  intro g
  set f' := (map (Submonoid.powers g.1) _ _ f).extendScalarsOfIsLocalization
    (Submonoid.powers g.1) (Localization.Away g.1)
  have : (localized (Submonoid.powers g.1) (LinearMap.ker f)) =
    LinearMap.ker f' := LinearMap.localized'_ker_eq_ker_localizedMap _ _ _ _ _
  rw [this]
  have : Module.Finite (Localization.Away g.1) (LocalizedModule (Submonoid.powers g.1) (Fin n → R))
    := Module.Finite.of_isLocalizedModule (Submonoid.powers g.1) (mkLinearMap _ (Fin n → R))
  apply Module.FinitePresentation.fg_ker f' (LinearMap.range_eq_top.mp ?_)
  have : (localized (Submonoid.powers g.1) (LinearMap.range f)) = LinearMap.range f'
    := LinearMap.localized'_range_eq_range_localizedMap _ _ _ _
  rw [← this, LinearMap.range_eq_top.mpr fsur]
  ext x
  have : ∃ m : M, ∃ s : (Submonoid.powers g.1), LocalizedModule.mk m s = x :=
    ⟨(Quotient.out x).1, (Quotient.out x).2, (Quotient.out_eq _)⟩
  obtain ⟨m, s, eq⟩ := this
  exact ⟨by simp, fun _ ↦ (mem_localized' (Localization _) _ (mkLinearMap _ M) ⊤ x).mpr
    ⟨m, trivial, s, by rw [← eq, (mk_eq_mk' s m)]⟩⟩

lemma isNoetherian_of_localization_finitespan {R M : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] (s : Finset R) (spn : span (s : Set R) = ⊤) (h : ∀ r : s,
    IsNoetherian (Localization.Away r.1) (LocalizedModule.Away r.1 M)) : IsNoetherian R M :=
  isNoetherian_def.mpr <| fun _ => submodule.of_localizationSpan_finite _ _ spn <|
  fun r => isNoetherian_def.mp (h r) <| _

lemma isNoetherianRing_of_localization_finitespan {R : Type*} [CommRing R](s : Finset R)
    (spn : span (s : Set R) = ⊤) (h : ∀ r : s, IsNoetherianRing (Localization.Away r.1)) :
    IsNoetherianRing R :=
  (isNoetherianRing_iff_ideal_fg _).mpr <| fun _ => Ideal.fg_of_localizationSpan _ spn <|
  fun r => (isNoetherianRing_iff_ideal_fg _).mp (h r) <| _
