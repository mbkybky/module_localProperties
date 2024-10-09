/-
Copyright (c) 2024 Sihan Su. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SiHan Su
-/
import Mathlib.RingTheory.Flat.Basic
import Mathlib.Algebra.Module.Submodule.Localization

import ModuleLocalProperties.MissingLemmas.LocalizedModule
import ModuleLocalProperties.MissingLemmas.Submodule
import ModuleLocalProperties.MissingLemmas.FlatIff
import ModuleLocalProperties.MissingLemmas.TensorProduct
import ModuleLocalProperties.Basic

open Submodule IsLocalizedModule LocalizedModule Ideal IsLocalization LinearMap

lemma inj_of_local {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] (f : M →ₗ[R] N) (h : ∀ (J : Ideal R) (hJ : J.IsMaximal), Function.Injective (map' J.primeCompl f)) : Function.Injective f := by
  simp only [← ker_eq_bot] at h ⊢
  exact submodule_eq_bot_of_localization _ fun J hJ ↦ (localized'_ker_eq_ker_localizedMap _ _ _ _ f).trans (h J hJ)

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

lemma LocalizedModule.map_mk {N :Type*} [AddCommGroup N] [Module R N] (S : Submonoid R) (f : N →ₗ[R] M) (n : N) (s : S): (((map' S) f) (mk n s)) = mk (f n) s := by
  unfold map' LocalizedModule.map
  simp only [LinearMap.coe_mk, AddHom.coe_mk, extendScalarsOfIsLocalization_apply', mk_eq_mk', IsLocalizedModule.map_mk']

theorem Flat_of_localization (h : ∀ (J : Ideal R) (hJ : J.IsMaximal), Module.Flat (Localization.AtPrime J)
    (LocalizedModule.AtPrime J M)) : Module.Flat R M := by
  apply (Module.Flat.iff_rTensor_preserves_injective_linearMap' R M).mpr
  intro N N' _ _ _ _ f finj
  apply inj_of_local
  intro J hJ
  have inj : Function.Injective (map' J.primeCompl f) := by
    unfold map' LocalizedModule.map
    rw [← ker_eq_bot, LinearMap.coe_mk, AddHom.coe_mk, ← localized'_ker_eq_ker_localizedMap, ker_eq_bot.mpr finj, localized'_bot]
  set g1 := (rTensor (LocalizedModule.AtPrime J M) ((map' J.primeCompl) f))
  set g2 := ((map' J.primeCompl) (rTensor M f))
  have : (Eqv N' M J.primeCompl) ∘ₗ g1 = g2 ∘ₗ (Eqv N M J.primeCompl) := by
    apply TensorProduct.ext'
    intro x y
    unfold_let
    unfold Eqv Map BiMap
    simp only [LinearEquiv.ofLinear_toLinearMap, coe_comp, Function.comp_apply,
      rTensor_tmul, TensorProduct.lift.tmul, LinearMap.coe_mk, AddHom.coe_mk]
    obtain ⟨n, sn, eqx⟩ : ∃ n : N, ∃ sn : J.primeCompl, mk n sn = x := ⟨(Quotient.out x).1, (Quotient.out x).2, (Quotient.out_eq _)⟩
    obtain ⟨m, sm, eqy⟩ : ∃ m : M, ∃ sm : J.primeCompl, mk m sm = y := ⟨(Quotient.out y).1, (Quotient.out y).2, (Quotient.out_eq _)⟩
    rw [← eqx, ← eqy, map_mk]
    unfold Map1 LocalizedMapLift
    simp only [map_mk, LiftOnLocalization_mk, smul_apply, TensorProduct.mk_apply, mk_smul_mk, one_smul, rTensor_tmul]
  have inj : Function.Injective ((Eqv N' M J.primeCompl).toLinearMap ∘ₗ g1) := by
    simp only [coe_comp, LinearEquiv.coe_coe, EmbeddingLike.comp_injective]
    exact ((Module.Flat.iff_rTensor_preserves_injective_linearMap' _ _).mp (h J hJ) (map' J.primeCompl f) inj)
  rw [this] at inj
  simp only [coe_comp, LinearEquiv.coe_coe, EquivLike.injective_comp] at inj
  exact inj
