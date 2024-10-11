/-
Copyright (c) 2024 Sihan Su. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SiHan Su
-/
import Mathlib.RingTheory.Flat.Basic
import Mathlib.Algebra.Module.Submodule.Localization
import Mathlib.RingTheory.Localization.BaseChange

import ModuleLocalProperties.MissingLemmas.LocalizedModule
import ModuleLocalProperties.MissingLemmas.Submodule
import ModuleLocalProperties.MissingLemmas.FlatIff
import ModuleLocalProperties.MissingLemmas.TensorProduct
import ModuleLocalProperties.Basic

open Submodule IsLocalizedModule LocalizedModule Ideal IsLocalization LinearMap

lemma inj_of_local {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] (f : M →ₗ[R] N) (h : ∀ (J : Ideal R) (hJ : J.IsMaximal), Function.Injective (map' J.primeCompl f)) : Function.Injective f := by
  simp only [← ker_eq_bot] at h ⊢
  exact submodule_eq_bot_of_localization _ fun J hJ ↦ (localized'_ker_eq_ker_localizedMap _ _ _ _ f).trans (h J hJ)

section Tensor
open TensorProduct IsBaseChange LinearEquiv

variable {R : Type*} (M N : Type*) [CommRing R] (S : Submonoid R) [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

lemma LocalizedModule.map'_mk {N :Type*} [AddCommGroup N] [Module R N] (S : Submonoid R) (f : N →ₗ[R] M) (n : N) (s : S): (((map' S) f) (mk n s)) = mk (f n) s := by
  unfold map' LocalizedModule.map
  simp only [LinearMap.coe_mk, AddHom.coe_mk, extendScalarsOfIsLocalization_apply', mk_eq_mk', IsLocalizedModule.map_mk']

noncomputable def tensor_eqv_local : Localization S ⊗[R] M ≃ₗ[Localization S] LocalizedModule S M
  := (IsLocalizedModule.isBaseChange S (Localization S) (mkLinearMap S M)).equiv

noncomputable def eqv1 :=(TensorProduct.assoc R (Localization S) M N) ≪≫ₗ ((tensor_eqv_local (M ⊗[R] N) S).restrictScalars R)

noncomputable def eqv2 := TensorProduct.congr ((TensorProduct.rid (Localization S) (Localization S ⊗[R] M)).restrictScalars R) (refl R N)

noncomputable def eqv3 := (AlgebraTensorModule.assoc R (Localization S) (Localization S) (Localization S ⊗[R] M) (Localization S) N).symm

noncomputable def eqv4 := TensorProduct.congr (tensor_eqv_local M S).symm (tensor_eqv_local N S).symm

noncomputable def eqv' := ((eqv4 M N S).restrictScalars R) ≪≫ₗ (((eqv3 M N S).restrictScalars R) ≪≫ₗ ((eqv2 M N S) ≪≫ₗ (eqv1 M N S)))

noncomputable def lmap := (eqv' M N S).extendScalarsOfIsLocalization S (Localization S)

noncomputable def rmap := (eqv' M N S).symm.extendScalarsOfIsLocalization S (Localization S)

noncomputable def eqv := ofLinear (lmap M N S) (rmap M N S) (re₂₁ := RingHomInvPair.ids) (re₁₂ := RingHomInvPair.ids) (by unfold lmap rmap; ext x; simp) (by unfold lmap rmap; ext x; simp)

lemma tensor_eqv_local_apply (m : M) (sm : S) : (tensor_eqv_local M S) (Localization.mk 1 sm ⊗ₜ[R] m) = (LocalizedModule.mk m sm) := by rw [tensor_eqv_local, equiv_tmul, mkLinearMap_apply, mk_smul_mk, mul_one, one_smul]

lemma tensor_eqv_local_symm_apply (m : M) (sm : S) : (tensor_eqv_local M S).symm (LocalizedModule.mk m sm) = Localization.mk 1 sm ⊗ₜ[R] m := (symm_apply_eq _).mpr <| (tensor_eqv_local_apply _ _ _ _).symm

lemma eqv'_mk_apply (m : M) (n : N) : (eqv' M N S) (mk m sm ⊗ₜ[Localization S] mk n sn) = mk (m ⊗ₜ[R] n) (sm * sn) := by
  unfold eqv'
  simp only [trans_apply, LinearEquiv.restrictScalars_apply, eqv4, congr_tmul, tensor_eqv_local_symm_apply, eqv3, AlgebraTensorModule.assoc_symm_tmul, eqv2, refl_apply, rid_tmul, eqv1, smul_tmul', assoc_tmul, smul_eq_mul, Localization.mk_mul, one_mul, mul_comm, tensor_eqv_local_apply]

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
  have : (eqv N' M J.primeCompl) ∘ₗ g1 = g2 ∘ₗ (eqv N M J.primeCompl) := by
    apply TensorProduct.ext'
    intro x y
    unfold_let
    unfold eqv lmap
    simp only [ofLinear_toLinearMap, coe_comp, Function.comp_apply, LinearMap.rTensor_tmul,
      extendScalarsOfIsLocalization_apply', LinearEquiv.coe_coe]
    obtain ⟨n, sn, eqx⟩ : ∃ n : N, ∃ sn : J.primeCompl, mk n sn = x := ⟨(Quotient.out x).1, (Quotient.out x).2, (Quotient.out_eq _)⟩
    obtain ⟨m, sm, eqy⟩ : ∃ m : M, ∃ sm : J.primeCompl, mk m sm = y := ⟨(Quotient.out y).1, (Quotient.out y).2, (Quotient.out_eq _)⟩
    simp only [← eqx, ← eqy, map'_mk, eqv'_mk_apply, LinearMap.rTensor_tmul]
  have inj : Function.Injective ((eqv N' M J.primeCompl).toLinearMap ∘ₗ g1) := by
    simp only [coe_comp, LinearEquiv.coe_coe, EmbeddingLike.comp_injective]
    exact ((Module.Flat.iff_rTensor_preserves_injective_linearMap' _ _).mp (h J hJ) (map' J.primeCompl f) inj)
  rw [this] at inj
  simp only [coe_comp, LinearEquiv.coe_coe, EquivLike.injective_comp] at inj
  exact inj

end Tensor

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

theorem Flat_of_localization' (h : ∀ (J : Ideal R) (hJ : J.IsMaximal), Module.Flat (Localization.AtPrime J)
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
    rw [← eqx, ← eqy, map'_mk]
    unfold Map1 LocalizedMapLift
    simp only [map'_mk, LiftOnLocalization_mk, smul_apply, TensorProduct.mk_apply, mk_smul_mk, one_smul, rTensor_tmul]
  have inj : Function.Injective ((Eqv N' M J.primeCompl).toLinearMap ∘ₗ g1) := by
    simp only [coe_comp, LinearEquiv.coe_coe, EmbeddingLike.comp_injective]
    exact ((Module.Flat.iff_rTensor_preserves_injective_linearMap' _ _).mp (h J hJ) (map' J.primeCompl f) inj)
  rw [this] at inj
  simp only [coe_comp, LinearEquiv.coe_coe, EquivLike.injective_comp] at inj
  exact inj
