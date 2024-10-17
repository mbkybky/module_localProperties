/-
Copyright (c) 2024 Sihan Su. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SiHan Su
-/
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Flat.Stability

import ModuleLocalProperties.MissingLemmas.FlatIff
import ModuleLocalProperties.Basic
import ModuleLocalProperties.Isom
import ModuleLocalProperties.SpanIsom

open Submodule IsLocalizedModule LocalizedModule Ideal IsLocalization LinearMap LinearEquiv TensorProduct

section Tensor
open IsBaseChange

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

lemma tensor_eqv_local_apply (m : M) (sm : S) (r : R) : (tensor_eqv_local M S) (Localization.mk r sm ⊗ₜ[R] m) = (LocalizedModule.mk (r • m) sm) := by rw [tensor_eqv_local, equiv_tmul, mkLinearMap_apply, mk_smul_mk, mul_one]

lemma tensor_eqv_local_symm_apply (m : M) (sm : S) : (tensor_eqv_local M S).symm (LocalizedModule.mk m sm) = Localization.mk 1 sm ⊗ₜ[R] m := (symm_apply_eq _).mpr <| by
  have := ((one_smul R m) ▸ (tensor_eqv_local_apply _ _ m sm 1).symm); exact this

lemma eqv'_mk_apply (m : M) (n : N) : (eqv' M N S) (mk m sm ⊗ₜ[Localization S] mk n sn) = mk (m ⊗ₜ[R] n) (sm * sn) := by
  unfold eqv'
  simp only [trans_apply, LinearEquiv.restrictScalars_apply, eqv4, congr_tmul, tensor_eqv_local_symm_apply, eqv3, AlgebraTensorModule.assoc_symm_tmul, eqv2, refl_apply, rid_tmul, eqv1, smul_tmul', assoc_tmul, smul_eq_mul, Localization.mk_mul, one_mul, mul_comm, tensor_eqv_local_apply, one_smul]

end Tensor

section flatlocal
variable {R : Type*} (M N : Type*) [CommRing R] (S : Submonoid R) [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

theorem Flat_of_localization (h : ∀ (J : Ideal R) (hJ : J.IsMaximal), Module.Flat (Localization.AtPrime J)
    (LocalizedModule.AtPrime J M)) : Module.Flat R M := by
  apply (Module.Flat.iff_rTensor_preserves_injective_linearMap R M).mpr
  intro N N' _ _ _ _ f finj
  apply injective_of_localization
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

variable (s : Finset R) (spn : span (s : Set R) = ⊤)
include spn

theorem Flat_of_localization_finitespan  (h : ∀ r : s, Module.Flat (Localization (Submonoid.powers r.1)) (LocalizedModule (Submonoid.powers r.1) M)) : Module.Flat R M := by
  apply (Module.Flat.iff_rTensor_preserves_injective_linearMap R M).mpr
  intro N N' _ _ _ _ f finj
  apply injective_of_localization_finitespan s spn
  intro r
  have inj : Function.Injective (map' (Submonoid.powers r.1) f) := by
    unfold map' LocalizedModule.map
    rw [← ker_eq_bot, LinearMap.coe_mk, AddHom.coe_mk, ← localized'_ker_eq_ker_localizedMap, ker_eq_bot.mpr finj, localized'_bot]
  set g1 := (rTensor (LocalizedModule (Submonoid.powers r.1) M) ((map' (Submonoid.powers r.1)) f))
  set g2 := ((map' (Submonoid.powers r.1)) (rTensor M f))
  have : (eqv N' M (Submonoid.powers r.1)) ∘ₗ g1 = g2 ∘ₗ (eqv N M (Submonoid.powers r.1)) := by
    apply TensorProduct.ext'
    intro x y
    unfold_let
    unfold eqv lmap
    simp only [ofLinear_toLinearMap, coe_comp, Function.comp_apply, LinearMap.rTensor_tmul,
      extendScalarsOfIsLocalization_apply', LinearEquiv.coe_coe]
    obtain ⟨n, sn, eqx⟩ : ∃ n : N, ∃ sn : (Submonoid.powers r.1), mk n sn = x := ⟨(Quotient.out x).1, (Quotient.out x).2, (Quotient.out_eq _)⟩
    obtain ⟨m, sm, eqy⟩ : ∃ m : M, ∃ sm : (Submonoid.powers r.1), mk m sm = y := ⟨(Quotient.out y).1, (Quotient.out y).2, (Quotient.out_eq _)⟩
    simp only [← eqx, ← eqy, map'_mk, eqv'_mk_apply, LinearMap.rTensor_tmul]
  have inj : Function.Injective ((eqv N' M (Submonoid.powers r.1)).toLinearMap ∘ₗ g1) := by
    simp only [coe_comp, LinearEquiv.coe_coe, EmbeddingLike.comp_injective]
    exact ((Module.Flat.iff_rTensor_preserves_injective_linearMap' _ _).mp (h r) (map' (Submonoid.powers r.1) f) inj)
  rw [this] at inj
  simp only [coe_comp, LinearEquiv.coe_coe, EquivLike.injective_comp] at inj
  exact inj
end flatlocal

variable (R R' : Type*) [CommRing R] [CommRing R'] [Algebra R R'] (S : Submonoid R) [IsLocalization S R']
include S
instance : Module.Flat R (Localization S) := by
  apply (Module.Flat.iff_lTensor_preserves_injective_linearMap R _).mpr
  intro N N' _ _ _ _ f finj
  set g1 := ((tensor_eqv_local N' S).restrictScalars R).toLinearMap ∘ₗ (LinearMap.lTensor (Localization S) f)
  set g2 := (map' S f).restrictScalars R ∘ₗ ((tensor_eqv_local N S).restrictScalars R).toLinearMap
  have eq : g1 = g2 := by
    apply TensorProduct.ext'
    intro x y
    unfold_let
    obtain ⟨n, sn, eqx⟩:= IsLocalization.mk'_surjective S x
    rw [← Localization.mk_eq_mk'] at eqx
    rw [← eqx]
    simp only [coe_comp, LinearEquiv.coe_coe, Function.comp_apply, LinearMap.lTensor_tmul,
      LinearEquiv.restrictScalars_apply, LinearMap.coe_restrictScalars, tensor_eqv_local_apply,
      map'_mk, _root_.map_smul]
  have : Function.Injective g2 := by
    unfold_let
    simp only [coe_comp, LinearMap.coe_restrictScalars, LinearEquiv.coe_coe,
      EquivLike.injective_comp]
    simp only [← ker_eq_bot] at finj ⊢
    unfold map' LocalizedModule.map
    rw [LinearMap.coe_mk, AddHom.coe_mk, ← localized'_ker_eq_ker_localizedMap, finj]
    exact localized'_bot _ _ _
  rw [← eq] at this
  unfold_let at this
  simp only [coe_comp, LinearEquiv.coe_coe, EmbeddingLike.comp_injective] at this
  exact this

lemma IsLocalization.Flat : Module.Flat R R' :=
  (Module.Flat.of_linearEquiv R (Localization S) R' (Localization.algEquiv S R').symm)

variable {M' : Type*} [AddCommGroup M'] [Module R M'] [Module R' M'] [IsScalarTower R R' M']

theorem flat_iff_localization : Module.Flat R' M' ↔ Module.Flat R M' := by
  letI := isLocalizedModule_id S M' R'
  letI := IsLocalization.Flat R R' S
  exact ⟨fun h ↦ Module.Flat.comp R R' M', fun h ↦ Module.Flat.of_isLocalizedModule R' S LinearMap.id⟩
