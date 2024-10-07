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

open Submodule IsLocalizedModule LocalizedModule Ideal IsLocalization

lemma inj_of_local {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] (f : M →ₗ[R] N) (h : ∀ (J : Ideal R) (hJ : J.IsMaximal), Function.Injective (map' J.primeCompl f)) : Function.Injective f := by
  simp only [← LinearMap.ker_eq_bot] at h ⊢
  exact submodule_eq_bot_of_localization _ fun J hJ ↦ (LinearMap.localized'_ker_eq_ker_localizedMap _ _ _ _ f).trans (h J hJ)

#check Localization.localRingHom
#check LocalizedModule.map
#check IsLocalizedModule.linearEquiv
#check Submodule.subtype
#check LinearMap.ker_eq_bot'

#check IsLocalizedModule.iso
#check IsLocalizedModule

noncomputable def eqv1 {R : Type*} (M : Type*) [CommRing R] [AddCommGroup M] [Module R M] (S : Submonoid R) (I : Ideal R) : LocalizedModule S (TensorProduct R I M) ≃ₗ[R] TensorProduct (Localization S) (Ideal.map (algebraMap R (Localization S)) I) (LocalizedModule S M) := by
  set f : (TensorProduct R I M) →ₗ[R] TensorProduct (Localization S) (Ideal.map (algebraMap R (Localization S)) I) (LocalizedModule S M) := by

    sorry
  letI : IsLocalizedModule S f (M := (TensorProduct R I M)) (M' := TensorProduct (Localization S) (Ideal.map (algebraMap R (Localization S)) I) (LocalizedModule S M)) := by

    sorry
  exact IsLocalizedModule.iso S f

def eqv2 {R : Type*} (M : Type*) [CommRing R] [AddCommGroup M] [Module R M]  (S : Submonoid R) (I : Ideal R) : LocalizedModule S (TensorProduct R R M) ≃ₗ[R] TensorProduct (Localization S) (Localization S) (LocalizedModule S M) := by

  sorry

example {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] (h : ∀ (J : Ideal R) (hJ : J.IsMaximal), Module.Flat (Localization.AtPrime J) (LocalizedModule.AtPrime J M)) : Module.Flat R M := by
  apply (Module.Flat.iff_rTensor_injective' R M).mpr
  intro I
  apply inj_of_local
  intro J maxJ
  have hj := (Module.Flat.iff_rTensor_injective' _ _).mp (h J maxJ) (I.map (algebraMap R (Localization J.primeCompl)))

  set fi := (Submodule.subtype (Ideal.map (algebraMap R (Localization J.primeCompl)) I))
  set f' := LinearMap.rTensor (LocalizedModule.AtPrime J M) fi
  unfold LocalizedModule.AtPrime at f'
  set g := LinearMap.rTensor M (Submodule.subtype I)
  set g' := map' J.primeCompl g
  have : g' = (eqv2 M J.primeCompl I).symm ∘ f' ∘ (eqv1 M J.primeCompl I) := by sorry

  rw [this]
  simp only [EmbeddingLike.comp_injective, EquivLike.injective_comp]
  exact hj


#check IsLocalization.map_comap
#check mem_map_algebraMap_iff


example {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (h : ∀ (J : Ideal R) (hJ : J.IsMaximal), Module.Flat (Localization.AtPrime J)
    (LocalizedModule.AtPrime J M)) : Module.Flat R M := by
  apply (Module.Flat.iff_rTensor_preserves_injective_linearMap' R M).mpr
  intro N N' _ _ _ _ f finj
  apply inj_of_local
  intro J hJ
  have inj : Function.Injective (map' J.primeCompl f) := by
    apply LinearMap.ker_eq_bot.mp
    unfold map' LocalizedModule.map
    rw [LinearMap.coe_mk, AddHom.coe_mk, ← LinearMap.localized'_ker_eq_ker_localizedMap,
      LinearMap.ker_eq_bot.mpr finj, localized'_bot]
  have H := (Module.Flat.iff_rTensor_preserves_injective_linearMap' _ _).mp (h J hJ) (map' J.primeCompl f) inj
  set g1 := (LinearMap.rTensor (LocalizedModule.AtPrime J M) ((map' J.primeCompl) f))
  set g2 := ((map' J.primeCompl) (LinearMap.rTensor M f))
  have : g1 = (Eqv N' M J.primeCompl).symm ∘ₗ g2 ∘ₗ (Eqv N M J.primeCompl) := by

    sorry
  simp only [this, LinearMap.coe_comp, LinearEquiv.coe_coe, EmbeddingLike.comp_injective,
    EquivLike.injective_comp] at H
  exact H
