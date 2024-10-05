/-
Copyright (c) 2024 Yongle Hu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongle Hu, Sihan Su
-/
import Mathlib.Algebra.Module.Submodule.Localization
import Mathlib.RingTheory.Localization.AtPrime
import ModuleLocalProperties.Basic


open Submodule IsLocalizedModule LocalizedModule Ideal

variable {R M M' : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M']
(s : Finset R) (spn : span (s : Set R) = ⊤) (f : M →ₗ[R] M')
include spn

lemma injective_of_localization_finitespan (h : ∀ r : s, Function.Injective
    ((map (Submonoid.powers r.1) f).extendScalarsOfIsLocalization (Submonoid.powers r.1)
    (Localization (Submonoid.powers r.1)))) :
    Function.Injective f := by
  simp only [← LinearMap.ker_eq_bot, Subtype.forall] at h ⊢
  apply submodule_eq_bot_of_localization_finitespan
  exact spn
  simp only [Subtype.forall]
  intro a ains
  specialize h a ains
  unfold LocalizedModule.map at h
  rw [← LinearMap.localized'_ker_eq_ker_localizedMap] at h
  unfold localized
  rw [h]

lemma surjective_of_localization_finitespan (h : ∀ r : s, Function.Surjective
    ((map (Submonoid.powers r.1) f).extendScalarsOfIsLocalization (Submonoid.powers r.1)
    (Localization (Submonoid.powers r.1)))) :
    Function.Surjective f := by
  simp only [← LinearMap.range_eq_top, Subtype.forall] at h ⊢
  apply submodule_eq_top_of_localization_finitespan
  exact spn
  simp only [Subtype.forall]
  intro a ains
  specialize h a ains
  unfold LocalizedModule.map at h
  rw [← LinearMap.localized'_range_eq_range_localizedMap] at h
  unfold localized
  rw [h]

lemma bijective_of_localization_finitespan (h : ∀ r : s, Function.Bijective
    ((map (Submonoid.powers r.1) f).extendScalarsOfIsLocalization (Submonoid.powers r.1)
    (Localization (Submonoid.powers r.1)))) :
    Function.Bijective f :=
    have h1 := fun r => (h r).1
    have h2 := fun r => (h r).2
    ⟨injective_of_localization_finitespan _ spn _ h1,
    surjective_of_localization_finitespan _ spn _ h2⟩

noncomputable def linearEquivOfLocalizationFinitespan (h : ∀ r : s, Function.Bijective
    ((map (Submonoid.powers r.1) f).extendScalarsOfIsLocalization (Submonoid.powers r.1)
    (Localization (Submonoid.powers r.1)))) : M ≃ₗ[R] M' :=
  LinearEquiv.ofBijective f <| bijective_of_localization_finitespan _ spn _ h
