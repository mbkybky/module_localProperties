/-
Copyright (c) 2024 Yongle Hu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongle Hu, Sihan Su
-/
import Mathlib.Algebra.Module.Submodule.Localization
import Mathlib.RingTheory.Localization.AtPrime
import ModuleLocalProperties.Basic

open Submodule IsLocalizedModule LocalizedModule Ideal

#check LinearMap.localized'_ker_eq_ker_localizedMap
#check submodule_eq_of_localization_finitespan



lemma submodule_eq_bot_of_localization_finitespan {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] (N : Submodule R M) (P : Submodule R M) (s : Finset R) (spn : span (s : Set R) = ⊤) (h : ∀ r : s, localized (Submonoid.powers r.1) N = ⊥) : N = ⊥ := by
  apply submodule_eq_of_localization_finitespan
  apply spn
  simp only [h, Subtype.forall]
  intros
  sorry

lemma injective_of_localization_finitespan {R M M' : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M'] (f : M →ₗ[R] M')
(s : Finset R) (spn : span (s : Set R) = ⊤)
(h : ∀ r : s, Function.Injective
  ((map (Submonoid.powers r.1) f).extendScalarsOfIsLocalization (Submonoid.powers r.1) (Localization (Submonoid.powers r.1)))
  ) :
    Function.Injective f := by
  simp only [← LinearMap.ker_eq_bot, Subtype.forall] at h ⊢
  apply submodule_eq_of_localization_finitespan
  apply spn
  simp only [Subtype.forall]
  intro a ains
  specialize h a ains
  unfold LocalizedModule.map at h
  rw[← LinearMap.localized'_ker_eq_ker_localizedMap ] at h
  unfold localized
  rw[h]

  sorry
