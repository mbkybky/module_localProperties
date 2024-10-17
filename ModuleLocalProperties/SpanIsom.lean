/-
Copyright (c) 2024 Yi Song. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yi Song, Yongle Hu
-/

import ModuleLocalProperties.Basic

open Submodule LocalizedModule Ideal LinearMap

variable {R M M' : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M']
(s : Finset R) (spn : span (s : Set R) = ⊤) (f : M →ₗ[R] M')
include spn

lemma injective_of_localization_finitespan (h : ∀ r : s, Function.Injective
    (map' (Submonoid.powers r.1) f)) :
    Function.Injective f :=
  ker_eq_bot.mp <| submodule_eq_bot_of_localization_finitespan _ _ spn <|
  fun r ↦ (localized'_ker_eq_ker_localizedMap _ _ _ _ f).trans <| ker_eq_bot.mpr <| h r

lemma surjective_of_localization_finitespan (h : ∀ r : s, Function.Surjective
    (map' (Submonoid.powers r.1) f)) :
    Function.Surjective f :=
  range_eq_top.mp <| submodule_eq_top_of_localization_finitespan _ _ spn <|
  fun r ↦ (localized'_range_eq_range_localizedMap _ _ _ f).trans <| range_eq_top.mpr <| h r

lemma bijective_of_localization_finitespan (h : ∀ r : s, Function.Bijective
    (map' (Submonoid.powers r.1) f)) :
    Function.Bijective f :=
  ⟨injective_of_localization_finitespan _ spn _ fun r => (h r).1,
  surjective_of_localization_finitespan _ spn _ fun r => (h r).2⟩

noncomputable def linearEquivOfLocalizationFinitespan (h : ∀ r : s, Function.Bijective
    (map' (Submonoid.powers r.1) f)) : M ≃ₗ[R] M' :=
  LinearEquiv.ofBijective f <| bijective_of_localization_finitespan _ spn _ h

lemma linearEquivOfLocalizationFinitespan_apply (h : ∀ r : s, Function.Bijective
    (map' (Submonoid.powers r.1) f)) (m : M) :
    linearEquivOfLocalizationFinitespan s spn f h m = f m := rfl
