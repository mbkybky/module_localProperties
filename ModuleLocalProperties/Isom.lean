/-
Copyright (c) 2024 Yi Song. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yi Song, SiHan Su
-/
import Mathlib.Algebra.Module.Submodule.Localization

import ModuleLocalProperties.Basic

open Submodule LocalizedModule Ideal LinearMap

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N)

lemma injective_of_localization
    (h : ∀ (J : Ideal R) (hJ : J.IsMaximal), Function.Injective (map' J.primeCompl f)) :
    Function.Injective f :=
  ker_eq_bot.mp <| submodule_eq_bot_of_localization _ <|
  fun J hJ ↦ (localized'_ker_eq_ker_localizedMap _ _ _ _ f).trans <| ker_eq_bot.mpr <| h J hJ

lemma surjective_of_localization
    (h : ∀ (J : Ideal R) (hJ : J.IsMaximal), Function.Surjective (map' J.primeCompl f)) :
    Function.Surjective f :=
  range_eq_top.mp <| submodule_eq_top_of_localization _ <|
  fun J hJ ↦ (localized'_range_eq_range_localizedMap _ _ _ f).trans <| range_eq_top.mpr <| h J hJ

lemma bijective_of_localization
    (h : ∀ (J : Ideal R) (hJ : J.IsMaximal), Function.Bijective (map' J.primeCompl f)) :
    Function.Bijective f :=
  ⟨injective_of_localization _ fun J hJ => (h J hJ).1,
  surjective_of_localization _ fun J hJ => (h J hJ).2⟩

noncomputable def linearEquivOfLocalization (h : ∀ (J : Ideal R) (hJ : J.IsMaximal),
    Function.Bijective (map' J.primeCompl f)) : M ≃ₗ[R] N :=
  LinearEquiv.ofBijective f <| bijective_of_localization _ h

lemma linearEquivOfLocalization_apply (h : ∀ (J : Ideal R) (hJ : J.IsMaximal),
    Function.Bijective (map' J.primeCompl f)) (m : M) : linearEquivOfLocalization f h m = f m := rfl
