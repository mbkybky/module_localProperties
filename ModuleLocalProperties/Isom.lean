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
    (h : ∀ (J : Ideal R) (_ : J.IsMaximal), Function.Injective (map' J.primeCompl f)) :
    Function.Injective f :=
  ker_eq_bot.mp <| submodule_eq_bot_of_localization _ <|
  fun J hJ ↦ (localized'_ker_eq_ker_localizedMap _ _ _ _ f).trans <| ker_eq_bot.mpr <| h J hJ

lemma surjective_of_localization
    (h : ∀ (J : Ideal R) (_ : J.IsMaximal), Function.Surjective (map' J.primeCompl f)) :
    Function.Surjective f :=
  range_eq_top.mp <| submodule_eq_top_of_localization _ <|
  fun J hJ ↦ (localized'_range_eq_range_localizedMap _ _ _ f).trans <| range_eq_top.mpr <| h J hJ

lemma bijective_of_localization
    (h : ∀ (J : Ideal R) (_ : J.IsMaximal), Function.Bijective (map' J.primeCompl f)) :
    Function.Bijective f :=
  ⟨injective_of_localization _ fun J hJ => (h J hJ).1,
  surjective_of_localization _ fun J hJ => (h J hJ).2⟩

noncomputable def linearEquivOfLocalization (h : ∀ (J : Ideal R) (_ : J.IsMaximal),
    Function.Bijective (map' J.primeCompl f)) : M ≃ₗ[R] N :=
  LinearEquiv.ofBijective f <| bijective_of_localization _ h

lemma linearEquivOfLocalization_apply (h : ∀ (J : Ideal R) (_ : J.IsMaximal),
    Function.Bijective (map' J.primeCompl f)) (m : M) : linearEquivOfLocalization f h m = f m := rfl

variable {R S: Type*} [CommRing R] [CommRing S] [Algebra R S](p: Submonoid R)[IsLocalization p S]
variable {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] [Module S N][IsScalarTower R S N]
   (f : M →ₗ[R] N) [IsLocalizedModule p f]
variable {P Q : Type*} [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q] [Module S Q][IsScalarTower R S Q]
   (f' : P →ₗ[R] Q) [IsLocalizedModule p f'] {g: M →ₗ[R] P}

lemma localization_injective (h : Function.Injective g) : Function.Injective (LinearMap.extendScalarsOfIsLocalization p S ((IsLocalizedModule.map p f f') g )) := by
  apply LinearMap.ker_eq_bot.mp
  rw [← LinearMap.localized'_ker_eq_ker_localizedMap, LinearMap.ker_eq_bot.mpr h]
  exact (Submodule.eq_bot_iff (localized' S p f ⊥)).mpr
    (by simp only [localized'_bot, Submodule.mem_bot, imp_self, implies_true])

theorem injective_localizationPreserves (h : Function.Injective g) :
    Function.Injective ((IsLocalizedModule.map p f f') g) := sorry

theorem surjective_localizationPreserves (h : Function.Surjective g) :
    Function.Surjective ((IsLocalizedModule.map p f f') g) := sorry

theorem bijective_localizationPreserves (h : Function.Bijective g) :
    Function.Bijective ((IsLocalizedModule.map p f f') g) :=
  ⟨injective_localizationPreserves p f f' h.1, surjective_localizationPreserves p f f' h.2⟩
