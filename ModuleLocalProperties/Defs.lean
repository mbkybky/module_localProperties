/-
Copyright (c) 2024 Yongle Hu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongle Hu
-/
import Mathlib.Algebra.Module.LocalizedModule
import Mathlib.RingTheory.Localization.AtPrime

/-!
# Local properties of modules

In this file, we define local properties of modules in general.

-/

abbrev IsLocalizedModule.AtPrime {R M M': Type*} [CommSemiring R] (J : Ideal R) [J.IsPrime] [AddCommMonoid M] [AddCommMonoid M'] [Module R M] [Module R M'] (f : M →ₗ[R] M'):=
  IsLocalizedModule J.primeCompl f

abbrev LocalizedModule.AtPrime {R : Type*} [CommSemiring R] (J : Ideal R) [J.IsPrime] (M : Type*) [AddCommMonoid M] [Module R M]:=
  LocalizedModule J.primeCompl M

open scoped Pointwise Classical

universe u v u' v'

section Properties

section Module

variable (P : ∀ {R : Type u} [CommRing R] (M : Type v) [AddCommGroup M] [Module R M], Prop)

def IsLocalizedModulePreserves : Prop :=
  ∀ {R : Type u} (S : Type u) {M N : Type v} [CommRing R] [CommRing S] [AddCommGroup M]
  [AddCommGroup N] [Module R M] [Module R N] [Algebra R S] [Module S N] [IsScalarTower R S N]
  (p : Submonoid R) [IsLocalization p S] (f : M →ₗ[R] N) [IsLocalizedModule p f],
  @P R _ M _ _ → @P S _ N _ _
/-
def LocalizedModulePreserves : Prop :=
  ∀ {R : Type u} (S : Type u) {M N : Type v} [CommRing R] [CommRing S] [AddCommGroup M] [Module R M]
  (p : Submonoid R),
  @P R _ M _ _ → @P (Localization p) _ (LocalizedModule p M) _ _

/-- A property `P` of comm rings satisfies `OfLocalizationMaximal`
  if `P` holds for `R` whenever `P` holds for `Rₘ` for all maximal ideal `m`. -/
def OfLocalizedModuleMaximal : Prop :=
  ∀ {R : Type u} [CommRing R] (M : Type v) [AddCommGroup M] [Module R M],
    (∀ (J : Ideal R) (_ : J.IsMaximal), P (LocalizedModule.AtPrime J M)) → P M
 -/
end Module

end Properties
