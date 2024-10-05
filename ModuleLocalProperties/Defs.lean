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

universe u v

protected abbrev IsLocalizedModule.AtPrime {R M M': Type*} [CommSemiring R] (J : Ideal R)
    [J.IsPrime] [AddCommMonoid M] [AddCommMonoid M'] [Module R M] [Module R M'] (f : M →ₗ[R] M'):=
  IsLocalizedModule J.primeCompl f

protected abbrev LocalizedModule.AtPrime {R : Type*} [CommSemiring R] (J : Ideal R) [J.IsPrime]
    (M : Type*) [AddCommMonoid M] [Module R M]:=
  LocalizedModule J.primeCompl M

protected abbrev IsLocalizedModule.Away {R M M': Type*} [CommSemiring R] (x : R) [AddCommMonoid M]
    [Module R M] [AddCommMonoid M'] [Module R M'] (f : M →ₗ[R] M') :=
  IsLocalizedModule (Submonoid.powers x) f

protected abbrev LocalizedModule.Away {R : Type*} [CommSemiring R] (x : R)
    (M : Type*) [AddCommMonoid M] [Module R M] :=
  LocalizedModule (Submonoid.powers x) M

section Properties

section IsLocalizedModule

variable (P : ∀ (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M], Prop)

def IsLocalizedModulePreserves : Prop :=
  ∀ {R : Type u} (S : Type u) {M N : Type v} [CommRing R] [CommRing S] [AddCommGroup M]
  [AddCommGroup N] [Module R M] [Module R N] [Algebra R S] [Module S N] [IsScalarTower R S N]
  (p : Submonoid R) [IsLocalization p S] (f : M →ₗ[R] N) [IsLocalizedModule p f],
  P R M → P S N

end IsLocalizedModule

section LocalizedModule

variable (P : ∀ (R : Type u) [CommRing R] (M : Type max u v) [AddCommGroup M] [Module R M], Prop)

def LocalizedModulePreserves : Prop :=
  ∀ {R : Type u} (S : Type u) {M : Type v} [CommRing R] [CommRing S] [AddCommGroup M] [Module R M]
  (p : Submonoid R),
  P R (ULift.{u} M) → P (Localization p) (LocalizedModule p M)

/-- A property `P` of comm rings satisfies `OfLocalizedModuleMaximal`
  if `P` holds for `M` whenever `P` holds for `Mₘ` for all maximal ideal `m`. -/
def OfLocalizedModuleMaximal : Prop :=
  ∀ {R : Type u} [CommRing R] (M : Type v) [AddCommGroup M] [Module R M],
  (∀ (J : Ideal R) (_ : J.IsMaximal), P (Localization.AtPrime J) (LocalizedModule.AtPrime J M)) →
  P R (ULift.{u} M)

/-- A property `P` of a `R`-module `M` satisfies `OfLocalizedModuleFiniteSpan`
  if `P` holds for `M` whenever there exists a finite set `{ r }` that spans `R` such that
  `P` holds for `Mᵣ`.

  Note that this is equivalent to `OfLocalizedModuleSpan` via
  `ofLocalizedModuleSpan_iff_finite`, but this is easier to prove. -/
def OfLocalizedModuleFiniteSpan :=
  ∀ {R : Type u} [CommRing R] (M : Type v) [AddCommGroup M] [Module R M] (s : Finset R)
  (_ : Ideal.span (s : Set R) = ⊤)
  (_ : ∀ r : s, P (Localization.Away r.1) (LocalizedModule.Away r.1 M)), P R (ULift.{u} M)

/-- A property `P` of a `R`-module `M` satisfies `OfLocalizedModuleSpan`
  if `P` holds for `M` whenever there exists a set `{ r }` that spans `R` such that
  `P` holds for `Mᵣ`.

  Note that this is equivalent to `OfLocalizedModuleFiniteSpan` via
  `ofLocalizedModuleSpan_iff_finite`, but this is easier to prove. -/
def OfLocalizedModuleSpan :=
  ∀ {R : Type u} [CommRing R] (M : Type v) [AddCommGroup M] [Module R M] (s : Set R)
  (_ : Ideal.span s = ⊤)
  (_ : ∀ r : s, P (Localization.Away r.1) (LocalizedModule.Away r.1 M)), P R (ULift.{u} M)

theorem ofLocalizedModuleSpan_iff_finite :
    OfLocalizedModuleSpan @P ↔ OfLocalizedModuleFiniteSpan @P := by
  apply forall₅_congr
  intros
  constructor
  · intro h s; exact h s
  · intro h s hs hs'
    obtain ⟨s', h₁, h₂⟩ := (Ideal.span_eq_top_iff_finite s).mp hs
    exact h s' h₂ fun x => hs' ⟨_, h₁ x.prop⟩

end LocalizedModule

end Properties
