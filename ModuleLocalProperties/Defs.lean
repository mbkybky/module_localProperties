/-
Copyright (c) 2024 Yongle Hu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongle Hu
-/
import Mathlib.RingTheory.Localization.AtPrime
import Mathlib.RingTheory.Localization.Module
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.RingTheory.Flat.Basic

/-!
# Local properties of modules

In this file, we define local properties of modules in general.

-/

universe u v v'

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

noncomputable def LocalizedModule.map {R : Type*} [CommSemiring R] (S : Submonoid R) {M M' : Type*}
    [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M'] :
    (M →ₗ[R] M') →ₗ[R] (LocalizedModule S M) →ₗ[R] (LocalizedModule S M') :=
  IsLocalizedModule.map S (mkLinearMap S M) (mkLinearMap S M')

section LocalizedModule.map'

variable {R : Type*} [CommSemiring R] (S : Submonoid R) {M N : Type*}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

noncomputable def map' : (M →ₗ[R] N) →ₗ[R] LocalizedModule S M →ₗ[Localization S] LocalizedModule S N where
  toFun := fun f => LinearMap.extendScalarsOfIsLocalization S _ <| LocalizedModule.map S f
  map_add' := by
    intro f g
    ext x
    dsimp
    rw [map_add, LinearMap.add_apply]
  map_smul' := by
    intro r f
    ext x
    dsimp
    rw [map_smul, LinearMap.smul_apply]

end LocalizedModule.map'

section Properties

section IsLocalizedModule

variable (P : ∀ (R : Type u) (M : Type v) [CommRing R] [AddCommGroup M] [Module R M], Prop)

/-- A property `P` of `R`-modules is said to be preserved by localization
  if `P` holds for `p⁻¹M` whenever `P` holds for `M`. -/
def IsLocalizedModulePreserves : Prop :=
  ∀ {R : Type u} (S : Type u) {M N : Type v} [CommRing R] [CommRing S] [AddCommGroup M]
  [AddCommGroup N] [Module R M] [Module R N] [Algebra R S] [Module S N] [IsScalarTower R S N]
  (p : Submonoid R) [IsLocalization p S] (f : M →ₗ[R] N) [IsLocalizedModule p f],
  P R M → P S N

end IsLocalizedModule

section LocalizedModule

variable (P : ∀ (R : Type u) (M : Type max u v) [CommRing R] [AddCommGroup M] [Module R M], Prop)

/-- A property `P` of `R`-modules is said to be preserved by localization
  if `P` holds for `p⁻¹M` whenever `P` holds for `M`. -/
def LocalizedModulePreserves : Prop :=
  ∀ {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M] (p : Submonoid R),
    P R (ULift.{u} M) → P (Localization p) (LocalizedModule p M)

/-- A property `P` of `R`-modules satisfies `OfLocalizedModuleMaximal`
  if `P` holds for `M` whenever `P` holds for `Mₘ` for all maximal ideal `m`. -/
def OfLocalizedModuleMaximal : Prop :=
  ∀ {R : Type u} (M : Type v) [CommRing R] [AddCommGroup M] [Module R M],
    (∀ (J : Ideal R) (_ : J.IsMaximal), P (Localization.AtPrime J) (LocalizedModule.AtPrime J M)) →
    P R (ULift.{u} M)

/-- A property `P` of `R`-modules satisfies `OfLocalizedModuleFiniteSpan`
  if `P` holds for `M` whenever there exists a finite set `{ r }` that spans `R` such that
  `P` holds for `Mᵣ`.

  Note that this is equivalent to `OfLocalizedModuleSpan` via
  `ofLocalizedModuleSpan_iff_finite`, but this is easier to prove. -/
def OfLocalizedModuleFiniteSpan :=
  ∀ {R : Type u} [CommRing R] (M : Type v) [AddCommGroup M] [Module R M] (s : Finset R)
    (_ : Ideal.span (s : Set R) = ⊤)
    (_ : ∀ r : s, P (Localization.Away r.1) (LocalizedModule.Away r.1 M)), P R (ULift.{u} M)

/-- A property `P` of `R`-modules satisfies `OfLocalizedModuleSpan`
  if `P` holds for `M` whenever there exists a set `{ r }` that spans `R` such that
  `P` holds for `Mᵣ`.

  Note that this is equivalent to `OfLocalizedModuleFiniteSpan` via
  `ofLocalizedModuleSpan_iff_finite`, but this is easier to prove. -/
def OfLocalizedModuleSpan :=
  ∀ {R : Type u} [CommRing R] (M : Type v) [AddCommGroup M] [Module R M] (s : Set R)
    (_ : Ideal.span s = ⊤)
    (_ : ∀ r : s, P (Localization.Away r.1) (LocalizedModule.Away r.1 M)), P R (ULift.{u} M)

theorem ofLocalizedModuleSpan_iff_finite :
    OfLocalizedModuleSpan P ↔ OfLocalizedModuleFiniteSpan P := by
  apply forall₅_congr
  intros
  constructor
  · intro h s; exact h s
  · intro h s hs hs'
    obtain ⟨s', h₁, h₂⟩ := (Ideal.span_eq_top_iff_finite s).mp hs
    exact h s' h₂ fun x => hs' ⟨_, h₁ x.prop⟩

end LocalizedModule

section LinearMap

variable (P : ∀ {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
  {N : Type v'} [AddCommGroup N] [Module R N] (_ : M →ₗ[R] N), Prop)

/-- A property `P` of ring homs is said to be preserved by localization
 if `P` holds for `M⁻¹R →+* M⁻¹S` whenever `P` holds for `R →+* S`. -/
def LinearMap.LocalizedModulePreserves :=
  ∀ ⦃R : Type u⦄ [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
    {N : Type v'} [AddCommGroup N] [Module R N] (f : M →ₗ[R] N)
    (p : Submonoid R) (S : Type u) [CommRing S] [Algebra R S] [IsLocalization p S]
    {M' : Type v} [AddCommGroup M'] [Module R M'] [Module S M'] [IsScalarTower R S M']
    (fm : M →ₗ[R] M') {N' : Type v'} [AddCommGroup N'] [Module R N'] [Module S N']
    [IsScalarTower R S N'] (fn : N →ₗ[R] N') [IsLocalizedModule p fm] [IsLocalizedModule p fn],
    P f → P ((IsLocalizedModule.map p fm fn f).extendScalarsOfIsLocalization p S)
/-
/-- A property `P` of ring homs satisfies `RingHom.OfLocalizationFiniteSpan`
if `P` holds for `R →+* S` whenever there exists a finite set `{ r }` that spans `R` such that
`P` holds for `Rᵣ →+* Sᵣ`.

Note that this is equivalent to `RingHom.OfLocalizationSpan` via
`RingHom.ofLocalizationSpan_iff_finite`, but this is easier to prove. -/
def LinearMap.OfLocalizedModuleFiniteSpan :=
  ∀ ⦃R S : Type u⦄ [CommRing R] [CommRing S] (f : R →+* S) (s : Finset R)
    (_ : Ideal.span (s : Set R) = ⊤) (_ : ∀ r : s, P (Localization.awayMap f r)), P f

/-- A property `P` of ring homs satisfies `RingHom.OfLocalizationFiniteSpan`
if `P` holds for `R →+* S` whenever there exists a set `{ r }` that spans `R` such that
`P` holds for `Rᵣ →+* Sᵣ`.

Note that this is equivalent to `RingHom.OfLocalizationFiniteSpan` via
`RingHom.ofLocalizationSpan_iff_finite`, but this has less restrictions when applying. -/
def LinearMap.OfLocalizedModuleSpan :=
  ∀ ⦃R S : Type u⦄ [CommRing R] [CommRing S] (f : R →+* S) (s : Set R) (_ : Ideal.span s = ⊤)
    (_ : ∀ r : s, P (Localization.awayMap f r)), P f
 -/
end LinearMap

section LocalizedModule'

variable (P : ∀ (R : Type u) (M : Type max u v) [CommRing R] [AddCommGroup M] [Module R M], Prop)
  (Q : ∀ (R : Type u) (M : Type v) [CommRing R] [AddCommGroup M] [Module R M], Prop)

/-- A property `P` of `R`-modules satisfies `OfLocalizedModuleMaximal`
  if `P` holds for `M` whenever `P` holds for `Mₘ` for all maximal ideal `m`. -/
def OfLocalizedModuleMaximal' : Prop :=
  ∀ {R : Type u} [CommRing R] (M : Type v) [AddCommGroup M] [Module R M],
    (∀ (J : Ideal R) (_ : J.IsMaximal), P (Localization.AtPrime J) (LocalizedModule.AtPrime J M)) →
    Q R M

/-- A property `P` of `R`-modules satisfies `OfLocalizedModuleFiniteSpan`
  if `P` holds for `M` whenever there exists a finite set `{ r }` that spans `R` such that
  `P` holds for `Mᵣ`.

  Note that this is equivalent to `OfLocalizedModuleSpan` via
  `ofLocalizedModuleSpan_iff_finite`, but this is easier to prove. -/
def OfLocalizedModuleFiniteSpan' :=
  ∀ {R : Type u} [CommRing R] (M : Type v) [AddCommGroup M] [Module R M] (s : Finset R)
    (_ : Ideal.span (s : Set R) = ⊤)
    (_ : ∀ r : s, P (Localization.Away r.1) (LocalizedModule.Away r.1 M)), Q R M

/-- A property `P` of `R`-modules satisfies `OfLocalizedModuleSpan`
  if `P` holds for `M` whenever there exists a set `{ r }` that spans `R` such that
  `P` holds for `Mᵣ`.

  Note that this is equivalent to `OfLocalizedModuleFiniteSpan` via
  `ofLocalizedModuleSpan_iff_finite`, but this is easier to prove. -/
def OfLocalizedModuleSpan' :=
  ∀ {R : Type u} [CommRing R] (M : Type v) [AddCommGroup M] [Module R M] (s : Set R)
    (_ : Ideal.span s = ⊤)
    (_ : ∀ r : s, P (Localization.Away r.1) (LocalizedModule.Away r.1 M)), Q R M

theorem ofLocalizedModuleSpan_iff_finite' :
    OfLocalizedModuleSpan' P Q ↔ OfLocalizedModuleFiniteSpan' P Q := by
  apply forall₅_congr
  intros
  constructor
  · intro h s; exact h s
  · intro h s hs hs'
    obtain ⟨s', h₁, h₂⟩ := (Ideal.span_eq_top_iff_finite s).mp hs
    exact h s' h₂ fun x => hs' ⟨_, h₁ x.prop⟩

end LocalizedModule'

end Properties
