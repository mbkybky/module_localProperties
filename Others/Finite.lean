/-
Copyright (c) 2024 Yongle Hu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongle Hu
-/
import Mathlib.NumberTheory.NumberField.Basic

section

open Ideal

attribute [local instance] Ideal.Quotient.field in
/-- If `p` is a non-zero ideal of the `ℤ`, then `ℤ ⧸ p` is finite. -/
theorem Int.Quotient.finite_of_ne_bot {I : Ideal ℤ} (h : I ≠ ⊥) : Finite (ℤ ⧸ I) := by
  have equiv := Int.quotientSpanEquivZMod (Submodule.IsPrincipal.generator I)
  rw [span_singleton_generator I] at equiv
  haveI : NeZero (Submodule.IsPrincipal.generator I).natAbs := ⟨fun eq ↦
    h ((Submodule.IsPrincipal.eq_bot_iff_generator_eq_zero I).mpr (Int.natAbs_eq_zero.mp eq))⟩
  exact Finite.of_equiv (ZMod (Submodule.IsPrincipal.generator I).natAbs) equiv.symm

/-- In particular, if `p` is a maximal ideal of the `ℤ`, then `ℤ ⧸ p` is a finite field. -/
instance Int.Quotient.finite_of_is_maxiaml (p : Ideal ℤ) [hpm : p.IsMaximal] :
    Finite (ℤ ⧸ p) :=
  finite_of_ne_bot (Ring.ne_bot_of_isMaximal_of_not_isField hpm Int.not_isField)

/- #check Module.finite_of_finite
#check FiniteDimensional.fintypeOfFintype
def Module.Finite.finiteOfFinite {R M : Type*} [CommRing R] [Finite R] [AddCommMonoid M] [Module R M]
    [Module.Finite R M] : Finite M := by
  have := exists_fin' R M --exact .of_surjective f hf
  sorry -/

variable {R : Type*} [CommRing R] [h : Module.Finite ℤ R]

theorem Ideal.Quotient.finite_of_module_finite_int {I : Ideal R} (hp : I ≠ ⊥) : Finite (R ⧸ I) := sorry

-- `NoZeroSMulDivisors` can be removed
instance Ideal.Quotient.finite_of_module_finite_int_of_isMaxiaml [NoZeroSMulDivisors ℤ R] [IsDomain R]
    (p : Ideal R) [hpm : p.IsMaximal] : Finite (R ⧸ p) :=
  Ideal.Quotient.finite_of_module_finite_int <| Ring.ne_bot_of_isMaximal_of_not_isField hpm <|
    fun hf => Int.not_isField <|
      (Algebra.IsIntegral.isField_iff_isField (NoZeroSMulDivisors.algebraMap_injective ℤ R)).mpr hf

end

namespace NumberField

variable {K : Type*} [Field K] [NumberField K]

/-- For any nonzero ideal `I` of `𝓞 K`, `(𝓞 K) ⧸ I` has only finite elements.
  Note that if `I` is maximal, then `Finite ((𝓞 K) ⧸ I)` can be obtained by `inferInstance`. -/
theorem quotientFiniteOfNeBot {I : Ideal (𝓞 K)} (h : I ≠ ⊥) : Finite ((𝓞 K) ⧸ I) :=
  Ideal.Quotient.finite_of_module_finite_int h

example (p : Ideal (𝓞 K)) [p.IsMaximal] : Finite ((𝓞 K) ⧸ p) := inferInstance

/- instance quotientFiniteOfIsMaxiaml (p : Ideal (𝓞 K)) [hpm : p.IsMaximal] : Finite ((𝓞 K) ⧸ p) :=
  quotientFiniteOfNeBot (Ring.ne_bot_of_isMaximal_of_not_isField hpm (RingOfIntegers.not_isField K)) -/

end NumberField
