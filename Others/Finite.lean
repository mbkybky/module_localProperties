/-
Copyright (c) 2024 Yongle Hu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongle Hu
-/
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Ideal.Quotient
import Mathlib.RingTheory.Finiteness
import Mathlib.RingTheory.Ideal.Over

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

--Version issue: it's available in mathlib, but not in our library.
lemma My_copy_Module.finite_of_finite (R : Type u_1) {M : Type u_4} [Semiring R] [AddCommMonoid M] [Module R M]
  [Finite R] [Module.Finite R M] : Finite M := by
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' R M;
  exact .of_surjective f hf

theorem Ideal.Quotient.finite_of_module_finite_int [IsDomain R]{I : Ideal R} (hp : I ≠ ⊥) : Finite (R ⧸ I) := by
  have : I.comap (algebraMap ℤ R) ≠ ⊥ := by
    obtain ⟨x, hx1, hx2⟩ : ∃ x : R ,x ∈ I ∧ x ≠ 0 :=
      Set.not_subset.mp <| mt (Submodule.eq_bot_iff I).mpr hp
    apply Ideal.comap_ne_bot_of_integral_mem hx2 hx1 <| Algebra.IsIntegral.isIntegral x
  have t1 : Module.Finite (ℤ ⧸ I.comap (algebraMap ℤ R)) (R ⧸ I) :=
    Module.Finite.of_restrictScalars_finite ℤ (ℤ ⧸ I.comap (algebraMap ℤ R)) (R ⧸ I)
  have t2 : Finite (ℤ ⧸ I.comap (algebraMap ℤ R)) :=
    Int.Quotient.finite_of_ne_bot this
  exact My_copy_Module.finite_of_finite (ℤ ⧸ comap (algebraMap ℤ R) I)

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
