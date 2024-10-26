/-
Copyright (c) 2024 Yongle Hu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongle Hu
-/
import Mathlib.Algebra.Algebra.Subalgebra.Tower
import Mathlib.LinearAlgebra.Dimension.Finrank

variable (R S A : Type*) [CommSemiring R] [CommSemiring S] [Semiring A] [Algebra R S] [Algebra S A]
  [Algebra R A] [IsScalarTower R S A]

def AlgEquiv.restrictScalarsHom : (A ≃ₐ[S] A) →* (A ≃ₐ[R] A) where
  toFun f := AlgEquiv.restrictScalars R f
  map_one' := rfl
  map_mul' _ _ := rfl

theorem AlgEquiv.restrictScalarsHom_injective : Function.Injective (AlgEquiv.restrictScalarsHom R S A) :=
  AlgEquiv.restrictScalars_injective R

theorem AlgEquiv.restrictScalarsHom_bot_surjective :
    Function.Surjective (AlgEquiv.restrictScalarsHom R (⊥ : Subalgebra R S) S) := sorry

noncomputable def subalgebra_bot_aut_equiv : (S ≃ₐ[(⊥ : Subalgebra R S)] S) ≃* (S ≃ₐ[R] S) :=
  MulEquiv.ofBijective _
    ⟨AlgEquiv.restrictScalarsHom_injective R _ S, AlgEquiv.restrictScalarsHom_bot_surjective R S⟩

noncomputable def aut_equiv_of_finrank_eq_one {R S : Type*} (A : Type*) [CommSemiring R] [CommRing S]
    [Semiring A] [Algebra R S] [Algebra S A] [Algebra R A] [IsScalarTower R S A]
    (h : Module.finrank R S = 1) : (A ≃ₐ[S] A) ≃* (A ≃ₐ[R] A) := sorry
