/-
Copyright (c) 2024 Yongle Hu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongle Hu, Zixun Guo
-/
import Mathlib.Algebra.Algebra.Subalgebra.Tower
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

section
variable (R S A : Type*) [CommSemiring R] [CommSemiring S] [Semiring A] [Algebra R S] [Algebra S A]
  [Algebra R A] [IsScalarTower R S A]

def AlgEquiv.restrictScalarsHom : (A ≃ₐ[S] A) →* (A ≃ₐ[R] A) where
  toFun f := AlgEquiv.restrictScalars R f
  map_one' := rfl
  map_mul' _ _ := rfl

-- theorem AlgEquiv.restrictScalarsHom_injective : Function.Injective (AlgEquiv.restrictScalarsHom R S A) :=
--   AlgEquiv.restrictScalars_injective R

-- theorem AlgEquiv.restrictScalarsHom_bot_surjective :
--     Function.Surjective (AlgEquiv.restrictScalarsHom R (⊥ : Subalgebra R S) S) := sorry


-- noncomputable def subalgebra_bot_aut_equiv : (S ≃ₐ[(⊥ : Subalgebra R S)] S) ≃* (S ≃ₐ[R] S) :=
--   MulEquiv.ofBijective _
--     ⟨AlgEquiv.restrictScalarsHom_injective R _ S, AlgEquiv.restrictScalarsHom_bot_surjective R S⟩

end

/-- a reverse map form S to R with its property which is proved internally
-/
noncomputable def reverse_map_if_rank_eq_one {F S : Type*}
[Field F] [CommRing S] [Nontrivial S]
[Algebra F S]
(h : Module.finrank F S = 1) :
{f: S → F // ∀ w:S, (f w) • 1 = w}
:=  let h1 := (finrank_eq_one_iff_of_nonzero' (1: S) (by simp)).mp h
    ⟨fun x =>
      let h2 := h1 x
      Classical.choose h2,
      fun x => Classical.choose_spec (h1 x)⟩

/-- the exsistant property which reverse map relies on also has uniqueness
-/
theorem reverse_map_uniqueness {F S : Type*}
[Field F] [CommRing S] [Nontrivial S]
[Algebra F S]
(h : Module.finrank F S = 1)
(w: S) {y: F}
(h1: y • 1 = w): y = (reverse_map_if_rank_eq_one h).1 w := by
  have h2 := (reverse_map_if_rank_eq_one h).2 w
  rw [<-h2] at h1
  apply_fun (fun x => x • (1: S))
  simp only
  exact h1
  apply smul_left_injective
  simp only [ne_eq, one_ne_zero, not_false_eq_true]

/-- the reverse map is a ring homomorphism
-/
noncomputable def reverse_hom_if_rank_eq_one {F S : Type*}
[Field F] [CommRing S] [Nontrivial S]
[Algebra F S]
(h : Module.finrank F S = 1)
: S →+* F where
  toFun := (reverse_map_if_rank_eq_one h).1
  map_one' := by
    apply Eq.symm
    apply reverse_map_uniqueness h 1
    exact one_smul _ _
  map_mul' := by
    intro x y
    simp only
    apply Eq.symm
    apply reverse_map_uniqueness h (x * y)
    rw [mul_smul]
    rw [(reverse_map_if_rank_eq_one _).2]
    rw [<-mul_smul_one]
    rw [(reverse_map_if_rank_eq_one _).2]
    rw [mul_comm]
  map_zero' := by
    simp only
    apply Eq.symm
    apply reverse_map_uniqueness h 0
    exact zero_smul _ _
  map_add' := by
    simp only
    intro x y
    apply Eq.symm
    apply reverse_map_uniqueness h (x + y)
    rw [add_smul]
    repeat rw [(reverse_map_if_rank_eq_one _).2]

theorem reverse_hom_smul_one_eq_self {F S : Type*}
[Field F] [CommRing S] [Nontrivial S]
[Algebra F S]
(h : Module.finrank F S = 1)
(w: S): (reverse_hom_if_rank_eq_one h w) • 1 = w :=(reverse_map_if_rank_eq_one h).2 w

/-- the reverse homomorphism is an algebra homomorphism
-/
noncomputable def reverse_algebra_if_rank_eq_one {F S : Type*}
[Field F] [CommRing S] [Nontrivial S]
[Algebra F S]
(h : Module.finrank F S = 1)
: Algebra S F where
  smul := fun s f => (reverse_hom_if_rank_eq_one h s) * f
  toFun := (reverse_hom_if_rank_eq_one h)
  smul_def' := by
    intro r x
    simp only [RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk]
    rfl
  map_one' := by
    apply Eq.symm
    apply reverse_map_uniqueness h 1
    exact one_smul _ _
  commutes' := by
    intro r x
    simp only [RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk]
    rw [mul_comm]
  map_mul' := by
    intro x y
    simp only
    apply Eq.symm
    apply reverse_map_uniqueness h (x * y)
    rw [mul_smul, reverse_hom_smul_one_eq_self, <-mul_smul_one, reverse_hom_smul_one_eq_self, mul_comm]
  map_zero' := by
    apply Eq.symm
    apply reverse_map_uniqueness h 0
    exact zero_smul _ _
  map_add' := by
    intro x y
    simp only
    apply Eq.symm
    apply reverse_map_uniqueness h (x + y)
    rw [add_smul]
    repeat rw [reverse_hom_smul_one_eq_self]

noncomputable def reverse_algebra_is_scalar_tower {F S A : Type*}
[Semiring A]
[Field F] [CommRing S] [Nontrivial S]
[Algebra S A] [Algebra F A][Algebra F S]
[IsScalarTower F S A]
(h : Module.finrank F S = 1)
: @IsScalarTower S F A ((reverse_algebra_if_rank_eq_one h).toSMul) _ _ :=
  by
    let smul_instance := (reverse_algebra_if_rank_eq_one h).toSMul
    let smul := fun s f => (reverse_hom_if_rank_eq_one h s) * f
    apply @IsScalarTower.mk _ _ _ (smul_instance) _ _
    intro r x y
    show (smul r x) • y = r • x • y
    unfold_let smul
    simp only
    rw [mul_smul, <-mul_smul_one]
    rw [show (1: A) = (1: S) • (1: A) from by simp only [one_smul]]
    rw [<-smul_assoc, reverse_hom_smul_one_eq_self]
    simp only [Algebra.mul_smul_comm, mul_one]




noncomputable def aut_equiv_of_finrank_eq_one {F S A : Type*}
[Semiring A]
[Field F] [CommRing S] [Nontrivial S]
[Algebra S A] [Algebra F A][Algebra F S]
[IsScalarTower F S A]
(h : Module.finrank F S = 1)
: (A ≃ₐ[S] A) ≃* (A ≃ₐ[F] A) where
  toFun := AlgEquiv.restrictScalarsHom F S A
  invFun := @AlgEquiv.restrictScalarsHom S F A _ _ _ (reverse_algebra_if_rank_eq_one h) _ _ (reverse_algebra_is_scalar_tower h)
  left_inv := by
    intro x
    apply AlgEquiv.ext
    intro y
    simp only [AlgEquiv.restrictScalarsHom, AlgEquiv.restrictScalars, RingEquiv.toEquiv_eq_coe,
      MonoidHom.coe_mk, OneHom.coe_mk, AlgEquiv.coe_mk, EquivLike.coe_coe, AlgEquiv.coe_ringEquiv]
  right_inv := by
    intro x
    apply AlgEquiv.ext
    intro y
    simp?  [AlgEquiv.restrictScalarsHom, AlgEquiv.restrictScalars]
  map_mul' := (AlgEquiv.restrictScalarsHom F S A).map_mul'
