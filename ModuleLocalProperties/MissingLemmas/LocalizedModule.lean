/-
Copyright (c) 2024 Yi Song. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yi Song
-/
import Mathlib.Algebra.Module.Submodule.Localization

open Submodule IsLocalizedModule LocalizedModule Ideal IsLocalization TensorProduct

example {R : Type*} [CommRing R] (S : Submonoid R) {M N : Type*} [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] [Module (Localization S) N] [IsScalarTower R (Localization S) N]
  (f : M →ₗ[R] N) : LocalizedModule S M →ₗ[Localization S] N := sorry



/-
example {R : Type*} (M N : Type*) [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N]
    [Module R N] (S : Submonoid R) : IsLocalizedModule S (LocalizedModule.map S M N) := sorry

#check quotEquivOfEq

lemma Equiv1 {R : Type u} [CommSemiring R] (S : Submonoid R) (a : R × S) (b : R × S) : LocalizedModule.r S R a b ↔ (OreLocalization.oreEqv S R).r a b := by
  show (∃ (u : S), u • b.2 • a.1 = u • a.2 • b.1) ↔ ∃ (u : S) (v : R), u • b.1 = v • a.1 ∧ u * b.2 = v * a.2
  rcases a with ⟨x, ⟨y, hy⟩⟩
  rcases b with ⟨z, ⟨w, hw⟩⟩
  dsimp
  constructor
  all_goals intro h
  · rcases h with ⟨⟨u, hu⟩ , h⟩
    use ⟨u * y, S.mul_mem' hu hy⟩ , u * w
    dsimp at *
    rw[← mul_assoc,← mul_assoc] at h
    constructor
    · exact h.symm
    · ring
  · rcases h with ⟨⟨u, hu⟩, v, h1, h2⟩
    use ⟨u * w, S.mul_mem' hu hw⟩
    dsimp at *
    nth_rw 1 [h2,mul_assoc, ← mul_assoc y, mul_comm, mul_assoc, mul_comm x, ← h1]
    ring

lemma Equiv2 {R : Type u} [CommSemiring R] (S : Submonoid R) (a : R × S) (b : R × S) : (LocalizedModule.r.setoid S R).r a b ↔ (OreLocalization.oreEqv S R).r a b := Equiv1 _

def Equiv4 {R : Type u} [CommSemiring R] (S : Submonoid R) : LocalizedModule S R ≃+* Localization S where
  toFun := sorry
  invFun := sorry
  left_inv := sorry
  right_inv := sorry
  map_mul' := sorry
  map_add' := sorry

def Equiv3 {R : Type u} [CommSemiring R] (S : Submonoid R) : Localization S  ≃+* LocalizedModule S R := by
  let e := Equiv.refl (R × S)
  let eq := fun (a : (R × S)) b => (Equiv2 S a b).symm
  let r := (LocalizedModule.r.setoid S R)
  let s := (OreLocalization.oreEqv S R)
  let a := @Quotient.congr_mk s r e eq
  exact {
  @Quotient.congr s r (Equiv.refl _) eq
  with
  map_mul' := by
    rintro ⟨x⟩ ⟨y⟩

    sorry
  map_add' := by
    rintro ⟨x⟩ ⟨y⟩

    sorry
}
variable  {R : Type u} [CommSemiring R] (S : Submonoid R)
#synth CommSemiring (LocalizedModule S R)
 -/
