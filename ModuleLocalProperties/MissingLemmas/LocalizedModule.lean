/-
Copyright (c) 2024 Yi Song. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yi Song
-/
import Mathlib.Algebra.Module.Submodule.Localization

import ModuleLocalProperties.Defs

import ModuleLocalProperties.MissingLemmas.Units

open Submodule TensorProduct LocalizedModule

section LiftOnLocalization

variable {R : Type*} [CommRing R] (S : Submonoid R) {M N : Type*} [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] [Module (Localization S) N] [IsScalarTower R (Localization S) N]

def inv (s : S) : Module.End R N where
  toFun := fun n => (Localization.mk 1 s) • n
  map_add' := smul_add _
  map_smul' := smul_comm _

lemma right_inv (s : S) : (algebraMap R (Module.End R N)) s * inv S s = 1 := by
  ext n
  rw [LinearMap.mul_apply, Module.algebraMap_end_apply, LinearMap.one_apply, inv]
  dsimp
  rw [← smul_assoc, Localization.smul_mk, smul_eq_mul, mul_one, Localization.mk_eq_monoidOf_mk',
    Submonoid.LocalizationMap.mk'_self', one_smul]

lemma left_inv (s : S) : inv S s * (algebraMap R (Module.End R N)) s = 1 := by
  ext n
  rw [LinearMap.mul_apply, Module.algebraMap_end_apply, LinearMap.one_apply, inv]
  dsimp
  rw [smul_comm, ← smul_assoc, Localization.smul_mk, smul_eq_mul, mul_one,
    Localization.mk_eq_monoidOf_mk', Submonoid.LocalizationMap.mk'_self', one_smul]

lemma invertible (s : S) : IsUnit ((algebraMap R (Module.End R N)) s) :=
   isUnit_iff_exists.mpr ⟨(inv _ s), ⟨right_inv _ _, left_inv _ _⟩⟩

lemma isinv (s : S) : (invertible S s).unit⁻¹.val = inv S s (N := N) :=
  unit_inv_eq_of_both (left_inv _ _) (right_inv _ _)

variable (f : M →ₗ[R] N)

noncomputable def LiftOnLocalization' : LocalizedModule S M →ₗ[R] N where
    toFun := lift S f <| invertible _
    map_add' := map_add _
    map_smul' := map_smul _

lemma LiftOnLocalization'_mk (m : M) (s : S) :
    (LiftOnLocalization' S f) (mk m s) = Localization.mk 1 s • f m := by
  show (lift S f <| invertible _) (mk m s) = Localization.mk 1 s • f m
  rw [LocalizedModule.lift_mk, isinv]
  rfl

lemma LiftOnLocalization'_comp : LiftOnLocalization' S f ∘ₗ mkLinearMap S M = f :=
  LocalizedModule.lift_comp _ _ <| invertible _

lemma LiftOnLocalization'_unique (g : LocalizedModule S M →ₗ[R] N)
    (h : g ∘ₗ mkLinearMap S M = f) : LiftOnLocalization' S f = g :=
  LocalizedModule.lift_unique S f (invertible _) g h


noncomputable def LiftOnLocalization : LocalizedModule S M →ₗ[Localization S] N
  := LinearMap.extendScalarsOfIsLocalization S _ (LiftOnLocalization' _ f)

lemma LiftOnLocalization_mk (m : M) (s : S) :
    (LiftOnLocalization S f) (mk m s) = Localization.mk 1 s • f m :=
  LiftOnLocalization'_mk _ _ _ _

lemma LiftOnLocalization_comp : LiftOnLocalization S f ∘ mkLinearMap S M = f := by
  nth_rw 2 [← LiftOnLocalization'_comp S f]
  rw [LinearMap.coe_comp]
  rfl

lemma LiftOnLocalization_unique (g : LocalizedModule S M →ₗ[R] N)
    (h : g ∘ₗ mkLinearMap S M = f) : LiftOnLocalization S f = g :=
  LiftOnLocalization'_unique S f g h

end LiftOnLocalization

section LocalizedMapSubmodule

variable {R : Type*} [CommRing R] (S : Submonoid R) {M N : Type*}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

noncomputable def LocalizedModule.map' :
    (M →ₗ[R] N) →ₗ[R] LocalizedModule S M →ₗ[Localization S] LocalizedModule S N where
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

noncomputable def LocalizedMapLift : LocalizedModule S (M →ₗ[R] N) →ₗ[Localization S]
    LocalizedModule S M →ₗ[Localization S] LocalizedModule S N :=
  LiftOnLocalization _ (M := (M →ₗ[R] N))
  (N := LocalizedModule S M →ₗ[Localization S] LocalizedModule S N)
  <| LocalizedModule.map' _

lemma injective_LocalizedMapLift: Function.Injective (α := LocalizedModule S (M →ₗ[R] N))
    (LocalizedMapLift S) := sorry

end LocalizedMapSubmodule
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
