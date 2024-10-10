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

variable {R : Type*} [CommSemiring R] (S : Submonoid R) {M N : Type*} [AddCommGroup M] [Module R M]
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

section LocalizedMapLift
#check CommSemiring
variable {R : Type*} [CommSemiring R] (S : Submonoid R) {M N : Type*}
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

end LocalizedMapLift
#check Localization.liftOn
#check Localization.rec
section Localization_is_LocalizedModule
variable {R : Type*} [CommRing R] (S : Submonoid R)

def Localization.mkLinearMap : R →ₗ[R] Localization S where
  toFun := fun m => Localization.mk m (1 : S)
  map_add' := by
    intro x y
    dsimp
    rw[Localization.add_mk,add_comm, OneMemClass.coe_one, one_mul, one_mul, one_mul]
  map_smul' := by
    intro x y
    dsimp
    rw[Localization.smul_mk, smul_eq_mul]

#check LiftOnLocalization' S <| Localization.mkLinearMap S
#check AlgEquiv.ofBijective


end Localization_is_LocalizedModule
/-
example {R : Type*} (M N : Type*) [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N]
    [Module R N] (S : Submonoid R) : IsLocalizedModule S (LocalizedModule.map S M N) := sorry
-/
#check quotEquivOfEq
#check List.TFAE
variable {R : Type*} [CommRing R] (S : Submonoid R)

lemma equiv (a b : R × S) : r S R a b ↔ Localization.r S a b :=by
  show (∃ (u : S), u • b.2 • a.1 = u • a.2 • b.1) ↔ Localization.r S a b
  rw[Localization.r_iff_exists]
  constructor
  all_goals intro ⟨c, h⟩
  · use c
    repeat rw[← smul_assoc, smul_eq_mul] at h
    repeat rw[← mul_assoc]
    exact h
  · use c
    repeat rw[← smul_assoc, smul_eq_mul]
    repeat rw[← mul_assoc] at h
    exact h

lemma equiv1 (a b : R × S) :
    LocalizedModule.r S R a b ↔ (OreLocalization.oreEqv S R).r a b := by
  show (∃ (u : S), u • b.2 • a.1 = u • a.2 • b.1) ↔
    ∃ (u : S) (v : R), u • b.1 = v • a.1 ∧ u * b.2 = v * a.2
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



lemma equiv_tafe (a b : R × S) : [r S R a b, Localization.r S a b, (OreLocalization.oreEqv S R).r a b,
    Localization.r' S a b].TFAE := by
  apply List.tfae_of_forall (Localization.r S a b)

  simp only [List.mem_cons, List.not_mem_nil]
  rintro p (h | h | h | h | h)
  rw[h, equiv]
  rw[h]
  rw[h, Localization.r_iff_oreEqv_r]
  rw[h, Localization.r_eq_r']
  contradiction

lemma forliftOn {a c : R} {b d : S} (h : (Localization.r S) (a, b) (c, d)) : mk a b = mk c d := by
  rw [← equiv] at h
  exact mk_eq.mpr h

def Map0 : Localization S →ₐ[R] LocalizedModule S R where
  toFun := fun x => Localization.liftOn x mk <| fun h => forliftOn _ h
  map_one' := by
    dsimp
    rw[← Localization.mk_one]
    rfl
  map_mul' := by
    intro x y
    dsimp
    apply Localization.induction_on₂ (p := fun (x : Localization S) y => (x * y).liftOn LocalizedModule.mk _ = x.liftOn LocalizedModule.mk _ * y.liftOn LocalizedModule.mk _)
    intro x y
    rw [Localization.mk_mul]
    repeat rw [Localization.liftOn_mk]
    rw [mk_mul_mk]
  map_zero' := by
    dsimp
    rw[← Localization.mk_zero]
    apply Localization.liftOn_mk
  map_add' := by
    intro x y
    dsimp
    apply Localization.induction_on₂ (p := fun (x : Localization S) y => (x + y).liftOn LocalizedModule.mk _ = x.liftOn LocalizedModule.mk _ + y.liftOn LocalizedModule.mk _)
    intro x y
    rw [Localization.add_mk]
    repeat rw [Localization.liftOn_mk]
    rw [mk_add_mk]
    congr 1
    rw[mul_comm,add_comm]
    nth_rw 2 [mul_comm]
    rfl
  commutes' := by
    intro r
    dsimp
    rw[← Localization.mk_algebraMap]
    simp only [Algebra.id.map_eq_id, RingHom.id_apply, Localization.mk_eq_monoidOf_mk',
      Localization.liftOn_mk']
    show LocalizedModule.mk r 1 = (algebraMap (Localization S) (LocalizedModule S R)).comp (algebraMap R (Localization S)) r
    simp only [RingHom.coe_comp, Function.comp_apply]
    rw[← Localization.mk_algebraMap]
    simp only [Algebra.id.map_eq_id, RingHom.id_apply]
    rw [LocalizedModule.algebraMap_mk]
    simp only [Algebra.id.map_eq_id, RingHom.id_apply]


lemma Map_surj : Function.Surjective (Map0 S) := by
  intro b
  apply LocalizedModule.induction_on (β := fun b => ∃ a, Map0 S a = b)
  intro r s
  use Localization.mk r s
  show (Localization.mk r s).liftOn mk (fun h => forliftOn _ h) = mk r s
  apply Localization.liftOn_mk

lemma Localization.mk_eq_zero_iff (r : R) (s : S) : Localization.mk r s = 0 ↔ ∃ c : S, c * r = 0 :=by
  rw[← Localization.mk_zero s, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  constructor
  all_goals intro h
  · rcases h with ⟨c, h⟩
    dsimp only at h
    rw[mul_zero, mul_zero, ← mul_assoc, ← Submonoid.coe_mul] at h
    use c * s
  · rcases h with ⟨c, h⟩
    use c
    dsimp only
    rw[mul_zero, mul_zero, mul_comm s.val, ← mul_assoc, h, zero_mul]

lemma LocalizedModule.mk_eq_zero_iff {M : Type*} [AddCommGroup M] [Module R M] (m : M) (s : S) :
    LocalizedModule.mk m s = 0 ↔ ∃ c : S, c • m = 0 := by
  rw[← LocalizedModule.zero_mk s, LocalizedModule.mk_eq]
  constructor
  all_goals intro ⟨c, h⟩
  · rw [smul_zero, smul_zero, ← smul_assoc, smul_eq_mul] at h
    exact ⟨c * s, h⟩
  · use c
    rw [smul_zero, smul_zero, smul_comm, h, smul_zero]

lemma Map_inj : Function.Injective (Map0 S) := by
  rw[injective_iff_map_eq_zero]
  intro x
  apply Localization.induction_on (p := fun x => (Map0 S) x = 0 → x = 0)
  intro x h
  change (Localization.mk x.1 x.2).liftOn mk (fun h => forliftOn _ h) = 0 at h
  rw[Localization.liftOn_mk, LocalizedModule.mk_eq_zero_iff] at h
  rw[Localization.mk_eq_zero_iff]
  rcases h with ⟨c, h⟩
  exact ⟨c, h⟩

noncomputable def Map1 : Localization S ≃ₐ[R] LocalizedModule S R :=
  AlgEquiv.ofBijective (Map0 S) ⟨Map_inj _,Map_surj _⟩
