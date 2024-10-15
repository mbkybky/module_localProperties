/-
Copyright (c) 2024 Yi Song. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yi Song
-/
import Mathlib.Algebra.Module.Submodule.Localization

import ModuleLocalProperties.Defs

import ModuleLocalProperties.MissingLemmas.Units --unsed for lift.LiftOnLocalization'

open Submodule TensorProduct LocalizedModule

namespace LocalizedModule

--some usable lemma with mk

section mk_eq_lemma

variable {R : Type*} [CommSemiring R] (S : Submonoid R) {M : Type*} [AddCommMonoid M] [Module R M]

lemma Localization.mk_cancel (r : R) (s t : S) : Localization.mk (r * t) (s * t) = Localization.mk r s :=by
  rw[Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  use 1
  dsimp
  ring

lemma Localization.smul_mk_right_mul (r : R) (s t : S) : t • (Localization.mk r (s * t)) = Localization.mk r s := by
  show (t : R) • (Localization.mk r (s * t)) = Localization.mk r s
  rw [Localization.smul_mk, smul_eq_mul, mul_comm, Localization.mk_cancel]

lemma mk_right_smul_mk (m : M) (s t : S) : Localization.mk 1 s • mk m t = mk m (s * t) := by
  rw[mk_smul_mk, one_smul]

lemma mk_right_smul_mk_left (m : M) (s : S) : Localization.mk 1 s • mk m 1 = mk m s := by
  rw[mk_right_smul_mk, mul_one]

lemma mk_add_mk_right (m n : M) (s : S) : mk (m + n) s = mk m s + mk n s :=by
  rw[mk_add_mk, ← smul_add, mk_cancel_common_right]

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

lemma mk_eq_zero_iff {M : Type*} [AddCommGroup M] [Module R M] (m : M) (s : S) :
    mk m s = 0 ↔ ∃ c : S, c • m = 0 := by
  rw[← zero_mk s, mk_eq]
  constructor
  all_goals intro ⟨c, h⟩
  · rw [smul_zero, smul_zero, ← smul_assoc, smul_eq_mul] at h
    exact ⟨c * s, h⟩
  · use c
    rw [smul_zero, smul_zero, smul_comm, h, smul_zero]

end mk_eq_lemma

--use f : M → N to define the fuction f : S⁻¹M → N when N is S⁻¹R module

section liftOnLocalizationModule
-- the definition from liftOn which is computable
variable {R : Type*} [CommSemiring R] (S : Submonoid R) {M N : Type*} [AddCommMonoid M] [Module R M]
    [AddCommMonoid N] [Module R N] [Module (Localization S) N] [IsScalarTower R (Localization S) N]
    (f : M →ₗ[R] N)

lemma wd_for_LiftOnLocalizationModule' (a b : M × S) (h : r S M a b): Localization.mk 1 a.2 • f a.1 = Localization.mk 1 b.2 • f b.1 := by
  rcases h with ⟨u, h⟩
  repeat rw[← smul_assoc ,smul_eq_mul] at h
  rw [← Localization.smul_mk_right_mul (t := (u * b.2)), smul_assoc, smul_comm,
    ← LinearMap.CompatibleSMul.map_smul, h, ← mul_assoc]
  symm
  rw [← Localization.smul_mk_right_mul (t := (u * a.2)), smul_assoc, smul_comm,
    ← LinearMap.CompatibleSMul.map_smul, mul_comm, mul_comm a.2]

def LiftOnLocalizationModule' : LocalizedModule S M →ₗ[R] N where
  toFun := fun x => liftOn x (fun (m, s) => (Localization.mk 1 s) • f m)
    (fun a b h => wd_for_LiftOnLocalizationModule' _ _ _ _ h)
  map_add' := by
    dsimp
    intro x y
    induction' x with m s
    induction' y with n t
    rw [mk_add_mk, liftOn_mk, liftOn_mk, liftOn_mk, f.map_add]
    symm
    rw [← Localization.smul_mk_right_mul (t := t), smul_assoc, smul_comm, ← LinearMap.CompatibleSMul.map_smul]
    rw [← Localization.smul_mk_right_mul 1 t (t := s), smul_assoc, smul_comm,
      ← LinearMap.CompatibleSMul.map_smul f s, mul_comm, smul_add]
  map_smul' := by
    dsimp
    intro r x
    refine induction_on ?_ x
    intro m s
    rw[smul'_mk, liftOn_mk, liftOn_mk, f.map_smul, smul_comm]

lemma LiftOnLocalizationModule'_mk (m : M) (s : S) :
    (LiftOnLocalizationModule' S f) (mk m s) = Localization.mk 1 s • f m := by
  show (mk m s).liftOn _ (fun a b h => wd_for_LiftOnLocalizationModule' _ _ _ _ h) = Localization.mk 1 s • f m
  simp_rw [liftOn_mk]

lemma LiftOnLocalizationModule'_comp : LiftOnLocalizationModule' S f ∘ₗ mkLinearMap S M = f := by
  ext m
  dsimp
  rw[LiftOnLocalizationModule'_mk, Localization.mk_one, one_smul]

lemma LiftOnLocalizationModule'_unique (g : LocalizedModule S M →ₗ[R] N)
    (h : g ∘ₗ mkLinearMap S M = f) : LiftOnLocalizationModule' S f = g := by
  ext x
  induction' x with m s
  rw [LiftOnLocalizationModule'_mk, ← h]
  rw [LinearMap.coe_comp, Function.comp_apply,
    mkLinearMap_apply, ← mk_right_smul_mk_left (s := s)]
  repeat rw [← LinearMap.extendScalarsOfIsLocalization_apply' S (Localization S) g]
  rw [map_smul]

def LiftOnLocalizationModule : LocalizedModule S M →ₗ[Localization S] N :=
  LinearMap.extendScalarsOfIsLocalization S _ (LiftOnLocalizationModule' _ f)

lemma LiftOnLocalizationModule_mk (m : M) (s : S) :
    (LiftOnLocalizationModule S f) (mk m s) = Localization.mk 1 s • f m :=
  LiftOnLocalizationModule'_mk _ _ _ _

lemma LiftOnLocalizationModule_comp : LiftOnLocalizationModule S f ∘ mkLinearMap S M = f := by
  nth_rw 2 [← LiftOnLocalizationModule'_comp S f]
  rw [LinearMap.coe_comp]
  rfl

lemma LiftOnLocalizationModule_unique (g : LocalizedModule S M →ₗ[R] N)
    (h : g ∘ₗ mkLinearMap S M = f) : LiftOnLocalizationModule' S f = g :=
  LiftOnLocalizationModule'_unique S f g h

section lift.LiftOnLocalizationModule'
--the section for definition from lift
def lift.inv (s : S) : Module.End R N where
  toFun := fun n => (Localization.mk 1 s) • n
  map_add' := smul_add _
  map_smul' := smul_comm _

lemma lift.right_inv (s : S) : (algebraMap R (Module.End R N)) s * inv S s = 1 := by
  ext n
  rw [LinearMap.mul_apply, Module.algebraMap_end_apply, LinearMap.one_apply, inv]
  dsimp
  rw [← smul_assoc, Localization.smul_mk, smul_eq_mul, mul_one, Localization.mk_eq_monoidOf_mk',
    Submonoid.LocalizationMap.mk'_self', one_smul]

lemma lift.left_inv (s : S) : inv S s * (algebraMap R (Module.End R N)) s = 1 := by
  ext n
  rw [LinearMap.mul_apply, Module.algebraMap_end_apply, LinearMap.one_apply, inv]
  dsimp
  rw [smul_comm, ← smul_assoc, Localization.smul_mk, smul_eq_mul, mul_one,
    Localization.mk_eq_monoidOf_mk', Submonoid.LocalizationMap.mk'_self', one_smul]

lemma lift.invertible (s : S) : IsUnit ((algebraMap R (Module.End R N)) s) :=
   isUnit_iff_exists.mpr ⟨(inv _ s), ⟨right_inv _ _, left_inv _ _⟩⟩

lemma lift.isinv (s : S) : (invertible S s).unit⁻¹.val = inv S s (N := N) :=
  unit_inv_eq_of_both (left_inv _ _) (right_inv _ _)

noncomputable def lift.LiftOnLocalizationModule' : LocalizedModule S M →ₗ[R] N where
    toFun := lift S f <| invertible _
    map_add' := map_add _
    map_smul' := map_smul _

lemma lift.LiftOnLocalizationModule'_mk (m : M) (s : S) :
    (lift.LiftOnLocalizationModule' S f) (mk m s) = Localization.mk 1 s • f m := by
  show (lift S f <| invertible _) (mk m s) = Localization.mk 1 s • f m
  rw [LocalizedModule.lift_mk, isinv]
  rfl


lemma LiftOnLocalization'_eq : LiftOnLocalizationModule' S f = lift.LiftOnLocalizationModule' S f := by
  ext x
  induction' x with m s
  rw [lift.LiftOnLocalizationModule'_mk, LiftOnLocalizationModule'_mk]

end lift.LiftOnLocalizationModule'

end liftOnLocalizationModule

section LocalizedModule.map'

variable {R : Type*} [CommSemiring R] (S : Submonoid R) {M N : Type*}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

noncomputable def map' : (M →ₗ[R] N) →ₗ[R] LocalizedModule S M →ₗ[Localization S] LocalizedModule S N where
  toFun := fun f => LinearMap.extendScalarsOfIsLocalization S _ <| map S f
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

section LocalizedModule.mapfromlift
-- This is LocalizedModule.map and LocalizedModule.map' with out using IsLocalizedModule.map

variable {R : Type*} [CommSemiring R] (S : Submonoid R) {M N : Type*}
    [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]

noncomputable def mapfromlift' : (M →ₗ[R] N) →ₗ[R] LocalizedModule S M →ₗ[R] LocalizedModule S N where
  toFun := fun f => LiftOnLocalizationModule' S <| mkLinearMap S N ∘ₗ f
  map_add' := by
    intro f g
    dsimp
    ext x
    induction' x with m s
    rw [LinearMap.add_apply]
    simp only [LiftOnLocalizationModule'_mk, LinearMap.coe_comp, Function.comp_apply,
      LinearMap.add_apply, map_add, smul_add]
  map_smul' := by
    intro r f
    dsimp
    ext x
    induction' x with m s
    simp only [LiftOnLocalizationModule'_mk, LinearMap.coe_comp,
      Function.comp_apply, LinearMap.smul_apply, map_smul]
    rw[smul_comm]

lemma mapfromlift'_mk (f : M →ₗ[R] N) (m : M) (s : S) : mapfromlift' S f (mk m s) = mk (f m) s := by
  show (LiftOnLocalizationModule' S (mkLinearMap S N ∘ₗ f)) (mk m s) = mk (f m) s
  rw[LiftOnLocalizationModule'_mk, LinearMap.coe_comp, Function.comp_apply,
    mkLinearMap_apply, ← mk_right_smul_mk_left (s := s)]

noncomputable def mapfromlift :
    (M →ₗ[R] N) →ₗ[R] LocalizedModule S M →ₗ[Localization S] LocalizedModule S N where
  toFun := fun f => LinearMap.extendScalarsOfIsLocalization S _ <| mapfromlift' S f
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

lemma mapfromlift_mk (f : M →ₗ[R] N) (m : M) (s : S) : mapfromlift S f (mk m s) = mk (f m) s :=
  mapfromlift'_mk _ _ _ _

end LocalizedModule.mapfromlift

section eq_theorem_of_my_definition

variable {R : Type*} [CommSemiring R] (S : Submonoid R) {M N : Type*}
    [AddCommMonoid M] [Module R M] [AddCommGroup N] [Module R N]


end eq_theorem_of_my_definition

section LocalizedMapLift

variable {R : Type*} [CommSemiring R] (S : Submonoid R) {M N : Type*}
    [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]

noncomputable def LocalizedMapLift' : LocalizedModule S (M →ₗ[R] N) →ₗ[R]
    LocalizedModule S M →ₗ[R] LocalizedModule S N := LiftOnLocalizationModule' _ (M := (M →ₗ[R] N))
  (N := LocalizedModule S M →ₗ[R] LocalizedModule S N)
  <| mapfromlift' _

lemma LocalizedMapLift'_mk (f : M →ₗ[R] N) (m : M) (s t : S) :
    LocalizedMapLift' S (mk f s) (mk m t) = mk (f m) (s * t) := by
  unfold LocalizedMapLift'
  rw [LiftOnLocalizationModule'_mk, LinearMap.smul_apply, mapfromlift'_mk, mk_right_smul_mk]

noncomputable def LocalizedMapLift : LocalizedModule S (M →ₗ[R] N) →ₗ[Localization S]
    LocalizedModule S M →ₗ[Localization S] LocalizedModule S N :=
  LiftOnLocalizationModule _ (M := (M →ₗ[R] N))
  (N := LocalizedModule S M →ₗ[Localization S] LocalizedModule S N)
  <| mapfromlift _

lemma LocalizedMapLift_mk (f : M →ₗ[R] N) (m : M) (s t : S) :
    LocalizedMapLift S (mk f s) (mk m t) = mk (f m) (s * t) := by
  unfold LocalizedMapLift
  rw [LiftOnLocalizationModule_mk, LinearMap.smul_apply, mapfromlift_mk, mk_right_smul_mk]

end LocalizedMapLift

--to make a algebraequiv between Localzation S and LocalzedModule S R

section Localization_is_LocalizedModule

namespace Localization

variable {R : Type*} [CommSemiring R] (S : Submonoid R)

lemma r_iff_Localization_r (a b : R × S) : r S R a b ↔ Localization.r S a b :=by
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

lemma mk_eq_iff_Localization_mk_eq (a b : R × S) :
    mk a.1 a.2 = mk b.1 b.2 ↔ Localization.mk a.1 a.2 = Localization.mk b.1 b.2 := by
  rw[mk_eq, Localization.mk_eq_mk_iff, ← r_iff_Localization_r, r]

lemma r_tafe (a b : R × S) : [r S R a b, Localization.r S a b, (OreLocalization.oreEqv S R).r a b,
    Localization.r' S a b].TFAE := by
  apply List.tfae_of_forall (Localization.r S a b)
  simp only [List.mem_cons, List.not_mem_nil]
  rintro p (h | h | h | h | h)
  rw[h, r_iff_Localization_r]
  rw[h]
  rw[h, Localization.r_iff_oreEqv_r]
  rw[h, Localization.r_eq_r']
  contradiction

lemma forliftOn {a c : R} {b d : S} (h : (Localization.r S) (a, b) (c, d)) : mk a b = mk c d := by
  rw [← r_iff_Localization_r] at h
  exact mk_eq.mpr <| h

def Map : Localization S →ₐ[R] LocalizedModule S R where
  toFun := fun x => Localization.liftOn x mk <| fun h => forliftOn _ h
  map_one' := by
    dsimp
    rw[← Localization.mk_one]
    rfl
  map_mul' := by
    intro x y
    dsimp
    induction' x with a
    induction' y with b
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
    induction' x with a
    induction' y with b
    rw [Localization.add_mk]
    repeat rw [Localization.liftOn_mk]
    rw [mk_add_mk]
    congr 1
    rw[mul_comm,add_comm,mul_comm b.1]
    rfl
  commutes' := by
    intro r
    dsimp
    rw[← Localization.mk_algebraMap, Algebra.id.map_eq_id, RingHom.id_apply,
      Localization.mk_eq_monoidOf_mk', Localization.liftOn_mk']
    show mk r 1 =
      (algebraMap (Localization S) (LocalizedModule S R)).comp (algebraMap R (Localization S)) r
    rw [RingHom.coe_comp, Function.comp_apply, ← Localization.mk_algebraMap, Algebra.id.map_eq_id,
      RingHom.id_apply, algebraMap_mk, Algebra.id.map_eq_id, RingHom.id_apply]

lemma Map_mk (r : R) (s : S) : Map S (Localization.mk r s) = mk r s := rfl

lemma Map_surj : Function.Surjective (Map S) := by
  intro x
  induction' x with r s
  exact ⟨Localization.mk r s, Map_mk S r s⟩

lemma Map_inj : Function.Injective (Map S) := by
  intro x y
  induction' x with a
  induction' y with b
  rw [Map_mk, Map_mk, mk_eq_iff_Localization_mk_eq, imp_self]
  trivial

noncomputable def Equiv : Localization S ≃ₐ[R] LocalizedModule S R :=
  AlgEquiv.ofBijective (Map S) ⟨Map_inj _,Map_surj _⟩

lemma Equiv_mk (r : R) (s : S) : Equiv S (Localization.mk r s) = mk r s := rfl

lemma Equiv_symm_mk (r : R) (s : S) : (Equiv S).symm (mk r s) = Localization.mk r s :=
  (AlgEquiv.symm_apply_eq (Equiv S)).mpr rfl

end Localization
