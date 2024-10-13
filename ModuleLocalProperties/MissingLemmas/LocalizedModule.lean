/-
Copyright (c) 2024 Yi Song. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yi Song
-/
import Mathlib.Algebra.Module.Submodule.Localization

import ModuleLocalProperties.Defs

import ModuleLocalProperties.MissingLemmas.Units

open Submodule TensorProduct LocalizedModule

section liftOnLocalizationModule

namespace LocalizedModule

variable {R : Type*} [CommSemiring R] (S : Submonoid R) {M N : Type*} [AddCommMonoid M] [Module R M]
    [AddCommMonoid N] [Module R N] [Module (Localization S) N] [IsScalarTower R (Localization S) N]
    (f : M →ₗ[R] N)

lemma Localization.mk_cancel (r : R) (s t : S) : Localization.mk (r * t) (s * t) = Localization.mk r s :=by
  rw[Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  use 1
  dsimp
  ring

lemma Localization.smul_mk_den_mul (r : R) (s t : S) : t • (Localization.mk r (s * t)) = Localization.mk r s := by
  show (t : R) • (Localization.mk r (s * t)) = Localization.mk r s
  rw [Localization.smul_mk, smul_eq_mul, mul_comm, Localization.mk_cancel]

lemma wd_for_LiftOnLocalizationModule' (a b : M × S) (h : r S M a b): Localization.mk 1 a.2 • f a.1 = Localization.mk 1 b.2 • f b.1 := by
  rcases h with ⟨u, h⟩
  repeat rw[← smul_assoc ,smul_eq_mul] at h
  rw [← Localization.smul_mk_den_mul (t := (u * b.2)), smul_assoc, smul_comm,
    ← LinearMap.CompatibleSMul.map_smul, h, ← mul_assoc]
  symm
  rw [← Localization.smul_mk_den_mul (t := (u * a.2)), smul_assoc, smul_comm,
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
    rw [← Localization.smul_mk_den_mul (t := t), smul_assoc, smul_comm, ← LinearMap.CompatibleSMul.map_smul]
    rw [← Localization.smul_mk_den_mul 1 t (t := s), smul_assoc, smul_comm,
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

lemma mk_right_smul_mk (m : M) (s t : S) : Localization.mk 1 s • mk m t = mk m (s * t) := by
  rw[mk_smul_mk, one_smul]

lemma mk_right_smul_mk_den_one (m : M) (s : S) : Localization.mk 1 s • mk m 1 = mk m s := by
  rw[mk_right_smul_mk, mul_one]

lemma mk_add_mk_right (m n : M) (s : S) : mk (m + n) s = mk m s + mk n s :=by
  rw[mk_add_mk, ← smul_add, mk_cancel_common_right]


lemma LiftOnLocalizationModule'_unique (g : LocalizedModule S M →ₗ[R] N)
    (h : g ∘ₗ mkLinearMap S M = f) : LiftOnLocalizationModule' S f = g := by
  ext x
  induction' x with m s
  rw [LiftOnLocalizationModule'_mk, ← h]
  rw [LinearMap.coe_comp, Function.comp_apply,
    mkLinearMap_apply, ← mk_right_smul_mk_den_one (s := s)]
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

end LocalizedModule

section LocalizedModule.map'

namespace LocalizedModule

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
end LocalizedModule
section LocalizedModule.maplift
-- This is LocalizedModule.map and LocalizedModule.map' with out using IsLocalizedModule.map
namespace LocalizedModule

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
    mkLinearMap_apply, ← mk_right_smul_mk_den_one (s := s)]

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

end LocalizedModule

section LocalizedMapLift

namespace LocalizedModule

variable {R : Type*} [CommSemiring R] (S : Submonoid R) {M N : Type*}
    [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
/-
noncomputable def {R : Type*} [CommSemiring R] (S : Submonoid R) {M N : Type*}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] map' :
    (M →ₗ[R] N) →ₗ[R] LocalizedModule S M →ₗ[Localization S] LocalizedModule S N where
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
-/
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

end LocalizedModule

/-
example {R : Type*} (M N : Type*) [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N]
    [Module R N] (S : Submonoid R) : IsLocalizedModule S (LocalizedModule.map S M N) := sorry
-/
section Localization_is_LocalizedModule

namespace LocalizedModule

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
    r S R a b ↔ (OreLocalization.oreEqv S R).r a b := by
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
    show mk r 1 = (algebraMap (Localization S) (LocalizedModule S R)).comp (algebraMap R (Localization S)) r
    simp only [RingHom.coe_comp, Function.comp_apply]
    rw[← Localization.mk_algebraMap]
    simp only [Algebra.id.map_eq_id, RingHom.id_apply]
    rw [algebraMap_mk]
    simp only [Algebra.id.map_eq_id, RingHom.id_apply]


lemma Map_surj : Function.Surjective (Map0 S) := by
  intro b
  apply induction_on (β := fun b => ∃ a, Map0 S a = b)
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

lemma mk_eq_zero_iff {M : Type*} [AddCommGroup M] [Module R M] (m : M) (s : S) :
    mk m s = 0 ↔ ∃ c : S, c • m = 0 := by
  rw[← zero_mk s, mk_eq]
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
  rw[Localization.liftOn_mk, mk_eq_zero_iff] at h
  rw[Localization.mk_eq_zero_iff]
  rcases h with ⟨c, h⟩
  exact ⟨c, h⟩

noncomputable def Map' : Localization S ≃ₐ[R] LocalizedModule S R :=
  AlgEquiv.ofBijective (Map0 S) ⟨Map_inj _,Map_surj _⟩

end LocalizedModule
