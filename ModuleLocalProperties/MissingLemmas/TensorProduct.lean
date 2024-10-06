import Mathlib.RingTheory.Flat.Basic

import ModuleLocalProperties.Finite_presented

open Submodule IsLocalizedModule LocalizedModule Ideal IsLocalization TensorProduct

noncomputable def Map1 {R : Type*} (M N : Type*) [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] (S : Submonoid R) :
M →ₗ[R] N →ₗ[R] LocalizedModule S (M ⊗[R] N) where
  toFun := fun m => {
      toFun := fun n => LocalizedModule.mk (m ⊗ₜ[R] n) 1
      map_add' := by
        intro n1 n2
        simp only [tmul_add, mk_add_mk, one_smul, mul_one]
      map_smul' := by
        intro r n
        simp only [tmul_smul, RingHom.id_apply, smul'_mk]
    }
  map_add' := by
    intro m1 m2
    ext n
    dsimp
    simp only [add_tmul, mk_add_mk, one_smul, mul_one]
  map_smul' := by
    intro r m
    ext n
    dsimp
    simp only [smul'_mk, smul_tmul']

noncomputable def Map2 {R : Type*} (M N : Type*) [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] (S : Submonoid R) :
M → LocalizedModule S N →ₗ[R] LocalizedModule S (M ⊗[R] N) :=by
  intro m
  use LocalizedModule.lift S (Map1 M N S m) (by
  intro x
  apply isUnit_iff_exists.mpr ⟨{
    toFun := sorry
    map_add' := sorry
    map_smul' := sorry
  }, sorry, sorry⟩
  )
  sorry




noncomputable def BiMap {R : Type*} (M N : Type*) [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] (S : Submonoid R) :
(LocalizedModule S M) →ₗ[Localization S] (LocalizedModule S N) →ₗ[Localization S] LocalizedModule S (M ⊗[R] N) where
  toFun := by
    intro x

    exact {
      toFun := sorry
      map_add' := sorry
      map_smul' := sorry
    }

  map_add' := sorry
  map_smul' := sorry

noncomputable def Map {R : Type*} (M N : Type*) [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] (S : Submonoid R) :
(LocalizedModule S M) ⊗[Localization S] (LocalizedModule S N) →ₗ[Localization S] LocalizedModule S (M ⊗[R] N) := sorry

noncomputable def Eqv {R : Type*} (M N : Type*) [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] (S : Submonoid R) :
(LocalizedModule S M) ⊗[Localization S] (LocalizedModule S N) ≃ₗ[Localization S] LocalizedModule S (M ⊗[R] N) := sorry

open LinearMap Submodule TensorProduct DirectSum

theorem Module.Flat.iff_isTensorProduct_lift_injective (R M : Type*) [CommRing R] [AddCommGroup M]
    [Module R M] :  Module.Flat R M ↔ ∀ (I : Ideal R) {N : Type*} [AddCommGroup N] [Module R N]
    (f : I →ₗ[R] M →ₗ[R] N) (h : IsTensorProduct f),
    Function.Injective (IsTensorProduct.lift h ((lsmul R M).comp I.subtype)) := sorry
