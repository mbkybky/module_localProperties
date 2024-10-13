/-
Copyright (c) 2024 Yongle Hu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongle Hu, Sihan Su
-/
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.IsTensorProduct

universe v' u v

namespace Module.Flat

open LinearMap Submodule TensorProduct DirectSum Module

section IsTensorProduct

variable (R : Type u) (M : Type v) [CommRing R] [AddCommGroup M] [Module R M]

lemma eqid (I : Ideal R) : (isTensorProduct R I M).equiv = LinearEquiv.refl R _ :=
  LinearEquiv.ext fun x ↦ congrFun (congrArg DFunLike.coe lift_mk) x

-- Proof of this lemma could be simplified by using `LinearMap.lid_comp_rTensor`.
lemma diagram (I : Ideal R) : (isTensorProduct R I M).lift (lsmul R M ∘ₗ Submodule.subtype I)
    = (TensorProduct.lid R M) ∘ₗ (rTensor M (Submodule.subtype I)) := by
  ext x m
  simp only [IsTensorProduct.lift, AlgebraTensorModule.curry_apply, curry_apply,
    LinearMap.coe_restrictScalars, restrictScalars_comp, coe_comp, LinearEquiv.coe_coe,
    Function.comp_apply, rTensor_tmul, coe_subtype, lid_tmul]
  rw [eqid, LinearEquiv.refl_symm, LinearEquiv.refl_apply, lift.tmul, coe_comp, coe_subtype,
    Function.comp_apply, lsmul_apply]

theorem iff_isTensorProduct_lift_injective : Module.Flat R M ↔ ∀ (I : Ideal R)
  {N : Type max u v} [AddCommGroup N] [Module R N] (f : I →ₗ[R] M →ₗ[R] N) (h : IsTensorProduct f),
    Function.Injective (IsTensorProduct.lift h ((lsmul R M).comp I.subtype)) := by
  constructor
  · intro H I N _ _ f tf
    have eq : (TensorProduct.lid R M).toLinearMap ∘ₗ (rTensor M (Submodule.subtype I)) ∘ₗ tf.equiv.symm.toLinearMap = (tf.lift (lsmul R M ∘ₗ Submodule.subtype I)) := by
      rw [← comp_assoc, ← diagram, IsTensorProduct.lift, IsTensorProduct.lift, eqid, LinearEquiv.refl_symm]; rfl
    simp only [← eq, coe_comp, LinearEquiv.coe_coe, EmbeddingLike.comp_injective,
      EquivLike.injective_comp]
    exact ((Module.Flat.iff_rTensor_injective' R M).mp H I)
  · intro H
    apply (Module.Flat.iff_rTensor_injective' R M).mpr
    intro I
    have := H I (TensorProduct.mk R I M) (isTensorProduct R I M)
    rw [diagram, coe_comp, LinearEquiv.coe_coe, EmbeddingLike.comp_injective] at this
    exact this

theorem iff_exist_isTensorProduct_lift_injective : Module.Flat R M ↔ ∀ (I : Ideal R) ,
    ∃ (N : Type max u v) (_ : AddCommGroup N) (_ : Module R N) (f : I →ₗ[R] M →ₗ[R] N)
    (h : IsTensorProduct f), Function.Injective (h.lift ((lsmul R M).comp I.subtype)) := by
  constructor
  · intro hf I
    use (I ⊗[R] M), inferInstance, inferInstance, (TensorProduct.mk R I M), (isTensorProduct R I M)
    have eq : (TensorProduct.lid R M).toLinearMap ∘ₗ (rTensor M (Submodule.subtype I)) =
        ((isTensorProduct R I M).lift (lsmul R M ∘ₗ Submodule.subtype I)) := by
      apply (lid_comp_rTensor M (Submodule.subtype I)).trans
      simpa only [IsTensorProduct.lift, eqid R M I] using by rfl
    rw [← eq]
    exact (EquivLike.comp_injective _ (TensorProduct.lid R M)).mpr <|
      (Module.Flat.iff_rTensor_injective' R M).mp hf I
  · intro H
    apply (Module.Flat.iff_rTensor_injective' R M).mpr
    intro I
    rcases H I with ⟨N, _, _, f, h, hinj⟩
    have eq : ((TensorProduct.lid R M).toLinearMap ∘ₗ (rTensor M (Submodule.subtype I))) ∘ₗ
        h.equiv.symm.toLinearMap = (h.lift (lsmul R M ∘ₗ Submodule.subtype I)) :=
      congrFun (congrArg comp (lid_comp_rTensor M (Submodule.subtype I))) h.equiv.symm.toLinearMap
    apply (EquivLike.comp_injective _ (TensorProduct.lid R M)).mp
    rw [← eq] at hinj
    exact (EquivLike.injective_comp h.equiv.symm _).mp hinj

end IsTensorProduct

section rTensor

variable (R : Type u) (M : Type v) [CommRing R] [AddCommGroup M] [Module R M]

theorem iff_linearEquiv (R : Type*) [CommRing R] (M N : Type*) [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (e : M ≃ₗ[R] N) : Flat R M ↔ Flat R N :=
  ⟨fun _ => of_linearEquiv R M N e.symm, fun _ => of_linearEquiv R N M e⟩

/-- Drop `[Small.{v, u} R]` assumption in `iff_rTensor_preserves_injective_linearMap`. -/
theorem iff_rTensor_preserves_injective_linearMap' : Flat R M ↔
    ∀ ⦃N N' : Type max u v⦄ [AddCommGroup N] [AddCommGroup N'] [Module R N] [Module R N']
      (f : N →ₗ[R] N') (_ : Function.Injective f), Function.Injective (f.rTensor M) := by
  refine (iff_linearEquiv R M (ULift.{u} M) ULift.moduleEquiv.symm).trans <|
    iff_characterModule_injective.trans <|
      (injective_characterModule_iff_rTensor_preserves_injective_linearMap R (ULift.{u} M)).trans <|
        forall₅_congr <| fun N N' _ _ _ => forall₃_congr (fun _ f _ => ?_)
  let frmu := f.rTensor (ULift.{u, v} M)
  let frm := f.rTensor M
  let emn := TensorProduct.congr (N := ULift.{u} M) (LinearEquiv.refl R N) ULift.moduleEquiv
  let emn' := TensorProduct.congr (N := ULift.{u} M) (LinearEquiv.refl R N') ULift.moduleEquiv
  have h : emn'.toLinearMap.comp frmu = frm.comp emn.toLinearMap := TensorProduct.ext rfl
  apply (EmbeddingLike.comp_injective frmu emn').symm.trans
  apply Iff.trans (Eq.to_iff (congrArg Function.Injective _)) (EquivLike.injective_comp emn frm)
  ext x
  exact congrFun (congrArg DFunLike.coe h) x

/-- Drop `[Small.{v, u} R]` assumption in `iff_lTensor_preserves_injective_linearMap`. -/
theorem iff_lTensor_preserves_injective_linearMap' : Flat R M ↔
    ∀ ⦃N N' : Type max u v⦄ [AddCommGroup N] [AddCommGroup N'] [Module R N] [Module R N']
      (f : N →ₗ[R] N') (_ : Function.Injective f), Function.Injective (f.lTensor M) := by
  simp_rw [iff_rTensor_preserves_injective_linearMap', LinearMap.lTensor_inj_iff_rTensor_inj]

/-- M is flat if and only if `f ⊗ 𝟙 M` is injective whenever `f` is an injective linear map. -/
lemma iff_rTensor_preserves_injective_linearMap'' [Small.{v'} R] [Small.{v'} M] : Flat R M ↔
    ∀ ⦃N N' : Type v'⦄ [AddCommGroup N] [AddCommGroup N'] [Module R N] [Module R N']
      (f : N →ₗ[R] N') (_ : Function.Injective f), Function.Injective (f.rTensor M) := by
  refine (iff_linearEquiv R M (Shrink.{v'} M) (Shrink.linearEquiv M R).symm).trans <|
    iff_characterModule_injective.trans <|
      (injective_characterModule_iff_rTensor_preserves_injective_linearMap R (Shrink.{v'} M)).trans
        <| forall₅_congr <| fun N N' _ _ _ => forall₃_congr (fun _ f _ => ?_)
  let frmu := f.rTensor (Shrink.{v'} M)
  let frm := f.rTensor M
  let emn := TensorProduct.congr (LinearEquiv.refl R N) (Shrink.linearEquiv M R)
  let emn' := TensorProduct.congr (LinearEquiv.refl R N') (Shrink.linearEquiv M R)
  have h : emn'.toLinearMap.comp frmu = frm.comp emn.toLinearMap := TensorProduct.ext rfl
  apply (EmbeddingLike.comp_injective frmu emn').symm.trans
  apply Iff.trans (Eq.to_iff (congrArg Function.Injective _)) (EquivLike.injective_comp emn frm)
  exact congrArg DFunLike.coe h

/-- M is flat if and only if `𝟙 M ⊗ f` is injective whenever `f` is an injective linear map. -/
lemma iff_lTensor_preserves_injective_linearMap'' [Small.{v'} R] [Small.{v'} M] : Flat R M ↔
    ∀ ⦃N N' : Type v'⦄ [AddCommGroup N] [AddCommGroup N'] [Module R N] [Module R N']
      (L : N →ₗ[R] N'), Function.Injective L → Function.Injective (L.lTensor M) := by
  simp_rw [iff_rTensor_preserves_injective_linearMap'', LinearMap.lTensor_inj_iff_rTensor_inj]

-- The following two lemmas have been proved in PR [#17484](https://github.com/leanprover-community/mathlib4/pull/17484)

/-- M is flat if and only if `M ⊗ -` is a left exact functor. -/
theorem iff_lTensor_exact''' [Small.{v'} R] [Small.{v'} M] : Flat R M ↔
    ∀ ⦃N N' N'' : Type v'⦄ [AddCommGroup N] [AddCommGroup N'] [AddCommGroup N'']
      [Module R N] [Module R N'] [Module R N''] ⦃f : N →ₗ[R] N'⦄ ⦃g : N' →ₗ[R] N''⦄,
        Function.Exact f g → Function.Exact (f.lTensor M) (g.lTensor M) := sorry

/-- M is flat if and only if `- ⊗ M` is a left exact functor. -/
theorem iff_rTensor_exact' [Small.{v'} R] [Small.{v'} M] : Flat R M ↔
    ∀ ⦃N N' N'' : Type v'⦄ [AddCommGroup N] [AddCommGroup N'] [AddCommGroup N'']
      [Module R N] [Module R N'] [Module R N''] ⦃f : N →ₗ[R] N'⦄ ⦃g : N' →ₗ[R] N''⦄,
        Function.Exact f g → Function.Exact (f.rTensor M) (g.rTensor M) := sorry

end rTensor

end Module.Flat

section lTensor'

noncomputable def LinearMap.lTensor' {R : Type*} [CommSemiring R] {M N P : Type*}
    [AddCommMonoid M]
    [AddCommMonoid N] [AddCommMonoid P] [Module R M] [Module R N] [Module R P] (f : N →ₗ[R] P)
    {N' P' : Type*} [AddCommMonoid N'] [AddCommMonoid P'] [Module R N'] [Module R P']
    {fn : M →ₗ[R] N →ₗ[R] N'} (hn : IsTensorProduct fn) {fp : M →ₗ[R] P →ₗ[R] P'}
    (hp : IsTensorProduct fp) : N' →ₗ[R] P' :=
  IsTensorProduct.map hn hp id f

noncomputable def LinearMap.rTensor' {R : Type*} [CommSemiring R] {M N P : Type*} [AddCommMonoid M]
    [AddCommMonoid N] [AddCommMonoid P] [Module R M] [Module R N] [Module R P] (f : N →ₗ[R] P)
    {N' P' : Type*} [AddCommMonoid N'] [AddCommMonoid P'] [Module R N'] [Module R P']
    {fn : N →ₗ[R] M →ₗ[R] N'} (hn : IsTensorProduct fn) {fp : P →ₗ[R] M →ₗ[R] P'}
    (hp : IsTensorProduct fp) : N' →ₗ[R] P' :=
  IsTensorProduct.map hn hp f id

namespace Module.Flat

open IsTensorProduct LinearMap

variable (R : Type u) (M : Type v) [CommRing R] [AddCommGroup M] [Module R M]


lemma iff_exist_rTensor'_preserves_injective_linearMap
    [Small.{v'} R] [Small.{v'} M] : Flat R M ↔
    ∀ ⦃N N' : Type v'⦄ [AddCommGroup N] [AddCommGroup N'] [Module R N] [Module R N']
      (f : N →ₗ[R] N') (_ : Function.Injective f),
      ∃ (P : Type v') (_ : AddCommGroup P) (_ : Module R P)
        (p : N →ₗ[R] M →ₗ[R] P) (h : IsTensorProduct p)
        (P' : Type v') (_ : AddCommGroup P') (_ : Module R P') (p' : N' →ₗ[R] M →ₗ[R] P')
        (h' : IsTensorProduct p'), Function.Injective (f.rTensor' h h') := sorry

lemma iff_exist_lTensor'_preserves_injective_linearMap
    [Small.{v'} R] [Small.{v'} M] : Flat R M ↔
    ∀ ⦃N N' : Type v'⦄ [AddCommGroup N] [AddCommGroup N'] [Module R N] [Module R N']
      (f : N →ₗ[R] N') (_ : Function.Injective f),
      ∃ (P : Type v') (_ : AddCommGroup P) (_ : Module R P)
        (p : M →ₗ[R] N →ₗ[R] P) (h : IsTensorProduct p)
        (P' : Type v') (_ : AddCommGroup P') (_ : Module R P') (p' : M →ₗ[R] N' →ₗ[R] P')
        (h' : IsTensorProduct p'), Function.Injective (f.lTensor' h h') := sorry

/-- M is flat if and only if `M ⊗ -` is a left exact functor. -/
theorem iff_exist_lTensor'_exact [Small.{v'} R] [Small.{v'} M] : Flat R M ↔
    ∀ ⦃N N' N'' : Type v'⦄ [AddCommGroup N] [AddCommGroup N'] [AddCommGroup N'']
      [Module R N] [Module R N'] [Module R N''] ⦃f : N →ₗ[R] N'⦄ ⦃g : N' →ₗ[R] N''⦄,
      ∃ (P : Type v') (_ : AddCommGroup P) (_ : Module R P) (p : M →ₗ[R] N →ₗ[R] P)
        (h : IsTensorProduct p) (P' : Type v') (_ : AddCommGroup P') (_ : Module R P')
        (p' : M →ₗ[R] N' →ₗ[R] P') (h' : IsTensorProduct p')
        (P'' : Type v') (_ : AddCommGroup P'') (_ : Module R P'')
        (p'' : M →ₗ[R] N'' →ₗ[R] P'') (h'' : IsTensorProduct p''),
        Function.Exact f g → Function.Exact (f.lTensor' h h') (g.lTensor' h' h'') := sorry

/-- M is flat if and only if `M ⊗ -` is a left exact functor. -/
theorem iff_exist_rTensor'_exact [Small.{v'} R] [Small.{v'} M] : Flat R M ↔
    ∀ ⦃N N' N'' : Type v'⦄ [AddCommGroup N] [AddCommGroup N'] [AddCommGroup N'']
      [Module R N] [Module R N'] [Module R N''] ⦃f : N →ₗ[R] N'⦄ ⦃g : N' →ₗ[R] N''⦄,
      ∃ (P : Type v') (_ : AddCommGroup P) (_ : Module R P) (p : N →ₗ[R] M →ₗ[R] P)
        (h : IsTensorProduct p) (P' : Type v') (_ : AddCommGroup P') (_ : Module R P')
        (p' : N' →ₗ[R] M →ₗ[R] P') (h' : IsTensorProduct p')
        (P'' : Type v') (_ : AddCommGroup P'') (_ : Module R P'')
        (p'' : N'' →ₗ[R] M →ₗ[R] P'') (h'' : IsTensorProduct p''),
        Function.Exact f g → Function.Exact (f.rTensor' h h') (g.rTensor' h' h'') := sorry

lemma iff_rTensor'_preserves_injective_linearMap [Small.{v'} R] [Small.{v'} M] : Flat R M ↔
    ∀ ⦃N N' : Type v'⦄ [AddCommGroup N] [AddCommGroup N'] [Module R N] [Module R N']
      (f : N →ₗ[R] N') (_ : Function.Injective f)
      {P : Type v'} [AddCommGroup P] [Module R P] {p : N →ₗ[R] M →ₗ[R] P} (h : IsTensorProduct p)
      {P' : Type v'} [AddCommGroup P'] [Module R P'] {p' : N' →ₗ[R] M →ₗ[R] P'}
      (h' : IsTensorProduct p'), Function.Injective (f.rTensor' h h') := sorry

lemma iff_lTensor'_preserves_injective_linearMap [Small.{v'} R] [Small.{v'} M] : Flat R M ↔
    ∀ ⦃N N' : Type v'⦄ [AddCommGroup N] [AddCommGroup N'] [Module R N] [Module R N']
      (f : N →ₗ[R] N') (_ : Function.Injective f)
      {P : Type v'} [AddCommGroup P] [Module R P] {p : M →ₗ[R] N →ₗ[R] P} (h : IsTensorProduct p)
      {P' : Type v'} [AddCommGroup P'] [Module R P'] {p' : M →ₗ[R] N' →ₗ[R] P'}
      (h' : IsTensorProduct p'), Function.Injective (f.lTensor' h h') := sorry

/-- M is flat if and only if `M ⊗ -` is a left exact functor. -/
theorem iff_lTensor'_exact [Small.{v'} R] [Small.{v'} M] : Flat R M ↔
    ∀ ⦃N N' N'' : Type v'⦄ [AddCommGroup N] [AddCommGroup N'] [AddCommGroup N'']
      [Module R N] [Module R N'] [Module R N''] ⦃f : N →ₗ[R] N'⦄ ⦃g : N' →ₗ[R] N''⦄
      {P : Type v'} [AddCommGroup P] [Module R P] {p : M →ₗ[R] N →ₗ[R] P} (h : IsTensorProduct p)
      {P' : Type v'} [AddCommGroup P'] [Module R P'] {p' : M →ₗ[R] N' →ₗ[R] P'}
      (h' : IsTensorProduct p') {P'' : Type v'} [AddCommGroup P''] [Module R P'']
      {p'' : M →ₗ[R] N'' →ₗ[R] P''} (h'' : IsTensorProduct p''),
      Function.Exact f g → Function.Exact (f.lTensor' h h') (g.lTensor' h' h'') := sorry

/-- M is flat if and only if `M ⊗ -` is a right exact functor. -/
theorem iff_rTensor'_exact [Small.{v'} R] [Small.{v'} M] : Flat R M ↔
    ∀ ⦃N N' N'' : Type v'⦄ [AddCommGroup N] [AddCommGroup N'] [AddCommGroup N'']
      [Module R N] [Module R N'] [Module R N''] ⦃f : N →ₗ[R] N'⦄ ⦃g : N' →ₗ[R] N''⦄
      {P : Type v'} [AddCommGroup P] [Module R P] {p : N →ₗ[R] M →ₗ[R] P} (h : IsTensorProduct p)
      {P' : Type v'} [AddCommGroup P'] [Module R P'] {p' : N' →ₗ[R] M →ₗ[R] P'}
      (h' : IsTensorProduct p') {P'' : Type v'} [AddCommGroup P''] [Module R P'']
      {p'' : N'' →ₗ[R] M →ₗ[R] P''} (h'' : IsTensorProduct p''),
      Function.Exact f g → Function.Exact (f.rTensor' h h') (g.rTensor' h' h'') := sorry

end Module.Flat

end lTensor'
