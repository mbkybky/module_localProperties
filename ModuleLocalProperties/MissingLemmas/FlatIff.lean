/-
Copyright (c) 2024 Yongle Hu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongle Hu
-/
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.IsTensorProduct

open LinearMap Submodule TensorProduct DirectSum

theorem Module.Flat.iff_isTensorProduct_lift_injective (R M : Type*) [CommRing R] [AddCommGroup M]
    [Module R M] :  Module.Flat R M ↔ ∀ (I : Ideal R) {N : Type*} [AddCommGroup N] [Module R N]
    (f : I →ₗ[R] M →ₗ[R] N) (h : IsTensorProduct f),
    Function.Injective (IsTensorProduct.lift h ((lsmul R M).comp I.subtype)) := sorry
