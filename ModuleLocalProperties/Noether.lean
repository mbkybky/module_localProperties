/-
Copyright (c) 2024 Yi Song. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yi Song, Yongle Hu
-/
import Mathlib.Algebra.Module.Submodule.Localization
import Mathlib.RingTheory.Localization.Finiteness
import ModuleLocalProperties.Basic
import ModuleLocalProperties.Finite_presented

open Submodule IsLocalizedModule LocalizedModule Ideal

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] (s : Finset R)
(spn : span (s : Set R) = ⊤)
include spn

lemma isnoetherian_of_localization_finitespan (h : ∀ r : s,
    IsNoetherian (Localization.Away r.1) (LocalizedModule.Away r.1 M)) :  IsNoetherian R M :=
  isNoetherian_def.mpr <| fun N => submodule.of_localizationSpan_finite _ _ spn <|
  fun r => (isNoetherian_def.mp <| h <| r) <| (localized (Submonoid.powers ↑r) N)
