/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».Presheaf
import «Adic spaces».RationalSubsets

/-!
# Wedhorn Cover Normalization (insert-denominator transform)

Wedhorn Remark 7.30(3) at the rational-localization-data level: adding the
denominator `D.s` to the generating set `D.T` of a rational localization
datum produces the *same* rational open. This file lifts that observation
to a cover-level normalization, so that downstream consumers (notably the
C1/C2 Wedhorn-standard-cover assembly) can assume `D.s ∈ D.T` without
making it a final-theorem hypothesis.

## What this file gives

* `locSubring_mono_T` — `T₁ ⊆ T₂ → locSubring P T₁ s ≤ locSubring P T₂ s`.
* `RationalLocData.insertDenom` — the rational-locale-data transform that
  adds `D.s` to `D.T` while keeping `P, s` unchanged; `hopen` upgrades via
  `locSubring_mono_T`.
* `RationalLocData.insertDenom_s_mem` — `D.s ∈ D.insertDenom.T`.
* `RationalLocData.rationalOpen_insertDenom` — `rationalOpen` is unchanged.
* `RationalCovering.insertDenom` — the cover-level normalization, applying
  `RationalLocData.insertDenom` to base and each piece.
* `RationalCovering.insertDenom_normalized` — every piece satisfies
  `D.s ∈ D.T`.
* `RationalCovering.insertDenom_base_open` — the base rational open is
  unchanged as a set of valuations.

The transform is purely combinatorial / set-theoretic; no Lane B / Cor 8.32 /
Jacobson / faithful-flatness / T001 / final-acyclicity content. The single
analytic ingredient is `locSubring_mono_T`, which is a one-line monotonicity
on `Subring.closure`.
-/

namespace ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [DecidableEq A]

omit [IsTopologicalRing A] [DecidableEq A] in
/-- **Localization-subring monotonicity in `T`**. Adding more elements to
the generating set `T` enlarges (does not shrink) the ring of definition
`locSubring P T s`. Pure `Subring.closure` monotonicity. -/
theorem locSubring_mono_T {T₁ T₂ : Finset A} (h : T₁ ⊆ T₂)
    (P : PairOfDefinition A) (s : A) :
    locSubring P T₁ s ≤ locSubring P T₂ s := by
  unfold locSubring
  apply Subring.closure_mono
  apply Set.union_subset_union_right
  rintro _ ⟨⟨t, ht⟩, rfl⟩
  exact ⟨⟨t, h ht⟩, rfl⟩

/-- **Rational-locale-data insert-denominator transform** (Wedhorn Remark
7.30(3) at the data level). Adds the denominator `D.s` to `D.T`; `P, s`
are unchanged, and `hopen` upgrades via `locSubring_mono_T`. -/
def RationalLocData.insertDenom (D : RationalLocData A) : RationalLocData A where
  P := D.P
  T := insert D.s D.T
  s := D.s
  hopen := by
    obtain ⟨N, hN⟩ := D.hopen
    refine ⟨N, fun b hb => ?_⟩
    exact locSubring_mono_T (Finset.subset_insert _ _) D.P D.s (hN b hb)

@[simp]
theorem RationalLocData.insertDenom_s (D : RationalLocData A) :
    D.insertDenom.s = D.s := rfl

@[simp]
theorem RationalLocData.insertDenom_T (D : RationalLocData A) :
    D.insertDenom.T = insert D.s D.T := rfl

@[simp]
theorem RationalLocData.insertDenom_P (D : RationalLocData A) :
    D.insertDenom.P = D.P := rfl

/-- The denominator `D.s` is in the generating set after `insertDenom`. -/
theorem RationalLocData.insertDenom_s_mem (D : RationalLocData A) :
    D.s ∈ D.insertDenom.T :=
  Finset.mem_insert_self _ _

section RationalCoveringSection

variable [PlusSubring A]

/-- **Wedhorn Remark 7.30(3) at the data level**: the rational open is
preserved by `insertDenom`. Direct corollary of
`RationalSubsets.rationalOpen_insert_s`. The `[PlusSubring A]` instance
is needed because `rationalOpen` is defined relative to `Spa A A⁺`. -/
theorem RationalLocData.rationalOpen_insertDenom
    (D : RationalLocData A) :
    rationalOpen D.insertDenom.T D.insertDenom.s = rationalOpen D.T D.s :=
  rationalOpen_insert_s D.T D.s

/-- **Rational-cover insert-denominator transform**. Applies
`RationalLocData.insertDenom` to the base and to each piece; both base and
pieces satisfy `D.s ∈ D.T` after the transform. The rational-open structure
is unchanged on every piece because `rationalOpen_insert_s` is a set
equality, so `hsubset`/`hcover` carry over from `C`. -/
noncomputable def RationalCovering.insertDenom
    (C : RationalCovering A) : RationalCovering A :=
  letI : DecidableEq (RationalLocData A) := Classical.decEq _
  { base := C.base.insertDenom
    covers := C.covers.image RationalLocData.insertDenom
    hsubset := by
      intro D' hD'
      obtain ⟨D, hD, rfl⟩ := Finset.mem_image.mp hD'
      rw [RationalLocData.rationalOpen_insertDenom D,
        RationalLocData.rationalOpen_insertDenom C.base]
      exact C.hsubset D hD
    hcover := by
      intro v hv
      rw [RationalLocData.rationalOpen_insertDenom C.base] at hv
      obtain ⟨D, hD, hvD⟩ := C.hcover v hv
      refine ⟨D.insertDenom, Finset.mem_image.mpr ⟨D, hD, rfl⟩, ?_⟩
      rw [RationalLocData.rationalOpen_insertDenom D]
      exact hvD }

/-- After `RationalCovering.insertDenom`, every piece is normalized:
`D.s ∈ D.T`. -/
theorem RationalCovering.insertDenom_normalized
    (C : RationalCovering A) :
    ∀ D ∈ C.insertDenom.covers, D.s ∈ D.T := by
  letI : DecidableEq (RationalLocData A) := Classical.decEq _
  intro D hD
  obtain ⟨D₀, _, rfl⟩ := Finset.mem_image.mp hD
  exact D₀.insertDenom_s_mem

/-- After `RationalCovering.insertDenom`, the base rational open is
unchanged as a set of valuations. -/
theorem RationalCovering.insertDenom_base_open
    (C : RationalCovering A) :
    rationalOpen C.insertDenom.base.T C.insertDenom.base.s =
      rationalOpen C.base.T C.base.s :=
  RationalLocData.rationalOpen_insertDenom C.base

end RationalCoveringSection

end ValuationSpectrum
