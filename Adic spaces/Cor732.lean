/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».SpaCompact
import «Adic spaces».RationalSubsets

/-!
# Wedhorn Corollary 7.32: Dominating unit extraction

For a Tate ring `A` with `X = Spa(A, A⁺)` quasi-compact, and a finite family
`T ⊆ A` with no common zero on `X` (i.e. `∀ v ∈ X, ∃ t ∈ T, v(t) ≠ 0`), there
exists a unit `s ∈ Aˣ` such that for every `v ∈ X`, some `t ∈ T` satisfies
`v(s) < v(t)` (equivalently `v.vle s t ∧ ¬ v.vle t s`).

## Proof idea

Let `π : A` be a topologically nilpotent unit (pseudo-uniformizer). For each
`n : ℕ` consider the open set

  `U_n := ⋃_{t ∈ T} basicOpen (π^n) t = {v | ∃ t ∈ T, v(π^n) ≤ v(t) ∧ v(t) ≠ 0}`.

Three facts:

1. **`U_n` is open:** finite union of basic opens in `Spv A`.

2. **`(U_n)_n` covers `Spa`:** Fix `v ∈ Spa`. By hypothesis there is
   `t₀ ∈ T` with `v(t₀) ≠ 0`. Since `v(π) < 1` (continuity + topological
   nilpotency) and `v(t₀) > 0`, by `exists_pow_lt₀` applied to `v(π) < 1`
   we can find `n` with `v(π)^n < v(t₀)`, placing `v` in `U_n`.

3. **Monotonicity:** `U_n ⊆ U_m` for `n ≤ m`. Indeed `v(π^m) = v(π)^m ≤ v(π)^n
   = v(π^n)` because `v(π) ≤ 1`.

By compactness of `Spa` (from `SpaCompact`), the cover admits a finite
subcover. Taking `N := sup` of the involved indices yields `Spa ⊆ U_N` by
monotonicity. Setting `s := π^(N+1)` gives a unit with
`v(s) = v(π) · v(π^N) < v(π^N) ≤ v(t)` strictly, since `v(π) < 1` and
`v(π^N) ≠ 0` (powers of units are units).

## Main result

* `ValuationSpectrum.exists_dominating_unit`: the Tate-level Cor 7.32,
  conditional on a pseudo-uniformizer and MulArchimedean value groups.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn2019adic], Corollary 7.32.
-/

open Topology

namespace ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [IsLinearTopology A A] [PlusSubring A]

/-! ### The finite union of basic opens "dominated by `π^n`" -/

/-- The open set `⋃_{t ∈ T} basicOpen (π^n) t` whose increasing union over
`n : ℕ` covers `Spa A A⁺` under the hypotheses of Cor 7.32. -/
def dominatedBy (T : Finset A) (π : A) (n : ℕ) : Set (Spv A) :=
  ⋃ t ∈ T, basicOpen (π ^ n) t

omit [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A] [PlusSubring A] in
lemma isOpen_dominatedBy (T : Finset A) (π : A) (n : ℕ) :
    IsOpen (dominatedBy T π n) :=
  isOpen_biUnion fun t _ ↦ isOpen_basicOpen _ t

omit [IsTopologicalRing A] [IsLinearTopology A A] in
/-- On `Spa A A⁺` with topologically nilpotent `π`, `w π ≤ 1`. -/
private lemma valuation_pi_le_one_on_spa
    {v : Spv A} (hv : v ∈ Spa A A⁺)
    {π : A} (hπ_tn : IsTopologicallyNilpotent π) :
    letI : ValuativeRel A := v.toValuativeRel
    (ValuativeRel.valuation A) π ≤ 1 := by
  letI : ValuativeRel A := v.toValuativeRel
  have hcompat : (ValuativeRel.valuation A).Compatible := inferInstance
  set w := ValuativeRel.valuation A
  have hπ_lt : ¬ v.vle 1 π :=
    not_vle_one_of_mem_spa_of_topologicallyNilpotent hv hπ_tn
  have h_not : ¬ (w 1 ≤ w π) := fun h ↦ hπ_lt
    ((Valuation.Compatible.vle_iff_le (v := w) _ _).mpr h)
  rw [map_one] at h_not
  exact le_of_not_ge h_not

omit [IsTopologicalRing A] [IsLinearTopology A A] in
/-- Monotonicity in `n`: on `Spa A A⁺`, `dominatedBy T π n ⊆ dominatedBy T π m`
whenever `n ≤ m`, because `v(π) ≤ 1` forces `v(π^m) ≤ v(π^n)`. -/
lemma dominatedBy_mono_on_spa
    (T : Finset A) {π : A} (hπ_tn : IsTopologicallyNilpotent π)
    {n m : ℕ} (hnm : n ≤ m) :
    dominatedBy T π n ∩ Spa A A⁺ ⊆ dominatedBy T π m := by
  intro v ⟨hvU, hvSpa⟩
  simp only [dominatedBy, Set.mem_iUnion] at hvU ⊢
  obtain ⟨t, htT, hvt, hvt0⟩ := hvU
  refine ⟨t, htT, ?_, hvt0⟩
  letI : ValuativeRel A := v.toValuativeRel
  have hcompat : (ValuativeRel.valuation A).Compatible := inferInstance
  set w := ValuativeRel.valuation A
  have h_t : w (π ^ n) ≤ w t :=
    (Valuation.Compatible.vle_iff_le (v := w) _ _).mp hvt
  have hπ_le_one : w π ≤ 1 := valuation_pi_le_one_on_spa hvSpa hπ_tn
  have h_pow : w π ^ m ≤ w π ^ n :=
    pow_le_pow_of_le_one (zero_le') hπ_le_one hnm
  refine (Valuation.Compatible.vle_iff_le (v := w) _ _).mpr ?_
  calc w (π ^ m) = w π ^ m := by simp [map_pow]
    _ ≤ w π ^ n := h_pow
    _ = w (π ^ n) := by simp [map_pow]
    _ ≤ w t := h_t

/-! ### Coverage: every Spa-point lies in some `dominatedBy` -/

omit [IsTopologicalRing A] [IsLinearTopology A A] in
/-- **Coverage at a single point.** Given `v ∈ Spa A A⁺` and `t ∈ A` with
`v(t) ≠ 0`, under MulArchimedean of the value group some power `π^n` of a
topologically nilpotent element `π` satisfies `v(π^n) ≤ v(t)`, so `v` lies
in `basicOpen (π^n) t`. -/
lemma exists_mem_basicOpen_pow_of_tn
    {v : Spv A} (hv : v ∈ Spa A A⁺)
    {π : A} (hπ_tn : IsTopologicallyNilpotent π)
    (hArch :
      letI : ValuativeRel A := v.toValuativeRel
      MulArchimedean (ValuativeRel.ValueGroupWithZero A))
    {t : A} (htne : ¬ v.vle t 0) :
    ∃ n : ℕ, v ∈ basicOpen (π ^ n) t := by
  letI : ValuativeRel A := v.toValuativeRel
  haveI : MulArchimedean (ValuativeRel.ValueGroupWithZero A) := hArch
  have hcompat : (ValuativeRel.valuation A).Compatible := inferInstance
  set w := ValuativeRel.valuation A
  have hπ_lt : w π < 1 := by
    have hπ_not : ¬ v.vle 1 π :=
      not_vle_one_of_mem_spa_of_topologicallyNilpotent hv hπ_tn
    have hne : ¬ (w 1 ≤ w π) := fun h ↦ hπ_not
      ((Valuation.Compatible.vle_iff_le (v := w) _ _).mpr h)
    rw [map_one] at hne
    exact lt_of_not_ge hne
  have hwt_ne : w t ≠ 0 := by
    intro h
    refine htne ((Valuation.Compatible.vle_iff_le (v := w) _ _).mpr ?_)
    rw [map_zero]; exact le_of_eq h
  obtain ⟨n, hn⟩ := exists_pow_lt₀ hπ_lt (Units.mk0 (w t) hwt_ne)
  refine ⟨n, ?_, htne⟩
  refine (Valuation.Compatible.vle_iff_le (v := w) _ _).mpr ?_
  simp only [map_pow]
  exact le_of_lt (by simpa using hn)

/-! ### Compactness-based stabilisation -/

omit [IsTopologicalRing A] [IsLinearTopology A A] in
/-- Given compactness of `Spa A A⁺` and a topologically nilpotent element
`π`, the cover `{dominatedBy T π n}_{n ∈ ℕ}` admits a single-index dominator:
`Spa A A⁺ ⊆ dominatedBy T π N` for some `N`. -/
lemma exists_dominatedBy_cover
    (hSpa_compact : CompactSpace ↥(Spa A A⁺))
    (T : Finset A) {π : A} (hπ_tn : IsTopologicallyNilpotent π)
    (hArch : ∀ v : Spv A,
      letI : ValuativeRel A := v.toValuativeRel
      MulArchimedean (ValuativeRel.ValueGroupWithZero A))
    (hT : ∀ v ∈ Spa A A⁺, ∃ t ∈ T, ¬ v.vle t 0) :
    ∃ N : ℕ, (Spa A A⁺ : Set (Spv A)) ⊆ dominatedBy T π N := by
  -- Pull back to `↥(Spa A A⁺)` via `Subtype.val`.
  set S : ℕ → Set ↥(Spa A A⁺) :=
    fun n ↦ Subtype.val ⁻¹' dominatedBy T π n with hS_def
  have hS_open : ∀ n, IsOpen (S n) :=
    fun n ↦ (isOpen_dominatedBy T π n).preimage continuous_subtype_val
  have hS_cover : (Set.univ : Set ↥(Spa A A⁺)) ⊆ ⋃ n, S n := by
    rintro ⟨v, hvSpa⟩ _
    obtain ⟨t, htT, htne⟩ := hT v hvSpa
    obtain ⟨n, hn⟩ := exists_mem_basicOpen_pow_of_tn hvSpa hπ_tn (hArch v) htne
    refine Set.mem_iUnion.mpr ⟨n, ?_⟩
    simp only [hS_def, Set.mem_preimage, dominatedBy, Set.mem_iUnion]
    exact ⟨t, htT, hn⟩
  haveI := hSpa_compact
  obtain ⟨F, hF⟩ := isCompact_univ.elim_finite_subcover S hS_open hS_cover
  -- `N := F.sup id` bounds every element of `F`.
  set N : ℕ := F.sup id with hN_def
  refine ⟨N, fun v hvSpa ↦ ?_⟩
  -- `(⟨v, hvSpa⟩ : ↥(Spa A A⁺)) ∈ S n` for some `n ∈ F`.
  have hmem : (⟨v, hvSpa⟩ : ↥(Spa A A⁺)) ∈ (Set.univ : Set ↥(Spa A A⁺)) := Set.mem_univ _
  have hUnion := hF hmem
  simp only [Set.mem_iUnion] at hUnion
  obtain ⟨n, hnF, hvn⟩ := hUnion
  -- `v ∈ dominatedBy T π n`, and `n ≤ N`, so `v ∈ dominatedBy T π N` by monotonicity.
  have hle : n ≤ N := by
    have := Finset.le_sup (f := id) hnF
    simpa [hN_def] using this
  have hv_dom : v ∈ dominatedBy T π n := by
    simpa [hS_def, Set.mem_preimage] using hvn
  exact dominatedBy_mono_on_spa T hπ_tn hle ⟨hv_dom, hvSpa⟩

/-! ### Assembly: strict-domination unit -/

omit [IsLinearTopology A A] in
/-- **Wedhorn Corollary 7.32 (Tate version).**

For a Tate ring `A` with the hypotheses ensuring quasi-compactness of
`Spa(A, A⁺)` — pair of definition `P` with `P.A₀ ⊆ A⁺`, principal ideal
`P.I = (π)` with `π` a topologically nilpotent unit of `A`, and
MulArchimedean value groups — and a finite family `T ⊆ A` with no common
zero on `Spa(A, A⁺)`, there exists a unit `s ∈ Aˣ` such that for every
`v ∈ Spa(A, A⁺)`, some `t ∈ T` satisfies `v(s) < v(t)`.

Concretely, `s = π^(N+1)` for `N` extracted from the finite subcover by
`exists_dominatedBy_cover`. -/
theorem exists_dominating_unit
    (P : PairOfDefinition A) (hA₀_le : P.A₀ ≤ A⁺)
    (π : P.A₀) (hI : P.I = Ideal.span {π})
    (hπ_tn : IsTopologicallyNilpotent (P.A₀.subtype π))
    (hπ_unit : IsUnit (P.A₀.subtype π))
    (hArch : ∀ v : Spv A,
      letI : ValuativeRel A := v.toValuativeRel
      MulArchimedean (ValuativeRel.ValueGroupWithZero A))
    (T : Finset A)
    (hT : ∀ v ∈ Spa A A⁺, ∃ t ∈ T, ¬ v.vle t 0) :
    ∃ s : Aˣ, ∀ v ∈ Spa A A⁺, ∃ t ∈ T,
      v.vle (s : A) t ∧ ¬ v.vle t (s : A) := by
  -- Compactness via SpaCompact.
  haveI hSpa_compact : CompactSpace ↥(Spa A A⁺) :=
    instCompactSpace_spa_of_tate_pseudouniformizer P hA₀_le π hI hπ_tn hπ_unit hArch
  -- Finite `N` dominator.
  set πA : A := P.A₀.subtype π with hπA_def
  obtain ⟨N, hN⟩ :=
    exists_dominatedBy_cover hSpa_compact T hπ_tn hArch hT
  -- Define `s := π^(N+1)`. It is a unit since π is.
  have hπN1_unit : IsUnit (πA ^ (N + 1)) := hπ_unit.pow (N + 1)
  refine ⟨hπN1_unit.unit, fun v hvSpa ↦ ?_⟩
  -- `v ∈ dominatedBy T πA N`, so pick `t ∈ T` with `v.vle (πA^N) t ∧ ¬ v.vle t 0`.
  have hv_dom : v ∈ dominatedBy T πA N := hN hvSpa
  simp only [dominatedBy, Set.mem_iUnion] at hv_dom
  obtain ⟨t, htT, hvt, hvt0⟩ := hv_dom
  refine ⟨t, htT, ?_, ?_⟩
  · -- `v.vle (πA^(N+1)) t` via `v(πA^(N+1)) = v(πA) * v(πA^N) ≤ v(πA^N) ≤ v(t)`.
    letI : ValuativeRel A := v.toValuativeRel
    have hcompat : (ValuativeRel.valuation A).Compatible := inferInstance
    set w := ValuativeRel.valuation A
    have h_t : w (πA ^ N) ≤ w t :=
      (Valuation.Compatible.vle_iff_le (v := w) _ _).mp hvt
    have hπ_le_one : w πA ≤ 1 := valuation_pi_le_one_on_spa hvSpa hπ_tn
    refine (Valuation.Compatible.vle_iff_le (v := w) _ _).mpr ?_
    have hunit_val : ((hπN1_unit.unit : Aˣ) : A) = πA ^ (N + 1) :=
      hπN1_unit.unit_spec
    rw [hunit_val]
    calc w (πA ^ (N + 1))
        = w (πA ^ N) * w πA := by
          rw [pow_succ, map_mul]
      _ ≤ w (πA ^ N) * 1 :=
          mul_le_mul_of_nonneg_left hπ_le_one (zero_le' (a := w (πA ^ N)))
      _ = w (πA ^ N) := by rw [mul_one]
      _ ≤ w t := h_t
  · -- `¬ v.vle t (πA^(N+1))` via strict `w πA < 1`.
    letI : ValuativeRel A := v.toValuativeRel
    haveI : MulArchimedean (ValuativeRel.ValueGroupWithZero A) := hArch v
    have hcompat : (ValuativeRel.valuation A).Compatible := inferInstance
    set w := ValuativeRel.valuation A
    have h_t : w (πA ^ N) ≤ w t :=
      (Valuation.Compatible.vle_iff_le (v := w) _ _).mp hvt
    -- Strict `w πA < 1`.
    have hπ_lt_one : w πA < 1 := by
      have hπ_not : ¬ v.vle 1 πA :=
        not_vle_one_of_mem_spa_of_topologicallyNilpotent hvSpa hπ_tn
      have hne : ¬ (w 1 ≤ w πA) := fun h ↦ hπ_not
        ((Valuation.Compatible.vle_iff_le (v := w) _ _).mpr h)
      rw [map_one] at hne
      exact lt_of_not_ge hne
    -- `w (πA^N) ≠ 0` since πA is a unit.
    have hπN_unit : IsUnit (πA ^ N) := hπ_unit.pow N
    have hwπN_ne : w (πA ^ N) ≠ 0 := by
      intro h
      exact not_vle_zero_of_isUnit hπN_unit v
        ((Valuation.Compatible.vle_iff_le (v := w) _ _).mpr (by rw [map_zero]; exact le_of_eq h))
    -- `w t ≠ 0` since `v ∈ basicOpen (πA^N) t`.
    have hwt_ne : w t ≠ 0 := by
      intro h
      refine hvt0 ((Valuation.Compatible.vle_iff_le (v := w) _ _).mpr ?_)
      rw [map_zero]; exact le_of_eq h
    -- Show `w t > w (πA^(N+1))`.
    have h_sN1_lt_sN : w (πA ^ (N + 1)) < w (πA ^ N) := by
      rw [pow_succ, map_mul]
      have h1 : w (πA ^ N) * w πA < w (πA ^ N) * 1 :=
        mul_lt_mul_of_pos_left hπ_lt_one (zero_lt_iff.mpr hwπN_ne)
      simpa using h1
    have h_lt_t : w (πA ^ (N + 1)) < w t := lt_of_lt_of_le h_sN1_lt_sN h_t
    -- Translate back to `vle` and `¬ vle`.
    intro hvle
    have hunit_val : ((hπN1_unit.unit : Aˣ) : A) = πA ^ (N + 1) :=
      hπN1_unit.unit_spec
    rw [hunit_val] at hvle
    have h_le := (Valuation.Compatible.vle_iff_le (v := w) t (πA ^ (N + 1))).mp hvle
    exact absurd h_le (not_le.mpr h_lt_t)

end ValuationSpectrum
