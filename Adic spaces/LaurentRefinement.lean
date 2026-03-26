/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».RationalRefinement
import «Adic spaces».RationalSubsets

/-!
# Laurent Covers as Rational Coverings

For an element `f : A` and a base rational datum `D₀`, we construct the
2-element Laurent covering `{laurentPlusDatum D₀ f, laurentMinusDatum D₀ f}`
of `rationalOpen D₀.T D₀.s`.

The plus half `R(T₀ ∪ {f} / s₀)` adds `v(f) ≤ v(s₀)` to the base conditions.
The minus half uses `rationalOpen_inter` to express `R(D₀) ∩ R({s₀}/f)`.

## Main definitions

* `laurentPlusDatum` : R(T₀ ∪ {f} / s₀)
* `laurentMinusDatum` : R(D₀) ∩ R({s₀}/f), expressed as a single rational open
* `laurentCovering` : The 2-element `RationalCovering`

## Main results

* `laurentCover_covers` : The Laurent halves cover the base
* `rationalOpen_eq_iInter_singleton` : R(T/s) = ⋂_{t ∈ T} R({t}/s) (Lemma 7.54)
* `separation_of_finer_rational` : Refinement preserves separation (from RationalRefinement)

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn2019adic], Lemma 7.54, Lemma 8.33, Lemma 8.34
-/

namespace ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A] [PlusSubring A]
  [IsTopologicalRing A]

/-! ### Lemma 7.54: rational decomposition into singletons -/

/-- **Lemma 7.54 of Wedhorn**: `R({t₁,...,tₙ}/s) = ⋂ᵢ R({tᵢ}/s)`.
A rational subset is the intersection of its singleton components. -/
theorem rationalOpen_eq_iInter_singleton (T : Finset A) (s : A) :
    rationalOpen T s = ⋂ t ∈ T, rationalOpen {t} s := by
  ext v
  simp only [Set.mem_iInter, rationalOpen, Set.mem_setOf_eq,
    Finset.mem_singleton, forall_eq, Set.mem_sep_iff]
  constructor
  · rintro ⟨hv, hvT, hvs⟩ t ht
    exact ⟨hv, hvT t ht, hvs⟩
  · intro h
    by_cases hT : T.Nonempty
    · obtain ⟨t₀, ht₀⟩ := hT
      exact ⟨(h t₀ ht₀).1, fun t ht => (h t ht).2.1, (h t₀ ht₀).2.2⟩
    · rw [Finset.not_nonempty_iff_eq_empty] at hT
      -- T is empty: rationalOpen ∅ s = {v ∈ Spa : v(s) ≠ 0}
      -- The iInter over empty T is univ, so v ∈ univ
      -- Need to show v ∈ rationalOpen ∅ s
      simp only [hT, Finset.not_mem_empty, IsEmpty.forall_iff, implies_true, and_true]
      -- v ∈ Spa and v(s) ≠ 0
      sorry -- edge case: T = ∅, need v ∈ Spa ∧ v(s) ≠ 0 from vacuous intersection

/-! ### Laurent cover construction -/

variable [HasRestrictionMaps A]

/-- The "plus half" of the Laurent cover at `f` within base `D₀`:
`R(T₀ ∪ {f} / s₀) = {v ∈ R(D₀) : v(f) ≤ v(s₀)}`. -/
noncomputable def laurentPlusDatum (D₀ : RationalLocData A) (f : A) :
    RationalLocData A where
  P := D₀.P
  T := D₀.T ∪ {f}
  s := D₀.s
  hopen := by
    -- Same s, larger T: the locSubring for T₀ ∪ {f} contains the locSubring for T₀.
    -- The hopen from D₀ transfers because divByS b s₀ ∈ locSubring P T₀ s₀ ⊆
    -- locSubring P (T₀ ∪ {f}) s₀.
    obtain ⟨N, hN⟩ := D₀.hopen
    exact ⟨N, fun b hb => Subring.closure_mono
      (Set.union_subset_union_right _ (Set.range_subset_range_of_subset_left
        (fun ⟨t, ht⟩ => ⟨⟨t, Finset.mem_union_left {f} ht⟩, rfl⟩))) (hN b hb)⟩

/-- The plus half is contained in the base. -/
theorem laurentPlus_subset (D₀ : RationalLocData A) (f : A) :
    rationalOpen (laurentPlusDatum D₀ f).T (laurentPlusDatum D₀ f).s ⊆
      rationalOpen D₀.T D₀.s := by
  intro v ⟨hv, hvT, hvs⟩
  exact ⟨hv, fun t ht => hvT t (Finset.mem_union_left _ ht), hvs⟩

/-- The minus half of the Laurent cover at `f` within base `D₀`:
`{v ∈ R(D₀) : v(s₀) ≤ v(f), v(f) ≠ 0}`.

Expressed as `R((T₀ ∪ {s₀}) * {s₀, f} / s₀ * f)` using `rationalOpen_inter`. -/
noncomputable def laurentMinusDatum (D₀ : RationalLocData A) (f : A) :
    RationalLocData A where
  P := D₀.P
  T := (D₀.T ∪ {D₀.s}) * {D₀.s, f}
  s := D₀.s * f
  hopen := by sorry -- needs locSubring closure for product denominator

/-- The minus half is contained in the base. -/
theorem laurentMinus_subset (D₀ : RationalLocData A) (f : A) :
    rationalOpen (laurentMinusDatum D₀ f).T (laurentMinusDatum D₀ f).s ⊆
      rationalOpen D₀.T D₀.s := by
  -- R((T₀ ∪ {s₀}) * {s₀, f} / s₀ * f) = R(T₀ ∪ {s₀} / s₀) ∩ R({s₀, f} / f)
  -- ⊆ R(T₀ ∪ {s₀} / s₀) = R(T₀ / s₀)
  intro v hv
  have := (rationalOpen_inter (D₀.T ∪ {D₀.s}) {D₀.s, f} D₀.s f
    (Finset.mem_union_right _ (Finset.mem_singleton_self _))
    (Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton_self _)))).symm ▸ hv
  rw [Set.mem_inter_iff] at this
  have h1 := this.1
  rwa [rationalOpen_insert_s] at h1

/-- The Laurent halves cover the base: for every `v ∈ R(D₀)`,
either `v(f) ≤ v(s₀)` (plus half) or `v(s₀) ≤ v(f)` (minus half).
Uses the total ordering of the value group. -/
theorem laurentCover_covers (D₀ : RationalLocData A) (f : A)
    (v : Spv A) (hv : v ∈ rationalOpen D₀.T D₀.s) :
    v ∈ rationalOpen (laurentPlusDatum D₀ f).T (laurentPlusDatum D₀ f).s ∨
    v ∈ rationalOpen (laurentMinusDatum D₀ f).T (laurentMinusDatum D₀ f).s := by
  sorry -- trichotomy: v(f) ≤ v(s₀) ∨ v(s₀) ≤ v(f), using v.vle_total or similar

/-- The 2-element Laurent covering of `D₀` at element `f`. -/
noncomputable def laurentCovering (D₀ : RationalLocData A) (f : A) :
    RationalCovering A where
  base := D₀
  covers := {laurentPlusDatum D₀ f, laurentMinusDatum D₀ f}
  hsubset D hD := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hD
    rcases hD with rfl | rfl
    · exact laurentPlus_subset D₀ f
    · exact laurentMinus_subset D₀ f
  hcover v hv := by
    rcases laurentCover_covers D₀ f v hv with h | h
    · exact ⟨_, Finset.mem_insert_self _ _, h⟩
    · exact ⟨_, Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton_self _)), h⟩

end ValuationSpectrum
