/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».RationalRefinement
import «Adic spaces».RationalSubsets
import «Adic spaces».TopologyComparison
import «Adic spaces».PresheafTateStructure
import «Adic spaces».LaurentCoverExact
import «Adic spaces».LaurentCoverTopology
import «Adic spaces».LaurentBaireSupport
import «Adic spaces».CompletionLocalization
import «Adic spaces».Example638
import «Adic spaces».IteratedRational
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors
import Mathlib.Topology.MetricSpace.Completion

/-!
# Laurent Covers and Tate Acyclicity Infrastructure

Infrastructure for proving IsSheafy (Wedhorn Theorem 8.28) via the
faithful flatness route (Corollary 8.31).

## Key facts (from reviewer):
- `1-sX` is NOT prime in `A⟨X⟩` in general (it can be a unit when s is
  topologically nilpotent). So `presheafValue D₀` is NOT a domain in general.
- The correct route: `1-sX` is a NON-ZERO-DIVISOR (regular) on `M⟨X⟩`
  for any module M. This gives flatness of `A⟨X⟩/(1-sX)` over A
  (Wedhorn Lemma 8.30, proved in `flat_quotient_oneSubfX_general`).
- IsSheafy follows from: Prop 8.15 (localization principle) + Cor 8.31
  (product restriction is faithfully flat) + Laurent cover exactness.

## Main results

* `rationalOpen_eq_iInter_singleton` : Lemma 7.54 (rational decomposition)
* `laurentCovering` : 2-element Laurent cover construction
* `rationalCovering_hasSeparation` : separation via faithful flatness
* `rationalCovering_hasGluing` : gluing via Laurent exactness

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn2019adic], Lemma 7.54, 8.30, 8.31,
  Corollary 8.31, Proposition 8.15, Theorem 8.28
-/

open Classical

noncomputable section

namespace ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A] [PlusSubring A]
  [IsTopologicalRing A]

/-! ### Lemma 7.54: rational decomposition into singletons -/

/-- **Lemma 7.54 of Wedhorn**: `R({t₁,...,tₙ}/s) = ⋂ᵢ R({tᵢ}/s)` for nonempty T. -/
theorem rationalOpen_eq_iInter_singleton (T : Finset A) (hT : T.Nonempty) (s : A) :
    rationalOpen T s = ⋂ t ∈ T, rationalOpen {t} s := by
  ext v
  simp only [Set.mem_iInter, rationalOpen, Set.mem_setOf_eq,
    Finset.mem_singleton, forall_eq, Set.mem_sep_iff]
  constructor
  · rintro ⟨hv, hvT, hvs⟩ t ht
    exact ⟨hv, hvT t ht, hvs⟩
  · intro h
    obtain ⟨t₀, ht₀⟩ := hT
    exact ⟨(h t₀ ht₀).1, fun t ht => (h t ht).2.1, (h t₀ ht₀).2.2⟩

/-! ### Laurent cover construction -/

variable [IsHuberRing A] [HasLocLiftPowerBounded A]

set_option maxHeartbeats 800000

/-- **Laurent normalization** (Wedhorn Remark 7.32 / Prop 6.4): two bundled
facts about a rational datum `D₀`:
- every element of `insert D₀.s D₀.T` is in the ring of definition `D₀.P.A₀`;
- `1 ∈ D₀.T` (plus-datum convention, giving `1/D₀.s ∈ locSubring`).

This is a strengthening of the open-ideal condition `D₀.hopen` that holds
whenever we have freely chosen `D₀.P.A₀` to contain `{D₀.s} ∪ D₀.T` and
added `1` to `T` (which does not shrink the rational subset since
`v(1) = 1 ≤ v(D₀.s)` is guaranteed after normalizing `D₀.s ∈ A⁺`).
By Wedhorn Proposition 6.4 any bounded subring extends to a ring of
definition, so for any `RationalLocData` one can always arrange this by
replacing `D₀.P` with a larger pair of definition (after normalizing
`D₀.s` to be power-bounded).

Captured as a typeclass so that instance resolution propagates the
hypothesis through the iterated-rational bridge infrastructure without
changing the signatures of individual lemmas. -/
class LaurentNormalized {A : Type*} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] (D₀ : RationalLocData A) : Prop where
  /-- Every element of `insert D₀.s D₀.T` lies in `D₀.P.A₀`. -/
  insert_s_T_subset_A₀ : ∀ a ∈ insert D₀.s D₀.T, a ∈ D₀.P.A₀
  /-- `1` lies in `D₀.T` (plus-datum convention). -/
  one_mem_T : (1 : A) ∈ D₀.T

/-- The "plus half" of the Laurent cover at `f` within base `D₀`. -/
noncomputable def laurentPlusDatum (D₀ : RationalLocData A) (f : A) :
    RationalLocData A where
  P := D₀.P
  T := insert f D₀.T
  s := D₀.s
  hopen := by
    obtain ⟨N, hN⟩ := D₀.hopen
    exact ⟨N, fun b hb => Subring.closure_mono (Set.union_subset_union_right _
      (Set.range_comp_subset_range (fun t : D₀.T => (⟨t, Finset.mem_insert_of_mem t.2⟩ :
        (insert f D₀.T : Finset A))) (fun t => divByS (t : A) D₀.s))) (hN b hb)⟩

/-- `divByS (a * b) (s * f) = divByS (a * f) (s * f) * divByS (b * s) (s * f)`.
Algebraically: `ab/(sf) = (af/(sf)) * (bs/(sf))` since `af*bs/(sf)^2 = ab/(sf)`. -/
private theorem divByS_factor' (a b s f : A) :
    divByS (a * b) (s * f) = divByS (a * f) (s * f) * divByS (b * s) (s * f) := by
  unfold divByS; rw [← IsLocalization.mk'_mul]
  exact IsLocalization.mk'_eq_of_eq (by simp only [Submonoid.coe_mul]; ring)

/-- `divByS (b * s) (s * f) = divByS (b * f) (s * f) * divByS (s * s) (s * f)`.
Both sides equal `b/f` in the localization. -/
private theorem divByS_factor2' (b s f : A) :
    divByS (b * s) (s * f) = divByS (b * f) (s * f) * divByS (s * s) (s * f) := by
  unfold divByS; rw [← IsLocalization.mk'_mul]
  exact IsLocalization.mk'_eq_of_eq (by simp only [Submonoid.coe_mul]; ring)

/-- `divByS` is additive in the numerator. -/
private theorem divByS_add' (a b s : A) :
    divByS (a + b) s = divByS a s + divByS b s := by
  unfold divByS; rw [← IsLocalization.mk'_add]
  exact IsLocalization.mk'_eq_of_eq (by simp only [Submonoid.coe_mul]; ring)

/-- The canonical lift `Away s₀ →+* Away (s₀ * f)` sends `divByS b s₀` to
`divByS (b * f) (s₀ * f)`. Both represent `b/s₀` in their respective localizations. -/
private theorem lift_divByS_eq' (s₀ f : A)
    (hs₀ : IsUnit (algebraMap A (Localization.Away (s₀ * f)) s₀)) (b : A) :
    (IsLocalization.Away.lift (S := Localization.Away s₀) (R := A) s₀ hs₀)
      (divByS b s₀) = divByS (b * f) (s₀ * f) := by
  unfold divByS
  rw [show IsLocalization.Away.lift (S := Localization.Away s₀) (R := A) s₀ hs₀ =
    IsLocalization.lift (fun (y : Submonoid.powers s₀) => by
      obtain ⟨n, hn⟩ := y.2; rw [← hn, map_pow]; exact hs₀.pow n) from rfl,
    IsLocalization.lift_mk'_spec,
    show (↑(⟨s₀, 1, pow_one s₀⟩ : Submonoid.powers s₀) : A) = s₀ from rfl]
  set S := Localization.Away (s₀ * f)
  set v := IsLocalization.mk' S (b * f)
    (⟨s₀ * f, 1, pow_one _⟩ : Submonoid.powers (s₀ * f))
  have h := IsLocalization.mk'_spec' S (b * f)
    (⟨s₀ * f, 1, pow_one _⟩ : Submonoid.powers _)
  change algebraMap A S (s₀ * f) * v = algebraMap A S (b * f) at h
  rw [map_mul, map_mul] at h
  have hf : IsUnit (algebraMap A S f) := by
    have := IsLocalization.Away.algebraMap_isUnit (R := A) (s₀ * f) (S := S)
    rw [map_mul] at this; exact isUnit_of_mul_isUnit_right this
  exact (hf.mul_right_cancel (by calc
    algebraMap A S s₀ * v * algebraMap A S f
        = algebraMap A S s₀ * algebraMap A S f * v := by ring
    _ = algebraMap A S b * algebraMap A S f := h)).symm

/-- For `b ∈ I^N₀`, `divByS (↑b * f) (s₀ * f) ∈ locSubring P T_product (s₀ * f)`.

Uses the canonical lift `φ : Away s₀ →+* Away (s₀ * f)` and `Subring.closure_induction`
to transfer the membership `divByS ↑b s₀ ∈ locSubring P T₀ s₀` from `D₀.hopen`. The lift
sends generators `algebraMap a ↦ algebraMap a` and `divByS t s₀ ↦ divByS (t*f) (s₀*f)`,
where `t*f ∈ T_product` for `t ∈ T₀`. -/
private theorem divByS_mul_f_mem' {P : PairOfDefinition A} {T₀ : Finset A}
    {s₀ : A} {N₀ : ℕ}
    (hN₀ : ∀ b : P.A₀, b ∈ P.I ^ N₀ → divByS (↑b : A) s₀ ∈ locSubring P T₀ s₀)
    (f : A) {b : P.A₀} (hb : b ∈ P.I ^ N₀) :
    let T_product := (insert s₀ T₀).product ({s₀, f} : Finset A)
        |>.image (fun p => p.1 * p.2)
    divByS ((↑b : A) * f) (s₀ * f) ∈ locSubring P T_product (s₀ * f) := by
  intro T_product
  have hs₀ : IsUnit (algebraMap A (Localization.Away (s₀ * f)) s₀) := by
    have := IsLocalization.Away.algebraMap_isUnit (R := A) (s₀ * f)
        (S := Localization.Away (s₀ * f))
    rw [map_mul] at this; exact isUnit_of_mul_isUnit_left this
  let φ : Localization.Away s₀ →+* Localization.Away (s₀ * f) :=
    IsLocalization.Away.lift (S := Localization.Away s₀) (R := A) s₀ hs₀
  rw [← lift_divByS_eq' s₀ f hs₀]
  refine Subring.closure_induction
    (p := fun x _ => φ x ∈ locSubring P T_product (s₀ * f)) ?_ ?_ ?_ ?_ ?_ ?_
    (hN₀ b hb)
  · intro x hx
    rcases hx with ⟨a, ha, rfl⟩ | ⟨⟨t, ht⟩, rfl⟩
    · rw [show φ (algebraMap A _ a) = algebraMap A _ a from
        IsLocalization.Away.lift_eq (S := Localization.Away s₀) (x := s₀) _ _]
      exact algebraMap_mem_locSubring P T_product (s₀ * f) ha
    · rw [lift_divByS_eq' s₀ f hs₀]
      exact divByS_mem_locSubring P T_product (s₀ * f) (Finset.mem_image.mpr
        ⟨(t, f), Finset.mem_product.mpr ⟨Finset.mem_insert_of_mem ht,
          Finset.mem_insert_of_mem (Finset.mem_singleton_self f)⟩, rfl⟩)
  · simp [map_zero, (locSubring P T_product (s₀ * f)).zero_mem]
  · simp [map_one, (locSubring P T_product (s₀ * f)).one_mem]
  · intro x y _ _ hx hy
    rw [map_add]; exact (locSubring P T_product (s₀ * f)).add_mem hx hy
  · intro x _ hx
    rw [map_neg]; exact (locSubring P T_product (s₀ * f)).neg_mem hx
  · intro x y _ _ hx hy
    rw [map_mul]; exact (locSubring P T_product (s₀ * f)).mul_mem hx hy

/-- The "minus half" of the Laurent cover at `f` within base `D₀`. -/
noncomputable def laurentMinusDatum (D₀ : RationalLocData A) (f : A) :
    RationalLocData A where
  P := D₀.P
  T := (insert D₀.s D₀.T).product ({D₀.s, f} : Finset A) |>.image (fun p => p.1 * p.2)
  s := D₀.s * f
  hopen := by
    obtain ⟨N₀, hN₀⟩ := D₀.hopen
    refine ⟨2 * N₀, fun b hb => ?_⟩
    rw [show 2 * N₀ = N₀ + N₀ from by omega, pow_add] at hb
    refine Submodule.mul_induction_on hb ?_ ?_
    · intro c hc d hd
      change divByS (↑(c * d) : A) _ ∈ _
      rw [show (c * d : D₀.P.A₀).val = c.val * d.val from rfl,
        divByS_factor' _ _ D₀.s f, divByS_factor2' _ D₀.s f]
      exact (locSubring _ _ _).mul_mem (divByS_mul_f_mem' hN₀ f hc)
        ((locSubring _ _ _).mul_mem (divByS_mul_f_mem' hN₀ f hd)
          (divByS_mem_locSubring _ _ _ (Finset.mem_image.mpr
            ⟨(D₀.s, D₀.s), Finset.mem_product.mpr ⟨Finset.mem_insert_self _ _,
              Finset.mem_insert_self _ _⟩, rfl⟩)))
    · intro y₁ y₂ hy₁ hy₂
      rw [show (y₁ + y₂ : D₀.P.A₀).val = y₁.val + y₂.val from rfl,
        divByS_add' _ _ _]
      exact (locSubring _ _ _).add_mem hy₁ hy₂

/-- The plus half is contained in the base. -/
theorem laurentPlus_subset (D₀ : RationalLocData A) (f : A) :
    rationalOpen (laurentPlusDatum D₀ f).T (laurentPlusDatum D₀ f).s ⊆
      rationalOpen D₀.T D₀.s := by
  intro v ⟨hv, hvT, hvs⟩
  refine ⟨hv, fun t ht => hvT t (Finset.mem_insert_of_mem ht), hvs⟩

open scoped Pointwise in
/-- The minus half is contained in the base. -/
theorem laurentMinus_subset (D₀ : RationalLocData A) (f : A) :
    rationalOpen (laurentMinusDatum D₀ f).T (laurentMinusDatum D₀ f).s ⊆
      rationalOpen D₀.T D₀.s := by
  have hT : (laurentMinusDatum D₀ f).T = insert D₀.s D₀.T * ({D₀.s, f} : Finset A) := by
    simp only [laurentMinusDatum, Finset.mul_def]; rfl
  rw [show (laurentMinusDatum D₀ f).s = D₀.s * f from rfl, hT,
    ← rationalOpen_inter (insert D₀.s D₀.T) ({D₀.s, f} : Finset A) D₀.s f
      (Finset.mem_insert_self D₀.s D₀.T) (Finset.mem_insert_of_mem (Finset.mem_singleton_self f)),
    rationalOpen_insert_s]
  exact Set.inter_subset_left

/-- The Laurent halves cover the base (valuation trichotomy). -/
theorem laurentCover_covers (D₀ : RationalLocData A) (f : A)
    (v : Spv A) (hv : v ∈ rationalOpen D₀.T D₀.s) :
    v ∈ rationalOpen (laurentPlusDatum D₀ f).T (laurentPlusDatum D₀ f).s ∨
    v ∈ rationalOpen (laurentMinusDatum D₀ f).T (laurentMinusDatum D₀ f).s := by
  obtain ⟨hvspa, hvT, hvs⟩ := hv
  rcases v.vle_total f D₀.s with h | h
  · left
    exact ⟨hvspa, fun t ht => by
      rcases Finset.mem_insert.mp ht with rfl | ht'
      · exact h
      · exact hvT t ht', hvs⟩
  · right
    open scoped Pointwise in
    rw [show rationalOpen (laurentMinusDatum D₀ f).T (laurentMinusDatum D₀ f).s =
      rationalOpen (insert D₀.s D₀.T) D₀.s ∩ rationalOpen {D₀.s, f} f from by
        simp only [laurentMinusDatum]
        rw [show Finset.image (fun p => p.1 * p.2) (Finset.product (insert D₀.s D₀.T) {D₀.s, f})
          = insert D₀.s D₀.T * ({D₀.s, f} : Finset A) from by simp [Finset.mul_def]]
        rw [← rationalOpen_inter (insert D₀.s D₀.T) {D₀.s, f} D₀.s f
          (Finset.mem_insert_self _ _) (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))]]
    rw [rationalOpen_insert_s]
    exact ⟨⟨hvspa, hvT, hvs⟩, ⟨hvspa, fun t ht => by
      rcases Finset.mem_insert.mp ht with rfl | ht'
      · exact h
      · rw [Finset.mem_singleton.mp ht']; exact v.vle_refl f,
      fun hf0 => hvs (v.vle_trans h hf0)⟩⟩

/-- The 2-element Laurent covering of `D₀` at element `f`. -/
noncomputable def laurentCovering (D₀ : RationalLocData A) (f : A) :
    RationalCovering A where
  base := D₀
  covers := {laurentPlusDatum D₀ f, laurentMinusDatum D₀ f}
  hsubset D hD := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hD
    exact hD.elim (· ▸ laurentPlus_subset D₀ f) (· ▸ laurentMinus_subset D₀ f)
  hcover v hv := by
    rcases laurentCover_covers D₀ f v hv with h | h
    · exact ⟨_, Finset.mem_insert_self _ _, h⟩
    · exact ⟨_, Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton_self _)), h⟩

/-! ### IsSheafy via faithful flatness (Wedhorn Corollary 8.31)

The correct proof route (per reviewer):
1. `1-sX` is regular on `M⟨X⟩` (Wedhorn Lemma 8.30) — gives flatness
2. Prop 8.15: presheafValue D = rational localization of presheafValue D₀
3. Cor 8.31: product restriction is faithfully flat for finite rational covers
4. Faithfully flat → injective → embedding (field 1 of IsSheafy)
5. Laurent cover Čech exactness → gluing (field 2 of IsSheafy)

Key existing results:
- `flat_quotient_oneSubfX_general` : A⟨X⟩/(1-sX) flat over A (0 sorry)
- `presheafValue_flat_of_tateQuotient` : presheafValue D flat over A (0 sorry)
- `epsilonHom_gen_injective` : Laurent separation (0 sorry)
- `laurentCover_exact` : full Laurent exactness (discrete, 0 sorry)

NOTE: `1-sX` is NOT prime in general (can be a unit when s is top. nilpotent).
So presheafValue D₀ is NOT necessarily a domain. The proof uses flatness
and faithful flatness, NOT the domain/localization argument. -/

/-! ### Defect-correction gluing — DELETED (2026-04-08)

The defect-correction approach (`density_approximation`, `defect_correction_exists`,
`compatible_sections_in_image`) was abandoned in favor of Wedhorn's flatness
route. It tried to prove a TOPOLOGICAL embedding for the product restriction via
Banach open mapping, but our `IsSheafy` class only requires sheaf-of-sets (no
topological embedding). Wedhorn's proof of Theorem 8.28(b) gives sheaf-of-
abelian-groups directly via Lemma 8.31 (flatness) + Lemma 8.33 (3×3 diagram
chase) + Lemma 8.34 (refinement transfer), with no topology.

See `docs/plans/2026-04-08-wedhorn-vs-zavyalov.md`. -/

/-! ### Laurent cover gluing via `row3_exact` (Wedhorn Lemma 8.33)

For a 2-element Laurent cover of `Spa(A)` at element `f`, the presheaf gluing
condition follows from the algebraic exact sequence

  `0 → A →ε B₁ × B₂ →δ B₁₂ → 0`

proved in `LaurentCoverExact.row3_exact`. The bridge between the algebraic
quotients (`B₁_gen f`, `B₂_gen f`) and the presheaf values (`presheafValue D`)
goes through `presheafValueCanonicalQuotientEquiv` from `TopologyComparison.lean`.

**Type identifications:**
- `B₁_gen f = A⟨X⟩/(f-X)`: evaluation at `X = f` gives `B₁_gen f ≅ A`
  (proved as `quotientFSubXEquiv` for discrete A; general case via
  `presheafValueCanonicalQuotientEquiv` applied to the plus-piece datum
  with `s = D₀.s`).
- `B₂_gen f = A⟨X⟩/(1-fX)`: this is definitionally `TateAlgebra A ⧸ oneSubfXIdeal f`,
  identified with `presheafValue (laurentMinusDatum D₀ f)` via
  `presheafValueCanonicalQuotientEquiv` (with `s = D₀.s * f`).
- `presheafValue D₀ ≅ A` when `D₀` is the trivial datum and `A` is complete.

**Restriction map correspondence:**
- `restrictionMap D₀ (laurentPlusDatum D₀ f)` corresponds to `π₁ ∘ ε` (first
  projection of the diagonal).
- `restrictionMap D₀ (laurentMinusDatum D₀ f)` corresponds to `π₂ ∘ ε` (second
  projection).
- Compatibility on the overlap (delta = 0) corresponds to the two sections
  agreeing in `B₁₂_gen f = A⟨ζ, ζ⁻¹⟩/(f-ζ)`. -/

/-! ### Helper lemmas for Laurent cover gluing (infrastructure gaps)

**Proof strategy** (updated from the original `row3_exact` transport plan):

The transport through `row3_exact` requires bridge lemmas identifying
`presheafValue (laurentPlusDatum D₀ f) ≃+* B₁_gen f` and similarly for the
minus piece. These bridges depend on nontrivial infrastructure (Phase 2 of the
Wedhorn plan: Example 6.38 as topological ring iso, Prop 6.17 on closed ideals).

Instead, the proof uses the partition-of-unity approach from `discrete_gluing`:
1. Find an algebraic preimage `x' : Localization.Away D₀.s` via the partition
   of unity for the 2-element Laurent cover.
2. Lift to `presheafValue D₀` via `D₀.coeRingHom` (the completion embedding).
3. Verify via `extensionHom_coe` (restriction maps commute with completion).

The proof of `laurentCover_gluing_presheaf` uses the 2-element Laurent covering
`{R(T ∪ {f} / s), R(T' / s·f)}` of the base `R(T/s)`.

**Architecture**: The partition-of-unity approach (as in `discrete_gluing` from
`TateAcyclicity.lean`) works at the localization level and lifts to completions.
For a 2-element cover `{D₊, D₋}`, the proof requires:
1. Finding `x' : Localization.Away D₀.s` with `restrictionMapAlg D₀ D± _ x' = f±`.
2. Lifting `x'` to `presheafValue D₀` via `D₀.coeRingHom`.

Step 1 reduces to the partition-of-unity argument: the elements `D₊.s` and `D₋.s`
generate the unit ideal in `Localization.Away D₀.s` (from the covering condition
on the spectrum), so `∑ c_i * s_i^N = 1` gives the global section `x' = ∑ c_i * r_i`.

The key infrastructure gaps are:
- `span_top_of_laurentCover`: the images of `D₊.s` and `D₋.s` generate `⊤` in
  `Localization.Away D₀.s`.
- `laurentCover_numerator_compat`: cross-compatibility of numerators after
  absorbing powers.
- `laurentCover_restrictionMapAlg_dense_surj`: every element of `presheafValue D±`
  is in the range of `restrictionMapAlg D₀ D± _` (the algebraic restriction is
  surjective onto the dense image, then extends).

**Note**: the plus datum has `(laurentPlusDatum D₀ f).s = D₀.s` (SAME generator),
so `Localization.Away (laurentPlusDatum D₀ f).s = Localization.Away D₀.s`. Only
the topology (determined by `T`) differs. The minus datum has
`(laurentMinusDatum D₀ f).s = D₀.s * f`, a genuinely different localization. -/

/-- The images of the Laurent-piece generators span `⊤` in the base localization.

For a Laurent cover `{D₊, D₋}` of `D₀`, the element `D₀.s` is in the radical
of `Ideal.span {D₊.s, D₋.s}` in `A` (from the covering condition: every point
of `rationalOpen D₀.T D₀.s` lies in one of the two pieces). Hence the images
span `⊤` in `Localization.Away D₀.s`. -/
theorem span_top_of_laurentCover
    [IsTateRing A] [IsNoetherianRing A] [T2Space A]
    [NonarchimedeanRing A]
    (D₀ : RationalLocData A) (f : A) :
    Ideal.span {algebraMap A (Localization.Away D₀.s) (laurentPlusDatum D₀ f).s,
      algebraMap A (Localization.Away D₀.s) (laurentMinusDatum D₀ f).s} = ⊤ := by
  -- (laurentPlusDatum D₀ f).s = D₀.s and (laurentMinusDatum D₀ f).s = D₀.s * f.
  -- So we need: Ideal.span {algebraMap D₀.s, algebraMap (D₀.s * f)} = ⊤
  -- in Localization.Away D₀.s.
  -- Since algebraMap D₀.s is a unit in Localization.Away D₀.s, we have
  -- 1 ∈ Ideal.span {algebraMap D₀.s, ...} immediately.
  change Ideal.span {algebraMap A (Localization.Away D₀.s) D₀.s,
    algebraMap A (Localization.Away D₀.s) (laurentMinusDatum D₀ f).s} = ⊤
  exact Ideal.eq_top_of_isUnit_mem _
    (Ideal.subset_span (Set.mem_insert _ _))
    (IsLocalization.Away.algebraMap_isUnit D₀.s)

/-! ### Laurent cover gluing — Route A (`Localization.Away` preimage)

Removed 2026-04-14. The theorem `laurentCover_algebraic_gluing` asked for a
pre-completion element `x' : Localization.Away D₀.s` restricting to the given
completed sections `u±`. This is strictly stronger than the presheaf-level
gluing (which allows `x : presheafValue D₀`) and requires the Baire-category
surjection `restrictionMapHom_surj` (PresheafTateStructure.lean:1226) — itself
a substantial sorry. Route B (below) avoids this entirely via `row3_exact` at
`presheafValue D₀` and five explicit type-bridge stubs. -/

/-! ### Route B: Laurent cover gluing via `row3_exact` at `presheafValue D₀`

The frozen 2026-04-14 investigation established that `LaurentCover.row3_exact`
instantiates cleanly at `A := presheafValue D₀`: the completion has the
required `[UniformSpace]`, `[IsUniformAddGroup]`, `[T2Space]`, `[CompleteSpace]`,
and `[NonarchimedeanRing]` instances. The theorem statement uses
`[CommRing]`/`[TopologicalSpace]`/`[NonarchimedeanRing]` plus the four uniform
properties — it does NOT require `[IsNoetherianRing]` or `[IsDomain]` on the
instantiated base.

This gives an alternative route to `laurentCover_gluing_presheaf` that avoids
`restrictionMapHom_surj` (the Baire blocker). The remaining work is the type
bridge: building `RingEquiv`s from `presheafValue (laurent±Datum D₀ f)` to the
algebraic quotients `B_gen (D₀.canonicalMap f)` in `TateAlgebra (presheafValue D₀)`,
with restriction maps factoring through them. Cf. `presheafValueTateQuotientEquiv`
(TopologyComparison.lean:831), which gives the base-level analogue over `A`.

The statement below captures the target. -/

/-! #### Iterated rational data over `B := presheafValue D₀`

Per the 2026-04-14 reviewer addendum, the Laurent bridges are recovered
from a single generic identification: `presheafValue_A(laurent±Datum D₀ f)`
matches a rational localization of `B = presheafValue D₀` at `canonicalMap f`
(Wedhorn Lemma 2.13 / Prop 8.7 — iterated rational localizations collapse
to rational localizations of the new base).

The data below packages the target rational datum on `B`. The plus branch
uses `T = {canonicalMap f}`, `s = 1`; the minus branch uses `T = {1}`,
`s = canonicalMap f`. In both cases the `hopen` condition is discharged by
`hopen_away_one` (the plus branch directly; the minus branch via the
standard "localization-at-1 identity"). -/

/-- The trivial "plus" rational datum on `B := presheafValue D₀` at
`canonicalMap f`. Carves out `{v_B : v_B(canonicalMap f) ≤ 1}` in `Spa B`,
which corresponds under Wedhorn Lemma 2.13 to `rationalOpen (laurentPlusDatum D₀ f).T
(laurentPlusDatum D₀ f).s ⊂ Spa A`. -/
noncomputable def iteratedPlusDatum_B
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (D₀ : RationalLocData A)
    [IsNoetherianRing (locSubring D₀.P D₀.T D₀.s)]
    (f : A) : RationalLocData (presheafValue D₀) where
  P := presheafValue_pairOfDefinition_concrete P D₀
  T := {D₀.canonicalMap f}
  s := 1
  hopen := hopen_away_one _ _

/-- The trivial "minus" rational datum on `B := presheafValue D₀` at
`canonicalMap f`. Carves out `{v_B : v_B(1) ≤ v_B(canonicalMap f)}`
(equivalently `v_B(canonicalMap f) ≥ 1`) in `Spa B`, which corresponds under
Wedhorn Lemma 2.13 to `rationalOpen (laurentMinusDatum D₀ f).T
(laurentMinusDatum D₀ f).s ⊂ Spa A`. -/
noncomputable def iteratedMinusDatum_B
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (D₀ : RationalLocData A)
    [IsNoetherianRing (locSubring D₀.P D₀.T D₀.s)]
    (f : A) : RationalLocData (presheafValue D₀) where
  P := presheafValue_pairOfDefinition_concrete P D₀
  T := {1}
  s := D₀.canonicalMap f
  hopen := ⟨0, fun b _ => by
    -- `divByS b.val (canonicalMap f) = algebraMap b.val * divByS 1 (canonicalMap f)`
    -- and both factors lie in `locSubring P_B {1} (canonicalMap f)`:
    -- `algebraMap b.val` via `algebraMap_mem_locSubring` (since `b.val ∈ P_B.A₀`),
    -- `divByS 1 (canonicalMap f)` via `divByS_mem_locSubring` (since `1 ∈ {1}`).
    have hmul : algebraMap (presheafValue D₀) _ (b : presheafValue D₀) *
        divByS (1 : presheafValue D₀) (D₀.canonicalMap f) =
        divByS (b : presheafValue D₀) (D₀.canonicalMap f) := by
      unfold divByS
      rw [← IsLocalization.mk'_one (M := Submonoid.powers (D₀.canonicalMap f))
            (S := Localization.Away (D₀.canonicalMap f)) (b : presheafValue D₀),
          ← IsLocalization.mk'_mul, one_mul, mul_one]
    rw [← hmul]
    exact (locSubring _ _ _).mul_mem
      (algebraMap_mem_locSubring _ _ _ b.2)
      (divByS_mem_locSubring _ _ _ (Finset.mem_singleton_self 1))⟩

/-! #### Uncompleted forward / backward infrastructure for Wedhorn Lemma 2.13

The iterated identifications `presheafValue (laurent±Datum D₀ f) ≃+*
presheafValue (iterated±Datum_B P D₀ f)` are built in three stages:

1. **Uncompleted maps** (below) — forward and backward ring homs at the
   `Localization.Away` level, fully proved via `IsLocalization.Away.lift`.
2. **Continuity** — the Wedhorn Prop 8.2 analogue across the base change
   `A → B = presheafValue D₀`. Currently expected as an explicit hypothesis
   in any closed-form proof of the equivs; this is what blocks a full
   closure of `presheafValue_iteratedPlus_equiv` / `presheafValue_iteratedMinus_equiv`
   without further infrastructure.
3. **Extension to completions + round-trip** via `UniformSpace.Completion.extensionHom`
   + `Completion.ext'`, using the backward-forward identity proved below.

This block provides the stage-1 infrastructure: it is fully proved (no sorries)
and is structural preparation for any future closure of the two equivs. -/

/-- `D₀.s` maps to a unit in `Localization.Away (1 : B)` under the composite
`A → B = presheafValue D₀ → Loc_B(1)`. -/
theorem iteratedPlus_D₀s_isUnit_in_Loc_B_one
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (D₀ : RationalLocData A) :
    IsUnit ((algebraMap (presheafValue D₀)
        (Localization.Away (1 : presheafValue D₀))).comp
      D₀.canonicalMap D₀.s) := by
  show IsUnit (algebraMap (presheafValue D₀) _ (D₀.canonicalMap D₀.s))
  exact (isUnit_s_in_presheafValue D₀).map _

/-- Forward uncompleted hom `Loc_A(D₀.s) →+* Loc_B(1)` for the plus branch.

Since `laurentPlusDatum D₀ f` has `s = D₀.s` (SAME generator as `D₀`), the
source is `Loc_A(D₀.s)`. The target `iteratedPlusDatum_B` has `s_B = 1`, so
`Loc_B(1)`. Built via `IsLocalization.Away.lift` from `A → B → Loc_B(1)`. -/
noncomputable def iteratedPlus_forwardLocHom
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (D₀ : RationalLocData A) :
    Localization.Away D₀.s →+*
      Localization.Away (1 : presheafValue D₀) :=
  IsLocalization.Away.lift (S := Localization.Away D₀.s) (R := A) D₀.s
    (iteratedPlus_D₀s_isUnit_in_Loc_B_one D₀)

/-- `iteratedPlus_forwardLocHom` on `algebraMap A _ a` equals
`algebraMap B _ (canonicalMap a)`. -/
theorem iteratedPlus_forwardLocHom_algebraMap
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (D₀ : RationalLocData A) (a : A) :
    iteratedPlus_forwardLocHom D₀
      (algebraMap A (Localization.Away D₀.s) a) =
      algebraMap (presheafValue D₀)
        (Localization.Away (1 : presheafValue D₀)) (D₀.canonicalMap a) :=
  IsLocalization.Away.lift_eq D₀.s (iteratedPlus_D₀s_isUnit_in_Loc_B_one D₀) a

/-- Forward uncompleted hom to the completion of `iteratedPlusDatum_B`:
the composite `Loc_A(D₀.s) → Loc_B(1) → presheafValue (iteratedPlusDatum_B)`. -/
noncomputable def iteratedPlus_forwardToCompletion
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (D₀ : RationalLocData A) [IsNoetherianRing (locSubring D₀.P D₀.T D₀.s)]
    (f : A) :
    Localization.Away (laurentPlusDatum D₀ f).s →+*
      presheafValue (iteratedPlusDatum_B P D₀ f) :=
  (iteratedPlusDatum_B P D₀ f).coeRingHom.comp (iteratedPlus_forwardLocHom D₀)

/-- Backward uncompleted hom `Loc_B(1) →+* presheafValue (laurentPlusDatum D₀ f)`
via `IsLocalization.Away.lift` at `1` (trivially a unit), with
`restrictionMapHom D₀ (laurentPlus)` as the base hom `B → presheafValue (laurentPlus)`. -/
noncomputable def iteratedPlus_backwardLocHom
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (D₀ : RationalLocData A) (f : A)
    (hsub : rationalOpen (laurentPlusDatum D₀ f).T (laurentPlusDatum D₀ f).s ⊆
      rationalOpen D₀.T D₀.s) :
    Localization.Away (1 : presheafValue D₀) →+*
      presheafValue (laurentPlusDatum D₀ f) :=
  IsLocalization.Away.lift (S := Localization.Away (1 : presheafValue D₀))
    (R := presheafValue D₀) (1 : presheafValue D₀)
    (g := restrictionMapHom D₀ (laurentPlusDatum D₀ f) hsub)
    (by simpa using isUnit_one)

/-- The backward loc hom composed with `algebraMap B _` equals `restrictionMapHom`. -/
theorem iteratedPlus_backwardLocHom_algebraMap
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (D₀ : RationalLocData A) (f : A)
    (hsub : rationalOpen (laurentPlusDatum D₀ f).T (laurentPlusDatum D₀ f).s ⊆
      rationalOpen D₀.T D₀.s)
    (b : presheafValue D₀) :
    iteratedPlus_backwardLocHom D₀ f hsub
      (algebraMap (presheafValue D₀)
        (Localization.Away (1 : presheafValue D₀)) b) =
      restrictionMapHom D₀ (laurentPlusDatum D₀ f) hsub b :=
  IsLocalization.Away.lift_eq (1 : presheafValue D₀)
    (by simpa using isUnit_one) b

/-- Backward-then-forward on the uncompleted level: going via
`backward : Loc_B(1) → presheafValue (laurentPlusDatum)` then
`forward_complete : presheafValue (laurentPlusDatum) → presheafValue (iteratedPlusDatum_B)`
is NOT the identity in general (it's only meaningful at the completion level).
However, the UNCOMPLETED composition `backward ∘ forward` from `Loc_A(D₀.s)` to
`presheafValue (laurentPlusDatum)` *is* the canonical map — see below.

Concretely: the composition `iteratedPlus_backwardLocHom ∘ iteratedPlus_forwardLocHom`
as a hom `Loc_A(D₀.s) → presheafValue (laurentPlusDatum)` equals
`(laurentPlusDatum D₀ f).coeRingHom`. This is the key uncompleted-level
identity needed for the `backward ∘ forward = id` round trip at the completion
level (via `Completion.ext'` on the dense `coeRingHom` image). -/
theorem iteratedPlus_backward_forward_locHom
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (D₀ : RationalLocData A) (f : A)
    (hsub : rationalOpen (laurentPlusDatum D₀ f).T (laurentPlusDatum D₀ f).s ⊆
      rationalOpen D₀.T D₀.s) :
    (iteratedPlus_backwardLocHom D₀ f hsub).comp
      (iteratedPlus_forwardLocHom D₀) =
      (laurentPlusDatum D₀ f).coeRingHom := by
  apply IsLocalization.ringHom_ext (Submonoid.powers D₀.s)
  ext a
  show iteratedPlus_backwardLocHom D₀ f hsub
    (iteratedPlus_forwardLocHom D₀ (algebraMap A _ a)) =
    (laurentPlusDatum D₀ f).coeRingHom (algebraMap A _ a)
  rw [iteratedPlus_forwardLocHom_algebraMap,
      iteratedPlus_backwardLocHom_algebraMap,
      restrictionMapHom_canonicalMap]
  rfl

/-! #### Minus branch: uncompleted forward / backward infrastructure -/

/-- Composite `A → presheafValue D₀ → Loc_B(canonicalMap f)`. -/
noncomputable def iteratedMinus_baseHom
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (D₀ : RationalLocData A) (f : A) :
    A →+* Localization.Away (D₀.canonicalMap f) :=
  (algebraMap (presheafValue D₀) (Localization.Away (D₀.canonicalMap f))).comp
    D₀.canonicalMap

/-- `D₀.s * f` becomes a unit in `Localization.Away (canonicalMap f)` via the
base hom: `D₀.s` maps to a unit (since `canonicalMap D₀.s` is a unit in B,
preserved by `algebraMap`) and `f` maps to a unit (localization element). -/
theorem iteratedMinus_D₀s_mul_f_isUnit
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (D₀ : RationalLocData A) (f : A) :
    IsUnit (iteratedMinus_baseHom D₀ f (D₀.s * f)) := by
  show IsUnit (algebraMap (presheafValue D₀) _ (D₀.canonicalMap (D₀.s * f)))
  rw [map_mul, map_mul]
  exact ((isUnit_s_in_presheafValue D₀).map _).mul
    (IsLocalization.Away.algebraMap_isUnit (D₀.canonicalMap f))

/-- Forward uncompleted hom `Loc_A(D₀.s·f) →+* Loc_B(canonicalMap f)`. -/
noncomputable def iteratedMinus_forwardLocHom
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (D₀ : RationalLocData A) (f : A) :
    Localization.Away (D₀.s * f) →+*
      Localization.Away (D₀.canonicalMap f) :=
  IsLocalization.Away.lift (S := Localization.Away (D₀.s * f)) (R := A)
    (D₀.s * f) (iteratedMinus_D₀s_mul_f_isUnit D₀ f)

/-- `iteratedMinus_forwardLocHom` on `algebraMap a` equals `iteratedMinus_baseHom a`. -/
theorem iteratedMinus_forwardLocHom_algebraMap
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (D₀ : RationalLocData A) (f : A) (a : A) :
    iteratedMinus_forwardLocHom D₀ f
      (algebraMap A (Localization.Away (D₀.s * f)) a) =
      iteratedMinus_baseHom D₀ f a :=
  IsLocalization.Away.lift_eq (D₀.s * f) (iteratedMinus_D₀s_mul_f_isUnit D₀ f) a

/-- Forward uncompleted hom to the completion of `iteratedMinusDatum_B`. -/
noncomputable def iteratedMinus_forwardToCompletion
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (D₀ : RationalLocData A) [IsNoetherianRing (locSubring D₀.P D₀.T D₀.s)]
    (f : A) :
    Localization.Away (laurentMinusDatum D₀ f).s →+*
      presheafValue (iteratedMinusDatum_B P D₀ f) :=
  (iteratedMinusDatum_B P D₀ f).coeRingHom.comp
    (iteratedMinus_forwardLocHom D₀ f)

/-- In `Localization.Away (D₀.s * f)`, the algebraMap of `f` is a unit. -/
theorem algebraMap_f_isUnit_in_laurentMinus
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (D₀ : RationalLocData A) (f : A) :
    IsUnit (algebraMap A (Localization.Away (D₀.s * f)) f) := by
  have hmul : algebraMap A (Localization.Away (D₀.s * f)) (D₀.s * f) =
      algebraMap A _ D₀.s * algebraMap A _ f := map_mul _ _ _
  have hu : IsUnit (algebraMap A (Localization.Away (D₀.s * f)) (D₀.s * f)) :=
    IsLocalization.Away.algebraMap_isUnit _
  rw [hmul] at hu
  exact isUnit_of_mul_isUnit_right hu

/-- In `presheafValue (laurentMinusDatum D₀ f)`, the canonical image of `f` is a unit. -/
theorem canonicalMap_f_isUnit_in_laurentMinus
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (D₀ : RationalLocData A) (f : A) :
    IsUnit ((laurentMinusDatum D₀ f).canonicalMap f) := by
  unfold RationalLocData.canonicalMap
  simp only [RingHom.coe_comp, Function.comp_apply]
  exact RingHom.isUnit_map _ (algebraMap_f_isUnit_in_laurentMinus D₀ f)

/-- `restrictionMapHom D₀ (laurentMinus) (canonicalMap f)` is a unit. -/
theorem restrictionMap_canonicalMap_f_isUnit_laurentMinus
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (D₀ : RationalLocData A) (f : A)
    (hsub : rationalOpen (laurentMinusDatum D₀ f).T (laurentMinusDatum D₀ f).s ⊆
      rationalOpen D₀.T D₀.s) :
    IsUnit (restrictionMapHom D₀ (laurentMinusDatum D₀ f) hsub
      (D₀.canonicalMap f)) := by
  rw [restrictionMapHom_canonicalMap]
  exact canonicalMap_f_isUnit_in_laurentMinus D₀ f

/-- Backward uncompleted hom `Loc_B(canonicalMap f) →+* presheafValue (laurentMinus)`
via `IsLocalization.Away.lift` with `canonicalMap f` sent to a unit in the target. -/
noncomputable def iteratedMinus_backwardLocHom
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (D₀ : RationalLocData A) (f : A)
    (hsub : rationalOpen (laurentMinusDatum D₀ f).T (laurentMinusDatum D₀ f).s ⊆
      rationalOpen D₀.T D₀.s) :
    Localization.Away (D₀.canonicalMap f) →+*
      presheafValue (laurentMinusDatum D₀ f) :=
  IsLocalization.Away.lift (S := Localization.Away (D₀.canonicalMap f))
    (R := presheafValue D₀) (D₀.canonicalMap f)
    (g := restrictionMapHom D₀ (laurentMinusDatum D₀ f) hsub)
    (restrictionMap_canonicalMap_f_isUnit_laurentMinus D₀ f hsub)

/-- Backward loc hom on `algebraMap B _`: equals `restrictionMapHom`. -/
theorem iteratedMinus_backwardLocHom_algebraMap
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (D₀ : RationalLocData A) (f : A)
    (hsub : rationalOpen (laurentMinusDatum D₀ f).T (laurentMinusDatum D₀ f).s ⊆
      rationalOpen D₀.T D₀.s) (b : presheafValue D₀) :
    iteratedMinus_backwardLocHom D₀ f hsub
      (algebraMap (presheafValue D₀)
        (Localization.Away (D₀.canonicalMap f)) b) =
      restrictionMapHom D₀ (laurentMinusDatum D₀ f) hsub b :=
  IsLocalization.Away.lift_eq (D₀.canonicalMap f)
    (restrictionMap_canonicalMap_f_isUnit_laurentMinus D₀ f hsub) b

/-- The uncompleted round-trip identity (minus branch): the composition
`iteratedMinus_backwardLocHom ∘ iteratedMinus_forwardLocHom` from
`Loc_A(D₀.s·f) → presheafValue (laurentMinusDatum)` equals
`(laurentMinusDatum D₀ f).coeRingHom`. -/
theorem iteratedMinus_backward_forward_locHom
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (D₀ : RationalLocData A) (f : A)
    (hsub : rationalOpen (laurentMinusDatum D₀ f).T (laurentMinusDatum D₀ f).s ⊆
      rationalOpen D₀.T D₀.s) :
    (iteratedMinus_backwardLocHom D₀ f hsub).comp
      (iteratedMinus_forwardLocHom D₀ f) =
      (laurentMinusDatum D₀ f).coeRingHom := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (D₀.s * f))
  ext a
  show iteratedMinus_backwardLocHom D₀ f hsub
    (iteratedMinus_forwardLocHom D₀ f (algebraMap A _ a)) =
    (laurentMinusDatum D₀ f).coeRingHom (algebraMap A _ a)
  rw [iteratedMinus_forwardLocHom_algebraMap,
      iteratedMinus_baseHom, RingHom.comp_apply,
      iteratedMinus_backwardLocHom_algebraMap,
      restrictionMapHom_canonicalMap]
  rfl

/-! #### Plus-branch continuity residuals (Wedhorn Prop 8.2 analogues)

Structure (mirroring the minus branch): the forward / backward homs are
extracted as named `noncomputable def`s depending on named continuity
theorems (Wedhorn Prop 8.2 analogues, recorded as sorries). The equiv
`presheafValue_iteratedPlus_equiv` (below) is assembled from these
ingredients plus two round-trip theorems — round-trip 1 is proved via
`Completion.ext'`; round-trip 2 is recorded as a named sorry pending the
density-of-canonicalMap argument. -/

/-! #### Power-boundedness helpers for the plus-branch forward map

The forward uncompleted map `iteratedPlus_forwardLocHom D₀ : Loc_A(D₀.s) →
Loc_B(1)` sends each generator `divByS t D₀.s` (for `t ∈ insert f D₀.T`,
the `T` of `laurentPlusDatum`) to an element which must be power-bounded
in `Loc_B(1)` with `(iteratedPlusDatum_B P D₀ f).topology`.

We package this as a single helper lemma `iteratedPlus_forwardLocHom_generators_powerBounded`
(Wedhorn Prop 8.2 / Lemma 2.13 content, deferred). -/

/-- Helper for the plus-forward power-bounded proof: the forward loc-hom
`Loc_A(D₀.s) → Loc_B(1)` sends `divByS x D₀.s` to
`algebraMap_B(D₀.coeRingHom(divByS x D₀.s))`. Both sides satisfy the same
defining equation (after multiplication by the unit `algebraMap_B(canonicalMap D₀.s)`). -/
private theorem iteratedPlus_forwardLocHom_divByS
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (D₀ : RationalLocData A) (x : A) :
    iteratedPlus_forwardLocHom D₀ (divByS x D₀.s) =
    algebraMap (presheafValue D₀) (Localization.Away (1 : presheafValue D₀))
      (D₀.coeRingHom (divByS x D₀.s)) := by
  set B := presheafValue D₀
  have hu_s_tgt : IsUnit (algebraMap B (Localization.Away (1 : B))
      (D₀.canonicalMap D₀.s)) := (isUnit_s_in_presheafValue D₀).map _
  apply hu_s_tgt.mul_right_cancel
  have hrel : divByS x D₀.s * algebraMap A (Localization.Away D₀.s) D₀.s =
      algebraMap A (Localization.Away D₀.s) x := by
    unfold divByS
    rw [← IsLocalization.mk'_one (M := Submonoid.powers D₀.s)
          (S := Localization.Away D₀.s) D₀.s,
        ← IsLocalization.mk'_mul,
        ← IsLocalization.mk'_one (M := Submonoid.powers D₀.s)
          (S := Localization.Away D₀.s) x]
    exact IsLocalization.mk'_eq_of_eq (by simp only [Submonoid.coe_mul]; ring)
  have hlhs := congrArg (iteratedPlus_forwardLocHom D₀) hrel
  rw [map_mul, iteratedPlus_forwardLocHom_algebraMap,
    iteratedPlus_forwardLocHom_algebraMap] at hlhs
  rw [hlhs, ← map_mul]
  congr 1
  -- Show `D₀.canonicalMap x = D₀.coeRingHom(divByS x D₀.s) * D₀.canonicalMap D₀.s`.
  change D₀.coeRingHom (algebraMap A _ x) =
    D₀.coeRingHom (divByS x D₀.s) * D₀.coeRingHom (algebraMap A _ D₀.s)
  rw [← map_mul, hrel]

/-- **Power-boundedness of the plus forward generator images** (Wedhorn
Prop 8.2 analogue, plus branch generator). For each `t ∈ (laurentPlusDatum D₀ f).T`
(= `insert f D₀.T`), the image of `divByS t D₀.s` under
`iteratedPlus_forwardLocHom D₀` is power-bounded in `Loc_B(1)` with the
`(iteratedPlusDatum_B P D₀ f).topology`.

**Mathematical content** (Wedhorn §8.2, Lemma 2.13).
Under the iterated-rational identification
`rationalOpen (laurentPlusDatum D₀ f).T D₀.s ⊂ Spa A ≃
 rationalOpen (iteratedPlusDatum_B P D₀ f).T (iteratedPlusDatum_B P D₀ f).s ⊂ Spa B`
(Lemma 2.13), the adic Nullstellensatz (Wedhorn Prop 7.14) on `B := presheafValue D₀`
gives power-boundedness of the generator images. The `A`-rational analogue is
`HasLocLiftPowerBounded.locLift_divByS_isPowerBounded` in `Presheaf.lean`.

**Unfolding the generator image**:
- For `t ∈ D₀.T` or `t = f`, `iteratedPlus_forwardLocHom D₀ (divByS t D₀.s) =
  algebraMap(D₀.canonicalMap t) * (algebraMap(D₀.canonicalMap D₀.s))⁻¹` in `Loc_B(1)`,
  where the inverse exists because `D₀.canonicalMap D₀.s` is a unit
  (`isUnit_s_in_presheafValue D₀`).
- The claim reduces to: this element is power-bounded in `(iteratedPlusDatum_B).topology`.

**Proof strategy**: via `iteratedPlus_forwardLocHom_divByS`, reduce to membership
of `algebraMap_B(coeRingHom(divByS t D₀.s))` in `locSubring (iteratedPlusDatum_B)`.
For `t ∈ D₀.T`, `divByS t D₀.s ∈ locSubring D₀` → `coeRingHom(...) ∈ A₀`.
For `t = f`, factor `divByS f D₀.s = algebraMap f * divByS 1 D₀.s` and use
`LaurentNormalized.one_mem_T` to get `divByS 1 D₀.s ∈ locSubring D₀`. -/
private theorem iteratedPlus_forwardLocHom_generators_powerBounded
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (D₀ : RationalLocData A)
    [IsNoetherianRing (locSubring D₀.P D₀.T D₀.s)]
    [LaurentNormalized D₀]
    (f : A) :
    ∀ t ∈ (laurentPlusDatum D₀ f).T,
      @TopologicalRing.IsPowerBounded _ _ (iteratedPlusDatum_B P D₀ f).topology
        (iteratedPlus_forwardLocHom D₀ (divByS t (laurentPlusDatum D₀ f).s)) := by
  intro t ht
  set B := presheafValue D₀
  -- Show forward image lies in `locSubring (iteratedPlusDatum_B)`, a bounded
  -- subring; then `isPowerBounded_of_mem_locSubring` finishes.
  apply isPowerBounded_of_mem_locSubring (iteratedPlusDatum_B P D₀ f)
  -- `(laurentPlusDatum D₀ f).s = D₀.s` definitionally.
  change iteratedPlus_forwardLocHom D₀ (divByS t D₀.s) ∈ _
  rcases Finset.mem_insert.mp ht with rfl | ht_orig
  · -- Case `t = f`. Factor `divByS f D₀.s = algebraMap f * divByS 1 D₀.s`.
    have hfactor : divByS t D₀.s = algebraMap A (Localization.Away D₀.s) t *
        divByS 1 D₀.s := by
      unfold divByS
      rw [← IsLocalization.mk'_one (M := Submonoid.powers D₀.s)
            (S := Localization.Away D₀.s) t,
          ← IsLocalization.mk'_mul, mul_one, one_mul]
    rw [hfactor, map_mul, iteratedPlus_forwardLocHom_algebraMap,
      iteratedPlus_forwardLocHom_divByS]
    refine (locSubring _ _ _).mul_mem ?_ ?_
    · -- `algebraMap_B(canonicalMap t) = divByS (canonicalMap t) 1 ∈ locSubring`.
      rw [show algebraMap B (Localization.Away (1 : B)) (D₀.canonicalMap t) =
          divByS (D₀.canonicalMap t) 1 from (divByS_eq_algebraMap _).symm]
      exact divByS_mem_locSubring _ _ _ (Finset.mem_singleton_self _)
    · -- `divByS 1 D₀.s ∈ locSubring D₀` since `1 ∈ D₀.T` (LaurentNormalized).
      have hdiv_mem : divByS (1 : A) D₀.s ∈ locSubring D₀.P D₀.T D₀.s :=
        divByS_mem_locSubring _ _ _ LaurentNormalized.one_mem_T
      have hcoe_mem : D₀.coeRingHom (divByS (1 : A) D₀.s) ∈
          presheafValue_ringOfDef D₀ :=
        Subring.le_topologicalClosure _ ⟨⟨divByS 1 D₀.s, hdiv_mem⟩, rfl⟩
      exact algebraMap_mem_locSubring _ _ _ hcoe_mem
  · -- Case `t ∈ D₀.T`. `divByS t D₀.s ∈ locSubring D₀` directly.
    rw [iteratedPlus_forwardLocHom_divByS]
    have hdiv_mem : divByS t D₀.s ∈ locSubring D₀.P D₀.T D₀.s :=
      divByS_mem_locSubring _ _ _ ht_orig
    have hcoe_mem : D₀.coeRingHom (divByS t D₀.s) ∈ presheafValue_ringOfDef D₀ :=
      Subring.le_topologicalClosure _ ⟨⟨divByS t D₀.s, hdiv_mem⟩, rfl⟩
    exact algebraMap_mem_locSubring _ _ _ hcoe_mem

/-- Continuity of the forward uncompleted hom to the completion
(Wedhorn Prop 8.2 analogue, plus branch).

**Proof**: Factor as `(iteratedPlusDatum_B).coeRingHom ∘
iteratedPlus_forwardLocHom D₀`. The right factor is continuous from
`(laurentPlusDatum D₀ f).topology` to `(iteratedPlusDatum_B).topology`
by the universal property of the localization topology
(`locTopology_continuous_lift`) applied to the generators `insert f D₀.T`;
the left factor is the completion embedding (always continuous). -/
theorem iteratedPlus_forwardToCompletion_continuous
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (D₀ : RationalLocData A)
    [IsNoetherianRing (locSubring D₀.P D₀.T D₀.s)]
    [LaurentNormalized D₀]
    (f : A) :
    @Continuous _ _ (laurentPlusDatum D₀ f).topology _
      (iteratedPlus_forwardToCompletion P D₀ f) := by
  -- Decompose as `coeRingHom ∘ forwardLocHom` and apply `locTopology_continuous_lift`
  -- for the inner hom, then compose with the continuous completion embedding.
  letI : TopologicalSpace (Localization.Away (laurentPlusDatum D₀ f).s) :=
    (laurentPlusDatum D₀ f).topology
  letI : IsTopologicalRing (Localization.Away (laurentPlusDatum D₀ f).s) :=
    (laurentPlusDatum D₀ f).isTopologicalRing
  letI : IsTopologicalAddGroup (Localization.Away (laurentPlusDatum D₀ f).s) :=
    (laurentPlusDatum D₀ f).isTopologicalAddGroup
  letI topB : TopologicalSpace (Localization.Away (1 : presheafValue D₀)) :=
    (iteratedPlusDatum_B P D₀ f).topology
  letI : TopologicalSpace (Localization.Away (iteratedPlusDatum_B P D₀ f).s) := topB
  letI : IsTopologicalRing (Localization.Away (1 : presheafValue D₀)) :=
    (iteratedPlusDatum_B P D₀ f).isTopologicalRing
  letI : IsTopologicalRing (Localization.Away (iteratedPlusDatum_B P D₀ f).s) :=
    (iteratedPlusDatum_B P D₀ f).isTopologicalRing
  letI : IsTopologicalAddGroup (Localization.Away (1 : presheafValue D₀)) :=
    (iteratedPlusDatum_B P D₀ f).isTopologicalAddGroup
  letI : IsTopologicalAddGroup (Localization.Away (iteratedPlusDatum_B P D₀ f).s) :=
    (iteratedPlusDatum_B P D₀ f).isTopologicalAddGroup
  letI usB : UniformSpace (Localization.Away (1 : presheafValue D₀)) :=
    (iteratedPlusDatum_B P D₀ f).uniformSpace
  letI : UniformSpace (Localization.Away (iteratedPlusDatum_B P D₀ f).s) := usB
  letI : IsUniformAddGroup (Localization.Away (1 : presheafValue D₀)) :=
    (iteratedPlusDatum_B P D₀ f).isUniformAddGroup
  letI : IsUniformAddGroup (Localization.Away (iteratedPlusDatum_B P D₀ f).s) :=
    (iteratedPlusDatum_B P D₀ f).isUniformAddGroup
  -- Target is nonarchimedean ring (for `locTopology_continuous_lift`).
  haveI naB : @NonarchimedeanRing (Localization.Away (1 : presheafValue D₀)) _
      (iteratedPlusDatum_B P D₀ f).topology :=
    (locBasis (iteratedPlusDatum_B P D₀ f).P (iteratedPlusDatum_B P D₀ f).T
      (iteratedPlusDatum_B P D₀ f).s (iteratedPlusDatum_B P D₀ f).hopen).nonarchimedean
  haveI : @NonarchimedeanRing (Localization.Away (iteratedPlusDatum_B P D₀ f).s) _
      (iteratedPlusDatum_B P D₀ f).topology := naB
  -- Factor `iteratedPlus_forwardToCompletion` as `coeRingHom ∘ forwardLocHom`.
  change @Continuous _ _ (laurentPlusDatum D₀ f).topology _
      ((iteratedPlusDatum_B P D₀ f).coeRingHom.comp (iteratedPlus_forwardLocHom D₀))
  -- The completion embedding `coeRingHom` is continuous.
  have hcoe : @Continuous _ _ (iteratedPlusDatum_B P D₀ f).topology
      (@UniformSpace.toTopologicalSpace _
        (@UniformSpace.Completion.uniformSpace _
          (iteratedPlusDatum_B P D₀ f).uniformSpace))
      (iteratedPlusDatum_B P D₀ f).coeRingHom :=
    @UniformSpace.Completion.continuous_coe _ (iteratedPlusDatum_B P D₀ f).uniformSpace
  -- Reduce to continuity of `iteratedPlus_forwardLocHom D₀`.
  suffices hlift : @Continuous _ _ (laurentPlusDatum D₀ f).topology
      (iteratedPlusDatum_B P D₀ f).topology (iteratedPlus_forwardLocHom D₀) by
    exact hcoe.comp hlift
  -- Continuity of `forwardLocHom ∘ algebraMap A`: the composite equals
  -- `algebraMap B _ ∘ D₀.canonicalMap` (by `iteratedPlus_forwardLocHom_algebraMap`),
  -- both continuous.
  have hf_alg : @Continuous _ _ _ (iteratedPlusDatum_B P D₀ f).topology
      ((iteratedPlus_forwardLocHom D₀).comp
        (algebraMap A (Localization.Away (laurentPlusDatum D₀ f).s))) := by
    have heq : (iteratedPlus_forwardLocHom D₀).comp
        (algebraMap A (Localization.Away (laurentPlusDatum D₀ f).s)) =
        (algebraMap (presheafValue D₀)
          (Localization.Away (iteratedPlusDatum_B P D₀ f).s)).comp D₀.canonicalMap := by
      ext a
      simp only [RingHom.comp_apply]
      show iteratedPlus_forwardLocHom D₀
          (algebraMap A (Localization.Away D₀.s) a) =
        algebraMap (presheafValue D₀) (Localization.Away (1 : presheafValue D₀))
          (D₀.canonicalMap a)
      exact iteratedPlus_forwardLocHom_algebraMap D₀ a
    rw [show ⇑((iteratedPlus_forwardLocHom D₀).comp
        (algebraMap A (Localization.Away (laurentPlusDatum D₀ f).s))) =
      ⇑((algebraMap (presheafValue D₀)
          (Localization.Away (iteratedPlusDatum_B P D₀ f).s)).comp D₀.canonicalMap) from
      congr_arg _ heq]
    exact (algebraMap_continuous_loc (iteratedPlusDatum_B P D₀ f)).comp
      (canonicalMap_continuous D₀)
  -- Power-boundedness hypothesis: from the packaged helper lemma.
  have hpow := iteratedPlus_forwardLocHom_generators_powerBounded P D₀ f
  -- Apply `locTopology_continuous_lift` to the loc-hom.
  exact locTopology_continuous_lift (laurentPlusDatum D₀ f).P
    (laurentPlusDatum D₀ f).T (laurentPlusDatum D₀ f).s
    (laurentPlusDatum D₀ f).hopen (iteratedPlus_forwardLocHom D₀) hf_alg hpow

/-! #### Backward (plus branch): power-boundedness sub-sorry

The backward uncompleted map
`iteratedPlus_backwardLocHom D₀ f hsub : Loc_B(1) →+*
presheafValue (laurentPlusDatum D₀ f)` sends the single generator
`divByS (canonicalMap f) 1` of `(iteratedPlusDatum_B P D₀ f).T = {canonicalMap f}`
to `(laurentPlusDatum D₀ f).canonicalMap f`, which must be power-bounded
in `presheafValue (laurentPlusDatum D₀ f)`.

We package this as `iteratedPlus_backwardLocHom_generator_powerBounded`
(parallels `iteratedMinus_backwardLocHom_generator_powerBounded` in the
minus direction). -/

/-- **Power-boundedness of the plus backward generator image** (Wedhorn
Prop 8.2 analogue, plus branch backward generator). The image of
`divByS (canonicalMap f) 1` (= the unique generator of `T = {canonicalMap f}`
in `iteratedPlusDatum_B P D₀ f`) under `iteratedPlus_backwardLocHom D₀ f hsub`
is power-bounded in `presheafValue (laurentPlusDatum D₀ f)`.

**Mathematical content** (Wedhorn §8.2, Lemma 2.13).
By `iteratedPlus_backwardLocHom_algebraMap` + `restrictionMapHom_canonicalMap`,
the image equals `(laurentPlusDatum D₀ f).canonicalMap f`, the canonical
image of `f` in the target. Since `f ∈ (laurentPlusDatum D₀ f).T = insert f D₀.T`,
we have `divByS f D₀.s ∈ locSubring (laurentPlusDatum D₀ f)` and hence
`canonicalMap (divByS f D₀.s · D₀.s) = canonicalMap f` lies in the target ring
of definition, giving power-boundedness directly.

**Proof strategy** (deferred):
1. By `iteratedPlus_backwardLocHom_algebraMap` and `divByS_eq_algebraMap` (since
   `s = 1` in `iteratedPlusDatum_B`), the image equals
   `restrictionMapHom D₀ (laurentPlusDatum D₀ f) hsub (D₀.canonicalMap f)`,
   which by `restrictionMapHom_canonicalMap` equals `(laurentPlusDatum D₀ f).canonicalMap f`.
2. `canonicalMap f` in the target: since `f ∈ (laurentPlusDatum).T` (via `Finset.mem_insert_self`),
   `divByS f D₀.s ∈ locSubring (laurentPlusDatum)`, and multiplication by the unit
   `canonicalMap D₀.s` gives `canonicalMap f ∈ presheafValue_ringOfDef`.
3. Elements of `presheafValue_ringOfDef` are power-bounded (Wedhorn Prop 7.14 /
   standard Nullstellensatz content).

**Status**: deferred as a single sub-sorry (Wedhorn §8.2 base-change
Nullstellensatz). Parallels `iteratedMinus_backwardLocHom_generator_powerBounded`. -/
private theorem iteratedPlus_backwardLocHom_generator_powerBounded
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (D₀ : RationalLocData A)
    [IsNoetherianRing (locSubring D₀.P D₀.T D₀.s)]
    [LaurentNormalized D₀]
    (f : A)
    (hsub : rationalOpen (laurentPlusDatum D₀ f).T (laurentPlusDatum D₀ f).s ⊆
      rationalOpen D₀.T D₀.s) :
    TopologicalRing.IsPowerBounded
      (iteratedPlus_backwardLocHom D₀ f hsub
        (divByS (D₀.canonicalMap f) (iteratedPlusDatum_B P D₀ f).s)) := by
  -- Wedhorn Prop 8.2 / Lemma 2.13 base-change content on `B := presheafValue D₀`,
  -- applied to the canonical image of `f` in `presheafValue (laurentPlusDatum D₀ f)`.
  -- Step 1: Rewrite the backward image to `(laurentPlusDatum D₀ f).canonicalMap f`.
  -- Since `s_B = 1`, `divByS (canonicalMap f) 1 = algebraMap B _ (canonicalMap f)`;
  -- then `backward ∘ algebraMap = restrictionMapHom`; then
  -- `restrictionMapHom ∘ canonicalMap = (laurentPlus).canonicalMap` at `f`.
  have hstep1 : iteratedPlus_backwardLocHom D₀ f hsub
      (divByS (D₀.canonicalMap f) (iteratedPlusDatum_B P D₀ f).s) =
      (laurentPlusDatum D₀ f).canonicalMap f := by
    show iteratedPlus_backwardLocHom D₀ f hsub
        (divByS (D₀.canonicalMap f) (1 : presheafValue D₀)) = _
    rw [divByS_eq_algebraMap, iteratedPlus_backwardLocHom_algebraMap,
      restrictionMapHom_canonicalMap]
  rw [hstep1]
  -- Step 2: `(laurentPlus).canonicalMap f = coeRingHom (algebraMap A _ f)`.
  show TopologicalRing.IsPowerBounded
    ((laurentPlusDatum D₀ f).coeRingHom (algebraMap A _ f))
  -- Step 3: `algebraMap A _ f ∈ locSubring (laurentPlus)`, since
  --   `algebraMap A _ f = algebraMap A _ D₀.s * divByS f D₀.s`
  --   with `D₀.s ∈ D₀.P.A₀` (LaurentNormalized) and `f ∈ insert f D₀.T`.
  have hs_A₀ : D₀.s ∈ D₀.P.A₀ :=
    LaurentNormalized.insert_s_T_subset_A₀ D₀.s (Finset.mem_insert_self _ _)
  have hs_eq : (laurentPlusDatum D₀ f).s = D₀.s := rfl
  have hprod : algebraMap A (Localization.Away (laurentPlusDatum D₀ f).s)
      D₀.s * divByS f (laurentPlusDatum D₀ f).s =
      algebraMap A (Localization.Away (laurentPlusDatum D₀ f).s) f := by
    rw [hs_eq]
    unfold divByS
    rw [← IsLocalization.mk'_one (M := Submonoid.powers D₀.s)
          (S := Localization.Away D₀.s) D₀.s,
        ← IsLocalization.mk'_mul,
        ← IsLocalization.mk'_one (M := Submonoid.powers D₀.s)
          (S := Localization.Away D₀.s) f]
    exact IsLocalization.mk'_eq_of_eq (by simp only [Submonoid.coe_mul]; ring)
  have hmem : algebraMap A (Localization.Away (laurentPlusDatum D₀ f).s) f ∈
      locSubring (laurentPlusDatum D₀ f).P (laurentPlusDatum D₀ f).T
        (laurentPlusDatum D₀ f).s := by
    rw [← hprod]
    exact (locSubring _ _ _).mul_mem
      (algebraMap_mem_locSubring _ _ _ hs_A₀)
      (divByS_mem_locSubring _ _ _ (Finset.mem_insert_self f D₀.T))
  -- Step 4: powers stay in `coeRingHom '' locSubring`, which is bounded.
  apply (CompletionLocalization.coeRingHom_image_locSubring_isBounded
    (laurentPlusDatum D₀ f)).subset
  rintro _ ⟨n, rfl⟩
  change ((laurentPlusDatum D₀ f).coeRingHom (algebraMap A _ f)) ^ n ∈ _
  rw [← map_pow]
  exact ⟨(algebraMap A _ f) ^ n,
    (locSubring _ _ _).pow_mem hmem n, rfl⟩

/-- Continuity of the backward uncompleted hom (plus branch).

**Proof**: Apply `locTopology_continuous_lift` to `iteratedPlus_backwardLocHom D₀ f hsub`
with base ring `B = presheafValue D₀`, source data
`((iteratedPlusDatum_B P D₀ f).P, {canonicalMap f}, 1)`, and target
`presheafValue (laurentPlusDatum D₀ f)`. Reduces to two conditions:

(a) `iteratedPlus_backwardLocHom ∘ algebraMap B = restrictionMapHom D₀ (laurentPlusDatum D₀ f) hsub`
    (by `iteratedPlus_backwardLocHom_algebraMap`), continuous by
    `restrictionMapHom_continuous`.
(b) For the single generator `divByS (canonicalMap f) 1`, the image is
    power-bounded: `iteratedPlus_backwardLocHom_generator_powerBounded`. -/
theorem iteratedPlus_backwardLocHom_continuous
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (D₀ : RationalLocData A)
    [IsNoetherianRing (locSubring D₀.P D₀.T D₀.s)]
    [LaurentNormalized D₀]
    (f : A)
    (hsub : rationalOpen (laurentPlusDatum D₀ f).T (laurentPlusDatum D₀ f).s ⊆
      rationalOpen D₀.T D₀.s) :
    @Continuous _ _ (iteratedPlusDatum_B P D₀ f).topology _
      (iteratedPlus_backwardLocHom D₀ f hsub) := by
  -- Apply `locTopology_continuous_lift` for the lift on source
  -- `Loc_B(1)` with `iteratedPlusDatum_B` topology.
  letI topB : TopologicalSpace (Localization.Away (1 : presheafValue D₀)) :=
    (iteratedPlusDatum_B P D₀ f).topology
  letI : TopologicalSpace (Localization.Away (iteratedPlusDatum_B P D₀ f).s) := topB
  letI : IsTopologicalRing (Localization.Away (1 : presheafValue D₀)) :=
    (iteratedPlusDatum_B P D₀ f).isTopologicalRing
  letI : IsTopologicalRing (Localization.Away (iteratedPlusDatum_B P D₀ f).s) :=
    (iteratedPlusDatum_B P D₀ f).isTopologicalRing
  -- Target is nonarchimedean ring (for `locTopology_continuous_lift`).
  haveI : NonarchimedeanRing (presheafValue (laurentPlusDatum D₀ f)) :=
    presheafValueNonarchimedeanRing (laurentPlusDatum D₀ f)
  -- Continuity of `backwardLocHom ∘ algebraMap B`: the composite equals
  -- `restrictionMapHom D₀ (laurentPlusDatum D₀ f) hsub` (by
  -- `iteratedPlus_backwardLocHom_algebraMap`), which is continuous by
  -- `restrictionMapHom_continuous`.
  have hf_alg : @Continuous _ _ _ _
      ((iteratedPlus_backwardLocHom D₀ f hsub).comp
        (algebraMap (presheafValue D₀)
          (Localization.Away (iteratedPlusDatum_B P D₀ f).s))) := by
    have heq : (iteratedPlus_backwardLocHom D₀ f hsub).comp
        (algebraMap (presheafValue D₀)
          (Localization.Away (iteratedPlusDatum_B P D₀ f).s)) =
        restrictionMapHom D₀ (laurentPlusDatum D₀ f) hsub := by
      ext b
      simp only [RingHom.comp_apply]
      exact iteratedPlus_backwardLocHom_algebraMap D₀ f hsub b
    rw [show ⇑((iteratedPlus_backwardLocHom D₀ f hsub).comp
        (algebraMap (presheafValue D₀)
          (Localization.Away (iteratedPlusDatum_B P D₀ f).s))) =
      ⇑(restrictionMapHom D₀ (laurentPlusDatum D₀ f) hsub) from
      congr_arg _ heq]
    exact restrictionMapHom_continuous D₀ (laurentPlusDatum D₀ f) hsub
  -- Power-boundedness of the single generator at `t = canonicalMap f`.
  have hpow : ∀ t ∈ (iteratedPlusDatum_B P D₀ f).T,
      TopologicalRing.IsPowerBounded
        (iteratedPlus_backwardLocHom D₀ f hsub
          (divByS t (iteratedPlusDatum_B P D₀ f).s)) := by
    intro t ht
    -- `T = {canonicalMap f}`, so `t = canonicalMap f`.
    rw [show (iteratedPlusDatum_B P D₀ f).T = {D₀.canonicalMap f} from rfl] at ht
    rw [Finset.mem_singleton] at ht
    subst ht
    exact iteratedPlus_backwardLocHom_generator_powerBounded P D₀ f hsub
  -- Apply `locTopology_continuous_lift`.
  exact locTopology_continuous_lift (iteratedPlusDatum_B P D₀ f).P
    (iteratedPlusDatum_B P D₀ f).T (iteratedPlusDatum_B P D₀ f).s
    (iteratedPlusDatum_B P D₀ f).hopen
    (iteratedPlus_backwardLocHom D₀ f hsub) hf_alg hpow

/-- The forward completion hom (plus branch): `extensionHom` of
`iteratedPlus_forwardToCompletion`. -/
noncomputable def iteratedPlus_forwardHom
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (D₀ : RationalLocData A)
    [IsNoetherianRing (locSubring D₀.P D₀.T D₀.s)]
    [LaurentNormalized D₀]
    (f : A) :
    presheafValue (laurentPlusDatum D₀ f) →+*
      presheafValue (iteratedPlusDatum_B P D₀ f) :=
  letI : UniformSpace (Localization.Away (laurentPlusDatum D₀ f).s) :=
    (laurentPlusDatum D₀ f).uniformSpace
  letI : IsUniformAddGroup (Localization.Away (laurentPlusDatum D₀ f).s) :=
    (laurentPlusDatum D₀ f).isUniformAddGroup
  letI : IsTopologicalRing (Localization.Away (laurentPlusDatum D₀ f).s) :=
    (laurentPlusDatum D₀ f).isTopologicalRing
  UniformSpace.Completion.extensionHom
    (iteratedPlus_forwardToCompletion P D₀ f)
    (iteratedPlus_forwardToCompletion_continuous P D₀ f)

/-- The backward completion hom (plus branch): `extensionHom` of
`iteratedPlus_backwardLocHom`. -/
noncomputable def iteratedPlus_backwardHom
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (D₀ : RationalLocData A)
    [IsNoetherianRing (locSubring D₀.P D₀.T D₀.s)]
    [LaurentNormalized D₀]
    (f : A)
    (hsub : rationalOpen (laurentPlusDatum D₀ f).T (laurentPlusDatum D₀ f).s ⊆
      rationalOpen D₀.T D₀.s) :
    presheafValue (iteratedPlusDatum_B P D₀ f) →+*
      presheafValue (laurentPlusDatum D₀ f) :=
  letI : UniformSpace (Localization.Away (iteratedPlusDatum_B P D₀ f).s) :=
    (iteratedPlusDatum_B P D₀ f).uniformSpace
  letI : IsUniformAddGroup (Localization.Away (iteratedPlusDatum_B P D₀ f).s) :=
    (iteratedPlusDatum_B P D₀ f).isUniformAddGroup
  letI : IsTopologicalRing (Localization.Away (iteratedPlusDatum_B P D₀ f).s) :=
    (iteratedPlusDatum_B P D₀ f).isTopologicalRing
  UniformSpace.Completion.extensionHom
    (iteratedPlus_backwardLocHom D₀ f hsub)
    (iteratedPlus_backwardLocHom_continuous P D₀ f hsub)

/-- Forward completion hom acting on `coeRingHom a`: definitional unwind
via `extensionHom_coe`. -/
theorem iteratedPlus_forwardHom_coeRingHom
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (D₀ : RationalLocData A)
    [IsNoetherianRing (locSubring D₀.P D₀.T D₀.s)]
    [LaurentNormalized D₀]
    (f : A)
    (a : Localization.Away (laurentPlusDatum D₀ f).s) :
    iteratedPlus_forwardHom P D₀ f ((laurentPlusDatum D₀ f).coeRingHom a) =
      iteratedPlus_forwardToCompletion P D₀ f a := by
  letI : UniformSpace (Localization.Away (laurentPlusDatum D₀ f).s) :=
    (laurentPlusDatum D₀ f).uniformSpace
  letI : IsUniformAddGroup (Localization.Away (laurentPlusDatum D₀ f).s) :=
    (laurentPlusDatum D₀ f).isUniformAddGroup
  letI : IsTopologicalRing (Localization.Away (laurentPlusDatum D₀ f).s) :=
    (laurentPlusDatum D₀ f).isTopologicalRing
  exact UniformSpace.Completion.extensionHom_coe _ _ a

/-- Backward completion hom acting on `coeRingHom b`: definitional unwind. -/
theorem iteratedPlus_backwardHom_coeRingHom
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (D₀ : RationalLocData A)
    [IsNoetherianRing (locSubring D₀.P D₀.T D₀.s)]
    [LaurentNormalized D₀]
    (f : A)
    (hsub : rationalOpen (laurentPlusDatum D₀ f).T (laurentPlusDatum D₀ f).s ⊆
      rationalOpen D₀.T D₀.s)
    (b : Localization.Away (iteratedPlusDatum_B P D₀ f).s) :
    iteratedPlus_backwardHom P D₀ f hsub ((iteratedPlusDatum_B P D₀ f).coeRingHom b) =
      iteratedPlus_backwardLocHom D₀ f hsub b := by
  letI : UniformSpace (Localization.Away (iteratedPlusDatum_B P D₀ f).s) :=
    (iteratedPlusDatum_B P D₀ f).uniformSpace
  letI : IsUniformAddGroup (Localization.Away (iteratedPlusDatum_B P D₀ f).s) :=
    (iteratedPlusDatum_B P D₀ f).isUniformAddGroup
  letI : IsTopologicalRing (Localization.Away (iteratedPlusDatum_B P D₀ f).s) :=
    (iteratedPlusDatum_B P D₀ f).isTopologicalRing
  exact UniformSpace.Completion.extensionHom_coe _ _ b

/-- Round-trip 1 (plus branch): `backwardHom ∘ forwardHom = id`. This is
the `Completion.ext'` chase using the uncompleted-level identity
`iteratedPlus_backward_forward_locHom`. -/
theorem iteratedPlus_backwardHom_comp_forwardHom
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (D₀ : RationalLocData A)
    [IsNoetherianRing (locSubring D₀.P D₀.T D₀.s)]
    [LaurentNormalized D₀]
    (f : A)
    (hsub : rationalOpen (laurentPlusDatum D₀ f).T (laurentPlusDatum D₀ f).s ⊆
      rationalOpen D₀.T D₀.s) :
    (iteratedPlus_backwardHom P D₀ f hsub).comp (iteratedPlus_forwardHom P D₀ f) =
      RingHom.id _ := by
  letI : UniformSpace (Localization.Away (laurentPlusDatum D₀ f).s) :=
    (laurentPlusDatum D₀ f).uniformSpace
  letI : IsUniformAddGroup (Localization.Away (laurentPlusDatum D₀ f).s) :=
    (laurentPlusDatum D₀ f).isUniformAddGroup
  letI : IsTopologicalRing (Localization.Away (laurentPlusDatum D₀ f).s) :=
    (laurentPlusDatum D₀ f).isTopologicalRing
  letI : UniformSpace (Localization.Away (iteratedPlusDatum_B P D₀ f).s) :=
    (iteratedPlusDatum_B P D₀ f).uniformSpace
  letI : IsUniformAddGroup (Localization.Away (iteratedPlusDatum_B P D₀ f).s) :=
    (iteratedPlusDatum_B P D₀ f).isUniformAddGroup
  letI : IsTopologicalRing (Localization.Away (iteratedPlusDatum_B P D₀ f).s) :=
    (iteratedPlusDatum_B P D₀ f).isTopologicalRing
  apply RingHom.ext
  intro x
  show iteratedPlus_backwardHom P D₀ f hsub (iteratedPlus_forwardHom P D₀ f x) = x
  refine @UniformSpace.Completion.ext' _ _ _ _ _ _ _
    ((UniformSpace.Completion.continuous_extension).comp
      UniformSpace.Completion.continuous_extension)
    continuous_id ?_ x
  intro a
  show iteratedPlus_backwardHom P D₀ f hsub
      (iteratedPlus_forwardHom P D₀ f ((laurentPlusDatum D₀ f).coeRingHom a)) =
    (laurentPlusDatum D₀ f).coeRingHom a
  rw [iteratedPlus_forwardHom_coeRingHom,
      show iteratedPlus_forwardToCompletion P D₀ f a =
        (iteratedPlusDatum_B P D₀ f).coeRingHom
          (iteratedPlus_forwardLocHom D₀ a) from rfl,
      iteratedPlus_backwardHom_coeRingHom]
  have := congr_fun (congrArg DFunLike.coe
    (iteratedPlus_backward_forward_locHom D₀ f hsub)) a
  exact this

/-- Core identity (plus branch): `forwardHom ∘ restrictionMapHom = canonicalMap`
(at the level of `presheafValue D₀`).

This is the dual of `iteratedPlus_backward_forward_locHom` (which works at
the uncompleted level for forward-then-backward). Here the equality is at the
completion level on the source — we check it via `Completion.ext'` on
`b : presheafValue D₀` plus `IsLocalization.ringHom_ext` on the reduced
`Loc_A(D₀.s) → presheafValue (iteratedPlusDatum_B)` homs.

This is the plus-branch analog of `iteratedMinus_forwardHom_comp_restrictionMapHom`
and is used as the core identity in `iteratedPlus_forwardHom_comp_backwardHom`. -/
theorem iteratedPlus_forwardHom_comp_restrictionMapHom
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (D₀ : RationalLocData A)
    [IsNoetherianRing (locSubring D₀.P D₀.T D₀.s)]
    [LaurentNormalized D₀]
    (f : A)
    (hsub : rationalOpen (laurentPlusDatum D₀ f).T (laurentPlusDatum D₀ f).s ⊆
      rationalOpen D₀.T D₀.s) :
    (iteratedPlus_forwardHom P D₀ f).comp
        (restrictionMapHom D₀ (laurentPlusDatum D₀ f) hsub) =
      (iteratedPlusDatum_B P D₀ f).canonicalMap := by
  letI : UniformSpace (Localization.Away D₀.s) := D₀.uniformSpace
  letI : IsUniformAddGroup (Localization.Away D₀.s) := D₀.isUniformAddGroup
  letI : IsTopologicalRing (Localization.Away D₀.s) := D₀.isTopologicalRing
  letI : UniformSpace (Localization.Away (laurentPlusDatum D₀ f).s) :=
    (laurentPlusDatum D₀ f).uniformSpace
  letI : IsUniformAddGroup (Localization.Away (laurentPlusDatum D₀ f).s) :=
    (laurentPlusDatum D₀ f).isUniformAddGroup
  letI : IsTopologicalRing (Localization.Away (laurentPlusDatum D₀ f).s) :=
    (laurentPlusDatum D₀ f).isTopologicalRing
  letI : UniformSpace (Localization.Away (iteratedPlusDatum_B P D₀ f).s) :=
    (iteratedPlusDatum_B P D₀ f).uniformSpace
  letI : IsUniformAddGroup (Localization.Away (iteratedPlusDatum_B P D₀ f).s) :=
    (iteratedPlusDatum_B P D₀ f).isUniformAddGroup
  letI : IsTopologicalRing (Localization.Away (iteratedPlusDatum_B P D₀ f).s) :=
    (iteratedPlusDatum_B P D₀ f).isTopologicalRing
  apply RingHom.ext
  intro b
  show iteratedPlus_forwardHom P D₀ f
      (restrictionMapHom D₀ (laurentPlusDatum D₀ f) hsub b) =
    (iteratedPlusDatum_B P D₀ f).canonicalMap b
  -- Apply Completion.ext' on b : presheafValue D₀ (a completion of Loc_A(D₀.s)).
  let lhsFun : presheafValue D₀ → presheafValue (iteratedPlusDatum_B P D₀ f) :=
    fun y => iteratedPlus_forwardHom P D₀ f
      (restrictionMapHom D₀ (laurentPlusDatum D₀ f) hsub y)
  let rhsFun : presheafValue D₀ → presheafValue (iteratedPlusDatum_B P D₀ f) :=
    fun y => (iteratedPlusDatum_B P D₀ f).canonicalMap y
  change lhsFun b = rhsFun b
  refine @UniformSpace.Completion.ext' (Localization.Away D₀.s) D₀.uniformSpace
    (presheafValue (iteratedPlusDatum_B P D₀ f)) _ _ lhsFun rhsFun ?_ ?_ ?_ b
  · -- Continuity LHS: composition of continuous restrictionMapHom and forwardHom.
    exact UniformSpace.Completion.continuous_extension.comp
      (restrictionMapHom_continuous D₀ (laurentPlusDatum D₀ f) hsub)
  · -- Continuity RHS: canonicalMap is continuous.
    exact canonicalMap_continuous (iteratedPlusDatum_B P D₀ f)
  -- Reduce to `b = D₀.coeRingHom a` for `a : Loc_A(D₀.s)`.
  intro a
  show lhsFun (D₀.coeRingHom a) = rhsFun (D₀.coeRingHom a)
  simp only [lhsFun, rhsFun]
  -- Further reduce via IsLocalization.ringHom_ext.
  let lhsHom : Localization.Away D₀.s →+*
      presheafValue (iteratedPlusDatum_B P D₀ f) :=
    (iteratedPlus_forwardHom P D₀ f).comp
      ((restrictionMapHom D₀ (laurentPlusDatum D₀ f) hsub).comp D₀.coeRingHom)
  let rhsHom : Localization.Away D₀.s →+*
      presheafValue (iteratedPlusDatum_B P D₀ f) :=
    ((iteratedPlusDatum_B P D₀ f).canonicalMap).comp D₀.coeRingHom
  suffices h : lhsHom = rhsHom by
    have := congr_fun (congrArg DFunLike.coe h) a
    show lhsHom a = rhsHom a
    exact this
  apply IsLocalization.ringHom_ext (Submonoid.powers D₀.s)
  ext c
  show lhsHom (algebraMap A _ c) = rhsHom (algebraMap A _ c)
  show iteratedPlus_forwardHom P D₀ f
      (restrictionMapHom D₀ (laurentPlusDatum D₀ f) hsub
        (D₀.coeRingHom (algebraMap A _ c))) =
    (iteratedPlusDatum_B P D₀ f).canonicalMap (D₀.coeRingHom (algebraMap A _ c))
  show iteratedPlus_forwardHom P D₀ f
      (restrictionMapHom D₀ (laurentPlusDatum D₀ f) hsub (D₀.canonicalMap c)) =
    (iteratedPlusDatum_B P D₀ f).canonicalMap (D₀.canonicalMap c)
  rw [restrictionMapHom_canonicalMap]
  show iteratedPlus_forwardHom P D₀ f
      ((laurentPlusDatum D₀ f).coeRingHom (algebraMap A _ c)) =
    (iteratedPlusDatum_B P D₀ f).canonicalMap (D₀.canonicalMap c)
  rw [iteratedPlus_forwardHom_coeRingHom]
  show (iteratedPlusDatum_B P D₀ f).coeRingHom
      (iteratedPlus_forwardLocHom D₀ (algebraMap A _ c)) =
    (iteratedPlusDatum_B P D₀ f).canonicalMap (D₀.canonicalMap c)
  rw [iteratedPlus_forwardLocHom_algebraMap]
  rfl

/-- Round-trip 2 (plus branch): `forwardHom ∘ backwardHom = id`. Proved via
`Completion.ext'` on `x : presheafValue (iteratedPlusDatum_B P D₀ f)` +
`IsLocalization.ringHom_ext` on `Loc_B(1)`, reducing to the core identity
`iteratedPlus_forwardHom_comp_restrictionMapHom`. -/
theorem iteratedPlus_forwardHom_comp_backwardHom
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (D₀ : RationalLocData A)
    [IsNoetherianRing (locSubring D₀.P D₀.T D₀.s)]
    [LaurentNormalized D₀]
    (f : A)
    (hsub : rationalOpen (laurentPlusDatum D₀ f).T (laurentPlusDatum D₀ f).s ⊆
      rationalOpen D₀.T D₀.s) :
    (iteratedPlus_forwardHom P D₀ f).comp (iteratedPlus_backwardHom P D₀ f hsub) =
      RingHom.id _ := by
  letI : UniformSpace (Localization.Away D₀.s) := D₀.uniformSpace
  letI : IsUniformAddGroup (Localization.Away D₀.s) := D₀.isUniformAddGroup
  letI : IsTopologicalRing (Localization.Away D₀.s) := D₀.isTopologicalRing
  letI : UniformSpace (Localization.Away (laurentPlusDatum D₀ f).s) :=
    (laurentPlusDatum D₀ f).uniformSpace
  letI : IsUniformAddGroup (Localization.Away (laurentPlusDatum D₀ f).s) :=
    (laurentPlusDatum D₀ f).isUniformAddGroup
  letI : IsTopologicalRing (Localization.Away (laurentPlusDatum D₀ f).s) :=
    (laurentPlusDatum D₀ f).isTopologicalRing
  letI : UniformSpace (Localization.Away (iteratedPlusDatum_B P D₀ f).s) :=
    (iteratedPlusDatum_B P D₀ f).uniformSpace
  letI : IsUniformAddGroup (Localization.Away (iteratedPlusDatum_B P D₀ f).s) :=
    (iteratedPlusDatum_B P D₀ f).isUniformAddGroup
  letI : IsTopologicalRing (Localization.Away (iteratedPlusDatum_B P D₀ f).s) :=
    (iteratedPlusDatum_B P D₀ f).isTopologicalRing
  apply RingHom.ext
  intro x
  show iteratedPlus_forwardHom P D₀ f (iteratedPlus_backwardHom P D₀ f hsub x) = x
  -- Completion.ext' on x : presheafValue (iteratedPlusDatum_B P D₀ f).
  refine @UniformSpace.Completion.ext'
    (Localization.Away (iteratedPlusDatum_B P D₀ f).s) _ _ _ _ _ _
    ((UniformSpace.Completion.continuous_extension).comp
      UniformSpace.Completion.continuous_extension)
    continuous_id ?_ x
  intro y
  -- Reduce to coeRingHom y.
  show iteratedPlus_forwardHom P D₀ f
      (iteratedPlus_backwardHom P D₀ f hsub
        ((iteratedPlusDatum_B P D₀ f).coeRingHom y)) =
    (iteratedPlusDatum_B P D₀ f).coeRingHom y
  rw [iteratedPlus_backwardHom_coeRingHom]
  -- Use IsLocalization.ringHom_ext on y : Loc_B(1) to reduce to
  -- y = algebraMap B _ b for b : presheafValue D₀.
  let lhsHom : Localization.Away (iteratedPlusDatum_B P D₀ f).s →+*
      presheafValue (iteratedPlusDatum_B P D₀ f) :=
    (iteratedPlus_forwardHom P D₀ f).comp (iteratedPlus_backwardLocHom D₀ f hsub)
  let rhsHom : Localization.Away (iteratedPlusDatum_B P D₀ f).s →+*
      presheafValue (iteratedPlusDatum_B P D₀ f) :=
    (iteratedPlusDatum_B P D₀ f).coeRingHom
  suffices h : lhsHom = rhsHom by
    have := congr_fun (congrArg DFunLike.coe h) y
    show lhsHom y = rhsHom y
    exact this
  apply IsLocalization.ringHom_ext (Submonoid.powers (iteratedPlusDatum_B P D₀ f).s)
  ext b
  show lhsHom (algebraMap (presheafValue D₀) _ b) =
    rhsHom (algebraMap (presheafValue D₀) _ b)
  show iteratedPlus_forwardHom P D₀ f
      (iteratedPlus_backwardLocHom D₀ f hsub
        (algebraMap (presheafValue D₀) _ b)) =
    (iteratedPlusDatum_B P D₀ f).coeRingHom (algebraMap (presheafValue D₀) _ b)
  rw [iteratedPlus_backwardLocHom_algebraMap]
  -- Goal: forwardHom (restrictionMapHom b) = (iteratedPlusDatum_B).canonicalMap b.
  -- This is the core identity `iteratedPlus_forwardHom_comp_restrictionMapHom`.
  exact congr_fun (congrArg DFunLike.coe
    (iteratedPlus_forwardHom_comp_restrictionMapHom P D₀ f hsub)) b

/-- **Iterated rational identification, plus branch (Wedhorn Lemma 2.13)**.

The completion of `A` at the Laurent-plus datum equals the completion of
`B := presheafValue D₀` at the trivial plus datum `{canonicalMap f}/1` on `B`.

Mathematical content: `rationalOpen (laurentPlusDatum D₀ f) ⊂ Spa A` maps
under the inclusion `Spa A ↔ Spa B` (induced by `canonicalMap`) to exactly
the rational open `rationalOpen (iteratedPlusDatum_B P D₀ f) ⊂ Spa B`.
Hence their global sections (presheafValues) agree.

This is the only new primitive the reviewer's Q3 plan requires (besides the
symmetric minus version). Once proved, composing with
`presheafValueTateQuotientEquiv` at `B` gives the Laurent-plus bridge. -/
noncomputable def presheafValue_iteratedPlus_equiv
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (D₀ : RationalLocData A)
    [IsNoetherianRing (locSubring D₀.P D₀.T D₀.s)]
    [LaurentNormalized D₀]
    (f : A) :
    presheafValue (laurentPlusDatum D₀ f) ≃+*
      presheafValue (iteratedPlusDatum_B P D₀ f) :=
  let hsub := laurentPlus_subset D₀ f
  { toFun := iteratedPlus_forwardHom P D₀ f
    invFun := iteratedPlus_backwardHom P D₀ f hsub
    left_inv := fun x =>
      congr_fun (congrArg DFunLike.coe
        (iteratedPlus_backwardHom_comp_forwardHom P D₀ f hsub)) x
    right_inv := fun y =>
      congr_fun (congrArg DFunLike.coe
        (iteratedPlus_forwardHom_comp_backwardHom P D₀ f hsub)) y
    map_mul' := map_mul _
    map_add' := map_add _ }

/-- The equiv's forward action equals `iteratedPlus_forwardHom` (definitional
unwind; enables downstream sub-sorries to reduce to the concrete `forwardHom`). -/
theorem presheafValue_iteratedPlus_equiv_apply
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (D₀ : RationalLocData A)
    [IsNoetherianRing (locSubring D₀.P D₀.T D₀.s)]
    [LaurentNormalized D₀]
    (f : A) (x : presheafValue (laurentPlusDatum D₀ f)) :
    presheafValue_iteratedPlus_equiv P D₀ f x =
      iteratedPlus_forwardHom P D₀ f x := rfl

/-- Equiv's action on `(laurentPlusDatum D₀ f).coeRingHom a`:
factors through `iteratedPlus_forwardToCompletion`. -/
theorem presheafValue_iteratedPlus_equiv_coeRingHom
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (D₀ : RationalLocData A)
    [IsNoetherianRing (locSubring D₀.P D₀.T D₀.s)]
    [LaurentNormalized D₀]
    (f : A)
    (a : Localization.Away (laurentPlusDatum D₀ f).s) :
    presheafValue_iteratedPlus_equiv P D₀ f
        ((laurentPlusDatum D₀ f).coeRingHom a) =
      (iteratedPlusDatum_B P D₀ f).coeRingHom
        (iteratedPlus_forwardLocHom D₀ a) := by
  rw [presheafValue_iteratedPlus_equiv_apply, iteratedPlus_forwardHom_coeRingHom]
  rfl

/-! #### Continuity and inducing topology of `presheafValue_iteratedPlus_equiv` (T146)

The forward / backward completion homs `iteratedPlus_forwardHom` and
`iteratedPlus_backwardHom` are both `UniformSpace.Completion.extensionHom`
of (uncompleted) continuous ring homs, hence continuous via
`UniformSpace.Completion.continuous_extension`. Combined with the fact
that they are mutual inverses, they assemble into a `Homeomorph`, and the
ring equiv `presheafValue_iteratedPlus_equiv` is `Topology.IsInducing`
in both directions. -/

/-- Continuity of the plus-branch forward completion hom. -/
theorem iteratedPlus_forwardHom_continuous
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (D₀ : RationalLocData A)
    [IsNoetherianRing (locSubring D₀.P D₀.T D₀.s)]
    [LaurentNormalized D₀]
    (f : A) :
    Continuous (iteratedPlus_forwardHom P D₀ f) := by
  letI : UniformSpace (Localization.Away (laurentPlusDatum D₀ f).s) :=
    (laurentPlusDatum D₀ f).uniformSpace
  letI : IsUniformAddGroup (Localization.Away (laurentPlusDatum D₀ f).s) :=
    (laurentPlusDatum D₀ f).isUniformAddGroup
  letI : IsTopologicalRing (Localization.Away (laurentPlusDatum D₀ f).s) :=
    (laurentPlusDatum D₀ f).isTopologicalRing
  exact UniformSpace.Completion.continuous_extension

/-- Continuity of the plus-branch backward completion hom. -/
theorem iteratedPlus_backwardHom_continuous
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (D₀ : RationalLocData A)
    [IsNoetherianRing (locSubring D₀.P D₀.T D₀.s)]
    [LaurentNormalized D₀]
    (f : A)
    (hsub : rationalOpen (laurentPlusDatum D₀ f).T (laurentPlusDatum D₀ f).s ⊆
      rationalOpen D₀.T D₀.s) :
    Continuous (iteratedPlus_backwardHom P D₀ f hsub) := by
  letI : UniformSpace (Localization.Away (iteratedPlusDatum_B P D₀ f).s) :=
    (iteratedPlusDatum_B P D₀ f).uniformSpace
  letI : IsUniformAddGroup (Localization.Away (iteratedPlusDatum_B P D₀ f).s) :=
    (iteratedPlusDatum_B P D₀ f).isUniformAddGroup
  letI : IsTopologicalRing (Localization.Away (iteratedPlusDatum_B P D₀ f).s) :=
    (iteratedPlusDatum_B P D₀ f).isTopologicalRing
  exact UniformSpace.Completion.continuous_extension

/-- **T146 plus: `presheafValue_iteratedPlus_equiv` packaged as `Homeomorph`.**
The ring equiv between the two presheafValues — at `laurentPlusDatum D₀ f` and
the iterated `iteratedPlusDatum_B P D₀ f` — is a topological homeomorphism,
since both directions of the underlying completion-extension hom are continuous. -/
noncomputable def presheafValue_iteratedPlus_equiv_homeomorph
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (D₀ : RationalLocData A)
    [IsNoetherianRing (locSubring D₀.P D₀.T D₀.s)]
    [LaurentNormalized D₀]
    (f : A) :
    presheafValue (laurentPlusDatum D₀ f) ≃ₜ
      presheafValue (iteratedPlusDatum_B P D₀ f) :=
  { (presheafValue_iteratedPlus_equiv P D₀ f).toEquiv with
    continuous_toFun := iteratedPlus_forwardHom_continuous P D₀ f
    continuous_invFun :=
      iteratedPlus_backwardHom_continuous P D₀ f (laurentPlus_subset D₀ f) }

/-- **T146 plus: `presheafValue_iteratedPlus_equiv` is `Topology.IsInducing`.**
Forward direction: `presheafValue (laurentPlusDatum D₀ f) →
presheafValue (iteratedPlusDatum_B P D₀ f)`. -/
theorem presheafValue_iteratedPlus_equiv_isInducing
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (D₀ : RationalLocData A)
    [IsNoetherianRing (locSubring D₀.P D₀.T D₀.s)]
    [LaurentNormalized D₀]
    (f : A) :
    Topology.IsInducing
      ((presheafValue_iteratedPlus_equiv P D₀ f) :
        presheafValue (laurentPlusDatum D₀ f) →
          presheafValue (iteratedPlusDatum_B P D₀ f)) :=
  (presheafValue_iteratedPlus_equiv_homeomorph P D₀ f).isInducing

/-- **T146 plus: `(presheafValue_iteratedPlus_equiv).symm` is `Topology.IsInducing`.**
Inverse direction: `presheafValue (iteratedPlusDatum_B P D₀ f) →
presheafValue (laurentPlusDatum D₀ f)`. -/
theorem presheafValue_iteratedPlus_equiv_symm_isInducing
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (D₀ : RationalLocData A)
    [IsNoetherianRing (locSubring D₀.P D₀.T D₀.s)]
    [LaurentNormalized D₀]
    (f : A) :
    Topology.IsInducing
      ((presheafValue_iteratedPlus_equiv P D₀ f).symm :
        presheafValue (iteratedPlusDatum_B P D₀ f) →
          presheafValue (laurentPlusDatum D₀ f)) :=
  (presheafValue_iteratedPlus_equiv_homeomorph P D₀ f).symm.isInducing

/-! #### Minus-branch continuity residuals (Wedhorn Prop 8.2 analogues)

The two continuity facts needed to extend the uncompleted forward / backward
maps to the completion level. Both are Wedhorn Prop 8.2 analogues across the
base change `A → B = presheafValue D₀`; see the Phase-2 plan for the full
structural proofs. Recorded here as named sorries so the downstream
`presheafValue_iteratedMinus_equiv` can refer to them as concrete theorems
(enabling the `_restrictionMap_canonicalMap` sub-sorry to be reduced). -/

/-! #### Power-boundedness helpers for the minus-branch forward map

The forward uncompleted map `iteratedMinus_forwardLocHom D₀ f :
Loc_A(D₀.s · f) → Loc_B(canonicalMap f)` sends each generator
`divByS t (D₀.s · f)` (for `t ∈ (laurentMinusDatum D₀ f).T`, the product
`(insert D₀.s D₀.T) × {D₀.s, f}` under `(·.1 * ·.2)`) to an element which
must be power-bounded in `Loc_B(canonicalMap f)` with
`(iteratedMinusDatum_B P D₀ f).topology`.

We package this as a single helper lemma
`iteratedMinus_forwardLocHom_generators_powerBounded`
(Wedhorn Prop 8.2 / Lemma 2.13 content, deferred). Parallels
`iteratedPlus_forwardLocHom_generators_powerBounded`. -/

/-- **Power-boundedness of the minus forward generator images** (Wedhorn
Prop 8.2 analogue, minus branch generator). For each
`t ∈ (laurentMinusDatum D₀ f).T` (a product Finset of elements of the form
`a · b` with `a ∈ insert D₀.s D₀.T` and `b ∈ {D₀.s, f}`), the image of
`divByS t (laurentMinusDatum D₀ f).s` (= `divByS t (D₀.s · f)`) under
`iteratedMinus_forwardLocHom D₀ f` is power-bounded in
`Loc_B(canonicalMap f)` with the `(iteratedMinusDatum_B P D₀ f).topology`.

**Mathematical content** (Wedhorn §8.2, Lemma 2.13).
Under the iterated-rational identification
`rationalOpen (laurentMinusDatum D₀ f).T (laurentMinusDatum D₀ f).s ⊂ Spa A ≃
 rationalOpen (iteratedMinusDatum_B P D₀ f).T (iteratedMinusDatum_B P D₀ f).s
 ⊂ Spa B` (Lemma 2.13), the adic Nullstellensatz (Wedhorn Prop 7.14) on
`B := presheafValue D₀` gives power-boundedness of the generator images. The
`A`-rational analogue is `HasLocLiftPowerBounded.locLift_divByS_isPowerBounded`
in `Presheaf.lean`.

**Unfolding the generator image**. For `t = a · b` (with `a ∈ insert D₀.s D₀.T`
and `b ∈ {D₀.s, f}`):
- `iteratedMinus_forwardLocHom D₀ f (divByS (a*b) (D₀.s*f))` lies in
  `Loc_B(canonicalMap f)`;
- Under Lemma 2.13 it corresponds to an element of the localization subring
  `locSubring (iteratedMinusDatum_B).P (iteratedMinusDatum_B).T
  (iteratedMinusDatum_B).s` (using `iteratedMinusDatum_B.T = {1}` and
  `s = canonicalMap f`).

**Proof strategy** (closable under `hnorm : ∀ a ∈ insert D₀.s D₀.T, a ∈ D₀.P.A₀`):
Let `B := presheafValue D₀`. Each `t = a * b ∈ T_product` with `a ∈ insert D₀.s D₀.T`,
`b ∈ {D₀.s, f}`. Show `forward(divByS t (D₀.s*f)) ∈ locSubring (iteratedMinusDatum_B)`
(a bounded subring by `locSubring_isBounded`, giving power-boundedness directly).

Case `b = D₀.s`: using `IsLocalization.Away.lift` + `iteratedMinus_forwardLocHom_algebraMap`,
`forward(divByS (a*D₀.s) (D₀.s*f)) = algebraMap B _ (canonicalMap a) * divByS 1 (canonicalMap f)`.
First factor ∈ `algebraMap '' presheafValue_ringOfDef D₀ ⊆ locSubring` via
`canonicalMap_mem_ringOfDef` + `a ∈ D₀.P.A₀` (from `hnorm`). Second factor ∈ `locSubring`
via `divByS_mem_locSubring` with `1 ∈ {1}`.

Case `b = f`: `forward(divByS (a*f) (D₀.s*f)) = algebraMap B _ (coeRingHom(divByS a D₀.s))`.
Since `divByS a D₀.s ∈ locSubring D₀` (either `= 1` when `a = D₀.s`, or by
`divByS_mem_locSubring` when `a ∈ D₀.T`), the `coeRingHom` image lies in
`presheafValue_ringOfDef D₀ = (iteratedMinusDatum_B).P.A₀` (using
`presheafValue_pairOfDefinition_concrete_A₀`). Hence the `algebraMap` image
is in `locSubring`. **Does NOT need `hnorm`**.

Both cases yield elements of the subring `locSubring (iteratedMinusDatum_B)`,
bounded by `locSubring_isBounded`. Powers stay in the subring (closed under
multiplication), so `IsBounded.subset` gives power-boundedness.

**Status**: currently `sorry` — closing requires threading `hnorm` through 21+ callers
of `iteratedMinus_forwardHom` downstream, best via a bundled `NormalizedRationalLocData`
structure. The `presheafValue_pairOfDefinition_concrete` API (`PresheafTateStructure.lean`)
gives the definitional `.P.A₀ = presheafValue_ringOfDef D₀` needed for the proof. -/
private theorem iteratedMinus_forwardLocHom_generators_powerBounded
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (D₀ : RationalLocData A)
    [IsNoetherianRing (locSubring D₀.P D₀.T D₀.s)]
    [LaurentNormalized D₀]
    (f : A) :
    ∀ t ∈ (laurentMinusDatum D₀ f).T,
      @TopologicalRing.IsPowerBounded _ _ (iteratedMinusDatum_B P D₀ f).topology
        (iteratedMinus_forwardLocHom D₀ f
          (divByS t (laurentMinusDatum D₀ f).s)) := by
  -- See docstring above for the proof outline.
  intro t ht
  -- Unpack `t = a * b` with `a ∈ insert D₀.s D₀.T` and `b ∈ {D₀.s, f}`.
  obtain ⟨⟨a, b⟩, hab_mem, hab_eq⟩ := Finset.mem_image.mp ht
  obtain ⟨ha, hb⟩ := Finset.mem_product.mp hab_mem
  change a ∈ insert D₀.s D₀.T at ha
  change b ∈ ({D₀.s, f} : Finset A) at hb
  change a * b = t at hab_eq
  subst hab_eq
  change @TopologicalRing.IsPowerBounded _ _ (iteratedMinusDatum_B P D₀ f).topology
    (iteratedMinus_forwardLocHom D₀ f (divByS (a * b) (D₀.s * f)))
  -- Show forward image lies in `locSubring` of `iteratedMinusDatum_B`, a
  -- bounded subring (`locSubring_isBounded`), so power-bounded by
  -- `isPowerBounded_of_mem_locSubring`.
  apply isPowerBounded_of_mem_locSubring (iteratedMinusDatum_B P D₀ f)
  -- Abbreviations for readability.
  set B := presheafValue D₀
  -- `a ∈ insert D₀.s D₀.T ⊆ D₀.P.A₀` (via `LaurentNormalized`).
  have ha_A₀ : a ∈ D₀.P.A₀ := LaurentNormalized.insert_s_T_subset_A₀ a ha
  have hcan_a : D₀.canonicalMap a ∈ (iteratedMinusDatum_B P D₀ f).P.A₀ :=
    canonicalMap_mem_ringOfDef D₀ ha_A₀
  -- Key fact: in `Localization.Away (D₀.s * f)`, both `algebraMap(D₀.s)` and
  -- `algebraMap(f)` are units. Similarly in the target.
  have hu_s_src : IsUnit (algebraMap A (Localization.Away (D₀.s * f)) D₀.s) := by
    have := IsLocalization.Away.algebraMap_isUnit (R := A) (D₀.s * f)
        (S := Localization.Away (D₀.s * f))
    rw [map_mul] at this; exact isUnit_of_mul_isUnit_left this
  have hu_f_src : IsUnit (algebraMap A (Localization.Away (D₀.s * f)) f) := by
    have := IsLocalization.Away.algebraMap_isUnit (R := A) (D₀.s * f)
        (S := Localization.Away (D₀.s * f))
    rw [map_mul] at this; exact isUnit_of_mul_isUnit_right this
  have hu_s_tgt : IsUnit (algebraMap B (Localization.Away (D₀.canonicalMap f))
      (D₀.canonicalMap D₀.s)) := (isUnit_s_in_presheafValue D₀).map _
  have hu_f_tgt : IsUnit (algebraMap B (Localization.Away (D₀.canonicalMap f))
      (D₀.canonicalMap f)) := IsLocalization.Away.algebraMap_isUnit _
  -- `forward(algebraMap A _ x) = algebraMap B _ (canonicalMap x)`.
  have hforward_alg : ∀ x : A, iteratedMinus_forwardLocHom D₀ f
      (algebraMap A (Localization.Away (D₀.s * f)) x) =
      algebraMap B (Localization.Away (D₀.canonicalMap f)) (D₀.canonicalMap x) := by
    intro x; exact iteratedMinus_forwardLocHom_algebraMap D₀ f x
  -- Split by `b`.
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  rcases hb with hb_s | hb_f
  · -- Case `b = D₀.s`. Show `divByS (a * D₀.s) (D₀.s * f) ∈ algebraMap(A) * divByS 1 f` image.
    subst hb_s
    -- We have `divByS (a * D₀.s) (D₀.s * f) * algebraMap(f) = algebraMap a` in Loc_A(D₀.s*f).
    -- By `IsLocalization.Away.lift`, forward of LHS = forward(algebraMap a) * (algebraMap f)⁻¹.
    -- Let u = forward of divByS (a * D₀.s) (D₀.s * f).
    -- Show u = algebraMap B (canonicalMap a) * divByS 1 (canonicalMap f).
    have hrel : divByS (a * D₀.s) (D₀.s * f) *
        algebraMap A (Localization.Away (D₀.s * f)) f =
        algebraMap A (Localization.Away (D₀.s * f)) a := by
      unfold divByS
      rw [← IsLocalization.mk'_one (M := Submonoid.powers (D₀.s * f))
            (S := Localization.Away (D₀.s * f)) f,
          ← IsLocalization.mk'_mul,
          ← IsLocalization.mk'_one (M := Submonoid.powers (D₀.s * f))
            (S := Localization.Away (D₀.s * f)) a]
      exact IsLocalization.mk'_eq_of_eq (by simp only [Submonoid.coe_mul]; ring)
    -- Apply forward map to hrel.
    have hforward_rel : iteratedMinus_forwardLocHom D₀ f
        (divByS (a * D₀.s) (D₀.s * f)) *
        algebraMap B (Localization.Away (D₀.canonicalMap f)) (D₀.canonicalMap f) =
        algebraMap B (Localization.Away (D₀.canonicalMap f)) (D₀.canonicalMap a) := by
      have := congrArg (iteratedMinus_forwardLocHom D₀ f) hrel
      rw [map_mul, hforward_alg, hforward_alg] at this; exact this
    -- Multiply both sides by `divByS 1 (canonicalMap f)`, which is the inverse.
    have hinv_f : algebraMap B (Localization.Away (D₀.canonicalMap f)) (D₀.canonicalMap f) *
        divByS (1 : B) (D₀.canonicalMap f) = 1 := by
      unfold divByS
      rw [← IsLocalization.mk'_one (M := Submonoid.powers (D₀.canonicalMap f))
            (S := Localization.Away (D₀.canonicalMap f)) (D₀.canonicalMap f),
          ← IsLocalization.mk'_mul, mul_one, one_mul]
      exact IsLocalization.mk'_self _ _
    have hforward_eq : iteratedMinus_forwardLocHom D₀ f (divByS (a * D₀.s) (D₀.s * f)) =
        algebraMap B (Localization.Away (D₀.canonicalMap f)) (D₀.canonicalMap a) *
          divByS (1 : B) (D₀.canonicalMap f) := by
      have := congrArg (· * divByS (1 : B) (D₀.canonicalMap f)) hforward_rel
      simp only at this
      rwa [mul_assoc, hinv_f, mul_one] at this
    rw [hforward_eq]
    -- Membership: both factors in `locSubring (iteratedMinusDatum_B)`.
    refine (locSubring _ _ _).mul_mem ?_ ?_
    · exact algebraMap_mem_locSubring _ _ _ hcan_a
    · exact divByS_mem_locSubring _ _ _ (Finset.mem_singleton_self 1)
  · -- Case `b = f`. Use `hb_f : b = f` but keep `f` as the free variable by rewriting.
    rw [hb_f]
    -- Now goal is about `divByS (a * f) (D₀.s * f)`.
    -- `divByS (a * f) (D₀.s * f) * algebraMap(D₀.s) = algebraMap(a)`.
    have hrel : divByS (a * f) (D₀.s * f) *
        algebraMap A (Localization.Away (D₀.s * f)) D₀.s =
        algebraMap A (Localization.Away (D₀.s * f)) a := by
      unfold divByS
      rw [← IsLocalization.mk'_one (M := Submonoid.powers (D₀.s * f))
            (S := Localization.Away (D₀.s * f)) D₀.s,
          ← IsLocalization.mk'_mul,
          ← IsLocalization.mk'_one (M := Submonoid.powers (D₀.s * f))
            (S := Localization.Away (D₀.s * f)) a]
      exact IsLocalization.mk'_eq_of_eq (by simp only [Submonoid.coe_mul]; ring)
    have hforward_rel : iteratedMinus_forwardLocHom D₀ f
        (divByS (a * f) (D₀.s * f)) *
        algebraMap B (Localization.Away (D₀.canonicalMap f)) (D₀.canonicalMap D₀.s) =
        algebraMap B (Localization.Away (D₀.canonicalMap f)) (D₀.canonicalMap a) := by
      have := congrArg (iteratedMinus_forwardLocHom D₀ f) hrel
      rw [map_mul, hforward_alg, hforward_alg] at this; exact this
    -- Now: forward = algebraMap(canonicalMap a) * (algebraMap(canonicalMap D₀.s))⁻¹
    --            = algebraMap(canonicalMap a * (canonicalMap D₀.s)⁻¹)
    --            = algebraMap(coeRingHom(divByS a D₀.s)).
    -- Get: canonicalMap D₀.s * coeRingHom(divByS a D₀.s) = canonicalMap a in B.
    have hcoeB : D₀.canonicalMap D₀.s * D₀.coeRingHom (divByS a D₀.s) =
        D₀.canonicalMap a := by
      change D₀.coeRingHom (algebraMap A _ D₀.s) * D₀.coeRingHom (divByS a D₀.s) =
        D₀.coeRingHom (algebraMap A _ a)
      rw [← map_mul]
      congr 1
      unfold divByS
      rw [← IsLocalization.mk'_one (M := Submonoid.powers D₀.s)
            (S := Localization.Away D₀.s) D₀.s,
          ← IsLocalization.mk'_mul,
          ← IsLocalization.mk'_one (M := Submonoid.powers D₀.s)
            (S := Localization.Away D₀.s) a]
      exact IsLocalization.mk'_eq_of_eq (by simp only [Submonoid.coe_mul]; ring)
    -- From `hforward_rel`: forward * algebraMap(canonicalMap D₀.s) = algebraMap(canonicalMap a).
    -- Apply `hu_s_tgt.mul_right_cancel` with target algebraMap(coeRingHom(divByS a D₀.s)).
    have hforward_eq : iteratedMinus_forwardLocHom D₀ f (divByS (a * f) (D₀.s * f)) =
        algebraMap B (Localization.Away (D₀.canonicalMap f))
          (D₀.coeRingHom (divByS a D₀.s)) := by
      apply hu_s_tgt.mul_right_cancel
      rw [hforward_rel, ← hcoeB, map_mul]; ring
    rw [hforward_eq]
    -- `divByS a D₀.s ∈ locSubring D₀.P D₀.T D₀.s`.
    have hdiv_mem_loc : divByS a D₀.s ∈ locSubring D₀.P D₀.T D₀.s := by
      simp only [Finset.mem_insert] at ha
      rcases ha with rfl | ha'
      · -- `a = D₀.s`: `divByS D₀.s D₀.s = 1`.
        have hself : divByS D₀.s D₀.s = 1 := by
          unfold divByS; exact IsLocalization.mk'_self _ _
        rw [hself]; exact (locSubring _ _ _).one_mem
      · exact divByS_mem_locSubring _ _ _ ha'
    -- `D₀.coeRingHom(divByS a D₀.s) ∈ presheafValue_ringOfDef D₀`.
    have hcoe_mem : D₀.coeRingHom (divByS a D₀.s) ∈ presheafValue_ringOfDef D₀ := by
      refine Subring.le_topologicalClosure _ ?_
      exact ⟨⟨divByS a D₀.s, hdiv_mem_loc⟩, rfl⟩
    exact algebraMap_mem_locSubring _ _ _ hcoe_mem

/-- Continuity of the forward uncompleted hom to the completion
(Wedhorn Prop 8.2 analogue, minus branch).

**Proof**: Factor as `(iteratedMinusDatum_B).coeRingHom ∘
iteratedMinus_forwardLocHom D₀ f`. The right factor is continuous from
`(laurentMinusDatum D₀ f).topology` to `(iteratedMinusDatum_B).topology`
by the universal property of the localization topology
(`locTopology_continuous_lift`) applied to the generators
`(laurentMinusDatum D₀ f).T`; the left factor is the completion embedding
(always continuous). -/
theorem iteratedMinus_forwardToCompletion_continuous
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (D₀ : RationalLocData A)
    [IsNoetherianRing (locSubring D₀.P D₀.T D₀.s)]
    [LaurentNormalized D₀]
    (f : A) :
    @Continuous _ _ (laurentMinusDatum D₀ f).topology _
      (iteratedMinus_forwardToCompletion P D₀ f) := by
  -- Decompose as `coeRingHom ∘ forwardLocHom` and apply
  -- `locTopology_continuous_lift` for the inner hom, then compose with the
  -- continuous completion embedding.
  letI : TopologicalSpace (Localization.Away (laurentMinusDatum D₀ f).s) :=
    (laurentMinusDatum D₀ f).topology
  letI : IsTopologicalRing (Localization.Away (laurentMinusDatum D₀ f).s) :=
    (laurentMinusDatum D₀ f).isTopologicalRing
  letI : IsTopologicalAddGroup (Localization.Away (laurentMinusDatum D₀ f).s) :=
    (laurentMinusDatum D₀ f).isTopologicalAddGroup
  letI topB : TopologicalSpace (Localization.Away (D₀.canonicalMap f)) :=
    (iteratedMinusDatum_B P D₀ f).topology
  letI : TopologicalSpace (Localization.Away (iteratedMinusDatum_B P D₀ f).s) := topB
  letI : IsTopologicalRing (Localization.Away (D₀.canonicalMap f)) :=
    (iteratedMinusDatum_B P D₀ f).isTopologicalRing
  letI : IsTopologicalRing (Localization.Away (iteratedMinusDatum_B P D₀ f).s) :=
    (iteratedMinusDatum_B P D₀ f).isTopologicalRing
  letI : IsTopologicalAddGroup (Localization.Away (D₀.canonicalMap f)) :=
    (iteratedMinusDatum_B P D₀ f).isTopologicalAddGroup
  letI : IsTopologicalAddGroup
      (Localization.Away (iteratedMinusDatum_B P D₀ f).s) :=
    (iteratedMinusDatum_B P D₀ f).isTopologicalAddGroup
  letI usB : UniformSpace (Localization.Away (D₀.canonicalMap f)) :=
    (iteratedMinusDatum_B P D₀ f).uniformSpace
  letI : UniformSpace (Localization.Away (iteratedMinusDatum_B P D₀ f).s) := usB
  letI : IsUniformAddGroup (Localization.Away (D₀.canonicalMap f)) :=
    (iteratedMinusDatum_B P D₀ f).isUniformAddGroup
  letI : IsUniformAddGroup (Localization.Away (iteratedMinusDatum_B P D₀ f).s) :=
    (iteratedMinusDatum_B P D₀ f).isUniformAddGroup
  -- Target is nonarchimedean ring (for `locTopology_continuous_lift`).
  haveI naB : @NonarchimedeanRing (Localization.Away (D₀.canonicalMap f)) _
      (iteratedMinusDatum_B P D₀ f).topology :=
    (locBasis (iteratedMinusDatum_B P D₀ f).P (iteratedMinusDatum_B P D₀ f).T
      (iteratedMinusDatum_B P D₀ f).s
      (iteratedMinusDatum_B P D₀ f).hopen).nonarchimedean
  haveI : @NonarchimedeanRing (Localization.Away (iteratedMinusDatum_B P D₀ f).s) _
      (iteratedMinusDatum_B P D₀ f).topology := naB
  -- Factor `iteratedMinus_forwardToCompletion` as `coeRingHom ∘ forwardLocHom`.
  change @Continuous _ _ (laurentMinusDatum D₀ f).topology _
      ((iteratedMinusDatum_B P D₀ f).coeRingHom.comp
        (iteratedMinus_forwardLocHom D₀ f))
  -- The completion embedding `coeRingHom` is continuous.
  have hcoe : @Continuous _ _ (iteratedMinusDatum_B P D₀ f).topology
      (@UniformSpace.toTopologicalSpace _
        (@UniformSpace.Completion.uniformSpace _
          (iteratedMinusDatum_B P D₀ f).uniformSpace))
      (iteratedMinusDatum_B P D₀ f).coeRingHom :=
    @UniformSpace.Completion.continuous_coe _
      (iteratedMinusDatum_B P D₀ f).uniformSpace
  -- Reduce to continuity of `iteratedMinus_forwardLocHom D₀ f`.
  suffices hlift : @Continuous _ _ (laurentMinusDatum D₀ f).topology
      (iteratedMinusDatum_B P D₀ f).topology
      (iteratedMinus_forwardLocHom D₀ f) by
    exact hcoe.comp hlift
  -- Continuity of `forwardLocHom ∘ algebraMap A`: the composite equals
  -- `algebraMap B _ ∘ D₀.canonicalMap` (by `iteratedMinus_forwardLocHom_algebraMap`
  -- / `iteratedMinus_baseHom`), both continuous.
  have hf_alg : @Continuous _ _ _ (iteratedMinusDatum_B P D₀ f).topology
      ((iteratedMinus_forwardLocHom D₀ f).comp
        (algebraMap A (Localization.Away (laurentMinusDatum D₀ f).s))) := by
    have heq : (iteratedMinus_forwardLocHom D₀ f).comp
        (algebraMap A (Localization.Away (laurentMinusDatum D₀ f).s)) =
        (algebraMap (presheafValue D₀)
          (Localization.Away (iteratedMinusDatum_B P D₀ f).s)).comp
          D₀.canonicalMap := by
      ext a
      simp only [RingHom.comp_apply]
      show iteratedMinus_forwardLocHom D₀ f
          (algebraMap A (Localization.Away (D₀.s * f)) a) =
        algebraMap (presheafValue D₀) (Localization.Away (D₀.canonicalMap f))
          (D₀.canonicalMap a)
      rw [iteratedMinus_forwardLocHom_algebraMap]
      rfl
    rw [show ⇑((iteratedMinus_forwardLocHom D₀ f).comp
        (algebraMap A (Localization.Away (laurentMinusDatum D₀ f).s))) =
      ⇑((algebraMap (presheafValue D₀)
          (Localization.Away (iteratedMinusDatum_B P D₀ f).s)).comp
          D₀.canonicalMap) from
      congr_arg _ heq]
    exact (algebraMap_continuous_loc (iteratedMinusDatum_B P D₀ f)).comp
      (canonicalMap_continuous D₀)
  -- Power-boundedness hypothesis: from the packaged helper lemma.
  have hpow := iteratedMinus_forwardLocHom_generators_powerBounded P D₀ f
  -- Apply `locTopology_continuous_lift` to the loc-hom.
  exact locTopology_continuous_lift (laurentMinusDatum D₀ f).P
    (laurentMinusDatum D₀ f).T (laurentMinusDatum D₀ f).s
    (laurentMinusDatum D₀ f).hopen (iteratedMinus_forwardLocHom D₀ f) hf_alg hpow

/-! #### Backward (minus branch): power-boundedness sub-sorry

The backward uncompleted map
`iteratedMinus_backwardLocHom D₀ f hsub : Loc_B(canonicalMap f) →+*
presheafValue (laurentMinusDatum D₀ f)` sends the single generator
`divByS 1 (canonicalMap f)` of `(iteratedMinusDatum_B P D₀ f).T = {1}` to
`1 / (laurentMinusDatum D₀ f).canonicalMap f`, which must be power-bounded
in `presheafValue (laurentMinusDatum D₀ f)`.

We package this as `iteratedMinus_backwardLocHom_generator_powerBounded`
(parallels `iteratedMinus_forwardLocHom_generators_powerBounded` in the
forward direction). -/

/-- **Power-boundedness of the minus backward generator image** (Wedhorn
Prop 8.2 analogue, minus branch backward generator). The image of
`divByS 1 (canonicalMap f)` (= the unique generator of `T = {1}` in
`iteratedMinusDatum_B P D₀ f`) under `iteratedMinus_backwardLocHom D₀ f hsub`
is power-bounded in `presheafValue (laurentMinusDatum D₀ f)`.

**Mathematical content** (Wedhorn §8.2, Lemma 2.13).
By `iteratedMinus_backwardLocHom_algebraMap` + `restrictionMapHom_canonicalMap`,
the image equals `((laurentMinusDatum D₀ f).canonicalMap f)⁻¹`, the inverse
of the canonical image of `f` in the target. Under Wedhorn Lemma 2.13
(`rationalOpen (laurentMinusDatum) ⊂ Spa A ≃ rationalOpen (iteratedMinusDatum_B)
⊂ Spa B`), power-boundedness of this inverse corresponds to the standard
adic Nullstellensatz content on `B := presheafValue D₀`.

**Proof strategy** (deferred):
1. Express `1 / canonicalMap f = coeRingHom(algebraMap f)⁻¹` via
   `canonicalMap_f_isUnit_in_laurentMinus`.
2. Inside `Loc_A(D₀.s * f)`, `algebraMap f` is a unit with inverse
   `divByS D₀.s (D₀.s * f)` (since `(D₀.s) * algebraMap f = algebraMap (D₀.s * f)`
   and `algebraMap (D₀.s * f)⁻¹ = mk' 1 (D₀.s * f)`).
3. The inverse `divByS D₀.s (D₀.s * f)` times `canonicalMap D₀.s` gives
   `divByS (D₀.s * D₀.s) (D₀.s * f)`, which lies in `locSubring` because
   `D₀.s * D₀.s = D₀.s * D₀.s ∈ (laurentMinusDatum).T`
   (via the product `(insert D₀.s D₀.T) × {D₀.s, f}` taking `a = b = D₀.s`).
4. Use the Wedhorn base-change Nullstellensatz (Prop 8.2) to derive full
   power-boundedness of the inverse.

**Status**: deferred as a single sub-sorry (Wedhorn §8.2 base-change
Nullstellensatz). Parallels `iteratedMinus_forwardLocHom_generators_powerBounded`. -/
private theorem iteratedMinus_backwardLocHom_generator_powerBounded
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (D₀ : RationalLocData A)
    [IsNoetherianRing (locSubring D₀.P D₀.T D₀.s)]
    [LaurentNormalized D₀]
    (f : A)
    (hsub : rationalOpen (laurentMinusDatum D₀ f).T (laurentMinusDatum D₀ f).s ⊆
      rationalOpen D₀.T D₀.s) :
    TopologicalRing.IsPowerBounded
      (iteratedMinus_backwardLocHom D₀ f hsub
        (divByS (1 : presheafValue D₀) (iteratedMinusDatum_B P D₀ f).s)) := by
  -- Step 1: Rewrite `backward(divByS 1 (canonicalMap f)) =
  -- (laurentMinus).coeRingHom(divByS D₀.s (D₀.s * f))`, which is in
  -- `coeRingHom '' locSubring (laurentMinus)`.
  -- In `Loc_A(D₀.s * f)`, `divByS D₀.s (D₀.s*f)` is the inverse of `algebraMap f`.
  have hinv_src : divByS D₀.s (D₀.s * f) *
      algebraMap A (Localization.Away (D₀.s * f)) f = 1 := by
    unfold divByS
    rw [← IsLocalization.mk'_one (M := Submonoid.powers (D₀.s * f))
          (S := Localization.Away (D₀.s * f)) f,
        ← IsLocalization.mk'_mul, mul_one]
    exact IsLocalization.mk'_self _ _
  -- Apply `(laurentMinus).coeRingHom` to get an inverse of `(laurentMinus).canonicalMap f`.
  have hinv_target : (laurentMinusDatum D₀ f).coeRingHom
      (divByS D₀.s (D₀.s * f)) * (laurentMinusDatum D₀ f).canonicalMap f = 1 := by
    have h : (laurentMinusDatum D₀ f).coeRingHom (divByS D₀.s (D₀.s * f)) *
        (laurentMinusDatum D₀ f).coeRingHom
          (algebraMap A (Localization.Away (D₀.s * f)) f) =
        (laurentMinusDatum D₀ f).coeRingHom 1 := by
      rw [← map_mul]
      exact congrArg _ hinv_src
    rw [map_one] at h
    exact h
  have hu_cf : IsUnit ((laurentMinusDatum D₀ f).canonicalMap f) :=
    canonicalMap_f_isUnit_in_laurentMinus D₀ f
  -- `backward(divByS 1 (canonicalMap f)) = ((laurentMinus).canonicalMap f)⁻¹`.
  have hbwd_eq : iteratedMinus_backwardLocHom D₀ f hsub
      (divByS (1 : presheafValue D₀) (iteratedMinusDatum_B P D₀ f).s) =
      (laurentMinusDatum D₀ f).coeRingHom (divByS D₀.s (D₀.s * f)) := by
    -- Both sides, multiplied by `(laurentMinus).canonicalMap f`, give 1.
    -- For LHS: `backward(divByS 1 (canonicalMap f)) * backward(algebraMap_B(canonicalMap f)) =
    --   backward(divByS 1 (canonicalMap f) * algebraMap_B(canonicalMap f)) = backward(1) = 1`.
    -- And `backward(algebraMap_B(canonicalMap f)) = restrictionMapHom(canonicalMap f) =
    --   (laurentMinus).canonicalMap f`.
    apply hu_cf.mul_right_cancel
    rw [hinv_target]
    have hprod : divByS (1 : presheafValue D₀) (D₀.canonicalMap f) *
        algebraMap (presheafValue D₀) (Localization.Away (D₀.canonicalMap f))
          (D₀.canonicalMap f) = 1 := by
      rw [mul_comm]
      unfold divByS
      rw [← IsLocalization.mk'_one (M := Submonoid.powers (D₀.canonicalMap f))
            (S := Localization.Away (D₀.canonicalMap f)) (D₀.canonicalMap f),
          ← IsLocalization.mk'_mul, mul_one, one_mul]
      exact IsLocalization.mk'_self _ _
    have := congrArg (iteratedMinus_backwardLocHom D₀ f hsub) hprod
    rw [map_mul, map_one, iteratedMinus_backwardLocHom_algebraMap,
      restrictionMapHom_canonicalMap] at this
    exact this
  rw [hbwd_eq]
  -- Step 2: `divByS D₀.s (D₀.s * f) ∈ locSubring (laurentMinus)`, because
  -- `D₀.s = 1 * D₀.s ∈ (laurentMinus).T` (via `LaurentNormalized.one_mem_T`).
  have hDs_mem : D₀.s ∈ (laurentMinusDatum D₀ f).T := by
    refine Finset.mem_image.mpr ⟨(1, D₀.s), ?_, by ring⟩
    refine Finset.mem_product.mpr ⟨?_, ?_⟩
    · exact Finset.mem_insert_of_mem LaurentNormalized.one_mem_T
    · exact Finset.mem_insert_self _ _
  have hdiv_mem : divByS D₀.s (D₀.s * f) ∈
      locSubring (laurentMinusDatum D₀ f).P (laurentMinusDatum D₀ f).T
        (laurentMinusDatum D₀ f).s :=
    divByS_mem_locSubring _ _ _ hDs_mem
  -- Step 3: `coeRingHom '' locSubring` is bounded; powers stay in it.
  apply (CompletionLocalization.coeRingHom_image_locSubring_isBounded
    (laurentMinusDatum D₀ f)).subset
  rintro _ ⟨n, rfl⟩
  change ((laurentMinusDatum D₀ f).coeRingHom (divByS D₀.s (D₀.s * f))) ^ n ∈ _
  rw [← map_pow]
  exact ⟨(divByS D₀.s (D₀.s * f)) ^ n,
    (locSubring _ _ _).pow_mem hdiv_mem n, rfl⟩

/-- Continuity of the backward uncompleted hom (minus branch).

**Proof**: Apply `locTopology_continuous_lift` to `iteratedMinus_backwardLocHom D₀ f hsub`
with base ring `B = presheafValue D₀`, source data
`((iteratedMinusDatum_B P D₀ f).P, {1}, canonicalMap f)`, and target
`presheafValue (laurentMinusDatum D₀ f)`. Reduces to two conditions:

(a) `iteratedMinus_backwardLocHom ∘ algebraMap B = restrictionMapHom D₀ (laurentMinusDatum D₀ f) hsub`
    (by `iteratedMinus_backwardLocHom_algebraMap`), continuous by
    `restrictionMapHom_continuous`.
(b) For the single generator `divByS 1 (canonicalMap f)`, the image is
    power-bounded: `iteratedMinus_backwardLocHom_generator_powerBounded`. -/
theorem iteratedMinus_backwardLocHom_continuous
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (D₀ : RationalLocData A)
    [IsNoetherianRing (locSubring D₀.P D₀.T D₀.s)]
    [LaurentNormalized D₀]
    (f : A)
    (hsub : rationalOpen (laurentMinusDatum D₀ f).T (laurentMinusDatum D₀ f).s ⊆
      rationalOpen D₀.T D₀.s) :
    @Continuous _ _ (iteratedMinusDatum_B P D₀ f).topology _
      (iteratedMinus_backwardLocHom D₀ f hsub) := by
  -- Apply `locTopology_continuous_lift` for the lift on source
  -- `Loc_B(canonicalMap f)` with `iteratedMinusDatum_B` topology.
  letI topB : TopologicalSpace (Localization.Away (D₀.canonicalMap f)) :=
    (iteratedMinusDatum_B P D₀ f).topology
  letI : TopologicalSpace (Localization.Away (iteratedMinusDatum_B P D₀ f).s) := topB
  letI : IsTopologicalRing (Localization.Away (D₀.canonicalMap f)) :=
    (iteratedMinusDatum_B P D₀ f).isTopologicalRing
  letI : IsTopologicalRing (Localization.Away (iteratedMinusDatum_B P D₀ f).s) :=
    (iteratedMinusDatum_B P D₀ f).isTopologicalRing
  -- Target is nonarchimedean ring (for `locTopology_continuous_lift`).
  haveI : NonarchimedeanRing (presheafValue (laurentMinusDatum D₀ f)) :=
    presheafValueNonarchimedeanRing (laurentMinusDatum D₀ f)
  -- Continuity of `backwardLocHom ∘ algebraMap B`: the composite equals
  -- `restrictionMapHom D₀ (laurentMinusDatum D₀ f) hsub` (by
  -- `iteratedMinus_backwardLocHom_algebraMap`), which is continuous by
  -- `restrictionMapHom_continuous`.
  have hf_alg : @Continuous _ _ _ _
      ((iteratedMinus_backwardLocHom D₀ f hsub).comp
        (algebraMap (presheafValue D₀)
          (Localization.Away (iteratedMinusDatum_B P D₀ f).s))) := by
    have heq : (iteratedMinus_backwardLocHom D₀ f hsub).comp
        (algebraMap (presheafValue D₀)
          (Localization.Away (iteratedMinusDatum_B P D₀ f).s)) =
        restrictionMapHom D₀ (laurentMinusDatum D₀ f) hsub := by
      ext b
      simp only [RingHom.comp_apply]
      exact iteratedMinus_backwardLocHom_algebraMap D₀ f hsub b
    rw [show ⇑((iteratedMinus_backwardLocHom D₀ f hsub).comp
        (algebraMap (presheafValue D₀)
          (Localization.Away (iteratedMinusDatum_B P D₀ f).s))) =
      ⇑(restrictionMapHom D₀ (laurentMinusDatum D₀ f) hsub) from
      congr_arg _ heq]
    exact restrictionMapHom_continuous D₀ (laurentMinusDatum D₀ f) hsub
  -- Power-boundedness of the single generator at `t = 1`.
  have hpow : ∀ t ∈ (iteratedMinusDatum_B P D₀ f).T,
      TopologicalRing.IsPowerBounded
        (iteratedMinus_backwardLocHom D₀ f hsub
          (divByS t (iteratedMinusDatum_B P D₀ f).s)) := by
    intro t ht
    -- `T = {1}`, so `t = 1`.
    rw [show (iteratedMinusDatum_B P D₀ f).T = {1} from rfl] at ht
    rw [Finset.mem_singleton] at ht
    subst ht
    exact iteratedMinus_backwardLocHom_generator_powerBounded P D₀ f hsub
  -- Apply `locTopology_continuous_lift`.
  exact locTopology_continuous_lift (iteratedMinusDatum_B P D₀ f).P
    (iteratedMinusDatum_B P D₀ f).T (iteratedMinusDatum_B P D₀ f).s
    (iteratedMinusDatum_B P D₀ f).hopen
    (iteratedMinus_backwardLocHom D₀ f hsub) hf_alg hpow

/-- The forward completion hom (minus branch): `extensionHom` of
`iteratedMinus_forwardToCompletion`. -/
noncomputable def iteratedMinus_forwardHom
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (D₀ : RationalLocData A)
    [IsNoetherianRing (locSubring D₀.P D₀.T D₀.s)]
    [LaurentNormalized D₀]
    (f : A) :
    presheafValue (laurentMinusDatum D₀ f) →+*
      presheafValue (iteratedMinusDatum_B P D₀ f) :=
  letI : UniformSpace (Localization.Away (laurentMinusDatum D₀ f).s) :=
    (laurentMinusDatum D₀ f).uniformSpace
  letI : IsUniformAddGroup (Localization.Away (laurentMinusDatum D₀ f).s) :=
    (laurentMinusDatum D₀ f).isUniformAddGroup
  letI : IsTopologicalRing (Localization.Away (laurentMinusDatum D₀ f).s) :=
    (laurentMinusDatum D₀ f).isTopologicalRing
  UniformSpace.Completion.extensionHom
    (iteratedMinus_forwardToCompletion P D₀ f)
    (iteratedMinus_forwardToCompletion_continuous P D₀ f)

/-- The backward completion hom (minus branch): `extensionHom` of
`iteratedMinus_backwardLocHom`. -/
noncomputable def iteratedMinus_backwardHom
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (D₀ : RationalLocData A)
    [IsNoetherianRing (locSubring D₀.P D₀.T D₀.s)]
    [LaurentNormalized D₀]
    (f : A)
    (hsub : rationalOpen (laurentMinusDatum D₀ f).T (laurentMinusDatum D₀ f).s ⊆
      rationalOpen D₀.T D₀.s) :
    presheafValue (iteratedMinusDatum_B P D₀ f) →+*
      presheafValue (laurentMinusDatum D₀ f) :=
  letI : UniformSpace (Localization.Away (iteratedMinusDatum_B P D₀ f).s) :=
    (iteratedMinusDatum_B P D₀ f).uniformSpace
  letI : IsUniformAddGroup (Localization.Away (iteratedMinusDatum_B P D₀ f).s) :=
    (iteratedMinusDatum_B P D₀ f).isUniformAddGroup
  letI : IsTopologicalRing (Localization.Away (iteratedMinusDatum_B P D₀ f).s) :=
    (iteratedMinusDatum_B P D₀ f).isTopologicalRing
  UniformSpace.Completion.extensionHom
    (iteratedMinus_backwardLocHom D₀ f hsub)
    (iteratedMinus_backwardLocHom_continuous P D₀ f hsub)

/-- Forward completion hom acting on `coeRingHom a`: definitional unwind
via `extensionHom_coe`. -/
theorem iteratedMinus_forwardHom_coeRingHom
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (D₀ : RationalLocData A)
    [IsNoetherianRing (locSubring D₀.P D₀.T D₀.s)]
    [LaurentNormalized D₀]
    (f : A)
    (a : Localization.Away (laurentMinusDatum D₀ f).s) :
    iteratedMinus_forwardHom P D₀ f ((laurentMinusDatum D₀ f).coeRingHom a) =
      iteratedMinus_forwardToCompletion P D₀ f a := by
  letI : UniformSpace (Localization.Away (laurentMinusDatum D₀ f).s) :=
    (laurentMinusDatum D₀ f).uniformSpace
  letI : IsUniformAddGroup (Localization.Away (laurentMinusDatum D₀ f).s) :=
    (laurentMinusDatum D₀ f).isUniformAddGroup
  letI : IsTopologicalRing (Localization.Away (laurentMinusDatum D₀ f).s) :=
    (laurentMinusDatum D₀ f).isTopologicalRing
  exact UniformSpace.Completion.extensionHom_coe _ _ a

/-- Backward completion hom acting on `coeRingHom b`: definitional unwind. -/
theorem iteratedMinus_backwardHom_coeRingHom
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (D₀ : RationalLocData A)
    [IsNoetherianRing (locSubring D₀.P D₀.T D₀.s)]
    [LaurentNormalized D₀]
    (f : A)
    (hsub : rationalOpen (laurentMinusDatum D₀ f).T (laurentMinusDatum D₀ f).s ⊆
      rationalOpen D₀.T D₀.s)
    (b : Localization.Away (iteratedMinusDatum_B P D₀ f).s) :
    iteratedMinus_backwardHom P D₀ f hsub ((iteratedMinusDatum_B P D₀ f).coeRingHom b) =
      iteratedMinus_backwardLocHom D₀ f hsub b := by
  letI : UniformSpace (Localization.Away (iteratedMinusDatum_B P D₀ f).s) :=
    (iteratedMinusDatum_B P D₀ f).uniformSpace
  letI : IsUniformAddGroup (Localization.Away (iteratedMinusDatum_B P D₀ f).s) :=
    (iteratedMinusDatum_B P D₀ f).isUniformAddGroup
  letI : IsTopologicalRing (Localization.Away (iteratedMinusDatum_B P D₀ f).s) :=
    (iteratedMinusDatum_B P D₀ f).isTopologicalRing
  exact UniformSpace.Completion.extensionHom_coe _ _ b

/-- Round-trip 1 (minus branch): `backwardHom ∘ forwardHom = id`. This is
the `Completion.ext'` chase using the uncompleted-level identity
`iteratedMinus_backward_forward_locHom`. -/
theorem iteratedMinus_backwardHom_comp_forwardHom
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (D₀ : RationalLocData A)
    [IsNoetherianRing (locSubring D₀.P D₀.T D₀.s)]
    [LaurentNormalized D₀]
    (f : A)
    (hsub : rationalOpen (laurentMinusDatum D₀ f).T (laurentMinusDatum D₀ f).s ⊆
      rationalOpen D₀.T D₀.s) :
    (iteratedMinus_backwardHom P D₀ f hsub).comp (iteratedMinus_forwardHom P D₀ f) =
      RingHom.id _ := by
  letI : UniformSpace (Localization.Away (laurentMinusDatum D₀ f).s) :=
    (laurentMinusDatum D₀ f).uniformSpace
  letI : IsUniformAddGroup (Localization.Away (laurentMinusDatum D₀ f).s) :=
    (laurentMinusDatum D₀ f).isUniformAddGroup
  letI : IsTopologicalRing (Localization.Away (laurentMinusDatum D₀ f).s) :=
    (laurentMinusDatum D₀ f).isTopologicalRing
  letI : UniformSpace (Localization.Away (iteratedMinusDatum_B P D₀ f).s) :=
    (iteratedMinusDatum_B P D₀ f).uniformSpace
  letI : IsUniformAddGroup (Localization.Away (iteratedMinusDatum_B P D₀ f).s) :=
    (iteratedMinusDatum_B P D₀ f).isUniformAddGroup
  letI : IsTopologicalRing (Localization.Away (iteratedMinusDatum_B P D₀ f).s) :=
    (iteratedMinusDatum_B P D₀ f).isTopologicalRing
  apply RingHom.ext
  intro x
  show iteratedMinus_backwardHom P D₀ f hsub (iteratedMinus_forwardHom P D₀ f x) = x
  refine @UniformSpace.Completion.ext' _ _ _ _ _ _ _
    ((UniformSpace.Completion.continuous_extension).comp
      UniformSpace.Completion.continuous_extension)
    continuous_id ?_ x
  intro a
  show iteratedMinus_backwardHom P D₀ f hsub
      (iteratedMinus_forwardHom P D₀ f ((laurentMinusDatum D₀ f).coeRingHom a)) =
    (laurentMinusDatum D₀ f).coeRingHom a
  rw [iteratedMinus_forwardHom_coeRingHom,
      show iteratedMinus_forwardToCompletion P D₀ f a =
        (iteratedMinusDatum_B P D₀ f).coeRingHom
          (iteratedMinus_forwardLocHom D₀ f a) from rfl,
      iteratedMinus_backwardHom_coeRingHom]
  have := congr_fun (congrArg DFunLike.coe
    (iteratedMinus_backward_forward_locHom D₀ f hsub)) a
  exact this

/-- The core uncompleted-plus-completed identity (minus branch):
`iteratedMinus_forwardHom ∘ restrictionMapHom = (iteratedMinusDatum_B).canonicalMap`
as a continuous ring hom `presheafValue D₀ → presheafValue (iteratedMinusDatum_B P D₀ f)`.

This is the dual of `iteratedMinus_backward_forward_locHom` (which works at
the uncompleted level for forward-then-backward). Here the equality is at the
completion level on the source — we check it via `Completion.ext'` on
`x : presheafValue D₀` plus `IsLocalization.ringHom_ext` on the reduced
`Loc_A(D₀.s) → presheafValue (iteratedMinusDatum_B)` homs. -/
theorem iteratedMinus_forwardHom_comp_restrictionMapHom
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (D₀ : RationalLocData A)
    [IsNoetherianRing (locSubring D₀.P D₀.T D₀.s)]
    [LaurentNormalized D₀]
    (f : A)
    (hsub : rationalOpen (laurentMinusDatum D₀ f).T (laurentMinusDatum D₀ f).s ⊆
      rationalOpen D₀.T D₀.s) :
    (iteratedMinus_forwardHom P D₀ f).comp
        (restrictionMapHom D₀ (laurentMinusDatum D₀ f) hsub) =
      (iteratedMinusDatum_B P D₀ f).canonicalMap := by
  letI : UniformSpace (Localization.Away D₀.s) := D₀.uniformSpace
  letI : IsUniformAddGroup (Localization.Away D₀.s) := D₀.isUniformAddGroup
  letI : IsTopologicalRing (Localization.Away D₀.s) := D₀.isTopologicalRing
  letI : UniformSpace (Localization.Away (laurentMinusDatum D₀ f).s) :=
    (laurentMinusDatum D₀ f).uniformSpace
  letI : IsUniformAddGroup (Localization.Away (laurentMinusDatum D₀ f).s) :=
    (laurentMinusDatum D₀ f).isUniformAddGroup
  letI : IsTopologicalRing (Localization.Away (laurentMinusDatum D₀ f).s) :=
    (laurentMinusDatum D₀ f).isTopologicalRing
  letI : UniformSpace (Localization.Away (iteratedMinusDatum_B P D₀ f).s) :=
    (iteratedMinusDatum_B P D₀ f).uniformSpace
  letI : IsUniformAddGroup (Localization.Away (iteratedMinusDatum_B P D₀ f).s) :=
    (iteratedMinusDatum_B P D₀ f).isUniformAddGroup
  letI : IsTopologicalRing (Localization.Away (iteratedMinusDatum_B P D₀ f).s) :=
    (iteratedMinusDatum_B P D₀ f).isTopologicalRing
  apply RingHom.ext
  intro b
  show iteratedMinus_forwardHom P D₀ f
      (restrictionMapHom D₀ (laurentMinusDatum D₀ f) hsub b) =
    (iteratedMinusDatum_B P D₀ f).canonicalMap b
  -- Apply Completion.ext' on b : presheafValue D₀ (a completion of Loc_A(D₀.s)).
  let lhsFun : presheafValue D₀ → presheafValue (iteratedMinusDatum_B P D₀ f) :=
    fun y => iteratedMinus_forwardHom P D₀ f
      (restrictionMapHom D₀ (laurentMinusDatum D₀ f) hsub y)
  let rhsFun : presheafValue D₀ → presheafValue (iteratedMinusDatum_B P D₀ f) :=
    fun y => (iteratedMinusDatum_B P D₀ f).canonicalMap y
  change lhsFun b = rhsFun b
  refine @UniformSpace.Completion.ext' (Localization.Away D₀.s) D₀.uniformSpace
    (presheafValue (iteratedMinusDatum_B P D₀ f)) _ _ lhsFun rhsFun ?_ ?_ ?_ b
  · -- Continuity LHS: composition of continuous restrictionMapHom and forwardHom.
    show Continuous (fun y : presheafValue D₀ =>
      iteratedMinus_forwardHom P D₀ f
        (restrictionMapHom D₀ (laurentMinusDatum D₀ f) hsub y))
    change Continuous (fun y : presheafValue D₀ =>
      iteratedMinus_forwardHom P D₀ f
        (restrictionMapHom D₀ (laurentMinusDatum D₀ f) hsub y))
    exact UniformSpace.Completion.continuous_extension.comp
      (restrictionMapHom_continuous D₀ (laurentMinusDatum D₀ f) hsub)
  · -- Continuity RHS: canonicalMap is continuous.
    exact canonicalMap_continuous (iteratedMinusDatum_B P D₀ f)
  -- Reduce to `b = D₀.coeRingHom a` for `a : Loc_A(D₀.s)`.
  intro a
  show lhsFun (D₀.coeRingHom a) = rhsFun (D₀.coeRingHom a)
  simp only [lhsFun, rhsFun]
  -- Further reduce via IsLocalization.ringHom_ext.
  let lhsHom : Localization.Away D₀.s →+*
      presheafValue (iteratedMinusDatum_B P D₀ f) :=
    (iteratedMinus_forwardHom P D₀ f).comp
      ((restrictionMapHom D₀ (laurentMinusDatum D₀ f) hsub).comp D₀.coeRingHom)
  let rhsHom : Localization.Away D₀.s →+*
      presheafValue (iteratedMinusDatum_B P D₀ f) :=
    ((iteratedMinusDatum_B P D₀ f).canonicalMap).comp D₀.coeRingHom
  suffices h : lhsHom = rhsHom by
    have := congr_fun (congrArg DFunLike.coe h) a
    show lhsHom a = rhsHom a
    exact this
  apply IsLocalization.ringHom_ext (Submonoid.powers D₀.s)
  ext c
  show lhsHom (algebraMap A _ c) = rhsHom (algebraMap A _ c)
  show iteratedMinus_forwardHom P D₀ f
      (restrictionMapHom D₀ (laurentMinusDatum D₀ f) hsub (D₀.coeRingHom (algebraMap A _ c))) =
    (iteratedMinusDatum_B P D₀ f).canonicalMap (D₀.coeRingHom (algebraMap A _ c))
  show iteratedMinus_forwardHom P D₀ f
      (restrictionMapHom D₀ (laurentMinusDatum D₀ f) hsub (D₀.canonicalMap c)) =
    (iteratedMinusDatum_B P D₀ f).canonicalMap (D₀.canonicalMap c)
  rw [restrictionMapHom_canonicalMap]
  show iteratedMinus_forwardHom P D₀ f
      ((laurentMinusDatum D₀ f).coeRingHom (algebraMap A _ c)) =
    (iteratedMinusDatum_B P D₀ f).canonicalMap (D₀.canonicalMap c)
  rw [iteratedMinus_forwardHom_coeRingHom]
  show (iteratedMinusDatum_B P D₀ f).coeRingHom
      (iteratedMinus_forwardLocHom D₀ f (algebraMap A _ c)) =
    (iteratedMinusDatum_B P D₀ f).canonicalMap (D₀.canonicalMap c)
  rw [iteratedMinus_forwardLocHom_algebraMap]
  rfl

/-- Round-trip 2 (minus branch): `forwardHom ∘ backwardHom = id`. Proved via
`Completion.ext'` on `x : presheafValue (iteratedMinusDatum_B P D₀ f)` +
`IsLocalization.ringHom_ext` on `Loc_B(canonicalMap f)`, reducing to the
core identity `iteratedMinus_forwardHom_comp_restrictionMapHom`. -/
theorem iteratedMinus_forwardHom_comp_backwardHom
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (D₀ : RationalLocData A)
    [IsNoetherianRing (locSubring D₀.P D₀.T D₀.s)]
    [LaurentNormalized D₀]
    (f : A)
    (hsub : rationalOpen (laurentMinusDatum D₀ f).T (laurentMinusDatum D₀ f).s ⊆
      rationalOpen D₀.T D₀.s) :
    (iteratedMinus_forwardHom P D₀ f).comp (iteratedMinus_backwardHom P D₀ f hsub) =
      RingHom.id _ := by
  letI : UniformSpace (Localization.Away D₀.s) := D₀.uniformSpace
  letI : IsUniformAddGroup (Localization.Away D₀.s) := D₀.isUniformAddGroup
  letI : IsTopologicalRing (Localization.Away D₀.s) := D₀.isTopologicalRing
  letI : UniformSpace (Localization.Away (laurentMinusDatum D₀ f).s) :=
    (laurentMinusDatum D₀ f).uniformSpace
  letI : IsUniformAddGroup (Localization.Away (laurentMinusDatum D₀ f).s) :=
    (laurentMinusDatum D₀ f).isUniformAddGroup
  letI : IsTopologicalRing (Localization.Away (laurentMinusDatum D₀ f).s) :=
    (laurentMinusDatum D₀ f).isTopologicalRing
  letI : UniformSpace (Localization.Away (iteratedMinusDatum_B P D₀ f).s) :=
    (iteratedMinusDatum_B P D₀ f).uniformSpace
  letI : IsUniformAddGroup (Localization.Away (iteratedMinusDatum_B P D₀ f).s) :=
    (iteratedMinusDatum_B P D₀ f).isUniformAddGroup
  letI : IsTopologicalRing (Localization.Away (iteratedMinusDatum_B P D₀ f).s) :=
    (iteratedMinusDatum_B P D₀ f).isTopologicalRing
  apply RingHom.ext
  intro x
  show iteratedMinus_forwardHom P D₀ f (iteratedMinus_backwardHom P D₀ f hsub x) = x
  -- Completion.ext' on x : presheafValue (iteratedMinusDatum_B P D₀ f).
  refine @UniformSpace.Completion.ext'
    (Localization.Away (iteratedMinusDatum_B P D₀ f).s) _ _ _ _ _ _
    ((UniformSpace.Completion.continuous_extension).comp
      UniformSpace.Completion.continuous_extension)
    continuous_id ?_ x
  intro y
  -- Reduce to coeRingHom y.
  show iteratedMinus_forwardHom P D₀ f
      (iteratedMinus_backwardHom P D₀ f hsub
        ((iteratedMinusDatum_B P D₀ f).coeRingHom y)) =
    (iteratedMinusDatum_B P D₀ f).coeRingHom y
  rw [iteratedMinus_backwardHom_coeRingHom]
  -- Use IsLocalization.ringHom_ext on y : Loc_B(canonicalMap f) to reduce
  -- to y = algebraMap B _ b for b : presheafValue D₀.
  let lhsHom : Localization.Away (iteratedMinusDatum_B P D₀ f).s →+*
      presheafValue (iteratedMinusDatum_B P D₀ f) :=
    (iteratedMinus_forwardHom P D₀ f).comp (iteratedMinus_backwardLocHom D₀ f hsub)
  let rhsHom : Localization.Away (iteratedMinusDatum_B P D₀ f).s →+*
      presheafValue (iteratedMinusDatum_B P D₀ f) :=
    (iteratedMinusDatum_B P D₀ f).coeRingHom
  suffices h : lhsHom = rhsHom by
    have := congr_fun (congrArg DFunLike.coe h) y
    show lhsHom y = rhsHom y
    exact this
  apply IsLocalization.ringHom_ext (Submonoid.powers (iteratedMinusDatum_B P D₀ f).s)
  ext b
  show lhsHom (algebraMap (presheafValue D₀) _ b) =
    rhsHom (algebraMap (presheafValue D₀) _ b)
  show iteratedMinus_forwardHom P D₀ f
      (iteratedMinus_backwardLocHom D₀ f hsub
        (algebraMap (presheafValue D₀) _ b)) =
    (iteratedMinusDatum_B P D₀ f).coeRingHom (algebraMap (presheafValue D₀) _ b)
  rw [iteratedMinus_backwardLocHom_algebraMap]
  -- Goal: forwardHom (restrictionMapHom b) = (iteratedMinusDatum_B).canonicalMap b.
  -- This is the core identity `iteratedMinus_forwardHom_comp_restrictionMapHom`.
  exact congr_fun (congrArg DFunLike.coe
    (iteratedMinus_forwardHom_comp_restrictionMapHom P D₀ f hsub)) b

/-- **Iterated rational identification, minus branch (Wedhorn Lemma 2.13)**.

The symmetric statement for the minus datum: `rationalOpen (laurentMinusDatum D₀ f)
⊂ Spa A` equals `rationalOpen (iteratedMinusDatum_B P D₀ f) ⊂ Spa B`,
and their global sections agree.

Composing with `presheafValueTateQuotientEquiv` at `B` with
`D := iteratedMinusDatum_B P D₀ f` gives the Laurent-minus bridge (since
`s_B = canonicalMap f` so the quotient is `B⟨X⟩/(1 − canonicalMap(f)·X) = B₂_gen`). -/
noncomputable def presheafValue_iteratedMinus_equiv
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (D₀ : RationalLocData A)
    [IsNoetherianRing (locSubring D₀.P D₀.T D₀.s)]
    [LaurentNormalized D₀]
    (f : A) :
    presheafValue (laurentMinusDatum D₀ f) ≃+*
      presheafValue (iteratedMinusDatum_B P D₀ f) :=
  let hsub := laurentMinus_subset D₀ f
  { toFun := iteratedMinus_forwardHom P D₀ f
    invFun := iteratedMinus_backwardHom P D₀ f hsub
    left_inv := fun x =>
      congr_fun (congrArg DFunLike.coe
        (iteratedMinus_backwardHom_comp_forwardHom P D₀ f hsub)) x
    right_inv := fun y =>
      congr_fun (congrArg DFunLike.coe
        (iteratedMinus_forwardHom_comp_backwardHom P D₀ f hsub)) y
    map_mul' := map_mul _
    map_add' := map_add _ }

/-- The equiv's forward action equals `iteratedMinus_forwardHom` (definitional
unwind; enables downstream sub-sorries to reduce to the concrete `forwardHom`). -/
theorem presheafValue_iteratedMinus_equiv_apply
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (D₀ : RationalLocData A)
    [IsNoetherianRing (locSubring D₀.P D₀.T D₀.s)]
    [LaurentNormalized D₀]
    (f : A) (x : presheafValue (laurentMinusDatum D₀ f)) :
    presheafValue_iteratedMinus_equiv P D₀ f x =
      iteratedMinus_forwardHom P D₀ f x := rfl

/-- Equiv's action on `(laurentMinusDatum D₀ f).coeRingHom a`:
factors through `iteratedMinus_forwardToCompletion`. -/
theorem presheafValue_iteratedMinus_equiv_coeRingHom
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (D₀ : RationalLocData A)
    [IsNoetherianRing (locSubring D₀.P D₀.T D₀.s)]
    [LaurentNormalized D₀]
    (f : A)
    (a : Localization.Away (laurentMinusDatum D₀ f).s) :
    presheafValue_iteratedMinus_equiv P D₀ f
        ((laurentMinusDatum D₀ f).coeRingHom a) =
      (iteratedMinusDatum_B P D₀ f).coeRingHom
        (iteratedMinus_forwardLocHom D₀ f a) := by
  rw [presheafValue_iteratedMinus_equiv_apply, iteratedMinus_forwardHom_coeRingHom]
  rfl

/-! #### Continuity and inducing topology of `presheafValue_iteratedMinus_equiv`
(T146 minus-branch analogue)

The forward / backward completion homs `iteratedMinus_forwardHom` and
`iteratedMinus_backwardHom` are both `UniformSpace.Completion.extensionHom`
of (uncompleted) continuous ring homs, hence continuous via
`UniformSpace.Completion.continuous_extension`. The minus-branch ring
equiv `presheafValue_iteratedMinus_equiv` is therefore
`Topology.IsInducing` in both directions. -/

/-- Continuity of the minus-branch forward completion hom. -/
theorem iteratedMinus_forwardHom_continuous
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (D₀ : RationalLocData A)
    [IsNoetherianRing (locSubring D₀.P D₀.T D₀.s)]
    [LaurentNormalized D₀]
    (f : A) :
    Continuous (iteratedMinus_forwardHom P D₀ f) := by
  letI : UniformSpace (Localization.Away (laurentMinusDatum D₀ f).s) :=
    (laurentMinusDatum D₀ f).uniformSpace
  letI : IsUniformAddGroup (Localization.Away (laurentMinusDatum D₀ f).s) :=
    (laurentMinusDatum D₀ f).isUniformAddGroup
  letI : IsTopologicalRing (Localization.Away (laurentMinusDatum D₀ f).s) :=
    (laurentMinusDatum D₀ f).isTopologicalRing
  exact UniformSpace.Completion.continuous_extension

/-- Continuity of the minus-branch backward completion hom. -/
theorem iteratedMinus_backwardHom_continuous
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (D₀ : RationalLocData A)
    [IsNoetherianRing (locSubring D₀.P D₀.T D₀.s)]
    [LaurentNormalized D₀]
    (f : A)
    (hsub : rationalOpen (laurentMinusDatum D₀ f).T (laurentMinusDatum D₀ f).s ⊆
      rationalOpen D₀.T D₀.s) :
    Continuous (iteratedMinus_backwardHom P D₀ f hsub) := by
  letI : UniformSpace (Localization.Away (iteratedMinusDatum_B P D₀ f).s) :=
    (iteratedMinusDatum_B P D₀ f).uniformSpace
  letI : IsUniformAddGroup (Localization.Away (iteratedMinusDatum_B P D₀ f).s) :=
    (iteratedMinusDatum_B P D₀ f).isUniformAddGroup
  letI : IsTopologicalRing (Localization.Away (iteratedMinusDatum_B P D₀ f).s) :=
    (iteratedMinusDatum_B P D₀ f).isTopologicalRing
  exact UniformSpace.Completion.continuous_extension

/-- **T146 minus: `presheafValue_iteratedMinus_equiv` packaged as `Homeomorph`.**
Both directions of the underlying completion-extension hom are continuous. -/
noncomputable def presheafValue_iteratedMinus_equiv_homeomorph
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (D₀ : RationalLocData A)
    [IsNoetherianRing (locSubring D₀.P D₀.T D₀.s)]
    [LaurentNormalized D₀]
    (f : A) :
    presheafValue (laurentMinusDatum D₀ f) ≃ₜ
      presheafValue (iteratedMinusDatum_B P D₀ f) :=
  { (presheafValue_iteratedMinus_equiv P D₀ f).toEquiv with
    continuous_toFun := iteratedMinus_forwardHom_continuous P D₀ f
    continuous_invFun :=
      iteratedMinus_backwardHom_continuous P D₀ f (laurentMinus_subset D₀ f) }

/-- **T146 minus: `presheafValue_iteratedMinus_equiv` is `Topology.IsInducing`.** -/
theorem presheafValue_iteratedMinus_equiv_isInducing
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (D₀ : RationalLocData A)
    [IsNoetherianRing (locSubring D₀.P D₀.T D₀.s)]
    [LaurentNormalized D₀]
    (f : A) :
    Topology.IsInducing
      ((presheafValue_iteratedMinus_equiv P D₀ f) :
        presheafValue (laurentMinusDatum D₀ f) →
          presheafValue (iteratedMinusDatum_B P D₀ f)) :=
  (presheafValue_iteratedMinus_equiv_homeomorph P D₀ f).isInducing

/-- **T146 minus: `(presheafValue_iteratedMinus_equiv).symm` is `Topology.IsInducing`.** -/
theorem presheafValue_iteratedMinus_equiv_symm_isInducing
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (D₀ : RationalLocData A)
    [IsNoetherianRing (locSubring D₀.P D₀.T D₀.s)]
    [LaurentNormalized D₀]
    (f : A) :
    Topology.IsInducing
      ((presheafValue_iteratedMinus_equiv P D₀ f).symm :
        presheafValue (iteratedMinusDatum_B P D₀ f) →
          presheafValue (laurentMinusDatum D₀ f)) :=
  (presheafValue_iteratedMinus_equiv_homeomorph P D₀ f).symm.isInducing

omit [PlusSubring A] [IsHuberRing A] [HasLocLiftPowerBounded A] in
/-- **Right-uniform-space `CompleteSpace` bridge for `presheafValue`** (T129).

The Route B Laurent bridge calls (e.g.,
`presheafValue_trivialPlus_fSubX_equiv` below) require a
`CompleteSpace` instance with respect to the **right-uniform-space**
structure on `presheafValue D` (the form Mathlib's
`UniformSpace.Completion`-style equivs ask for). The built-in
`CompleteSpace (presheafValue D)` instance from `Presheaf.lean` uses
the ambient `UniformSpace.Completion.uniformSpace` form, which agrees
with the right-uniform-space by `IsUniformAddGroup.rightUniformSpace_eq`.

This helper packages that two-line bridge so downstream Route B
ticket consumers can avoid open-coding it (cf. the explicit
`have hA_complete := …; rw [IsUniformAddGroup.rightUniformSpace_eq];
infer_instance` at the existing call sites in this file, e.g.
`presheafValue_iteratedMinus_fSubX_equiv` ~line 2607). -/
theorem CompleteSpace_presheafValue_rightUniformSpace
    (D : RationalLocData A) :
    @CompleteSpace (presheafValue D)
      (IsTopologicalAddGroup.rightUniformSpace (presheafValue D)) := by
  rw [IsUniformAddGroup.rightUniformSpace_eq]
  infer_instance

omit [PlusSubring A] [IsHuberRing A] [HasLocLiftPowerBounded A] in
/-- **T149 BaireSpace supplier for `presheafValue`.**

For any rational localization datum `D : RationalLocData A` over a
nonarchimedean topological ring `A`, the presheaf value `presheafValue D`
is a Baire space.

**Proof.** The localization topology `D.topology` has a countable basis
at `0` via `(locBasis D.P D.T D.s D.hopen).hasBasis_nhds_zero` (the basis
is indexed by `ℕ`). This makes the localization's nhds-of-zero filter
countably generated, hence — via `IsUniformAddGroup.uniformity_countably_generated`
— its uniformity is countably generated. By
`UniformSpace.pseudoMetricSpace`, the localization is then
pseudo-metrizable in a way compatible with its existing uniform
structure. Mathlib's `UniformSpace.Completion.instMetricSpace` then
upgrades the completion `presheafValue D` to a `MetricSpace`, and the
auto-chain `MetricSpace → IsCompletelyMetrizableSpace →
IsCompletelyPseudoMetrizableSpace → BaireSpace` finishes the job
(using also the auto-instance `CompleteSpace (presheafValue D)` from
`Presheaf.lean`).

Used by T147's `laurentCover_isEmbedding_presheaf_via_bridges` to
discharge both `hBaire_plus_B` and `hBaire_minus_B`. -/
theorem presheafValue_baireSpace
    [NonarchimedeanRing A]
    (D : RationalLocData A) :
    BaireSpace (presheafValue D) := by
  letI : UniformSpace (Localization.Away D.s) := D.uniformSpace
  letI : IsTopologicalRing (Localization.Away D.s) := D.isTopologicalRing
  letI : IsTopologicalAddGroup (Localization.Away D.s) := D.isTopologicalAddGroup
  letI : IsUniformAddGroup (Localization.Away D.s) := D.isUniformAddGroup
  -- The localization topology has countable basis at `0` (locBasis indexed by ℕ).
  haveI : (nhds (0 : Localization.Away D.s)).IsCountablyGenerated :=
    (locBasis D.P D.T D.s D.hopen).hasBasis_nhds_zero.isCountablyGenerated
  -- Hence the uniformity is countably generated.
  haveI : Filter.IsCountablyGenerated (uniformity (Localization.Away D.s)) :=
    IsUniformAddGroup.uniformity_countably_generated
  -- Pseudo-metrize the localization (compatible with its existing UniformSpace).
  letI : PseudoMetricSpace (Localization.Away D.s) :=
    UniformSpace.pseudoMetricSpace _
  -- The completion inherits a MetricSpace structure via
  -- `UniformSpace.Completion.instMetricSpace` (in `Mathlib.Topology.MetricSpace.Completion`).
  -- The bundled `toUniformSpace` of this metric agrees data-wise with the auto
  -- `instUniformSpacePresheafValue D` from `Presheaf.lean` (both are
  -- `UniformSpace.Completion.uniformSpace` of a uniform structure that
  -- equals `D.uniformSpace`), but Lean does not see this definitionally
  -- because the metric goes through `PseudoMetricSpace.toUniformSpace` of
  -- the letI'd `UniformSpace.pseudoMetricSpace _`. We work around this
  -- diamond by `letI`-ing the metric's `UniformSpace` directly so subsequent
  -- typeclass synthesis sees a single `UniformSpace` instance through which
  -- the auto-chain `MetricSpace ⟹ IsCompletelyPseudoMetrizableSpace ⟹ BaireSpace`
  -- can fire.
  letI hM : MetricSpace (presheafValue D) := UniformSpace.Completion.instMetricSpace
  letI : UniformSpace (presheafValue D) := hM.toUniformSpace
  haveI : @CompleteSpace (presheafValue D) hM.toUniformSpace := by
    -- `hM.toUniformSpace = Completion.uniformSpace D.uniformSpace`
    -- = `instUniformSpacePresheafValue D` by construction; the auto
    -- `CompleteSpace` from Presheaf.lean transports.
    show CompleteSpace (presheafValue D)
    infer_instance
  haveI : Filter.IsCountablyGenerated (uniformity (presheafValue D)) :=
    (Metric.uniformity_basis_dist_inv_nat_succ
      (α := presheafValue D)).isCountablyGenerated
  -- `IsCompletelyPseudoMetrizableSpace.of_completeSpace_pseudometrizable` and
  -- `BaireSpace.of_completelyPseudoMetrizable` close the goal.
  infer_instance

omit [PlusSubring A] [IsHuberRing A] [HasLocLiftPowerBounded A] in
/-- **T152 supplier: SigmaCompactSpace transports along continuous surjections.**

A general topology helper: if `X` is `SigmaCompactSpace` and `f : X → Y` is
continuous and surjective, then `Y` is `SigmaCompactSpace`. Proof:
`range f = univ` (by surjectivity), and `isSigmaCompact_range` gives that
the range of a continuous map from a sigma-compact space is sigma compact.

Used by the T152 quotient suppliers below to transport the (hard)
`SigmaCompactSpace (TateAlgebra A)` hypothesis through the canonical
quotient map onto the various `(TateAlgebra A) ⧸ I` quotients used by
the OMT chain (T142, T145). -/
theorem _root_.Function.Surjective.sigmaCompactSpace
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [SigmaCompactSpace X]
    {f : X → Y} (hf_surj : Function.Surjective f) (hf_cont : Continuous f) :
    SigmaCompactSpace Y := by
  rw [← isSigmaCompact_univ_iff, ← hf_surj.range_eq]
  exact isSigmaCompact_range hf_cont

omit [PlusSubring A] [IsHuberRing A] [HasLocLiftPowerBounded A] in
/-- **T152 supplier (plus-side): SigmaCompactSpace of the plus quotient under
the canonical quotient topology, given `SigmaCompactSpace (TateAlgebra B)`.**

Transports `SigmaCompactSpace (TateAlgebra B)` through the continuous
surjective canonical quotient map `Ideal.Quotient.mk (plusFSubXIdeal B b)`
to the quotient `(TateAlgebra B) ⧸ plusFSubXIdeal B b` with its canonical
quotient topology. Mirrors the structure of the Banach-OMT chain in
`Example638.lean` and `Adic spaces/LaurentRefinement.lean`'s consumer
wrappers. -/
theorem quotientPlusFSubXIdeal_sigmaCompactSpace_of_source
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (b : A)
    (_ : SigmaCompactSpace ↥(TateAlgebra A)) :
    @SigmaCompactSpace (↥(TateAlgebra A) ⧸ plusFSubXIdeal A b)
      (quotientPlusFSubXIdealTopology A b) := by
  letI τ : TopologicalSpace (↥(TateAlgebra A) ⧸ plusFSubXIdeal A b) :=
    quotientPlusFSubXIdealTopology A b
  letI _hringQ : @IsTopologicalRing (↥(TateAlgebra A) ⧸ plusFSubXIdeal A b) τ _ :=
    quotientPlusFSubXIdealTopology_isTopologicalRing A b
  -- The quotient map `mk : TateAlgebra A → (TateAlgebra A) ⧸ plusFSubXIdeal A b`
  -- is continuous (under the canonical quotient topology τ) and surjective.
  have hcont : Continuous (Ideal.Quotient.mk (plusFSubXIdeal A b)) :=
    continuous_quot_mk
  have hsurj : Function.Surjective (Ideal.Quotient.mk (plusFSubXIdeal A b)) :=
    Ideal.Quotient.mk_surjective
  exact hsurj.sigmaCompactSpace hcont

omit [PlusSubring A] [IsHuberRing A] [HasLocLiftPowerBounded A] in
/-- **T152 supplier (minus-side): SigmaCompactSpace of the `oneSubfXIdeal`
quotient under its canonical quotient topology, given
`SigmaCompactSpace (TateAlgebra A)`.**

Minus-branch analogue of `quotientPlusFSubXIdeal_sigmaCompactSpace_of_source`,
matching the form of the `hSigma_minus_B` hypothesis used by T149's
`laurentCover_isEmbedding_presheaf_via_bridges_baire_auto`. -/
theorem quotientOneSubfXIdeal_sigmaCompactSpace_of_source
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (s : A)
    (_ : SigmaCompactSpace ↥(TateAlgebra A)) :
    @SigmaCompactSpace (↥(TateAlgebra A) ⧸ TateAlgebra.oneSubfXIdeal s)
      (TateAlgebra.quotientOneSubfXIdealTopology s) := by
  letI τ : TopologicalSpace (↥(TateAlgebra A) ⧸ TateAlgebra.oneSubfXIdeal s) :=
    TateAlgebra.quotientOneSubfXIdealTopology s
  letI _hringQ :
      @IsTopologicalRing (↥(TateAlgebra A) ⧸ TateAlgebra.oneSubfXIdeal s) τ _ :=
    TateAlgebra.quotientOneSubfXIdealTopology_isTopologicalRing s
  have hcont : Continuous (Ideal.Quotient.mk (TateAlgebra.oneSubfXIdeal s)) :=
    continuous_quot_mk
  have hsurj :
      Function.Surjective (Ideal.Quotient.mk (TateAlgebra.oneSubfXIdeal s)) :=
    Ideal.Quotient.mk_surjective
  exact hsurj.sigmaCompactSpace hcont

/-! ### T152 route-decision documentation: SigmaCompactSpace blocker scope

The two `quotient*_sigmaCompactSpace_of_source` suppliers above transport
the SigmaCompactSpace hypothesis through the quotient map, but the
**source** hypothesis `SigmaCompactSpace (TateAlgebra A)` (with the
canonical Tate topology) cannot be discharged generically over an
arbitrary strongly noetherian Tate ring `A`.

**Mathematical reason.** `TateAlgebra A` has a "ring of definition"
`pairSubring P : Subring (TateAlgebra A)` with the `pairIdeal P`-adic
topology. With a topologically nilpotent unit `π ∈ A`, every element of
`TateAlgebra A` lies in `π^(-n) · pairSubring P` for some `n`, giving the
covering decomposition
`TateAlgebra A = ⋃_{n : ℕ} π^(-n) · pairSubring P`.
Each piece `π^(-n) · pairSubring P` is compact iff `pairSubring P` is
compact, iff `pairSubring P` is profinite-with-finite-residue-quotients,
which holds iff `A` is a *local field* setting (`A₀ = ℤ_p`, `𝔽_p[[t]]`,
or similar). For a generic noetherian Tate ring (e.g.,
`A = ℂ((t))` with `A₀ = ℂ[[t]]`), `pairSubring P = ℂ[[t]]⟨X⟩` is **not**
compact, and `TateAlgebra A` is **not** sigma compact.

**Consequence for the OMT chain.** Mathlib's only Banach OMT for
topological groups, `MonoidHom.isOpenMap_of_sigmaCompact`
(`Mathlib/Topology/Algebra/Group/OpenMapping.lean:113`), explicitly
requires SigmaCompactSpace on the source and notes "Note that a
sigma-compactness assumption is necessary"
(`Mathlib/Topology/Algebra/Group/OpenMapping.lean:19`,
counterexample: discrete-real → usual-real). The normed-space variant
`ContinuousLinearMap.isOpenMap` does not need sigma compactness but
requires `NormedSpace`, which `TateAlgebra` does not have.

**Replacement options for an OMT-based consumer:**

1. **Scope restriction `[CompactSpace ↥(TateAlgebra.pairSubring P)]`**
   (where `P` is the canonical principal pair). This gives compactness
   of `pairSubring P` and then `SigmaCompactSpace (TateAlgebra A)` via
   the `π^(-n) · pairSubring P` decomposition (currently not on disk;
   would require Wedhorn-style Tate-algebra structure infrastructure).
   Concrete and clean, but applies only to the local-field setting.

2. **Scope restriction `[LocallyCompactSpace A]`**. By the structure
   theory of Tate rings, this implies `A₀` has a compact open subgroup,
   from which `CompactSpace ↥(TateAlgebra.pairSubring P)` follows.
   Equivalent to (1) but stated at the base level.

3. **Direct construction of the inducing map** without OMT. For Tate
   algebras, the inverse of the relevant restriction map could be
   constructed explicitly (e.g., via "evaluate at a topologically
   nilpotent unit"). Substantial new infrastructure.

4. **Bypass the OMT chain entirely.** As noted in the docstring of
   `tateAcyclicity` (this file, line 5422 sequence), the final Tate
   acyclicity theorem (`tateAcyclicity`) uses Wedhorn's flatness route
   and does **not** depend on the OMT-derived strict embedding lemmas.
   The OMT chain (T134–T149, plus the present file's
   `laurentCover_isEmbedding_presheaf_*` family) is parameterized
   infrastructure for *future* consumers that want strict-embedding
   properties beyond the sheaf-of-sets statement.

**Replacement theorem statement** (the SigmaCompact source hypothesis
that would unblock the consumer chain, leaving open only the question
of *when* it is supplied):
```
theorem tateAlgebra_sigmaCompactSpace [scope_restriction] :
    SigmaCompactSpace ↥(TateAlgebra A)
```
where `[scope_restriction]` is one of (1)–(2) above, depending on the
desired generality.

This T152 ticket therefore lands the two `quotient_*_sigmaCompactSpace_of_source`
transport suppliers above (axiom-clean, no scope assumption beyond
`[SigmaCompactSpace ↥(TateAlgebra A)]`) but does **not** ship a generic
`SigmaCompactSpace (TateAlgebra A)` supplier, because none exists at
the level of generality this project's strongly-noetherian Tate setup
operates at. -/

/-- **Non-discrete `f − X` quotient equivalence over a generic Tate base B**
(Q3-STEP2D, the primitive the reviewer flagged as genuinely new for Q3).

The generic version at arbitrary complete strongly noetherian Tate base is
proved in `Example638.lean` as `example638Plus_equiv`. We instantiate it at
`B := presheafValue D₀` with `b := D₀.canonicalMap f`. This requires several
hypotheses on `presheafValue D₀` (noetherianness; HasLocLiftPowerBounded;
noetherianness of the pair-of-definition subring; completeness in the
right-uniform-space sense; noetherianness of the Tate-algebra pair subring;
continuity of the forward quotient hom) which we hoist into the signature —
the same pattern used by `laurentMinusBridge` for the minus branch.

The target equivalence holds up to the definitional identities
`iteratedPlusDatum_B = trivialPlusDatum` and
`B₁_gen = TateAlgebra ⧸ plusFSubXIdeal`; both hold by `rfl`. -/
noncomputable def presheafValue_trivialPlus_fSubX_equiv
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (D₀ : RationalLocData A)
    [IsNoetherianRing (locSubring D₀.P D₀.T D₀.s)]
    (f : A)
    (hNoeth_B : IsNoetherianRing (presheafValue D₀))
    (hLocLift_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      HasLocLiftPowerBounded (presheafValue D₀))
    (hA₀Noeth_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      letI : IsNoetherianRing (presheafValue D₀) := hNoeth_B
      IsNoetherianRing ↥((presheafValue_pairOfDefinition_concrete P D₀).A₀))
    (hA_complete_B : @CompleteSpace (presheafValue D₀)
      (IsTopologicalAddGroup.rightUniformSpace (presheafValue D₀)))
    (hnoeth_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      IsNoetherianRing ↥(TateAlgebra.pairSubring
        (IsTateRing.principalPair (presheafValue D₀)).toPairOfDefinition))
    (hcont_forward_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      letI : HasLocLiftPowerBounded (presheafValue D₀) := hLocLift_B
      letI : IsNoetherianRing (presheafValue D₀) := hNoeth_B
      letI P_B : PairOfDefinition (presheafValue D₀) :=
        presheafValue_pairOfDefinition_concrete P D₀
      letI : IsNoetherianRing ↥P_B.A₀ := hA₀Noeth_B
      @Continuous _ _
        (quotientPlusFSubXIdealTopology (presheafValue D₀) (D₀.canonicalMap f))
        (inferInstance : TopologicalSpace (presheafValue
          (trivialPlusDatum (presheafValue D₀) P_B (D₀.canonicalMap f))))
        (example638Plus_forwardHom (presheafValue D₀) P_B (D₀.canonicalMap f))) :
    presheafValue (iteratedPlusDatum_B P D₀ f) ≃+*
      LaurentCover.B₁_gen (D₀.canonicalMap f) := by
  haveI : IsTateRing (presheafValue D₀) := presheafValue_isTateRing P D₀
  haveI : HasLocLiftPowerBounded (presheafValue D₀) := hLocLift_B
  haveI : IsNoetherianRing (presheafValue D₀) := hNoeth_B
  letI P_B : PairOfDefinition (presheafValue D₀) :=
    presheafValue_pairOfDefinition_concrete P D₀
  haveI : IsNoetherianRing ↥P_B.A₀ := hA₀Noeth_B
  -- `iteratedPlusDatum_B P D₀ f = trivialPlusDatum (presheafValue D₀) P_B (canonicalMap f)`
  -- definitionally (same P, T = {canonicalMap f}, s = 1, hopen = hopen_away_one _ _).
  -- `B₁_gen (canonicalMap f) = TateAlgebra (presheafValue D₀) ⧸ plusFSubXIdeal _ _`
  -- definitionally (same quotient ideal structure).
  -- Use `.symm` of `example638Plus_equiv` at B := presheafValue D₀, b := canonicalMap f.
  exact (example638Plus_equiv (presheafValue D₀) P_B (D₀.canonicalMap f)
    hA_complete_B hnoeth_B hcont_forward_B).symm

/-- **Route B bridge (plus)** (Wedhorn Lemma 8.33 support):
`presheafValue (laurentPlusDatum D₀ f) ≃+* B₁_gen (D₀.canonicalMap f)`,
where `B₁_gen f' = (presheafValue D₀)⟨X⟩ ⧸ (f' - X)`.

Proof route: compose `presheafValue_iteratedPlus_equiv` (Wedhorn 2.13, iterated
rational identification with `B := presheafValue D₀`) with a non-discrete
`f − X` quotient equivalence over the generic Tate base `B`
(Q3-STEP2D, the one genuinely new primitive flagged by the reviewer).

The six plus-branch hypotheses (`hNoeth_B`, `hLocLift_B`, `hA₀Noeth_B`,
`hA_complete_B`, `hnoeth_B`, `hcont_forward_B`) propagate from
`presheafValue_trivialPlus_fSubX_equiv` — they are all about the generic base
`B := presheafValue D₀` rather than about `A`. -/
noncomputable def laurentPlusBridge
    [IsTateRing A] [IsNoetherianRing A] [T2Space A]
    [NonarchimedeanRing A]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (D₀ : RationalLocData A) [IsNoetherianRing (locSubring D₀.P D₀.T D₀.s)]
    [LaurentNormalized D₀]
    (f : A)
    (hNoeth_B : IsNoetherianRing (presheafValue D₀))
    (hLocLift_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      HasLocLiftPowerBounded (presheafValue D₀))
    (hA₀Noeth_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      letI : IsNoetherianRing (presheafValue D₀) := hNoeth_B
      IsNoetherianRing ↥((presheafValue_pairOfDefinition_concrete P D₀).A₀))
    (hA_complete_B : @CompleteSpace (presheafValue D₀)
      (IsTopologicalAddGroup.rightUniformSpace (presheafValue D₀)))
    (hnoeth_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      IsNoetherianRing ↥(TateAlgebra.pairSubring
        (IsTateRing.principalPair (presheafValue D₀)).toPairOfDefinition))
    (hcont_forward_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      letI : HasLocLiftPowerBounded (presheafValue D₀) := hLocLift_B
      letI : IsNoetherianRing (presheafValue D₀) := hNoeth_B
      letI P_B : PairOfDefinition (presheafValue D₀) :=
        presheafValue_pairOfDefinition_concrete P D₀
      letI : IsNoetherianRing ↥P_B.A₀ := hA₀Noeth_B
      @Continuous _ _
        (quotientPlusFSubXIdealTopology (presheafValue D₀) (D₀.canonicalMap f))
        (inferInstance : TopologicalSpace (presheafValue
          (trivialPlusDatum (presheafValue D₀) P_B (D₀.canonicalMap f))))
        (example638Plus_forwardHom (presheafValue D₀) P_B (D₀.canonicalMap f))) :
    presheafValue (laurentPlusDatum D₀ f) ≃+*
      LaurentCover.B₁_gen (D₀.canonicalMap f) :=
  (presheafValue_iteratedPlus_equiv P D₀ f).trans
    (presheafValue_trivialPlus_fSubX_equiv P D₀ f
      hNoeth_B hLocLift_B hA₀Noeth_B hA_complete_B hnoeth_B hcont_forward_B)

/-- **Route B bridge (minus)** (Wedhorn Lemma 8.33 support):
`presheafValue (laurentMinusDatum D₀ f) ≃+* B₂_gen (D₀.canonicalMap f)`,
where `B₂_gen f' = (presheafValue D₀)⟨X⟩ ⧸ (1 - f' · X)`.

Proof route (composition): `presheafValue_iteratedMinus_equiv` (Wedhorn 2.13,
iterated rational identification) composed with
`presheafValueCanonicalQuotientEquiv` at `A := presheafValue D₀`,
`D := iteratedMinusDatum_B P D₀ f` (whose `s` is `canonicalMap f`, so the
quotient equiv yields `B⟨X⟩ / (1 − canonicalMap(f) · X) = B₂_gen (canonicalMap f)`
directly — by definition `oneSubfXIdeal (canonicalMap f) =
Ideal.span {1 − algebraMap B _ (canonicalMap f) · X}`).

**Hypothesis design.** Following the `example638Minus_equiv` pattern in
`IteratedRational.lean`, we expose the two residual structural hypotheses
as explicit arguments (rather than burying them as `sorry`):
* `hnoeth_B` : `IsNoetherianRing ↥(TateAlgebra.pairSubring
  (IsTateRing.principalPair (presheafValue D₀)).toPairOfDefinition)`.
  The "rational localizations preserve strongly noetherian" direction of
  Wedhorn Theorem 7.47 / Example 6.38. Not yet in project infrastructure.
* `hcont_eval_B` : canonical-quotient-to-presheafValue continuity of
  `tateQuotientToPresheafHom (iteratedMinusDatum_B P D₀ f) hb` at
  `B := presheafValue D₀`. This is the Phase 2.6 continuity residual
  transported to the rational localization.

The three "automatic" hypotheses (`hb`, `hT_pb`, `hA_complete`) are
discharged in place: `T = {1}` so `hT_pb` reduces to `IsPowerBounded 1`;
`hb` follows from `invS_isPowerBounded_of_one_mem_T` since `1 ∈ T`;
`hA_complete` is `IsUniformAddGroup.rightUniformSpace_eq` + completion
completeness. -/
noncomputable def laurentMinusBridge
    [IsTateRing A] [IsNoetherianRing A] [T2Space A]
    [NonarchimedeanRing A]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (D₀ : RationalLocData A) [IsNoetherianRing (locSubring D₀.P D₀.T D₀.s)]
    [LaurentNormalized D₀]
    (f : A)
    (hnoeth_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      IsNoetherianRing ↥(TateAlgebra.pairSubring
        (IsTateRing.principalPair (presheafValue D₀)).toPairOfDefinition))
    (hcont_eval_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      let D : RationalLocData (presheafValue D₀) := iteratedMinusDatum_B P D₀ f
      ∀ hb : TopologicalRing.IsPowerBounded (invS D),
        @Continuous _ _
          (TateAlgebra.quotientOneSubfXIdealTopology D.s)
          (inferInstance : TopologicalSpace (presheafValue D))
          (tateQuotientToPresheafHom D hb)) :
    presheafValue (laurentMinusDatum D₀ f) ≃+*
      LaurentCover.B₂_gen (D₀.canonicalMap f) := by
  haveI : IsTateRing (presheafValue D₀) := presheafValue_isTateRing P D₀
  -- Step 1: iterated rational identification (Wedhorn Lemma 2.13).
  refine (presheafValue_iteratedMinus_equiv P D₀ f).trans ?_
  -- Step 2: Phase 2 canonical-topology iso at B := presheafValue D₀ applied to
  -- `iteratedMinusDatum_B`, whose `s` is `D₀.canonicalMap f`. The quotient target
  -- `TateAlgebra B ⧸ oneSubfXIdeal (canonicalMap f)` equals `B₂_gen (canonicalMap f)`
  -- definitionally.
  -- `hb`: invS is power-bounded because `1 ∈ T = {1}` for `iteratedMinusDatum_B`.
  -- This requires rewriting `invS = coeRingHom (divByS 1 s)`, which in turn uses
  -- that `canonicalMap s * invS = 1` and the cancellation property.
  have hinvS_eq : invS (iteratedMinusDatum_B P D₀ f) =
      (iteratedMinusDatum_B P D₀ f).coeRingHom
        (divByS 1 (iteratedMinusDatum_B P D₀ f).s) := by
    set D : RationalLocData (presheafValue D₀) := iteratedMinusDatum_B P D₀ f
    have h1 : D.canonicalMap D.s * invS D = 1 := canonicalMap_s_mul_invS D
    have halg : algebraMap (presheafValue D₀) (Localization.Away D.s) D.s *
        divByS 1 D.s = 1 := by
      rw [← invSelf_eq_divByS, IsLocalization.Away.mul_invSelf]
    have h2 : D.canonicalMap D.s * D.coeRingHom (divByS 1 D.s) = 1 := by
      show D.coeRingHom (algebraMap (presheafValue D₀) (Localization.Away D.s) D.s) *
        D.coeRingHom (divByS 1 D.s) = 1
      rw [← map_mul, halg, map_one]
    have hu : IsUnit (D.canonicalMap D.s) := isUnit_s_in_presheafValue D
    exact hu.mul_left_cancel (h1.trans h2.symm)
  have hb : TopologicalRing.IsPowerBounded
      (invS (iteratedMinusDatum_B P D₀ f)) := by
    rw [hinvS_eq]
    exact CompletionLocalization.invS_isPowerBounded_of_one_mem_T
      (iteratedMinusDatum_B P D₀ f) (Finset.mem_singleton_self 1)
  -- `hT_pb`: T = {1}, so this reduces to `IsPowerBounded 1`.
  have hT_pb : ∀ t ∈ (iteratedMinusDatum_B P D₀ f).T,
      TopologicalRing.IsPowerBounded t := by
    intro t ht
    rw [Finset.mem_singleton.mp ht]
    exact TopologicalRing.isPowerBounded_one
  -- `hA_complete`: `presheafValue D₀` is complete via the completion's uniform
  -- structure, which agrees with the rightUniformSpace by
  -- `IsUniformAddGroup.rightUniformSpace_eq`.
  have hA_complete : @CompleteSpace (presheafValue D₀)
      (IsTopologicalAddGroup.rightUniformSpace (presheafValue D₀)) := by
    rw [IsUniformAddGroup.rightUniformSpace_eq]
    infer_instance
  -- `hnoeth_B` and `hcont_eval_B` are supplied by the caller.
  exact presheafValueCanonicalQuotientEquiv (iteratedMinusDatum_B P D₀ f)
    (hb := hb)
    (hA_complete := hA_complete)
    (hnoeth := hnoeth_B)
    (hT_pb := hT_pb)
    (hcont_eval := hcont_eval_B hb)

/-- **Compatibility of `presheafValue_iteratedPlus_equiv` with `canonicalMap`.**

`presheafValue_iteratedPlus_equiv` identifies the two presheaf values in a way
that respects the canonical maps from `A` (via the tower
`A → presheafValue D₀ → presheafValue (iteratedPlusDatum_B P D₀ f)`, which
matches `A → presheafValue (laurentPlusDatum D₀ f)` under the identification).

**Proof.** Via `Completion.ext'` on `x : presheafValue D₀` reduce to the
dense subset `x = D₀.coeRingHom a`, then via `IsLocalization.ringHom_ext`
reduce to `a = algebraMap A _ b`, and finish by unfolding the forward and
canonical maps. Parallel to the minus-branch closure. -/
theorem presheafValue_iteratedPlus_equiv_restrictionMap_canonicalMap
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (D₀ : RationalLocData A)
    [IsNoetherianRing (locSubring D₀.P D₀.T D₀.s)]
    [LaurentNormalized D₀]
    (f : A)
    (hplus : rationalOpen (laurentPlusDatum D₀ f).T (laurentPlusDatum D₀ f).s ⊆
      rationalOpen D₀.T D₀.s) (x : presheafValue D₀) :
    presheafValue_iteratedPlus_equiv P D₀ f
        (restrictionMap D₀ (laurentPlusDatum D₀ f) hplus x) =
      (iteratedPlusDatum_B P D₀ f).canonicalMap x := by
  -- Mirror of the minus-branch proof. Reduce via `Completion.ext'` on
  -- `x : presheafValue D₀` to the dense subset `x = D₀.coeRingHom a`, then
  -- via `IsLocalization.ringHom_ext` to `a = algebraMap A _ b`.
  letI : UniformSpace (Localization.Away D₀.s) := D₀.uniformSpace
  letI : IsUniformAddGroup (Localization.Away D₀.s) := D₀.isUniformAddGroup
  letI : IsTopologicalRing (Localization.Away D₀.s) := D₀.isTopologicalRing
  letI : UniformSpace (Localization.Away (laurentPlusDatum D₀ f).s) :=
    (laurentPlusDatum D₀ f).uniformSpace
  letI : IsUniformAddGroup (Localization.Away (laurentPlusDatum D₀ f).s) :=
    (laurentPlusDatum D₀ f).isUniformAddGroup
  letI : IsTopologicalRing (Localization.Away (laurentPlusDatum D₀ f).s) :=
    (laurentPlusDatum D₀ f).isTopologicalRing
  letI : UniformSpace (Localization.Away (iteratedPlusDatum_B P D₀ f).s) :=
    (iteratedPlusDatum_B P D₀ f).uniformSpace
  letI : IsUniformAddGroup (Localization.Away (iteratedPlusDatum_B P D₀ f).s) :=
    (iteratedPlusDatum_B P D₀ f).isUniformAddGroup
  letI : IsTopologicalRing (Localization.Away (iteratedPlusDatum_B P D₀ f).s) :=
    (iteratedPlusDatum_B P D₀ f).isTopologicalRing
  let lhsFun : presheafValue D₀ → presheafValue (iteratedPlusDatum_B P D₀ f) :=
    fun y => presheafValue_iteratedPlus_equiv P D₀ f
      (restrictionMap D₀ (laurentPlusDatum D₀ f) hplus y)
  let rhsFun : presheafValue D₀ → presheafValue (iteratedPlusDatum_B P D₀ f) :=
    fun y => (iteratedPlusDatum_B P D₀ f).canonicalMap y
  change lhsFun x = rhsFun x
  refine @UniformSpace.Completion.ext' (Localization.Away D₀.s) D₀.uniformSpace
    (presheafValue (iteratedPlusDatum_B P D₀ f)) _ _ lhsFun rhsFun ?_ ?_ ?_ x
  · -- LHS continuity: `equiv ∘ restrictionMap`.
    show Continuous (fun y : presheafValue D₀ =>
      presheafValue_iteratedPlus_equiv P D₀ f
        (restrictionMap D₀ (laurentPlusDatum D₀ f) hplus y))
    change Continuous (fun y : presheafValue D₀ =>
      iteratedPlus_forwardHom P D₀ f (restrictionMapHom D₀ (laurentPlusDatum D₀ f) hplus y))
    exact UniformSpace.Completion.continuous_extension.comp
      (restrictionMapHom_continuous D₀ (laurentPlusDatum D₀ f) hplus)
  · -- RHS continuity: `canonicalMap` of `iteratedPlusDatum_B`.
    exact canonicalMap_continuous (iteratedPlusDatum_B P D₀ f)
  -- Inductive step on `a : Localization.Away D₀.s`.
  intro a
  show lhsFun (D₀.coeRingHom a) = rhsFun (D₀.coeRingHom a)
  simp only [lhsFun, rhsFun]
  let lhsHom : Localization.Away D₀.s →+*
      presheafValue (iteratedPlusDatum_B P D₀ f) :=
    (iteratedPlus_forwardHom P D₀ f).comp
      ((restrictionMapHom D₀ (laurentPlusDatum D₀ f) hplus).comp D₀.coeRingHom)
  let rhsHom : Localization.Away D₀.s →+*
      presheafValue (iteratedPlusDatum_B P D₀ f) :=
    ((iteratedPlusDatum_B P D₀ f).canonicalMap).comp D₀.coeRingHom
  suffices h : lhsHom = rhsHom by
    have := congr_fun (congrArg DFunLike.coe h) a
    show lhsHom a = rhsHom a
    exact this
  apply IsLocalization.ringHom_ext (Submonoid.powers D₀.s)
  ext b
  show lhsHom (algebraMap A _ b) = rhsHom (algebraMap A _ b)
  show iteratedPlus_forwardHom P D₀ f
      (restrictionMapHom D₀ (laurentPlusDatum D₀ f) hplus
        (D₀.coeRingHom (algebraMap A _ b))) =
    (iteratedPlusDatum_B P D₀ f).canonicalMap (D₀.coeRingHom (algebraMap A _ b))
  -- `D₀.coeRingHom (algebraMap A _ b) = D₀.canonicalMap b` by def.
  show iteratedPlus_forwardHom P D₀ f
      (restrictionMapHom D₀ (laurentPlusDatum D₀ f) hplus (D₀.canonicalMap b)) =
    (iteratedPlusDatum_B P D₀ f).canonicalMap (D₀.canonicalMap b)
  rw [restrictionMapHom_canonicalMap]
  -- Now: forwardHom ((laurentPlus).canonicalMap b) = (iteratedPlusDatum_B).canonicalMap (D₀.canonicalMap b)
  show iteratedPlus_forwardHom P D₀ f
      ((laurentPlusDatum D₀ f).coeRingHom (algebraMap A _ b)) =
    (iteratedPlusDatum_B P D₀ f).canonicalMap (D₀.canonicalMap b)
  rw [iteratedPlus_forwardHom_coeRingHom]
  show (iteratedPlusDatum_B P D₀ f).coeRingHom
      (iteratedPlus_forwardLocHom D₀ (algebraMap A _ b)) =
    (iteratedPlusDatum_B P D₀ f).canonicalMap (D₀.canonicalMap b)
  rw [iteratedPlus_forwardLocHom_algebraMap]
  -- Goal: coeRingHom_B (algebraMap_B (D₀.canonicalMap b)) = (iteratedPlusDatum_B).canonicalMap (D₀.canonicalMap b)
  -- Both are `(iteratedPlusDatum_B).coeRingHom.comp algebraMap B _` applied to
  -- `D₀.canonicalMap b`, i.e., `(iteratedPlusDatum_B).canonicalMap (D₀.canonicalMap b)` by def.
  rfl

/-- **Route B bridge (plus compatibility)**: the plus bridge intertwines
`restrictionMap` and the first projection of `epsilonHom_gen`.

Proof structure: `laurentPlusBridge` is `(presheafValue_iteratedPlus_equiv).trans
(presheafValue_trivialPlus_fSubX_equiv ...)`. The second factor is
`(example638Plus_equiv ...).symm`, which maps
`(iteratedPlusDatum_B P D₀ f).canonicalMap x ↦ mk(algebraMap x)` by
`example638Plus_equiv_symm_canonicalMap` (via the definitional equality
`iteratedPlusDatum_B = trivialPlusDatum`). The first factor's action on
`restrictionMap ... x` is the content of
`presheafValue_iteratedPlus_equiv_restrictionMap_canonicalMap` (proved via
`Completion.ext'` and `IsLocalization.ringHom_ext`; parallel to the
minus-branch sub-sorry closure).

The theorem reduces by direct computation. -/
theorem laurentPlusBridge_restrictionMap
    [IsTateRing A] [IsNoetherianRing A] [T2Space A]
    [NonarchimedeanRing A]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (D₀ : RationalLocData A) [IsNoetherianRing (locSubring D₀.P D₀.T D₀.s)]
    [LaurentNormalized D₀]
    (f : A)
    (hNoeth_B : IsNoetherianRing (presheafValue D₀))
    (hLocLift_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      HasLocLiftPowerBounded (presheafValue D₀))
    (hA₀Noeth_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      letI : IsNoetherianRing (presheafValue D₀) := hNoeth_B
      IsNoetherianRing ↥((presheafValue_pairOfDefinition_concrete P D₀).A₀))
    (hA_complete_B : @CompleteSpace (presheafValue D₀)
      (IsTopologicalAddGroup.rightUniformSpace (presheafValue D₀)))
    (hnoeth_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      IsNoetherianRing ↥(TateAlgebra.pairSubring
        (IsTateRing.principalPair (presheafValue D₀)).toPairOfDefinition))
    (hcont_forward_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      letI : HasLocLiftPowerBounded (presheafValue D₀) := hLocLift_B
      letI : IsNoetherianRing (presheafValue D₀) := hNoeth_B
      letI P_B : PairOfDefinition (presheafValue D₀) :=
        presheafValue_pairOfDefinition_concrete P D₀
      letI : IsNoetherianRing ↥P_B.A₀ := hA₀Noeth_B
      @Continuous _ _
        (quotientPlusFSubXIdealTopology (presheafValue D₀) (D₀.canonicalMap f))
        (inferInstance : TopologicalSpace (presheafValue
          (trivialPlusDatum (presheafValue D₀) P_B (D₀.canonicalMap f))))
        (example638Plus_forwardHom (presheafValue D₀) P_B (D₀.canonicalMap f)))
    (hplus : rationalOpen (laurentPlusDatum D₀ f).T (laurentPlusDatum D₀ f).s ⊆
      rationalOpen D₀.T D₀.s) :
    ∀ x : presheafValue D₀,
      laurentPlusBridge P D₀ f hNoeth_B hLocLift_B hA₀Noeth_B hA_complete_B
          hnoeth_B hcont_forward_B
        (restrictionMap D₀ (laurentPlusDatum D₀ f) hplus x) =
        (LaurentCover.epsilonHom_gen (D₀.canonicalMap f) x).1 := by
  intro x
  haveI : IsTateRing (presheafValue D₀) := presheafValue_isTateRing P D₀
  haveI : HasLocLiftPowerBounded (presheafValue D₀) := hLocLift_B
  haveI : IsNoetherianRing (presheafValue D₀) := hNoeth_B
  letI P_B : PairOfDefinition (presheafValue D₀) :=
    presheafValue_pairOfDefinition_concrete P D₀
  haveI : IsNoetherianRing ↥P_B.A₀ := hA₀Noeth_B
  -- Step 1: Reduce via the `trans` structure of `laurentPlusBridge`.
  -- `laurentPlusBridge = (presheafValue_iteratedPlus_equiv).trans
  --   (presheafValue_trivialPlus_fSubX_equiv ...)`, so applying it amounts to
  -- applying the trivial-plus `fSubX` equiv to the iterated equiv image.
  -- Step 2: Use the sub-sorry to rewrite the iterated equiv's output as
  -- `(iteratedPlusDatum_B P D₀ f).canonicalMap x`.
  have hstep :
      presheafValue_iteratedPlus_equiv P D₀ f
          (restrictionMap D₀ (laurentPlusDatum D₀ f) hplus x) =
        (iteratedPlusDatum_B P D₀ f).canonicalMap x :=
    presheafValue_iteratedPlus_equiv_restrictionMap_canonicalMap P D₀ f hplus x
  -- Step 3: Unfold `laurentPlusBridge` as a `trans` composition.
  change (presheafValue_trivialPlus_fSubX_equiv P D₀ f hNoeth_B hLocLift_B
      hA₀Noeth_B hA_complete_B hnoeth_B hcont_forward_B)
    ((presheafValue_iteratedPlus_equiv P D₀ f)
      (restrictionMap D₀ (laurentPlusDatum D₀ f) hplus x)) = _
  rw [hstep]
  -- Step 4: `presheafValue_trivialPlus_fSubX_equiv = (example638Plus_equiv _).symm`,
  -- and `iteratedPlusDatum_B P D₀ f = trivialPlusDatum (presheafValue D₀) P_B
  -- (D₀.canonicalMap f)` definitionally. So apply `example638Plus_equiv_symm_canonicalMap`.
  -- The RHS `(epsilonHom_gen (canonicalMap f) x).1` is `mk(algebraMap x)` in
  -- `B₁_gen = TateAlgebra B ⧸ plusFSubXIdeal B (canonicalMap f)` definitionally.
  unfold presheafValue_trivialPlus_fSubX_equiv
  exact example638Plus_equiv_symm_canonicalMap (presheafValue D₀) P_B (D₀.canonicalMap f)
    hA_complete_B hnoeth_B hcont_forward_B x

/-- **Sub-sorry: compatibility of `presheafValue_iteratedMinus_equiv` with
`canonicalMap`.**

This is the single residual fact blocking `laurentMinusBridge_restrictionMap`.
Morally, `presheafValue_iteratedMinus_equiv` identifies the two presheaf values
in a way that respects the canonical maps from `A` (via the tower
`A → presheafValue D₀ → presheafValue (iteratedMinusDatum_B P D₀ f)`, which
matches `A → presheafValue (laurentMinusDatum D₀ f)` under the identification).

Currently `presheafValue_iteratedMinus_equiv` is itself a sorry'd `noncomputable
def`; once it is defined concretely, this compatibility will be a straightforward
consequence of the definition. We expose it as a separate sub-sorry so that
`laurentMinusBridge_restrictionMap` can be proved modulo this precise claim. -/
theorem presheafValue_iteratedMinus_equiv_restrictionMap_canonicalMap
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (D₀ : RationalLocData A)
    [IsNoetherianRing (locSubring D₀.P D₀.T D₀.s)]
    [LaurentNormalized D₀]
    (f : A)
    (hminus : rationalOpen (laurentMinusDatum D₀ f).T (laurentMinusDatum D₀ f).s ⊆
      rationalOpen D₀.T D₀.s) (x : presheafValue D₀) :
    presheafValue_iteratedMinus_equiv P D₀ f
        (restrictionMap D₀ (laurentMinusDatum D₀ f) hminus x) =
      (iteratedMinusDatum_B P D₀ f).canonicalMap x := by
  -- Reduce via `presheafValue_iteratedMinus_equiv_apply` to a direct `iteratedMinus_forwardHom`
  -- statement, then apply the core identity `iteratedMinus_forwardHom_comp_restrictionMapHom`.
  rw [presheafValue_iteratedMinus_equiv_apply]
  show iteratedMinus_forwardHom P D₀ f
      (restrictionMapHom D₀ (laurentMinusDatum D₀ f) hminus x) =
    (iteratedMinusDatum_B P D₀ f).canonicalMap x
  exact congr_fun (congrArg DFunLike.coe
    (iteratedMinus_forwardHom_comp_restrictionMapHom P D₀ f hminus)) x

/-- **Route B bridge (minus compatibility)**: the minus bridge intertwines
`restrictionMap` and the second projection of `epsilonHom_gen`.

Proof structure: `laurentMinusBridge` is `(presheafValue_iteratedMinus_equiv).trans
(presheafValueCanonicalQuotientEquiv ...)`. The second factor maps
`(iteratedMinusDatum_B P D₀ f).canonicalMap x ↦ mk(algebraMap x)` by
`presheafValueCanonicalQuotientEquiv_canonicalMap`. The first factor's action on
`restrictionMap ... x` is the content of
`presheafValue_iteratedMinus_equiv_restrictionMap_canonicalMap` (currently a
sub-sorry; it is the single residual fact blocking a full proof).

Modulo that sub-sorry, the theorem reduces by direct computation. -/
theorem laurentMinusBridge_restrictionMap
    [IsTateRing A] [IsNoetherianRing A] [T2Space A]
    [NonarchimedeanRing A]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (D₀ : RationalLocData A) [IsNoetherianRing (locSubring D₀.P D₀.T D₀.s)]
    [LaurentNormalized D₀]
    (f : A)
    (hnoeth_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      IsNoetherianRing ↥(TateAlgebra.pairSubring
        (IsTateRing.principalPair (presheafValue D₀)).toPairOfDefinition))
    (hcont_eval_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      let D : RationalLocData (presheafValue D₀) := iteratedMinusDatum_B P D₀ f
      ∀ hb : TopologicalRing.IsPowerBounded (invS D),
        @Continuous _ _
          (TateAlgebra.quotientOneSubfXIdealTopology D.s)
          (inferInstance : TopologicalSpace (presheafValue D))
          (tateQuotientToPresheafHom D hb))
    (hminus : rationalOpen (laurentMinusDatum D₀ f).T (laurentMinusDatum D₀ f).s ⊆
      rationalOpen D₀.T D₀.s) :
    ∀ x : presheafValue D₀,
      laurentMinusBridge P D₀ f hnoeth_B hcont_eval_B
        (restrictionMap D₀ (laurentMinusDatum D₀ f) hminus x) =
        (LaurentCover.epsilonHom_gen (D₀.canonicalMap f) x).2 := by
  intro x
  haveI : IsTateRing (presheafValue D₀) := presheafValue_isTateRing P D₀
  -- Step 1: Reduce via the `trans` structure of `laurentMinusBridge`.
  -- `laurentMinusBridge = (presheafValue_iteratedMinus_equiv).trans
  --   (presheafValueCanonicalQuotientEquiv ...)`, so applying it amounts to
  -- applying the canonical quotient equiv to the iterated equiv image.
  -- Step 2: Use the sub-sorry to rewrite the iterated equiv's output as
  -- `(iteratedMinusDatum_B P D₀ f).canonicalMap x`.
  have hstep :
      presheafValue_iteratedMinus_equiv P D₀ f
          (restrictionMap D₀ (laurentMinusDatum D₀ f) hminus x) =
        (iteratedMinusDatum_B P D₀ f).canonicalMap x :=
    presheafValue_iteratedMinus_equiv_restrictionMap_canonicalMap P D₀ f hminus x
  -- Step 3: Unfold `laurentMinusBridge` and apply the canonical quotient equiv.
  -- The inner `have hb`, `have hT_pb`, `have hA_complete` in the bridge
  -- definition are internal; we recompute them here.
  have hinvS_eq : invS (iteratedMinusDatum_B P D₀ f) =
      (iteratedMinusDatum_B P D₀ f).coeRingHom
        (divByS 1 (iteratedMinusDatum_B P D₀ f).s) := by
    set D : RationalLocData (presheafValue D₀) := iteratedMinusDatum_B P D₀ f
    have h1 : D.canonicalMap D.s * invS D = 1 := canonicalMap_s_mul_invS D
    have halg : algebraMap (presheafValue D₀) (Localization.Away D.s) D.s *
        divByS 1 D.s = 1 := by
      rw [← invSelf_eq_divByS, IsLocalization.Away.mul_invSelf]
    have h2 : D.canonicalMap D.s * D.coeRingHom (divByS 1 D.s) = 1 := by
      show D.coeRingHom (algebraMap (presheafValue D₀) (Localization.Away D.s) D.s) *
        D.coeRingHom (divByS 1 D.s) = 1
      rw [← map_mul, halg, map_one]
    have hu : IsUnit (D.canonicalMap D.s) := isUnit_s_in_presheafValue D
    exact hu.mul_left_cancel (h1.trans h2.symm)
  have hb : TopologicalRing.IsPowerBounded
      (invS (iteratedMinusDatum_B P D₀ f)) := by
    rw [hinvS_eq]
    exact CompletionLocalization.invS_isPowerBounded_of_one_mem_T
      (iteratedMinusDatum_B P D₀ f) (Finset.mem_singleton_self 1)
  have hT_pb : ∀ t ∈ (iteratedMinusDatum_B P D₀ f).T,
      TopologicalRing.IsPowerBounded t := by
    intro t ht
    rw [Finset.mem_singleton.mp ht]
    exact TopologicalRing.isPowerBounded_one
  have hA_complete : @CompleteSpace (presheafValue D₀)
      (IsTopologicalAddGroup.rightUniformSpace (presheafValue D₀)) := by
    rw [IsUniformAddGroup.rightUniformSpace_eq]
    infer_instance
  -- Compute the bridge as the composition of the two equivs.
  change (presheafValueCanonicalQuotientEquiv (iteratedMinusDatum_B P D₀ f)
      (hb := hb) (hA_complete := hA_complete) (hnoeth := hnoeth_B)
      (hT_pb := hT_pb) (hcont_eval := hcont_eval_B hb))
    ((presheafValue_iteratedMinus_equiv P D₀ f)
      (restrictionMap D₀ (laurentMinusDatum D₀ f) hminus x)) = _
  rw [hstep]
  rw [presheafValueCanonicalQuotientEquiv_canonicalMap (iteratedMinusDatum_B P D₀ f)
    hb hA_complete hnoeth_B hT_pb (hcont_eval_B hb) x]
  -- `(epsilonHom_gen (canonicalMap f) x).2 = mk(algebraMap x)` by definition.
  rfl

/-! #### Bridge IsInducing consumers (T147)

`laurentPlusBridge_isInducing` and `laurentMinusBridge_isInducing` compose
the iterated rational identification IsInducing facts (T146) with the
canonical-quotient IsInducing facts at the leaf (T142 minus, T145 plus).
They discharge the historic `hτ_plus_inducing` / `hτ_minus_inducing`
hypotheses of T141's `laurentCover_isEmbedding_presheaf_of_complete`. -/

/-- **T147 plus: `laurentPlusBridge` is `Topology.IsInducing`.**

Compose T146's `presheafValue_iteratedPlus_equiv_isInducing` (no extra
hypotheses) with T145's `example638Plus_equiv_symm_isInducing`. The
T145 step requires explicit Baire / sigma-compact discharge at the
trivial-plus presheafValue / quotient layer. The `hDom_B` hypothesis
is needed only to discharge the `LaurentCover.B₁_gen` topology
instance, which lives in a `[IsDomain A]`-section of
`LaurentCoverTopology.lean` (carried over from the historical
section structure even though the topology itself does not require
domain-ness). -/
theorem laurentPlusBridge_isInducing
    [IsTateRing A] [IsNoetherianRing A] [T2Space A]
    [NonarchimedeanRing A]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (D₀ : RationalLocData A) [IsNoetherianRing (locSubring D₀.P D₀.T D₀.s)]
    [LaurentNormalized D₀]
    (f : A)
    (hNoeth_B : IsNoetherianRing (presheafValue D₀))
    (hDom_B : IsDomain (presheafValue D₀))
    (hLocLift_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      HasLocLiftPowerBounded (presheafValue D₀))
    (hA₀Noeth_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      letI : IsNoetherianRing (presheafValue D₀) := hNoeth_B
      IsNoetherianRing ↥((presheafValue_pairOfDefinition_concrete P D₀).A₀))
    (hA_complete_B : @CompleteSpace (presheafValue D₀)
      (IsTopologicalAddGroup.rightUniformSpace (presheafValue D₀)))
    (hnoeth_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      IsNoetherianRing ↥(TateAlgebra.pairSubring
        (IsTateRing.principalPair (presheafValue D₀)).toPairOfDefinition))
    (hcont_forward_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      letI : HasLocLiftPowerBounded (presheafValue D₀) := hLocLift_B
      letI : IsNoetherianRing (presheafValue D₀) := hNoeth_B
      letI P_B : PairOfDefinition (presheafValue D₀) :=
        presheafValue_pairOfDefinition_concrete P D₀
      letI : IsNoetherianRing ↥P_B.A₀ := hA₀Noeth_B
      @Continuous _ _
        (quotientPlusFSubXIdealTopology (presheafValue D₀) (D₀.canonicalMap f))
        (inferInstance : TopologicalSpace (presheafValue
          (trivialPlusDatum (presheafValue D₀) P_B (D₀.canonicalMap f))))
        (example638Plus_forwardHom (presheafValue D₀) P_B (D₀.canonicalMap f)))
    (hBaire_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      letI : IsNoetherianRing (presheafValue D₀) := hNoeth_B
      letI : HasLocLiftPowerBounded (presheafValue D₀) := hLocLift_B
      letI P_B : PairOfDefinition (presheafValue D₀) :=
        presheafValue_pairOfDefinition_concrete P D₀
      @BaireSpace
        (presheafValue
          (trivialPlusDatum (presheafValue D₀) P_B (D₀.canonicalMap f))) _)
    (hSigma_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      @SigmaCompactSpace
        (↥(TateAlgebra (presheafValue D₀)) ⧸
          plusFSubXIdeal (presheafValue D₀) (D₀.canonicalMap f))
        (quotientPlusFSubXIdealTopology (presheafValue D₀)
          (D₀.canonicalMap f))) :
    letI : IsTateRing (presheafValue D₀) := presheafValue_isTateRing P D₀
    letI : IsNoetherianRing (presheafValue D₀) := hNoeth_B
    letI : IsDomain (presheafValue D₀) := hDom_B
    Topology.IsInducing
      ((laurentPlusBridge P D₀ f hNoeth_B hLocLift_B hA₀Noeth_B hA_complete_B
          hnoeth_B hcont_forward_B) :
        presheafValue (laurentPlusDatum D₀ f) →
          LaurentCover.B₁_gen (D₀.canonicalMap f)) := by
  haveI : IsTateRing (presheafValue D₀) := presheafValue_isTateRing P D₀
  haveI : HasLocLiftPowerBounded (presheafValue D₀) := hLocLift_B
  haveI : IsNoetherianRing (presheafValue D₀) := hNoeth_B
  haveI : IsDomain (presheafValue D₀) := hDom_B
  letI P_B : PairOfDefinition (presheafValue D₀) :=
    presheafValue_pairOfDefinition_concrete P D₀
  haveI : IsNoetherianRing ↥P_B.A₀ := hA₀Noeth_B
  -- T146 plus equiv inducing.
  have h₁ : Topology.IsInducing
      ((presheafValue_iteratedPlus_equiv P D₀ f) :
        presheafValue (laurentPlusDatum D₀ f) →
          presheafValue (iteratedPlusDatum_B P D₀ f)) :=
    presheafValue_iteratedPlus_equiv_isInducing P D₀ f
  -- T145 example638Plus symm inducing.
  have h₂ : Topology.IsInducing
      ((example638Plus_equiv (presheafValue D₀) P_B (D₀.canonicalMap f)
          hA_complete_B hnoeth_B hcont_forward_B).symm :
        presheafValue
            (trivialPlusDatum (presheafValue D₀) P_B (D₀.canonicalMap f)) →
          ↥(TateAlgebra (presheafValue D₀)) ⧸
            plusFSubXIdeal (presheafValue D₀) (D₀.canonicalMap f)) :=
    example638Plus_equiv_symm_isInducing (presheafValue D₀) P_B
      (D₀.canonicalMap f) hA_complete_B hnoeth_B hcont_forward_B hBaire_B hSigma_B
  -- The bridge `laurentPlusBridge ...` definitionally equals the trans
  -- `(presheafValue_iteratedPlus_equiv P D₀ f).trans
  --   (presheafValue_trivialPlus_fSubX_equiv P D₀ f ...)`, and
  -- `presheafValue_trivialPlus_fSubX_equiv ...` definitionally equals
  -- `(example638Plus_equiv ...).symm`. As a function, the `trans` is
  -- the composition `(... .symm) ∘ (presheafValue_iteratedPlus_equiv ...)`.
  show Topology.IsInducing
    (fun x : presheafValue (laurentPlusDatum D₀ f) =>
      ((example638Plus_equiv (presheafValue D₀) P_B (D₀.canonicalMap f)
          hA_complete_B hnoeth_B hcont_forward_B).symm)
        ((presheafValue_iteratedPlus_equiv P D₀ f) x))
  exact h₂.comp h₁

/-- **T147 minus: `laurentMinusBridge` is `Topology.IsInducing`.**

Compose T146's `presheafValue_iteratedMinus_equiv_isInducing` with T142's
`presheafValueCanonicalQuotientEquiv_isInducing`. The internal `hb`,
`hT_pb`, `hA_complete` parameters of `laurentMinusBridge` are recomputed
in the proof body (mirroring the bridge's definition); T142 then
discharges the canonical-quotient inducing under explicit Baire /
sigma-compact hypotheses. The `hNoeth_B` and `hDom_B` hypotheses are
needed to discharge the `LaurentCover.B₂_gen` topology instance from
`LaurentCoverTopology.lean`. -/
theorem laurentMinusBridge_isInducing
    [IsTateRing A] [IsNoetherianRing A] [T2Space A]
    [NonarchimedeanRing A]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (D₀ : RationalLocData A) [IsNoetherianRing (locSubring D₀.P D₀.T D₀.s)]
    [LaurentNormalized D₀]
    (f : A)
    (hNoeth_B : IsNoetherianRing (presheafValue D₀))
    (hDom_B : IsDomain (presheafValue D₀))
    (hnoeth_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      IsNoetherianRing ↥(TateAlgebra.pairSubring
        (IsTateRing.principalPair (presheafValue D₀)).toPairOfDefinition))
    (hcont_eval_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      let D : RationalLocData (presheafValue D₀) := iteratedMinusDatum_B P D₀ f
      ∀ hb : TopologicalRing.IsPowerBounded (invS D),
        @Continuous _ _
          (TateAlgebra.quotientOneSubfXIdealTopology D.s)
          (inferInstance : TopologicalSpace (presheafValue D))
          (tateQuotientToPresheafHom D hb))
    (hBaire_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      @BaireSpace (presheafValue (iteratedMinusDatum_B P D₀ f)) _)
    (hSigma_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      @SigmaCompactSpace
        (↥(TateAlgebra (presheafValue D₀)) ⧸
          TateAlgebra.oneSubfXIdeal (iteratedMinusDatum_B P D₀ f).s)
        (TateAlgebra.quotientOneSubfXIdealTopology
          (iteratedMinusDatum_B P D₀ f).s)) :
    letI : IsTateRing (presheafValue D₀) := presheafValue_isTateRing P D₀
    letI : IsNoetherianRing (presheafValue D₀) := hNoeth_B
    letI : IsDomain (presheafValue D₀) := hDom_B
    Topology.IsInducing
      ((laurentMinusBridge P D₀ f hnoeth_B hcont_eval_B) :
        presheafValue (laurentMinusDatum D₀ f) →
          LaurentCover.B₂_gen (D₀.canonicalMap f)) := by
  haveI : IsTateRing (presheafValue D₀) := presheafValue_isTateRing P D₀
  haveI : IsNoetherianRing (presheafValue D₀) := hNoeth_B
  haveI : IsDomain (presheafValue D₀) := hDom_B
  -- Recompute the internal `hb`, `hT_pb`, `hA_complete` from the
  -- `laurentMinusBridge` body, mirroring `laurentMinusBridge_restrictionMap`.
  have hinvS_eq : invS (iteratedMinusDatum_B P D₀ f) =
      (iteratedMinusDatum_B P D₀ f).coeRingHom
        (divByS 1 (iteratedMinusDatum_B P D₀ f).s) := by
    set D : RationalLocData (presheafValue D₀) := iteratedMinusDatum_B P D₀ f
    have h1 : D.canonicalMap D.s * invS D = 1 := canonicalMap_s_mul_invS D
    have halg : algebraMap (presheafValue D₀) (Localization.Away D.s) D.s *
        divByS 1 D.s = 1 := by
      rw [← invSelf_eq_divByS, IsLocalization.Away.mul_invSelf]
    have h2 : D.canonicalMap D.s * D.coeRingHom (divByS 1 D.s) = 1 := by
      show D.coeRingHom (algebraMap (presheafValue D₀) (Localization.Away D.s) D.s) *
        D.coeRingHom (divByS 1 D.s) = 1
      rw [← map_mul, halg, map_one]
    have hu : IsUnit (D.canonicalMap D.s) := isUnit_s_in_presheafValue D
    exact hu.mul_left_cancel (h1.trans h2.symm)
  have hb : TopologicalRing.IsPowerBounded
      (invS (iteratedMinusDatum_B P D₀ f)) := by
    rw [hinvS_eq]
    exact CompletionLocalization.invS_isPowerBounded_of_one_mem_T
      (iteratedMinusDatum_B P D₀ f) (Finset.mem_singleton_self 1)
  have hT_pb : ∀ t ∈ (iteratedMinusDatum_B P D₀ f).T,
      TopologicalRing.IsPowerBounded t := by
    intro t ht
    rw [Finset.mem_singleton.mp ht]
    exact TopologicalRing.isPowerBounded_one
  have hA_complete : @CompleteSpace (presheafValue D₀)
      (IsTopologicalAddGroup.rightUniformSpace (presheafValue D₀)) := by
    rw [IsUniformAddGroup.rightUniformSpace_eq]
    infer_instance
  -- T146 minus equiv inducing.
  have h₁ : Topology.IsInducing
      ((presheafValue_iteratedMinus_equiv P D₀ f) :
        presheafValue (laurentMinusDatum D₀ f) →
          presheafValue (iteratedMinusDatum_B P D₀ f)) :=
    presheafValue_iteratedMinus_equiv_isInducing P D₀ f
  -- T142 canonical quotient inducing.
  have h₂ : @Topology.IsInducing _ _ _
      (TateAlgebra.quotientOneSubfXIdealTopology
        (iteratedMinusDatum_B P D₀ f).s)
      ((presheafValueCanonicalQuotientEquiv (iteratedMinusDatum_B P D₀ f)
          hb hA_complete hnoeth_B hT_pb (hcont_eval_B hb)) :
        presheafValue (iteratedMinusDatum_B P D₀ f) →
          (↥(TateAlgebra (presheafValue D₀)) ⧸
            TateAlgebra.oneSubfXIdeal (iteratedMinusDatum_B P D₀ f).s)) :=
    presheafValueCanonicalQuotientEquiv_isInducing
      (iteratedMinusDatum_B P D₀ f) hb hA_complete hnoeth_B hT_pb
      (hcont_eval_B hb) hBaire_B hSigma_B
  -- The bridge as a function is the composition (mirroring the
  -- `change` step in `laurentMinusBridge_restrictionMap`).
  show Topology.IsInducing
    (fun x : presheafValue (laurentMinusDatum D₀ f) =>
      (presheafValueCanonicalQuotientEquiv (iteratedMinusDatum_B P D₀ f)
          hb hA_complete hnoeth_B hT_pb (hcont_eval_B hb))
        ((presheafValue_iteratedMinus_equiv P D₀ f) x))
  exact h₂.comp h₁

/-! ### Overlap infrastructure for `laurentBridge_delta_eq_zero_of_compat`

The delta-vanishing theorem below relies on an *overlap bridge* identifying
the presheaf value at the double-Laurent refinement with the algebraic
overlap ring `B₁₂_gen`. We expose the residual facts as explicit sub-sorries,
following the sub-sorry pattern used for the plus/minus bridge compatibility
lemmas above. -/

/-- The overlap rational datum for the Laurent cover at `f`: the common
refinement of `laurentPlusDatum` and `laurentMinusDatum`, realised as the
double refinement `laurentMinusDatum (laurentPlusDatum D₀ f) f`.

Its `s` is `(laurentPlusDatum D₀ f).s · f = D₀.s · f`, and its rational open
equals `rationalOpen(plus) ∩ rationalOpen(minus)` (Remark 7.30(5)). -/
noncomputable def laurentOverlapDatum (D₀ : RationalLocData A) (f : A) :
    RationalLocData A :=
  laurentMinusDatum (laurentPlusDatum D₀ f) f

/-- The overlap is contained in the plus half. Immediate from
`laurentMinus_subset` applied to `laurentPlusDatum D₀ f`. -/
theorem laurentOverlap_subset_plus (D₀ : RationalLocData A) (f : A) :
    rationalOpen (laurentOverlapDatum D₀ f).T (laurentOverlapDatum D₀ f).s ⊆
      rationalOpen (laurentPlusDatum D₀ f).T (laurentPlusDatum D₀ f).s :=
  laurentMinus_subset (laurentPlusDatum D₀ f) f

/-- The overlap is contained in the minus half.

Both sides have the same `s = D₀.s · f`, and the overlap's `T` contains the
minus's `T` (the overlap has `Dp.T = insert f D₀.T` on the left factor,
whereas the minus has `D₀.T`; both share the right factor `{D₀.s, f}`).
A bigger `T` imposes more valuation constraints, hence a smaller rational
open. -/
theorem laurentOverlap_subset_minus (D₀ : RationalLocData A) (f : A) :
    rationalOpen (laurentOverlapDatum D₀ f).T (laurentOverlapDatum D₀ f).s ⊆
      rationalOpen (laurentMinusDatum D₀ f).T (laurentMinusDatum D₀ f).s := by
  -- `D_overlap.s = (laurentPlusDatum D₀ f).s · f = D₀.s · f = (laurentMinusDatum D₀ f).s`
  -- `D_overlap.T = (insert Dp.s Dp.T) * {Dp.s, f}` with `Dp.s = D₀.s, Dp.T = insert f D₀.T`
  -- so `D_overlap.T = (insert D₀.s (insert f D₀.T)) * {D₀.s, f}`
  -- `(laurentMinusDatum D₀ f).T = (insert D₀.s D₀.T) * {D₀.s, f}`
  -- The overlap T contains the minus T (extra factor `f` in the first factor),
  -- so the valuation constraint ∀t∈T, v(t) ≤ v(s) on the overlap T implies
  -- the same constraint on the minus T.
  intro v hv
  obtain ⟨hv_spa, hv_T, hv_s⟩ := hv
  -- Show the `s` parts agree (both = D₀.s * f).
  refine ⟨hv_spa, fun t ht => ?_, ?_⟩
  · -- Every `t ∈ (laurentMinusDatum D₀ f).T` is also in `(laurentOverlapDatum D₀ f).T`.
    -- (laurentMinusDatum D₀ f).T = (insert D₀.s D₀.T).product {D₀.s, f} |>.image (·.1 * ·.2)
    -- (laurentOverlapDatum D₀ f).T
    --   = (insert (laurentPlusDatum D₀ f).s (laurentPlusDatum D₀ f).T).product {(laurentPlusDatum D₀ f).s, f} |>.image (·.1 * ·.2)
    --   = (insert D₀.s (insert f D₀.T)).product {D₀.s, f} |>.image (·.1 * ·.2)
    -- The insert D₀.s (insert f D₀.T) ⊇ insert D₀.s D₀.T (left factor containment).
    -- So the overlap T ⊇ minus T.
    apply hv_T
    -- Reduce both sides to the image form.
    rcases Finset.mem_image.mp ht with ⟨⟨t₁, t₂⟩, ht_prod, rfl⟩
    rcases Finset.mem_product.mp ht_prod with ⟨ht₁, ht₂⟩
    refine Finset.mem_image.mpr ⟨(t₁, t₂), ?_, rfl⟩
    refine Finset.mem_product.mpr ⟨?_, ht₂⟩
    -- t₁ ∈ insert D₀.s D₀.T ⊆ insert D₀.s (insert f D₀.T) = insert (laurentPlusDatum D₀ f).s (laurentPlusDatum D₀ f).T
    rcases Finset.mem_insert.mp ht₁ with h | h
    · exact Finset.mem_insert.mpr (Or.inl h)
    · exact Finset.mem_insert.mpr
        (Or.inr (Finset.mem_insert.mpr (Or.inr h)))
  · -- `s` parts are equal: overlap `s = D₀.s * f = (laurentMinusDatum D₀ f).s`.
    exact hv_s

/-! #### Compatibility predicate for the overlap bridge

The existence sorry `laurentOverlapBridge_exists` returns `Nonempty` of an
arbitrary ring equiv, which by itself is insufficient to run the intertwining
computations: for a generic `RingEquiv`, the intertwining equations
```
τ₁₂ ∘ restrictionMap(plus, overlap) = posLift ∘ laurentPlusBridge
τ₁₂ ∘ restrictionMap(minus, overlap) = negLift ∘ laurentMinusBridge
```
cannot be established because the bridge is not constrained to come from a
canonical construction.

The right formulation is: `laurentOverlapBridge_exists` should produce a
bridge satisfying these intertwining identities *by construction*. The
predicate below captures this compatibility, and the existence sorry below
is strengthened (in spirit) to "there exists a COMPATIBLE bridge". The
intertwining theorems for the compatibility predicate are then tautologies.

The concrete construction of such a compatible bridge is the Laurent analog
of Example 6.38: an `evalHomBounded`-style map from the bivariate Laurent
algebra `LaurentTateAlgebra (presheafValue D₀)` to `presheafValue(overlap)`,
sending `ζ ↦ canonicalMap f` and `ζ⁻¹ ↦ (canonicalMap f)⁻¹` (where the
inverse exists because `f` is invertible in the overlap). This primitive is
NOT yet available in the project infrastructure (the existing `evalHomBounded`
only handles the univariate Tate algebra). -/

/-- Compatibility predicate for an overlap bridge. A `τ₁₂` satisfying
`LaurentOverlapBridgeCompatible` intertwines with both plus and minus
restrictions. This is the "right" notion of bridge — it is the conjunction
of the two intertwining identities. -/
structure LaurentOverlapBridgeCompatible
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (D₀ : RationalLocData A) [IsNoetherianRing (locSubring D₀.P D₀.T D₀.s)]
    [LaurentNormalized D₀]
    (f : A)
    (hNoeth_B : IsNoetherianRing (presheafValue D₀))
    (hLocLift_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      HasLocLiftPowerBounded (presheafValue D₀))
    (hA₀Noeth_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      letI : IsNoetherianRing (presheafValue D₀) := hNoeth_B
      IsNoetherianRing ↥((presheafValue_pairOfDefinition_concrete P D₀).A₀))
    (hA_complete_B : @CompleteSpace (presheafValue D₀)
      (IsTopologicalAddGroup.rightUniformSpace (presheafValue D₀)))
    (hnoeth_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      IsNoetherianRing ↥(TateAlgebra.pairSubring
        (IsTateRing.principalPair (presheafValue D₀)).toPairOfDefinition))
    (hcont_forward_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      letI : HasLocLiftPowerBounded (presheafValue D₀) := hLocLift_B
      letI : IsNoetherianRing (presheafValue D₀) := hNoeth_B
      letI P_B : PairOfDefinition (presheafValue D₀) :=
        presheafValue_pairOfDefinition_concrete P D₀
      letI : IsNoetherianRing ↥P_B.A₀ := hA₀Noeth_B
      @Continuous _ _
        (quotientPlusFSubXIdealTopology (presheafValue D₀) (D₀.canonicalMap f))
        (inferInstance : TopologicalSpace (presheafValue
          (trivialPlusDatum (presheafValue D₀) P_B (D₀.canonicalMap f))))
        (example638Plus_forwardHom (presheafValue D₀) P_B (D₀.canonicalMap f)))
    (hcont_eval_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      let D : RationalLocData (presheafValue D₀) := iteratedMinusDatum_B P D₀ f
      ∀ hb : TopologicalRing.IsPowerBounded (invS D),
        @Continuous _ _
          (TateAlgebra.quotientOneSubfXIdealTopology D.s)
          (inferInstance : TopologicalSpace (presheafValue D))
          (tateQuotientToPresheafHom D hb))
    (τ₁₂ : presheafValue (laurentOverlapDatum D₀ f) ≃+*
      LaurentCover.B₁₂_gen (D₀.canonicalMap f)) : Prop where
  /-- `τ₁₂` intertwines with `posLift` on the plus side. -/
  plus_compat : ∀ uplus : presheafValue (laurentPlusDatum D₀ f),
    τ₁₂ (restrictionMap (laurentPlusDatum D₀ f) (laurentOverlapDatum D₀ f)
          (laurentOverlap_subset_plus D₀ f) uplus) =
      LaurentCover.posLift (D₀.canonicalMap f)
        (laurentPlusBridge P D₀ f hNoeth_B hLocLift_B hA₀Noeth_B hA_complete_B
          hnoeth_B hcont_forward_B uplus)
  /-- `τ₁₂` intertwines with `negLift` on the minus side. -/
  minus_compat : ∀ uminus : presheafValue (laurentMinusDatum D₀ f),
    τ₁₂ (restrictionMap (laurentMinusDatum D₀ f) (laurentOverlapDatum D₀ f)
          (laurentOverlap_subset_minus D₀ f) uminus) =
      LaurentCover.negLift (D₀.canonicalMap f)
        (laurentMinusBridge P D₀ f hnoeth_B hcont_eval_B uminus)

-- REMOVED 2026-04-16: `laurentOverlapBridge_exists` — the weak `Nonempty`-returning
-- variant with no call sites. Superseded by `laurentOverlapBridge_exists_compatible`
-- below, which produces the bridge together with a compatibility witness
-- (`LaurentOverlapBridgeCompatible`). The only downstream consumer
-- (`laurentBridge_delta_eq_zero_of_compat`) already uses the stronger variant.

-- REMOVED 2026-04-16: `laurentOverlap_plus_intertwine`, `laurentOverlap_minus_intertwine`.
--
-- These theorems took an arbitrary `τ₁₂` as input and claimed an intertwining
-- identity that fails for generic equivs; only the canonical compatible bridge
-- satisfies it. The proper usage (via `LaurentOverlapBridgeCompatible`) is
-- captured by `laurentOverlap_plus_intertwine_of_compatible` and
-- `laurentOverlap_minus_intertwine_of_compatible` below, which directly project
-- the compatibility structure's fields. No external callers (all downstream
-- code in `laurentBridge_delta_eq_zero_of_compat` uses the `_of_compatible`
-- variants via `hcompat_bridge.plus_compat` / `hcompat_bridge.minus_compat`).

/-! #### Strengthened existence: a compatible overlap bridge

The three sorries above (`laurentOverlapBridge_exists`,
`laurentOverlap_plus_intertwine`, `laurentOverlap_minus_intertwine`) cannot
be closed in isolation because, as phrased, the two intertwining theorems
take an *arbitrary* ring equiv `τ₁₂` as input and try to prove identities
that are sensitive to which specific equiv was chosen. A generic equiv
will fail both intertwinings; only the canonical one (constructed via the
evaluation `ζ ↦ canonicalMap f` in the Laurent analog of Example 6.38) is
compatible.

The strengthened existence theorem below states what should really be
produced: a bridge together with a witness that it is compatible. Once
this strengthened form is available (via the Laurent-analog primitive),
it immediately implies both intertwining theorems for the chosen bridge.

The consumer `laurentBridge_delta_eq_zero_of_compat` currently uses the
weak form (and the two sorries it routes through) — refactoring to use
the strengthened form is a safe migration that is independent of filling
the underlying new primitive. -/
theorem laurentOverlapBridge_exists_compatible
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (D₀ : RationalLocData A) [IsNoetherianRing (locSubring D₀.P D₀.T D₀.s)]
    [LaurentNormalized D₀]
    (f : A)
    (hNoeth_B : IsNoetherianRing (presheafValue D₀))
    (hLocLift_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      HasLocLiftPowerBounded (presheafValue D₀))
    (hA₀Noeth_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      letI : IsNoetherianRing (presheafValue D₀) := hNoeth_B
      IsNoetherianRing ↥((presheafValue_pairOfDefinition_concrete P D₀).A₀))
    (hA_complete_B : @CompleteSpace (presheafValue D₀)
      (IsTopologicalAddGroup.rightUniformSpace (presheafValue D₀)))
    (hnoeth_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      IsNoetherianRing ↥(TateAlgebra.pairSubring
        (IsTateRing.principalPair (presheafValue D₀)).toPairOfDefinition))
    (hcont_forward_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      letI : HasLocLiftPowerBounded (presheafValue D₀) := hLocLift_B
      letI : IsNoetherianRing (presheafValue D₀) := hNoeth_B
      letI P_B : PairOfDefinition (presheafValue D₀) :=
        presheafValue_pairOfDefinition_concrete P D₀
      letI : IsNoetherianRing ↥P_B.A₀ := hA₀Noeth_B
      @Continuous _ _
        (quotientPlusFSubXIdealTopology (presheafValue D₀) (D₀.canonicalMap f))
        (inferInstance : TopologicalSpace (presheafValue
          (trivialPlusDatum (presheafValue D₀) P_B (D₀.canonicalMap f))))
        (example638Plus_forwardHom (presheafValue D₀) P_B (D₀.canonicalMap f)))
    (hcont_eval_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      let D : RationalLocData (presheafValue D₀) := iteratedMinusDatum_B P D₀ f
      ∀ hb : TopologicalRing.IsPowerBounded (invS D),
        @Continuous _ _
          (TateAlgebra.quotientOneSubfXIdealTopology D.s)
          (inferInstance : TopologicalSpace (presheafValue D))
          (tateQuotientToPresheafHom D hb))
    (τ_preBiv : presheafValue (laurentOverlapDatum D₀ f) ≃+*
      (↥(TateAlgebra₂ (presheafValue D₀)) ⧸
        TateAlgebra.bivariateOverlapIdeal (D₀.canonicalMap f)))
    (τ_alg : (↥(TateAlgebra₂ (presheafValue D₀)) ⧸
        TateAlgebra.bivariateOverlapIdeal (D₀.canonicalMap f)) ≃+*
      LaurentCover.B₁₂_gen (D₀.canonicalMap f))
    (h_plus_compat : ∀ uplus : presheafValue (laurentPlusDatum D₀ f),
      τ_alg (τ_preBiv (restrictionMap (laurentPlusDatum D₀ f)
              (laurentOverlapDatum D₀ f)
              (laurentOverlap_subset_plus D₀ f) uplus)) =
        LaurentCover.posLift (D₀.canonicalMap f)
          (laurentPlusBridge P D₀ f hNoeth_B hLocLift_B hA₀Noeth_B hA_complete_B
            hnoeth_B hcont_forward_B uplus))
    (h_minus_compat : ∀ uminus : presheafValue (laurentMinusDatum D₀ f),
      τ_alg (τ_preBiv (restrictionMap (laurentMinusDatum D₀ f)
              (laurentOverlapDatum D₀ f)
              (laurentOverlap_subset_minus D₀ f) uminus)) =
        LaurentCover.negLift (D₀.canonicalMap f)
          (laurentMinusBridge P D₀ f hnoeth_B hcont_eval_B uminus)) :
    ∃ τ₁₂ : presheafValue (laurentOverlapDatum D₀ f) ≃+*
          LaurentCover.B₁₂_gen (D₀.canonicalMap f),
      LaurentOverlapBridgeCompatible P D₀ f hNoeth_B hLocLift_B hA₀Noeth_B
        hA_complete_B hnoeth_B hcont_forward_B hcont_eval_B τ₁₂ :=
  -- Sorry-free after accepting the bivariate factorization inputs: takes
  -- `(τ_preBiv, τ_alg, h_plus_compat, h_minus_compat)` and packages the
  -- compatible bridge witness via `τ₁₂ := τ_preBiv.trans τ_alg`. Same body as
  -- `laurentOverlapBridge_exists_compatible_from_bivariate_factorization`
  -- (below). Primary's `bivariateOverlap_equiv_B₁₂gen` (`LaurentOverlap.lean`)
  -- is the canonical `τ_alg`; the `_via_primary` caller chain in
  -- `LaurentOverlapConsumer.lean` binds that directly (see
  -- `laurentOverlapBridge_exists_compatible_via_primary`).
  ⟨τ_preBiv.trans τ_alg,
   { plus_compat := h_plus_compat
     minus_compat := h_minus_compat }⟩

/-- **Reduction of `laurentOverlapBridge_exists_compatible` to a bivariate
factorization** (T-OV-1 / S-OV-GLUE support). The target existential
`∃ τ₁₂ : presheafValue(overlap) ≃+* B₁₂_gen b, LaurentOverlapBridgeCompatible …`
is discharged whenever the bridge factors as `τ₁₂ = τ_preBiv.trans τ_alg`
through `TateAlgebra₂(B) ⧸ bivariateOverlapIdeal b` and the two
intertwining identities hold at the composed level.

**Intended usage**: plug in Primary's sorry-free
`bivariateOverlap_equiv_B₁₂gen` (LaurentOverlap.lean:630) as the
algebraic iso `τ_alg`. Primary's remaining Lane-A work then produces
`τ_preBiv` (the presheaf-level bivariate iso, Step A / S-OV-GLUE) and
the two intertwining identities — feeding this reduction to close the
`sorry` at `laurentOverlapBridge_exists_compatible`.

**Content**: trivial composition wrapping — no new mathematical content.
The value is a **named interface** separating the bivariate algebraic
step (done, Primary's Step B) from the presheaf-level bivariate
identification (Primary's Step A / S-OV-GLUE). -/
theorem laurentOverlapBridge_exists_compatible_from_bivariate_factorization
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (D₀ : RationalLocData A) [IsNoetherianRing (locSubring D₀.P D₀.T D₀.s)]
    [LaurentNormalized D₀]
    (f : A)
    (hNoeth_B : IsNoetherianRing (presheafValue D₀))
    (hLocLift_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      HasLocLiftPowerBounded (presheafValue D₀))
    (hA₀Noeth_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      letI : IsNoetherianRing (presheafValue D₀) := hNoeth_B
      IsNoetherianRing ↥((presheafValue_pairOfDefinition_concrete P D₀).A₀))
    (hA_complete_B : @CompleteSpace (presheafValue D₀)
      (IsTopologicalAddGroup.rightUniformSpace (presheafValue D₀)))
    (hnoeth_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      IsNoetherianRing ↥(TateAlgebra.pairSubring
        (IsTateRing.principalPair (presheafValue D₀)).toPairOfDefinition))
    (hcont_forward_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      letI : HasLocLiftPowerBounded (presheafValue D₀) := hLocLift_B
      letI : IsNoetherianRing (presheafValue D₀) := hNoeth_B
      letI P_B : PairOfDefinition (presheafValue D₀) :=
        presheafValue_pairOfDefinition_concrete P D₀
      letI : IsNoetherianRing ↥P_B.A₀ := hA₀Noeth_B
      @Continuous _ _
        (quotientPlusFSubXIdealTopology (presheafValue D₀) (D₀.canonicalMap f))
        (inferInstance : TopologicalSpace (presheafValue
          (trivialPlusDatum (presheafValue D₀) P_B (D₀.canonicalMap f))))
        (example638Plus_forwardHom (presheafValue D₀) P_B (D₀.canonicalMap f)))
    (hcont_eval_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      let D : RationalLocData (presheafValue D₀) := iteratedMinusDatum_B P D₀ f
      ∀ hb : TopologicalRing.IsPowerBounded (invS D),
        @Continuous _ _
          (TateAlgebra.quotientOneSubfXIdealTopology D.s)
          (inferInstance : TopologicalSpace (presheafValue D))
          (tateQuotientToPresheafHom D hb))
    (τ_preBiv : presheafValue (laurentOverlapDatum D₀ f) ≃+*
      (↥(TateAlgebra₂ (presheafValue D₀)) ⧸
        TateAlgebra.bivariateOverlapIdeal (D₀.canonicalMap f)))
    (τ_alg : (↥(TateAlgebra₂ (presheafValue D₀)) ⧸
        TateAlgebra.bivariateOverlapIdeal (D₀.canonicalMap f)) ≃+*
      LaurentCover.B₁₂_gen (D₀.canonicalMap f))
    (h_plus_compat : ∀ uplus : presheafValue (laurentPlusDatum D₀ f),
      τ_alg (τ_preBiv (restrictionMap (laurentPlusDatum D₀ f)
              (laurentOverlapDatum D₀ f)
              (laurentOverlap_subset_plus D₀ f) uplus)) =
        LaurentCover.posLift (D₀.canonicalMap f)
          (laurentPlusBridge P D₀ f hNoeth_B hLocLift_B hA₀Noeth_B hA_complete_B
            hnoeth_B hcont_forward_B uplus))
    (h_minus_compat : ∀ uminus : presheafValue (laurentMinusDatum D₀ f),
      τ_alg (τ_preBiv (restrictionMap (laurentMinusDatum D₀ f)
              (laurentOverlapDatum D₀ f)
              (laurentOverlap_subset_minus D₀ f) uminus)) =
        LaurentCover.negLift (D₀.canonicalMap f)
          (laurentMinusBridge P D₀ f hnoeth_B hcont_eval_B uminus)) :
    ∃ τ₁₂ : presheafValue (laurentOverlapDatum D₀ f) ≃+*
            LaurentCover.B₁₂_gen (D₀.canonicalMap f),
      LaurentOverlapBridgeCompatible P D₀ f hNoeth_B hLocLift_B
        hA₀Noeth_B hA_complete_B hnoeth_B hcont_forward_B hcont_eval_B τ₁₂ :=
  ⟨τ_preBiv.trans τ_alg,
   { plus_compat := h_plus_compat
     minus_compat := h_minus_compat }⟩

/-- **Consequence**: from a compatible bridge, the plus-side intertwining is
an immediate projection from the compatibility structure. This shows that
the original `laurentOverlap_plus_intertwine` holds when `τ₁₂` is chosen to
satisfy `LaurentOverlapBridgeCompatible` — which is the intended usage. -/
theorem laurentOverlap_plus_intertwine_of_compatible
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (D₀ : RationalLocData A) [IsNoetherianRing (locSubring D₀.P D₀.T D₀.s)]
    [LaurentNormalized D₀]
    (f : A)
    (hNoeth_B : IsNoetherianRing (presheafValue D₀))
    (hLocLift_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      HasLocLiftPowerBounded (presheafValue D₀))
    (hA₀Noeth_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      letI : IsNoetherianRing (presheafValue D₀) := hNoeth_B
      IsNoetherianRing ↥((presheafValue_pairOfDefinition_concrete P D₀).A₀))
    (hA_complete_B : @CompleteSpace (presheafValue D₀)
      (IsTopologicalAddGroup.rightUniformSpace (presheafValue D₀)))
    (hnoeth_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      IsNoetherianRing ↥(TateAlgebra.pairSubring
        (IsTateRing.principalPair (presheafValue D₀)).toPairOfDefinition))
    (hcont_forward_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      letI : HasLocLiftPowerBounded (presheafValue D₀) := hLocLift_B
      letI : IsNoetherianRing (presheafValue D₀) := hNoeth_B
      letI P_B : PairOfDefinition (presheafValue D₀) :=
        presheafValue_pairOfDefinition_concrete P D₀
      letI : IsNoetherianRing ↥P_B.A₀ := hA₀Noeth_B
      @Continuous _ _
        (quotientPlusFSubXIdealTopology (presheafValue D₀) (D₀.canonicalMap f))
        (inferInstance : TopologicalSpace (presheafValue
          (trivialPlusDatum (presheafValue D₀) P_B (D₀.canonicalMap f))))
        (example638Plus_forwardHom (presheafValue D₀) P_B (D₀.canonicalMap f)))
    (hcont_eval_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      let D : RationalLocData (presheafValue D₀) := iteratedMinusDatum_B P D₀ f
      ∀ hb : TopologicalRing.IsPowerBounded (invS D),
        @Continuous _ _
          (TateAlgebra.quotientOneSubfXIdealTopology D.s)
          (inferInstance : TopologicalSpace (presheafValue D))
          (tateQuotientToPresheafHom D hb))
    (τ₁₂ : presheafValue (laurentOverlapDatum D₀ f) ≃+*
      LaurentCover.B₁₂_gen (D₀.canonicalMap f))
    (hcompat_bridge : LaurentOverlapBridgeCompatible P D₀ f hNoeth_B hLocLift_B
      hA₀Noeth_B hA_complete_B hnoeth_B hcont_forward_B hcont_eval_B τ₁₂)
    (uplus : presheafValue (laurentPlusDatum D₀ f)) :
    τ₁₂ (restrictionMap (laurentPlusDatum D₀ f) (laurentOverlapDatum D₀ f)
          (laurentOverlap_subset_plus D₀ f) uplus) =
      LaurentCover.posLift (D₀.canonicalMap f)
        (laurentPlusBridge P D₀ f hNoeth_B hLocLift_B hA₀Noeth_B hA_complete_B
          hnoeth_B hcont_forward_B uplus) :=
  hcompat_bridge.plus_compat uplus

/-- **Consequence**: from a compatible bridge, the minus-side intertwining is
an immediate projection from the compatibility structure. Symmetric to
`laurentOverlap_plus_intertwine_of_compatible`. -/
theorem laurentOverlap_minus_intertwine_of_compatible
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (D₀ : RationalLocData A) [IsNoetherianRing (locSubring D₀.P D₀.T D₀.s)]
    [LaurentNormalized D₀]
    (f : A)
    (hNoeth_B : IsNoetherianRing (presheafValue D₀))
    (hLocLift_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      HasLocLiftPowerBounded (presheafValue D₀))
    (hA₀Noeth_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      letI : IsNoetherianRing (presheafValue D₀) := hNoeth_B
      IsNoetherianRing ↥((presheafValue_pairOfDefinition_concrete P D₀).A₀))
    (hA_complete_B : @CompleteSpace (presheafValue D₀)
      (IsTopologicalAddGroup.rightUniformSpace (presheafValue D₀)))
    (hnoeth_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      IsNoetherianRing ↥(TateAlgebra.pairSubring
        (IsTateRing.principalPair (presheafValue D₀)).toPairOfDefinition))
    (hcont_forward_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      letI : HasLocLiftPowerBounded (presheafValue D₀) := hLocLift_B
      letI : IsNoetherianRing (presheafValue D₀) := hNoeth_B
      letI P_B : PairOfDefinition (presheafValue D₀) :=
        presheafValue_pairOfDefinition_concrete P D₀
      letI : IsNoetherianRing ↥P_B.A₀ := hA₀Noeth_B
      @Continuous _ _
        (quotientPlusFSubXIdealTopology (presheafValue D₀) (D₀.canonicalMap f))
        (inferInstance : TopologicalSpace (presheafValue
          (trivialPlusDatum (presheafValue D₀) P_B (D₀.canonicalMap f))))
        (example638Plus_forwardHom (presheafValue D₀) P_B (D₀.canonicalMap f)))
    (hcont_eval_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      let D : RationalLocData (presheafValue D₀) := iteratedMinusDatum_B P D₀ f
      ∀ hb : TopologicalRing.IsPowerBounded (invS D),
        @Continuous _ _
          (TateAlgebra.quotientOneSubfXIdealTopology D.s)
          (inferInstance : TopologicalSpace (presheafValue D))
          (tateQuotientToPresheafHom D hb))
    (τ₁₂ : presheafValue (laurentOverlapDatum D₀ f) ≃+*
      LaurentCover.B₁₂_gen (D₀.canonicalMap f))
    (hcompat_bridge : LaurentOverlapBridgeCompatible P D₀ f hNoeth_B hLocLift_B
      hA₀Noeth_B hA_complete_B hnoeth_B hcont_forward_B hcont_eval_B τ₁₂)
    (uminus : presheafValue (laurentMinusDatum D₀ f)) :
    τ₁₂ (restrictionMap (laurentMinusDatum D₀ f) (laurentOverlapDatum D₀ f)
          (laurentOverlap_subset_minus D₀ f) uminus) =
      LaurentCover.negLift (D₀.canonicalMap f)
        (laurentMinusBridge P D₀ f hnoeth_B hcont_eval_B uminus) :=
  hcompat_bridge.minus_compat uminus

/-- **Route B bridge (delta vanishing on compatible pairs)**: compatibility
of `(uplus, uminus)` on every common refinement implies that their images
under the bridges map to a class annihilated by `deltaMap_gen`.

Mathematical content: `deltaMap_gen f'` is the algebraic difference of
`posLift` and `negLift` in `B₁₂_gen f'`; the compatibility on overlaps is
exactly the sheaf condition on the doubly-refined datum (with `s = D₀.s · f`
and `T` containing both halves), which equals the Laurent overlap.

**Proof.** Apply `hcompat` at `laurentOverlapDatum D₀ f` to obtain equality
of the plus and minus restrictions in `presheafValue(D_overlap)`. Apply the
overlap bridge `τ₁₂` (from `laurentOverlapBridge_exists`) to both sides and
use `laurentOverlap_plus_intertwine` / `laurentOverlap_minus_intertwine` to
transport the equality into `B₁₂_gen`. Subtracting yields `deltaMap_gen = 0`
by definition. -/
theorem laurentBridge_delta_eq_zero_of_compat
    [IsTateRing A] [IsNoetherianRing A] [T2Space A]
    [NonarchimedeanRing A]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (D₀ : RationalLocData A) [IsNoetherianRing (locSubring D₀.P D₀.T D₀.s)]
    [LaurentNormalized D₀]
    (f : A)
    (hNoeth_B : IsNoetherianRing (presheafValue D₀))
    (hLocLift_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      HasLocLiftPowerBounded (presheafValue D₀))
    (hA₀Noeth_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      letI : IsNoetherianRing (presheafValue D₀) := hNoeth_B
      IsNoetherianRing ↥((presheafValue_pairOfDefinition_concrete P D₀).A₀))
    (hA_complete_B : @CompleteSpace (presheafValue D₀)
      (IsTopologicalAddGroup.rightUniformSpace (presheafValue D₀)))
    (hnoeth_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      IsNoetherianRing ↥(TateAlgebra.pairSubring
        (IsTateRing.principalPair (presheafValue D₀)).toPairOfDefinition))
    (hcont_forward_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      letI : HasLocLiftPowerBounded (presheafValue D₀) := hLocLift_B
      letI : IsNoetherianRing (presheafValue D₀) := hNoeth_B
      letI P_B : PairOfDefinition (presheafValue D₀) :=
        presheafValue_pairOfDefinition_concrete P D₀
      letI : IsNoetherianRing ↥P_B.A₀ := hA₀Noeth_B
      @Continuous _ _
        (quotientPlusFSubXIdealTopology (presheafValue D₀) (D₀.canonicalMap f))
        (inferInstance : TopologicalSpace (presheafValue
          (trivialPlusDatum (presheafValue D₀) P_B (D₀.canonicalMap f))))
        (example638Plus_forwardHom (presheafValue D₀) P_B (D₀.canonicalMap f)))
    (hcont_eval_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      let D : RationalLocData (presheafValue D₀) := iteratedMinusDatum_B P D₀ f
      ∀ hb : TopologicalRing.IsPowerBounded (invS D),
        @Continuous _ _
          (TateAlgebra.quotientOneSubfXIdealTopology D.s)
          (inferInstance : TopologicalSpace (presheafValue D))
          (tateQuotientToPresheafHom D hb))
    (τ_preBiv : presheafValue (laurentOverlapDatum D₀ f) ≃+*
      (↥(TateAlgebra₂ (presheafValue D₀)) ⧸
        TateAlgebra.bivariateOverlapIdeal (D₀.canonicalMap f)))
    (τ_alg : (↥(TateAlgebra₂ (presheafValue D₀)) ⧸
        TateAlgebra.bivariateOverlapIdeal (D₀.canonicalMap f)) ≃+*
      LaurentCover.B₁₂_gen (D₀.canonicalMap f))
    (h_plus_compat : ∀ uplus : presheafValue (laurentPlusDatum D₀ f),
      τ_alg (τ_preBiv (restrictionMap (laurentPlusDatum D₀ f)
              (laurentOverlapDatum D₀ f)
              (laurentOverlap_subset_plus D₀ f) uplus)) =
        LaurentCover.posLift (D₀.canonicalMap f)
          (laurentPlusBridge P D₀ f hNoeth_B hLocLift_B hA₀Noeth_B hA_complete_B
            hnoeth_B hcont_forward_B uplus))
    (h_minus_compat : ∀ uminus : presheafValue (laurentMinusDatum D₀ f),
      τ_alg (τ_preBiv (restrictionMap (laurentMinusDatum D₀ f)
              (laurentOverlapDatum D₀ f)
              (laurentOverlap_subset_minus D₀ f) uminus)) =
        LaurentCover.negLift (D₀.canonicalMap f)
          (laurentMinusBridge P D₀ f hnoeth_B hcont_eval_B uminus))
    (uplus : presheafValue (laurentPlusDatum D₀ f))
    (uminus : presheafValue (laurentMinusDatum D₀ f))
    (hcompat : ∀ (D₃ : RationalLocData A)
      (h₃p : rationalOpen D₃.T D₃.s ⊆
        rationalOpen (laurentPlusDatum D₀ f).T (laurentPlusDatum D₀ f).s)
      (h₃m : rationalOpen D₃.T D₃.s ⊆
        rationalOpen (laurentMinusDatum D₀ f).T (laurentMinusDatum D₀ f).s),
      restrictionMap (laurentPlusDatum D₀ f) D₃ h₃p uplus =
        restrictionMap (laurentMinusDatum D₀ f) D₃ h₃m uminus) :
    LaurentCover.deltaMap_gen (D₀.canonicalMap f)
      (laurentPlusBridge P D₀ f hNoeth_B hLocLift_B hA₀Noeth_B hA_complete_B
          hnoeth_B hcont_forward_B uplus,
        laurentMinusBridge P D₀ f hnoeth_B hcont_eval_B uminus) = 0 := by
  -- **Step 1 — Extract a compatible overlap bridge.**
  -- Sorry-free after the 2026-04-22 refactor: `laurentOverlapBridge_exists_compatible`
  -- now takes `(τ_preBiv, τ_alg, h_plus_compat, h_minus_compat)` and returns the
  -- compatible bridge witness via `τ₁₂ := τ_preBiv.trans τ_alg`. Primary's
  -- `bivariateOverlap_equiv_B₁₂gen` (LaurentOverlap.lean) is the canonical `τ_alg`
  -- supplied by the `_via_primary` consumer chain.
  obtain ⟨τ₁₂, hcompat_bridge⟩ := laurentOverlapBridge_exists_compatible P D₀ f
    hNoeth_B hLocLift_B hA₀Noeth_B hA_complete_B hnoeth_B hcont_forward_B
    hcont_eval_B τ_preBiv τ_alg h_plus_compat h_minus_compat
  -- **Step 2 — Apply `hcompat` at the overlap datum.**
  have h_restr_eq : restrictionMap (laurentPlusDatum D₀ f) (laurentOverlapDatum D₀ f)
        (laurentOverlap_subset_plus D₀ f) uplus =
      restrictionMap (laurentMinusDatum D₀ f) (laurentOverlapDatum D₀ f)
        (laurentOverlap_subset_minus D₀ f) uminus :=
    hcompat (laurentOverlapDatum D₀ f)
      (laurentOverlap_subset_plus D₀ f) (laurentOverlap_subset_minus D₀ f)
  -- **Step 3 — Transport through τ₁₂.** Apply τ₁₂ to both sides, then rewrite
  -- each side using the compatibility projections from `hcompat_bridge`.
  have h_pos_eq_neg :
      LaurentCover.posLift (D₀.canonicalMap f)
        (laurentPlusBridge P D₀ f hNoeth_B hLocLift_B hA₀Noeth_B hA_complete_B
          hnoeth_B hcont_forward_B uplus) =
      LaurentCover.negLift (D₀.canonicalMap f)
        (laurentMinusBridge P D₀ f hnoeth_B hcont_eval_B uminus) := by
    have h1 := hcompat_bridge.plus_compat uplus
    have h2 := hcompat_bridge.minus_compat uminus
    rw [← h1, ← h2, h_restr_eq]
  -- **Step 4 — Conclude.** `deltaMap_gen (b₁, b₂) = posLift b₁ - negLift b₂`.
  show LaurentCover.posLift (D₀.canonicalMap f) _ -
    LaurentCover.negLift (D₀.canonicalMap f) _ = 0
  rw [h_pos_eq_neg]
  exact sub_self _

/-- **Laurent cover gluing via row3_exact** (Route B, Wedhorn Lemma 8.33),
parameterised by the two type bridges.

Reduces the Laurent gluing to three concrete obligations:
1. A ring iso `τ₊` identifying `presheafValue(plus)` with `B₁_gen(canonicalMap f)`.
2. A ring iso `τ₋` identifying `presheafValue(minus)` with `B₂_gen(canonicalMap f)`.
3. Compatibility of `τ₊, τ₋` with `restrictionMap` and `epsilonHom_gen`.
4. A "compat → delta = 0" translation: compatible pairs restrict to the same
   class in `B₁₂_gen`.

Once these are available, the proof is elementary algebra on the `row3_exact`
exactness at `A := presheafValue D₀`. No Baire category needed. -/
theorem laurentCover_gluing_presheaf_viaRow3
    [IsTateRing A] [IsNoetherianRing A] [T2Space A]
    [NonarchimedeanRing A]
    (D₀ : RationalLocData A) (f : A)
    (hplus : rationalOpen (laurentPlusDatum D₀ f).T (laurentPlusDatum D₀ f).s ⊆
      rationalOpen D₀.T D₀.s)
    (hminus : rationalOpen (laurentMinusDatum D₀ f).T (laurentMinusDatum D₀ f).s ⊆
      rationalOpen D₀.T D₀.s)
    (τ_plus : presheafValue (laurentPlusDatum D₀ f) ≃+*
      LaurentCover.B₁_gen (D₀.canonicalMap f))
    (τ_minus : presheafValue (laurentMinusDatum D₀ f) ≃+*
      LaurentCover.B₂_gen (D₀.canonicalMap f))
    (htau_plus : ∀ x : presheafValue D₀,
      τ_plus (restrictionMap D₀ (laurentPlusDatum D₀ f) hplus x) =
        (LaurentCover.epsilonHom_gen (D₀.canonicalMap f) x).1)
    (htau_minus : ∀ x : presheafValue D₀,
      τ_minus (restrictionMap D₀ (laurentMinusDatum D₀ f) hminus x) =
        (LaurentCover.epsilonHom_gen (D₀.canonicalMap f) x).2)
    (htop : (inferInstance : TopologicalSpace (presheafValue D₀)) =
      UniformSpace.toTopologicalSpace)
    (uplus : presheafValue (laurentPlusDatum D₀ f))
    (uminus : presheafValue (laurentMinusDatum D₀ f))
    (hdelta : LaurentCover.deltaMap_gen (D₀.canonicalMap f)
      (τ_plus uplus, τ_minus uminus) = 0) :
    ∃ x : presheafValue D₀,
      restrictionMap D₀ (laurentPlusDatum D₀ f) hplus x = uplus ∧
      restrictionMap D₀ (laurentMinusDatum D₀ f) hminus x = uminus := by
  -- Apply `row3_exact` at `A := presheafValue D₀`, `f' := D₀.canonicalMap f`.
  have key := LaurentCover.row3_exact (A := presheafValue D₀) (D₀.canonicalMap f) htop
  -- Extract existence of `a` from the `ker(δ) ⊆ im(ε)` part, at
  -- `(τ_plus uplus, τ_minus uminus)` (kernel condition from `hdelta`).
  obtain ⟨a, ha⟩ := key.2.1 (τ_plus uplus, τ_minus uminus) hdelta
  refine ⟨a, ?_, ?_⟩
  · -- `restrictionMap plus a = uplus` via `τ_plus`-injectivity.
    apply τ_plus.injective
    rw [htau_plus a, ha]
  · -- `restrictionMap minus a = uminus` via `τ_minus`-injectivity.
    apply τ_minus.injective
    rw [htau_minus a, ha]

/-- **Route B final assembly**: Laurent cover gluing using the named bridges.

Combines `laurentCover_gluing_presheaf_viaRow3` with the four Route B bridges
(`laurentPlusBridge`, `laurentMinusBridge`, the two compatibility lemmas, and
`laurentBridge_delta_eq_zero_of_compat`) to deliver the gluing conclusion
without the Baire-category dependency.

The `hnoeth_B` and `hcont_eval_B` hypotheses pack the Phase 2.5c / Phase 2.6
infrastructure residues for the rational base `B := presheafValue D₀`; they
are passed through to `laurentMinusBridge` and its companions. -/
theorem laurentCover_gluing_presheaf_viaBridges
    [IsTateRing A] [IsNoetherianRing A] [T2Space A]
    [NonarchimedeanRing A]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (D₀ : RationalLocData A) [IsNoetherianRing (locSubring D₀.P D₀.T D₀.s)]
    [LaurentNormalized D₀]
    (f : A)
    (hNoeth_B : IsNoetherianRing (presheafValue D₀))
    (hLocLift_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      HasLocLiftPowerBounded (presheafValue D₀))
    (hA₀Noeth_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      letI : IsNoetherianRing (presheafValue D₀) := hNoeth_B
      IsNoetherianRing ↥((presheafValue_pairOfDefinition_concrete P D₀).A₀))
    (hA_complete_B : @CompleteSpace (presheafValue D₀)
      (IsTopologicalAddGroup.rightUniformSpace (presheafValue D₀)))
    (hnoeth_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      IsNoetherianRing ↥(TateAlgebra.pairSubring
        (IsTateRing.principalPair (presheafValue D₀)).toPairOfDefinition))
    (hcont_forward_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      letI : HasLocLiftPowerBounded (presheafValue D₀) := hLocLift_B
      letI : IsNoetherianRing (presheafValue D₀) := hNoeth_B
      letI P_B : PairOfDefinition (presheafValue D₀) :=
        presheafValue_pairOfDefinition_concrete P D₀
      letI : IsNoetherianRing ↥P_B.A₀ := hA₀Noeth_B
      @Continuous _ _
        (quotientPlusFSubXIdealTopology (presheafValue D₀) (D₀.canonicalMap f))
        (inferInstance : TopologicalSpace (presheafValue
          (trivialPlusDatum (presheafValue D₀) P_B (D₀.canonicalMap f))))
        (example638Plus_forwardHom (presheafValue D₀) P_B (D₀.canonicalMap f)))
    (hcont_eval_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      let D : RationalLocData (presheafValue D₀) := iteratedMinusDatum_B P D₀ f
      ∀ hb : TopologicalRing.IsPowerBounded (invS D),
        @Continuous _ _
          (TateAlgebra.quotientOneSubfXIdealTopology D.s)
          (inferInstance : TopologicalSpace (presheafValue D))
          (tateQuotientToPresheafHom D hb))
    (τ_preBiv : presheafValue (laurentOverlapDatum D₀ f) ≃+*
      (↥(TateAlgebra₂ (presheafValue D₀)) ⧸
        TateAlgebra.bivariateOverlapIdeal (D₀.canonicalMap f)))
    (τ_alg : (↥(TateAlgebra₂ (presheafValue D₀)) ⧸
        TateAlgebra.bivariateOverlapIdeal (D₀.canonicalMap f)) ≃+*
      LaurentCover.B₁₂_gen (D₀.canonicalMap f))
    (h_plus_compat : ∀ uplus : presheafValue (laurentPlusDatum D₀ f),
      τ_alg (τ_preBiv (restrictionMap (laurentPlusDatum D₀ f)
              (laurentOverlapDatum D₀ f)
              (laurentOverlap_subset_plus D₀ f) uplus)) =
        LaurentCover.posLift (D₀.canonicalMap f)
          (laurentPlusBridge P D₀ f hNoeth_B hLocLift_B hA₀Noeth_B hA_complete_B
            hnoeth_B hcont_forward_B uplus))
    (h_minus_compat : ∀ uminus : presheafValue (laurentMinusDatum D₀ f),
      τ_alg (τ_preBiv (restrictionMap (laurentMinusDatum D₀ f)
              (laurentOverlapDatum D₀ f)
              (laurentOverlap_subset_minus D₀ f) uminus)) =
        LaurentCover.negLift (D₀.canonicalMap f)
          (laurentMinusBridge P D₀ f hnoeth_B hcont_eval_B uminus))
    (hplus : rationalOpen (laurentPlusDatum D₀ f).T (laurentPlusDatum D₀ f).s ⊆
      rationalOpen D₀.T D₀.s)
    (hminus : rationalOpen (laurentMinusDatum D₀ f).T (laurentMinusDatum D₀ f).s ⊆
      rationalOpen D₀.T D₀.s)
    (uplus : presheafValue (laurentPlusDatum D₀ f))
    (uminus : presheafValue (laurentMinusDatum D₀ f))
    (hcompat : ∀ (D₃ : RationalLocData A)
      (h₃p : rationalOpen D₃.T D₃.s ⊆
        rationalOpen (laurentPlusDatum D₀ f).T (laurentPlusDatum D₀ f).s)
      (h₃m : rationalOpen D₃.T D₃.s ⊆
        rationalOpen (laurentMinusDatum D₀ f).T (laurentMinusDatum D₀ f).s),
      restrictionMap (laurentPlusDatum D₀ f) D₃ h₃p uplus =
        restrictionMap (laurentMinusDatum D₀ f) D₃ h₃m uminus) :
    ∃ x : presheafValue D₀,
      restrictionMap D₀ (laurentPlusDatum D₀ f) hplus x = uplus ∧
      restrictionMap D₀ (laurentMinusDatum D₀ f) hminus x = uminus := by
  exact laurentCover_gluing_presheaf_viaRow3 D₀ f hplus hminus
    (laurentPlusBridge P D₀ f hNoeth_B hLocLift_B hA₀Noeth_B hA_complete_B
        hnoeth_B hcont_forward_B)
    (laurentMinusBridge P D₀ f hnoeth_B hcont_eval_B)
    (laurentPlusBridge_restrictionMap P D₀ f hNoeth_B hLocLift_B hA₀Noeth_B
        hA_complete_B hnoeth_B hcont_forward_B hplus)
    (laurentMinusBridge_restrictionMap P D₀ f hnoeth_B hcont_eval_B hminus)
    rfl
    uplus uminus
    (laurentBridge_delta_eq_zero_of_compat P D₀ f hNoeth_B hLocLift_B
      hA₀Noeth_B hA_complete_B hnoeth_B hcont_forward_B hcont_eval_B
      τ_preBiv τ_alg h_plus_compat h_minus_compat
      uplus uminus hcompat)

/-- **Two-piece Laurent restriction map: injectivity and continuity at presheaf
level** (T130 support result; embedding/inducing upgrade is blocked, see below).

For a Tate ring `A` and rational data `D₀`, the pair restriction map

```
ε_pres : presheafValue D₀ → presheafValue (laurentPlusDatum D₀ f) ×
                            presheafValue (laurentMinusDatum D₀ f),
  ε_pres x = (restrictionMap D₀ plus hplus x, restrictionMap D₀ minus hminus x)
```

is **injective and continuous** under the hypotheses below. These are the two
*basic* ingredients of `Topology.IsEmbedding`; the third — *inducing
topology* — is **not** proved here and is genuinely missing API at the
algebraic-Laurent-quotient level. See the "Inducing-topology blocker"
note at the end of this docstring.

The bridge-hypothesis style is the same as
`laurentCover_gluing_presheaf_viaRow3` (`τ_plus`, `τ_minus`, `htau_plus`,
`htau_minus`) — the τ's are RingEquivs that identify each
`presheafValue (laurentPlus/Minus)` algebraically with the corresponding
`B₁_gen / B₂_gen`. Continuity comes for free from
`restrictionMapHom_continuous`. Injectivity reduces — via the τ-bridges — to
`LaurentCover.epsilonHom_gen_injective` applied at `A := presheafValue D₀`,
`f := D₀.canonicalMap f`. That algebraic injectivity needs:

* `[IsNoetherianRing (presheafValue D₀)]` and `[IsDomain (presheafValue D₀)]`
  as presheafValue-level hypotheses (the `presheafValue` version of the
  ambient `[IsNoetherianRing A] [IsDomain A]` `section General` variables in
  `LaurentCoverExact.lean`); both are presheafValue-level conditions and hence
  do **not** add public `[CompleteSpace A]`, `[IsDomain A]`, or
  `D.s`-localization-base hypotheses to the outer `tateAcyclicity` boundary.
* `(hf_nonunit : ¬IsUnit (D₀.canonicalMap f))`, the standard non-unit
  side-condition of `epsilonHom_gen_injective` (Wedhorn 8.33 / Krull
  intersection on `Ideal.span {f}`).

## Inducing-topology blocker (T132 update)

Upgrading this support result to `Topology.IsEmbedding` requires showing
that the topology on `presheafValue D₀` equals the pullback topology from
the pair restriction map. T132
(`Adic spaces/LaurentCoverTopology.lean`, commit 53a4267) supplies the
**first half** of the previously-missing API:

* canonical `TopologicalSpace` instances on `LaurentCover.B₁_gen f`,
  `LaurentCover.B₂_gen f`, `LaurentCover.B₁₂_gen f` (quotient topology from
  the canonical `TateAlgebra A` / `LaurentTateAlgebra A` topologies);
* the supporting continuity API (`posIncl_continuous`, `negIncl_continuous`,
  `mkHom_continuous`, `posEmbHom_continuous`, `negEmbHom_continuous`,
  `posLift_continuous`, `negLift_continuous`,
  `deltaMap_gen_continuous`).

The companion T133 theorem `laurentCover_isEmbedding_presheaf` immediately
below packages the bridge-transport upgrade: given strict-exactness of the
algebraic Laurent diagonal `LaurentCover.epsilonHom_gen f` (i.e.,
`Topology.IsInducing (epsilonHom_gen f)` under the T132 quotient topologies)
together with the bridge homeomorphism conditions
`Topology.IsInducing τ_plus` and `Topology.IsInducing τ_minus`, the pair
restriction `ε_pres` is a topological embedding.

The single remaining algebraic-Laurent-level fact is therefore
`Topology.IsInducing (LaurentCover.epsilonHom_gen f)` — equivalently,
strict-exactness of the algebraic Laurent diagonal under the canonical
quotient topologies. The natural proof route uses
`AddMonoidHom.isOpenMap_of_complete_countable`
(`NoetherianTateModules.lean:158`) on the corestriction to
`range epsilonHom_gen = ker deltaMap_gen` (closed by
`deltaMap_gen_continuous` plus T2 of `B₁₂_gen f`), with completeness of
the source ring supplied by the Tate-ring framework. That step is the
next reusable algebraic-topology step beyond T132 and is not landed in
the present module.

The honest name of the prior support result is
`laurentCover_injective_continuous_presheaf` (see manager review of
T130). -/
theorem laurentCover_injective_continuous_presheaf
    [IsTateRing A] [IsNoetherianRing A] [T2Space A]
    [NonarchimedeanRing A]
    (D₀ : RationalLocData A) (f : A)
    (hf_nonunit : ¬IsUnit (D₀.canonicalMap f))
    (hNoeth_B : IsNoetherianRing (presheafValue D₀))
    (hDom_B : IsDomain (presheafValue D₀))
    (hplus : rationalOpen (laurentPlusDatum D₀ f).T (laurentPlusDatum D₀ f).s ⊆
      rationalOpen D₀.T D₀.s)
    (hminus : rationalOpen (laurentMinusDatum D₀ f).T (laurentMinusDatum D₀ f).s ⊆
      rationalOpen D₀.T D₀.s)
    (τ_plus : presheafValue (laurentPlusDatum D₀ f) ≃+*
      LaurentCover.B₁_gen (D₀.canonicalMap f))
    (τ_minus : presheafValue (laurentMinusDatum D₀ f) ≃+*
      LaurentCover.B₂_gen (D₀.canonicalMap f))
    (htau_plus : ∀ x : presheafValue D₀,
      τ_plus (restrictionMap D₀ (laurentPlusDatum D₀ f) hplus x) =
        (LaurentCover.epsilonHom_gen (D₀.canonicalMap f) x).1)
    (htau_minus : ∀ x : presheafValue D₀,
      τ_minus (restrictionMap D₀ (laurentMinusDatum D₀ f) hminus x) =
        (LaurentCover.epsilonHom_gen (D₀.canonicalMap f) x).2) :
    Function.Injective
      (fun x : presheafValue D₀ =>
        (restrictionMap D₀ (laurentPlusDatum D₀ f) hplus x,
         restrictionMap D₀ (laurentMinusDatum D₀ f) hminus x)) ∧
    Continuous
      (fun x : presheafValue D₀ =>
        (restrictionMap D₀ (laurentPlusDatum D₀ f) hplus x,
         restrictionMap D₀ (laurentMinusDatum D₀ f) hminus x)) := by
  letI := hNoeth_B
  letI := hDom_B
  refine ⟨?_, ?_⟩
  · -- Injectivity. Apply `epsilonHom_gen_injective` at `A := presheafValue D₀`,
    -- transported through `τ_plus, τ_minus` via `htau_plus, htau_minus`.
    intro x y hxy
    have hxy_plus : restrictionMap D₀ (laurentPlusDatum D₀ f) hplus x =
        restrictionMap D₀ (laurentPlusDatum D₀ f) hplus y :=
      (Prod.mk.injEq ..).mp hxy |>.1
    have hxy_minus : restrictionMap D₀ (laurentMinusDatum D₀ f) hminus x =
        restrictionMap D₀ (laurentMinusDatum D₀ f) hminus y :=
      (Prod.mk.injEq ..).mp hxy |>.2
    have hep_plus : (LaurentCover.epsilonHom_gen (D₀.canonicalMap f) x).1 =
        (LaurentCover.epsilonHom_gen (D₀.canonicalMap f) y).1 := by
      rw [← htau_plus x, ← htau_plus y, hxy_plus]
    have hep_minus : (LaurentCover.epsilonHom_gen (D₀.canonicalMap f) x).2 =
        (LaurentCover.epsilonHom_gen (D₀.canonicalMap f) y).2 := by
      rw [← htau_minus x, ← htau_minus y, hxy_minus]
    exact LaurentCover.epsilonHom_gen_injective (D₀.canonicalMap f) hf_nonunit
      (Prod.ext hep_plus hep_minus)
  · -- Continuity. Each component is `restrictionMapHom`, continuous by
    -- `restrictionMapHom_continuous`. The product map is then continuous via
    -- `Continuous.prodMk`.
    exact (restrictionMapHom_continuous D₀ (laurentPlusDatum D₀ f) hplus).prodMk
      (restrictionMapHom_continuous D₀ (laurentMinusDatum D₀ f) hminus)

/-- **Two-piece Laurent restriction map: topological embedding at presheaf level**
(T133 upgrade of `laurentCover_injective_continuous_presheaf`).

Strengthens the conjunction `Function.Injective ∧ Continuous` of
`laurentCover_injective_continuous_presheaf` to `Topology.IsEmbedding`
under three additional bridge-topology hypotheses:

* `hτ_plus_inducing`: the τ-bridge
  `presheafValue (laurentPlusDatum D₀ f) ≃+* B₁_gen (D₀.canonicalMap f)` is
  not only a ring iso but also induces the topology (i.e., it is a
  homeomorphism in addition to being a `RingEquiv`); concretely we ask for
  `Topology.IsInducing τ_plus.toFun`.
* `hτ_minus_inducing`: analogous for the minus bridge.
* `h_alg_inducing`: the algebraic Laurent diagonal
  `LaurentCover.epsilonHom_gen (D₀.canonicalMap f) :
    presheafValue D₀ → B₁_gen × B₂_gen`
  is a topological embedding (`Topology.IsInducing`) under the T132
  canonical quotient topologies on `B₁_gen` and `B₂_gen`.

The first two hypotheses are bridge-side strengthenings (the T130 bridges
were RingEquivs only). The third is the **first remaining
algebraic-Laurent-level fact** beyond T132: T132 supplies the canonical
topologies on `B₁_gen f`, `B₂_gen f`, `B₁₂_gen f`, plus
`deltaMap_gen_continuous`, but does not yet derive
`Topology.IsInducing epsilonHom_gen` itself, which would follow from a
Banach-OMT argument on the corestriction to
`range epsilonHom_gen = ker deltaMap_gen` (closed because
`deltaMap_gen` is continuous and `B₁₂_gen f` is T2 under the quotient
topology). That algebraic-level inducing fact is the next ticket. -/
theorem laurentCover_isEmbedding_presheaf
    [IsTateRing A] [IsNoetherianRing A] [T2Space A]
    [NonarchimedeanRing A]
    (D₀ : RationalLocData A) (f : A)
    (hf_nonunit : ¬IsUnit (D₀.canonicalMap f))
    (hNoeth_B : IsNoetherianRing (presheafValue D₀))
    (hDom_B : IsDomain (presheafValue D₀))
    (hTate_B : IsTateRing (presheafValue D₀))
    (hplus : rationalOpen (laurentPlusDatum D₀ f).T (laurentPlusDatum D₀ f).s ⊆
      rationalOpen D₀.T D₀.s)
    (hminus : rationalOpen (laurentMinusDatum D₀ f).T (laurentMinusDatum D₀ f).s ⊆
      rationalOpen D₀.T D₀.s)
    (τ_plus : presheafValue (laurentPlusDatum D₀ f) ≃+*
      LaurentCover.B₁_gen (D₀.canonicalMap f))
    (τ_minus : presheafValue (laurentMinusDatum D₀ f) ≃+*
      LaurentCover.B₂_gen (D₀.canonicalMap f))
    (htau_plus : ∀ x : presheafValue D₀,
      τ_plus (restrictionMap D₀ (laurentPlusDatum D₀ f) hplus x) =
        (LaurentCover.epsilonHom_gen (D₀.canonicalMap f) x).1)
    (htau_minus : ∀ x : presheafValue D₀,
      τ_minus (restrictionMap D₀ (laurentMinusDatum D₀ f) hminus x) =
        (LaurentCover.epsilonHom_gen (D₀.canonicalMap f) x).2)
    (hτ_plus_inducing : letI := hNoeth_B; letI := hDom_B; letI := hTate_B
      Topology.IsInducing
        (τ_plus :
          presheafValue (laurentPlusDatum D₀ f) →
            LaurentCover.B₁_gen (D₀.canonicalMap f)))
    (hτ_minus_inducing : letI := hNoeth_B; letI := hDom_B; letI := hTate_B
      Topology.IsInducing
        (τ_minus :
          presheafValue (laurentMinusDatum D₀ f) →
            LaurentCover.B₂_gen (D₀.canonicalMap f)))
    (h_alg_inducing : letI := hNoeth_B; letI := hDom_B; letI := hTate_B
      Topology.IsInducing
        (LaurentCover.epsilonHom_gen (D₀.canonicalMap f) :
          presheafValue D₀ →
            LaurentCover.B₁_gen (D₀.canonicalMap f) ×
              LaurentCover.B₂_gen (D₀.canonicalMap f))) :
    Topology.IsEmbedding
      (fun x : presheafValue D₀ =>
        (restrictionMap D₀ (laurentPlusDatum D₀ f) hplus x,
         restrictionMap D₀ (laurentMinusDatum D₀ f) hminus x)) := by
  letI := hNoeth_B
  letI := hDom_B
  letI := hTate_B
  -- Combine the existing injectivity / continuity result with the
  -- bridge-topology inputs to upgrade to `IsEmbedding`.
  obtain ⟨hpair_inj, hpair_cont⟩ :=
    laurentCover_injective_continuous_presheaf D₀ f hf_nonunit hNoeth_B hDom_B
      hplus hminus τ_plus τ_minus htau_plus htau_minus
  -- Define the pair restriction as a local function for clarity.
  set pair :
      presheafValue D₀ →
        presheafValue (laurentPlusDatum D₀ f) ×
          presheafValue (laurentMinusDatum D₀ f) :=
    fun x =>
      (restrictionMap D₀ (laurentPlusDatum D₀ f) hplus x,
       restrictionMap D₀ (laurentMinusDatum D₀ f) hminus x) with hpair_def
  -- The product map of the τ-bridges is inducing by `IsInducing.prodMap`.
  have hprod_ind :
      Topology.IsInducing
        (Prod.map
          (τ_plus :
            presheafValue (laurentPlusDatum D₀ f) →
              LaurentCover.B₁_gen (D₀.canonicalMap f))
          (τ_minus :
            presheafValue (laurentMinusDatum D₀ f) →
              LaurentCover.B₂_gen (D₀.canonicalMap f))) :=
    Topology.IsInducing.prodMap hτ_plus_inducing hτ_minus_inducing
  -- The composition `Prod.map τ_plus τ_minus ∘ pair` equals
  -- `epsilonHom_gen` extensionally, by `htau_plus` and `htau_minus`.
  have hcomp_eq :
      (Prod.map
          (τ_plus :
            presheafValue (laurentPlusDatum D₀ f) →
              LaurentCover.B₁_gen (D₀.canonicalMap f))
          (τ_minus :
            presheafValue (laurentMinusDatum D₀ f) →
              LaurentCover.B₂_gen (D₀.canonicalMap f))) ∘ pair =
        ⇑(LaurentCover.epsilonHom_gen (D₀.canonicalMap f)) := by
    funext x
    rw [hpair_def]
    show (τ_plus _, τ_minus _) =
      LaurentCover.epsilonHom_gen (D₀.canonicalMap f) x
    apply Prod.ext
    · exact htau_plus x
    · exact htau_minus x
  -- Hence the composition is `IsInducing` (transported from `h_alg_inducing`).
  have hcomp_ind :
      Topology.IsInducing
        ((Prod.map
            (τ_plus :
              presheafValue (laurentPlusDatum D₀ f) →
                LaurentCover.B₁_gen (D₀.canonicalMap f))
            (τ_minus :
              presheafValue (laurentMinusDatum D₀ f) →
                LaurentCover.B₂_gen (D₀.canonicalMap f))) ∘ pair) := by
    rw [hcomp_eq]; exact h_alg_inducing
  -- Cancel the outer `Prod.map (τ_plus, τ_minus)` (which is `IsInducing`)
  -- to obtain `IsInducing pair`.
  have hpair_cont' : Continuous pair := hpair_cont
  have hprod_cont :
      Continuous
        (Prod.map
          (τ_plus :
            presheafValue (laurentPlusDatum D₀ f) →
              LaurentCover.B₁_gen (D₀.canonicalMap f))
          (τ_minus :
            presheafValue (laurentMinusDatum D₀ f) →
              LaurentCover.B₂_gen (D₀.canonicalMap f))) :=
    hτ_plus_inducing.continuous.prodMap hτ_minus_inducing.continuous
  have hpair_ind : Topology.IsInducing pair :=
    Topology.IsInducing.of_comp hpair_cont' hprod_cont hcomp_ind
  -- Combine with injectivity to get `IsEmbedding`.
  exact ⟨hpair_ind, hpair_inj⟩

/-- **T141: Two-piece Laurent restriction map is a topological embedding,
with the algebraic-Laurent-level inducing hypothesis discharged.**

Specialization of `laurentCover_isEmbedding_presheaf` (T133) that consumes the
T140 algebraic-Laurent-level inducing theorem
`LaurentCover.epsilonHom_gen_inducing_of_complete`. The `h_alg_inducing`
hypothesis of T133 is replaced by the source-side Banach OMT prerequisites
on `presheafValue D₀` plus the closed-ideal infrastructure (univariate +
bivariate noetherian pair-subring hypotheses) that T140 needs underneath.

The presheafValue side already supplies the following automatically (so
they do *not* appear as explicit hypotheses): `CommRing`, `TopologicalSpace`,
`UniformSpace`, `IsTopologicalRing`, `IsUniformAddGroup`, `CompleteSpace`,
`T0Space`, `T2Space` (`presheafValueT2Space`), and `NonarchimedeanRing`
(`presheafValueNonarchimedeanRing`, requiring the public `[NonarchimedeanRing A]`).

The remaining presheafValue-side hypotheses are:

* `hSigCp_B : SigmaCompactSpace (presheafValue D₀)` — required by the Banach
  open-mapping theorem on `presheafValue D₀`.
* `hA_complete_B` — completeness of `presheafValue D₀` w.r.t. its
  `IsTopologicalAddGroup.rightUniformSpace` (the same form used by the
  `tateAlgebra_isClosed_ideal` infrastructure).
* `hnoeth_B`, `hnoeth₂_B` — noetherianity of the canonical univariate /
  bivariate pair-subrings of the presheafValue Tate ring; these feed the
  closed-ideal lemmas underlying the T2 supports `B₁₂_gen_t2Space` and
  `B₁_gen_x_B₂_gen_t2Space` consumed by T140.

The bridge hypotheses (`τ_plus`, `τ_minus`, `htau_plus`, `htau_minus`,
`hτ_plus_inducing`, `hτ_minus_inducing`) are unchanged from T133.

This is the strongest consumer-facing form of the T130 strict-exactness
theorem available without further upstream work. The next reusable step
beyond this would be to derive the bridge inducing hypotheses
`hτ_plus_inducing` and `hτ_minus_inducing` from the `presheafValueCanonicalQuotientEquiv`
construction in `TopologyComparison.lean`, eliminating the τ-level
hypotheses entirely. -/
theorem laurentCover_isEmbedding_presheaf_of_complete
    [IsTateRing A] [IsNoetherianRing A] [T2Space A]
    [NonarchimedeanRing A]
    (D₀ : RationalLocData A) (f : A)
    (hf_nonunit : ¬IsUnit (D₀.canonicalMap f))
    (hNoeth_B : IsNoetherianRing (presheafValue D₀))
    (hDom_B : IsDomain (presheafValue D₀))
    (hTate_B : IsTateRing (presheafValue D₀))
    (hSigCp_B : SigmaCompactSpace (presheafValue D₀))
    (hA_complete_B : @CompleteSpace (presheafValue D₀)
      (IsTopologicalAddGroup.rightUniformSpace (presheafValue D₀)))
    (hnoeth_B : letI := hTate_B
      IsNoetherianRing
        ↥(TateAlgebra.pairSubring
            (IsTateRing.principalPair (presheafValue D₀)).toPairOfDefinition))
    (hnoeth₂_B : letI := hTate_B
      IsNoetherianRing
        ↥(TateAlgebra.pairSubring₂
            (IsTateRing.principalPair (presheafValue D₀)).toPairOfDefinition))
    (hplus : rationalOpen (laurentPlusDatum D₀ f).T (laurentPlusDatum D₀ f).s ⊆
      rationalOpen D₀.T D₀.s)
    (hminus : rationalOpen (laurentMinusDatum D₀ f).T (laurentMinusDatum D₀ f).s ⊆
      rationalOpen D₀.T D₀.s)
    (τ_plus : presheafValue (laurentPlusDatum D₀ f) ≃+*
      LaurentCover.B₁_gen (D₀.canonicalMap f))
    (τ_minus : presheafValue (laurentMinusDatum D₀ f) ≃+*
      LaurentCover.B₂_gen (D₀.canonicalMap f))
    (htau_plus : ∀ x : presheafValue D₀,
      τ_plus (restrictionMap D₀ (laurentPlusDatum D₀ f) hplus x) =
        (LaurentCover.epsilonHom_gen (D₀.canonicalMap f) x).1)
    (htau_minus : ∀ x : presheafValue D₀,
      τ_minus (restrictionMap D₀ (laurentMinusDatum D₀ f) hminus x) =
        (LaurentCover.epsilonHom_gen (D₀.canonicalMap f) x).2)
    (hτ_plus_inducing : letI := hNoeth_B; letI := hDom_B; letI := hTate_B
      Topology.IsInducing
        (τ_plus :
          presheafValue (laurentPlusDatum D₀ f) →
            LaurentCover.B₁_gen (D₀.canonicalMap f)))
    (hτ_minus_inducing : letI := hNoeth_B; letI := hDom_B; letI := hTate_B
      Topology.IsInducing
        (τ_minus :
          presheafValue (laurentMinusDatum D₀ f) →
            LaurentCover.B₂_gen (D₀.canonicalMap f))) :
    Topology.IsEmbedding
      (fun x : presheafValue D₀ =>
        (restrictionMap D₀ (laurentPlusDatum D₀ f) hplus x,
         restrictionMap D₀ (laurentMinusDatum D₀ f) hminus x)) := by
  letI := hNoeth_B
  letI := hDom_B
  letI := hTate_B
  letI := hSigCp_B
  -- T140 produces the algebraic-Laurent-level inducing under the source-side
  -- Banach OMT prerequisites at `A := presheafValue D₀`. The topology
  -- equality `htop` is `rfl` because the canonical `TopologicalSpace
  -- (presheafValue D₀)` instance is defined as `UniformSpace.toTopologicalSpace`
  -- of the canonical `UniformSpace (presheafValue D₀)` instance.
  have h_alg_inducing :
      Topology.IsInducing
        (LaurentCover.epsilonHom_gen (D₀.canonicalMap f) :
          presheafValue D₀ →
            LaurentCover.B₁_gen (D₀.canonicalMap f) ×
              LaurentCover.B₂_gen (D₀.canonicalMap f)) :=
    LaurentCover.epsilonHom_gen_inducing_of_complete (D₀.canonicalMap f) rfl
      hf_nonunit hA_complete_B hnoeth_B hnoeth₂_B
  exact laurentCover_isEmbedding_presheaf D₀ f hf_nonunit hNoeth_B hDom_B
    hTate_B hplus hminus τ_plus τ_minus htau_plus htau_minus
    hτ_plus_inducing hτ_minus_inducing h_alg_inducing

/-- **T147 consumer wrapper: two-piece Laurent restriction map is a topological
embedding, with the τ-bridges supplied by `laurentPlusBridge` /
`laurentMinusBridge`.**

Specialization of `laurentCover_isEmbedding_presheaf_of_complete` (T141)
with `τ_plus := laurentPlusBridge ...`, `τ_minus := laurentMinusBridge ...`.
The `htau_plus` / `htau_minus` hypotheses of T141 are discharged by the
existing `laurentPlusBridge_restrictionMap` / `laurentMinusBridge_restrictionMap`
theorems; the `hτ_plus_inducing` / `hτ_minus_inducing` hypotheses are
discharged by the new T147 `laurentPlusBridge_isInducing` /
`laurentMinusBridge_isInducing`.

The hypothesis surface is the union of T141's source-side hypotheses
(without the τ-bridges and their two compatibility / inducing inputs)
and the bridge construction / discharge hypotheses needed by the T147
inducing theorems. -/
theorem laurentCover_isEmbedding_presheaf_via_bridges
    [IsTateRing A] [IsNoetherianRing A] [T2Space A]
    [NonarchimedeanRing A]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (D₀ : RationalLocData A) [IsNoetherianRing (locSubring D₀.P D₀.T D₀.s)]
    [LaurentNormalized D₀]
    (f : A)
    (hf_nonunit : ¬IsUnit (D₀.canonicalMap f))
    (hNoeth_B : IsNoetherianRing (presheafValue D₀))
    (hDom_B : IsDomain (presheafValue D₀))
    (hSigCp_B : SigmaCompactSpace (presheafValue D₀))
    (hA_complete_B : @CompleteSpace (presheafValue D₀)
      (IsTopologicalAddGroup.rightUniformSpace (presheafValue D₀)))
    (hnoeth_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      IsNoetherianRing
        ↥(TateAlgebra.pairSubring
            (IsTateRing.principalPair (presheafValue D₀)).toPairOfDefinition))
    (hnoeth₂_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      IsNoetherianRing
        ↥(TateAlgebra.pairSubring₂
            (IsTateRing.principalPair (presheafValue D₀)).toPairOfDefinition))
    (hLocLift_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      HasLocLiftPowerBounded (presheafValue D₀))
    (hA₀Noeth_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      letI : IsNoetherianRing (presheafValue D₀) := hNoeth_B
      IsNoetherianRing ↥((presheafValue_pairOfDefinition_concrete P D₀).A₀))
    (hcont_forward_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      letI : HasLocLiftPowerBounded (presheafValue D₀) := hLocLift_B
      letI : IsNoetherianRing (presheafValue D₀) := hNoeth_B
      letI P_B : PairOfDefinition (presheafValue D₀) :=
        presheafValue_pairOfDefinition_concrete P D₀
      letI : IsNoetherianRing ↥P_B.A₀ := hA₀Noeth_B
      @Continuous _ _
        (quotientPlusFSubXIdealTopology (presheafValue D₀) (D₀.canonicalMap f))
        (inferInstance : TopologicalSpace (presheafValue
          (trivialPlusDatum (presheafValue D₀) P_B (D₀.canonicalMap f))))
        (example638Plus_forwardHom (presheafValue D₀) P_B (D₀.canonicalMap f)))
    (hcont_eval_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      let D : RationalLocData (presheafValue D₀) := iteratedMinusDatum_B P D₀ f
      ∀ hb : TopologicalRing.IsPowerBounded (invS D),
        @Continuous _ _
          (TateAlgebra.quotientOneSubfXIdealTopology D.s)
          (inferInstance : TopologicalSpace (presheafValue D))
          (tateQuotientToPresheafHom D hb))
    (hBaire_plus_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      letI : IsNoetherianRing (presheafValue D₀) := hNoeth_B
      letI : HasLocLiftPowerBounded (presheafValue D₀) := hLocLift_B
      letI P_B : PairOfDefinition (presheafValue D₀) :=
        presheafValue_pairOfDefinition_concrete P D₀
      @BaireSpace
        (presheafValue
          (trivialPlusDatum (presheafValue D₀) P_B (D₀.canonicalMap f))) _)
    (hSigma_plus_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      @SigmaCompactSpace
        (↥(TateAlgebra (presheafValue D₀)) ⧸
          plusFSubXIdeal (presheafValue D₀) (D₀.canonicalMap f))
        (quotientPlusFSubXIdealTopology (presheafValue D₀)
          (D₀.canonicalMap f)))
    (hBaire_minus_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      @BaireSpace (presheafValue (iteratedMinusDatum_B P D₀ f)) _)
    (hSigma_minus_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      @SigmaCompactSpace
        (↥(TateAlgebra (presheafValue D₀)) ⧸
          TateAlgebra.oneSubfXIdeal (iteratedMinusDatum_B P D₀ f).s)
        (TateAlgebra.quotientOneSubfXIdealTopology
          (iteratedMinusDatum_B P D₀ f).s))
    (hplus : rationalOpen (laurentPlusDatum D₀ f).T (laurentPlusDatum D₀ f).s ⊆
      rationalOpen D₀.T D₀.s)
    (hminus : rationalOpen (laurentMinusDatum D₀ f).T (laurentMinusDatum D₀ f).s ⊆
      rationalOpen D₀.T D₀.s) :
    Topology.IsEmbedding
      (fun x : presheafValue D₀ =>
        (restrictionMap D₀ (laurentPlusDatum D₀ f) hplus x,
         restrictionMap D₀ (laurentMinusDatum D₀ f) hminus x)) := by
  haveI hTate_B : IsTateRing (presheafValue D₀) := presheafValue_isTateRing P D₀
  -- Build the bridges and discharge T141's six τ-side hypotheses.
  exact laurentCover_isEmbedding_presheaf_of_complete D₀ f hf_nonunit
    hNoeth_B hDom_B hTate_B hSigCp_B hA_complete_B hnoeth_B hnoeth₂_B
    hplus hminus
    (laurentPlusBridge P D₀ f hNoeth_B hLocLift_B hA₀Noeth_B hA_complete_B
      hnoeth_B hcont_forward_B)
    (laurentMinusBridge P D₀ f hnoeth_B hcont_eval_B)
    (laurentPlusBridge_restrictionMap P D₀ f hNoeth_B hLocLift_B hA₀Noeth_B
      hA_complete_B hnoeth_B hcont_forward_B hplus)
    (laurentMinusBridge_restrictionMap P D₀ f hnoeth_B hcont_eval_B hminus)
    (laurentPlusBridge_isInducing P D₀ f hNoeth_B hDom_B hLocLift_B
      hA₀Noeth_B hA_complete_B hnoeth_B hcont_forward_B hBaire_plus_B
      hSigma_plus_B)
    (laurentMinusBridge_isInducing P D₀ f hNoeth_B hDom_B hnoeth_B
      hcont_eval_B hBaire_minus_B hSigma_minus_B)

/-- **T149 consumer wrapper: T147's `via_bridges` with the two Baire hypotheses
discharged automatically.**

Specialization of `laurentCover_isEmbedding_presheaf_via_bridges` (T147)
that uses the new T149 `presheafValue_baireSpace` supplier to discharge
both `hBaire_plus_B` and `hBaire_minus_B`. The two `SigmaCompactSpace`
hypotheses on the source TateAlgebra quotients remain explicit because
TateAlgebras over a non-locally-compact base ring are not generally
sigma compact (this is the genuine Banach-OMT side-condition that
Mathlib's `MonoidHom.isOpenMap_of_sigmaCompact` cannot avoid). -/
theorem laurentCover_isEmbedding_presheaf_via_bridges_baire_auto
    [IsTateRing A] [IsNoetherianRing A] [T2Space A]
    [NonarchimedeanRing A]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (D₀ : RationalLocData A) [IsNoetherianRing (locSubring D₀.P D₀.T D₀.s)]
    [LaurentNormalized D₀]
    (f : A)
    (hf_nonunit : ¬IsUnit (D₀.canonicalMap f))
    (hNoeth_B : IsNoetherianRing (presheafValue D₀))
    (hDom_B : IsDomain (presheafValue D₀))
    (hSigCp_B : SigmaCompactSpace (presheafValue D₀))
    (hA_complete_B : @CompleteSpace (presheafValue D₀)
      (IsTopologicalAddGroup.rightUniformSpace (presheafValue D₀)))
    (hnoeth_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      IsNoetherianRing
        ↥(TateAlgebra.pairSubring
            (IsTateRing.principalPair (presheafValue D₀)).toPairOfDefinition))
    (hnoeth₂_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      IsNoetherianRing
        ↥(TateAlgebra.pairSubring₂
            (IsTateRing.principalPair (presheafValue D₀)).toPairOfDefinition))
    (hLocLift_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      HasLocLiftPowerBounded (presheafValue D₀))
    (hA₀Noeth_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      letI : IsNoetherianRing (presheafValue D₀) := hNoeth_B
      IsNoetherianRing ↥((presheafValue_pairOfDefinition_concrete P D₀).A₀))
    (hcont_forward_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      letI : HasLocLiftPowerBounded (presheafValue D₀) := hLocLift_B
      letI : IsNoetherianRing (presheafValue D₀) := hNoeth_B
      letI P_B : PairOfDefinition (presheafValue D₀) :=
        presheafValue_pairOfDefinition_concrete P D₀
      letI : IsNoetherianRing ↥P_B.A₀ := hA₀Noeth_B
      @Continuous _ _
        (quotientPlusFSubXIdealTopology (presheafValue D₀) (D₀.canonicalMap f))
        (inferInstance : TopologicalSpace (presheafValue
          (trivialPlusDatum (presheafValue D₀) P_B (D₀.canonicalMap f))))
        (example638Plus_forwardHom (presheafValue D₀) P_B (D₀.canonicalMap f)))
    (hcont_eval_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      let D : RationalLocData (presheafValue D₀) := iteratedMinusDatum_B P D₀ f
      ∀ hb : TopologicalRing.IsPowerBounded (invS D),
        @Continuous _ _
          (TateAlgebra.quotientOneSubfXIdealTopology D.s)
          (inferInstance : TopologicalSpace (presheafValue D))
          (tateQuotientToPresheafHom D hb))
    (hSigma_plus_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      @SigmaCompactSpace
        (↥(TateAlgebra (presheafValue D₀)) ⧸
          plusFSubXIdeal (presheafValue D₀) (D₀.canonicalMap f))
        (quotientPlusFSubXIdealTopology (presheafValue D₀)
          (D₀.canonicalMap f)))
    (hSigma_minus_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      @SigmaCompactSpace
        (↥(TateAlgebra (presheafValue D₀)) ⧸
          TateAlgebra.oneSubfXIdeal (iteratedMinusDatum_B P D₀ f).s)
        (TateAlgebra.quotientOneSubfXIdealTopology
          (iteratedMinusDatum_B P D₀ f).s))
    (hplus : rationalOpen (laurentPlusDatum D₀ f).T (laurentPlusDatum D₀ f).s ⊆
      rationalOpen D₀.T D₀.s)
    (hminus : rationalOpen (laurentMinusDatum D₀ f).T (laurentMinusDatum D₀ f).s ⊆
      rationalOpen D₀.T D₀.s) :
    Topology.IsEmbedding
      (fun x : presheafValue D₀ =>
        (restrictionMap D₀ (laurentPlusDatum D₀ f) hplus x,
         restrictionMap D₀ (laurentMinusDatum D₀ f) hminus x)) := by
  haveI : IsTateRing (presheafValue D₀) := presheafValue_isTateRing P D₀
  haveI : IsNoetherianRing (presheafValue D₀) := hNoeth_B
  haveI : HasLocLiftPowerBounded (presheafValue D₀) := hLocLift_B
  letI P_B : PairOfDefinition (presheafValue D₀) :=
    presheafValue_pairOfDefinition_concrete P D₀
  -- Discharge the two Baire hypotheses via the T149 generic supplier.
  have hBaire_plus_B :
      @BaireSpace
        (presheafValue
          (trivialPlusDatum (presheafValue D₀) P_B (D₀.canonicalMap f))) _ :=
    presheafValue_baireSpace
      (trivialPlusDatum (presheafValue D₀) P_B (D₀.canonicalMap f))
  have hBaire_minus_B :
      @BaireSpace (presheafValue (iteratedMinusDatum_B P D₀ f)) _ :=
    presheafValue_baireSpace (iteratedMinusDatum_B P D₀ f)
  exact laurentCover_isEmbedding_presheaf_via_bridges P D₀ f hf_nonunit
    hNoeth_B hDom_B hSigCp_B hA_complete_B hnoeth_B hnoeth₂_B
    hLocLift_B hA₀Noeth_B hcont_forward_B hcont_eval_B
    hBaire_plus_B hSigma_plus_B hBaire_minus_B hSigma_minus_B
    hplus hminus

/-- **T152 consumer wrapper: T149's `_baire_auto` with both quotient
SigmaCompactSpace hypotheses consolidated into one source-level
`SigmaCompactSpace ↥(TateAlgebra (presheafValue D₀))` hypothesis.**

Specialization of `laurentCover_isEmbedding_presheaf_via_bridges_baire_auto`
(T149) using the new T152 transport suppliers
`quotientPlusFSubXIdeal_sigmaCompactSpace_of_source` and
`quotientOneSubfXIdeal_sigmaCompactSpace_of_source`. The two quotient-level
SigmaCompactSpace hypotheses are derived inside the proof body from the
single source-level hypothesis via the canonical quotient map (continuous +
surjective, transports σ-compactness).

The remaining `SigmaCompactSpace ↥(TateAlgebra (presheafValue D₀))` hypothesis
is genuinely required: see the T152 route-decision documentation block
above (after `presheafValue_baireSpace`) for the mathematical reason it
cannot be discharged generically and the scope-restriction options
available to consumers (`[CompactSpace ↥(pairSubring P)]` /
`[LocallyCompactSpace A]`). -/
theorem laurentCover_isEmbedding_presheaf_via_bridges_baire_quotientSigma_auto
    [IsTateRing A] [IsNoetherianRing A] [T2Space A]
    [NonarchimedeanRing A]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (D₀ : RationalLocData A) [IsNoetherianRing (locSubring D₀.P D₀.T D₀.s)]
    [LaurentNormalized D₀]
    (f : A)
    (hf_nonunit : ¬IsUnit (D₀.canonicalMap f))
    (hNoeth_B : IsNoetherianRing (presheafValue D₀))
    (hDom_B : IsDomain (presheafValue D₀))
    (hSigCp_B : SigmaCompactSpace (presheafValue D₀))
    (hA_complete_B : @CompleteSpace (presheafValue D₀)
      (IsTopologicalAddGroup.rightUniformSpace (presheafValue D₀)))
    (hnoeth_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      IsNoetherianRing
        ↥(TateAlgebra.pairSubring
            (IsTateRing.principalPair (presheafValue D₀)).toPairOfDefinition))
    (hnoeth₂_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      IsNoetherianRing
        ↥(TateAlgebra.pairSubring₂
            (IsTateRing.principalPair (presheafValue D₀)).toPairOfDefinition))
    (hLocLift_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      HasLocLiftPowerBounded (presheafValue D₀))
    (hA₀Noeth_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      letI : IsNoetherianRing (presheafValue D₀) := hNoeth_B
      IsNoetherianRing ↥((presheafValue_pairOfDefinition_concrete P D₀).A₀))
    (hcont_forward_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      letI : HasLocLiftPowerBounded (presheafValue D₀) := hLocLift_B
      letI : IsNoetherianRing (presheafValue D₀) := hNoeth_B
      letI P_B : PairOfDefinition (presheafValue D₀) :=
        presheafValue_pairOfDefinition_concrete P D₀
      letI : IsNoetherianRing ↥P_B.A₀ := hA₀Noeth_B
      @Continuous _ _
        (quotientPlusFSubXIdealTopology (presheafValue D₀) (D₀.canonicalMap f))
        (inferInstance : TopologicalSpace (presheafValue
          (trivialPlusDatum (presheafValue D₀) P_B (D₀.canonicalMap f))))
        (example638Plus_forwardHom (presheafValue D₀) P_B (D₀.canonicalMap f)))
    (hcont_eval_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      let D : RationalLocData (presheafValue D₀) := iteratedMinusDatum_B P D₀ f
      ∀ hb : TopologicalRing.IsPowerBounded (invS D),
        @Continuous _ _
          (TateAlgebra.quotientOneSubfXIdealTopology D.s)
          (inferInstance : TopologicalSpace (presheafValue D))
          (tateQuotientToPresheafHom D hb))
    (hSigCp_TA : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      SigmaCompactSpace ↥(TateAlgebra (presheafValue D₀)))
    (hplus : rationalOpen (laurentPlusDatum D₀ f).T (laurentPlusDatum D₀ f).s ⊆
      rationalOpen D₀.T D₀.s)
    (hminus : rationalOpen (laurentMinusDatum D₀ f).T (laurentMinusDatum D₀ f).s ⊆
      rationalOpen D₀.T D₀.s) :
    Topology.IsEmbedding
      (fun x : presheafValue D₀ =>
        (restrictionMap D₀ (laurentPlusDatum D₀ f) hplus x,
         restrictionMap D₀ (laurentMinusDatum D₀ f) hminus x)) := by
  haveI : IsTateRing (presheafValue D₀) := presheafValue_isTateRing P D₀
  haveI : IsNoetherianRing (presheafValue D₀) := hNoeth_B
  haveI : IsDomain (presheafValue D₀) := hDom_B
  -- Discharge the two quotient SigmaCompactSpace hypotheses via the T152
  -- transport suppliers (continuous-surjective image of σ-compact is σ-compact).
  have hSigma_plus_B :
      @SigmaCompactSpace
        (↥(TateAlgebra (presheafValue D₀)) ⧸
          plusFSubXIdeal (presheafValue D₀) (D₀.canonicalMap f))
        (quotientPlusFSubXIdealTopology (presheafValue D₀)
          (D₀.canonicalMap f)) :=
    quotientPlusFSubXIdeal_sigmaCompactSpace_of_source (D₀.canonicalMap f)
      hSigCp_TA
  have hSigma_minus_B :
      @SigmaCompactSpace
        (↥(TateAlgebra (presheafValue D₀)) ⧸
          TateAlgebra.oneSubfXIdeal (iteratedMinusDatum_B P D₀ f).s)
        (TateAlgebra.quotientOneSubfXIdealTopology
          (iteratedMinusDatum_B P D₀ f).s) :=
    quotientOneSubfXIdeal_sigmaCompactSpace_of_source
      (iteratedMinusDatum_B P D₀ f).s hSigCp_TA
  exact laurentCover_isEmbedding_presheaf_via_bridges_baire_auto P D₀ f
    hf_nonunit hNoeth_B hDom_B hSigCp_B hA_complete_B hnoeth_B hnoeth₂_B
    hLocLift_B hA₀Noeth_B hcont_forward_B hcont_eval_B
    hSigma_plus_B hSigma_minus_B hplus hminus

/-- Laurent cover gluing on presheaf values (Wedhorn Lemma 8.33, presheaf level).

Delegates to `laurentCover_gluing_presheaf_viaBridges` — the Route B path
through the five named bridge stubs. Avoids the Baire-category blocker
(`restrictionMapHom_surj`) that the algebraic-core Route A would need.

The `hnoeth_B` and `hcont_eval_B` hypotheses are passed through from the
bridges (Phase 2.5c / Phase 2.6 infrastructure at `B := presheafValue D₀`). -/
theorem laurentCover_gluing_presheaf
    [IsTateRing A] [IsNoetherianRing A] [T2Space A]
    [NonarchimedeanRing A]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (D₀ : RationalLocData A) [IsNoetherianRing (locSubring D₀.P D₀.T D₀.s)]
    [LaurentNormalized D₀]
    (f : A)
    (hNoeth_B : IsNoetherianRing (presheafValue D₀))
    (hLocLift_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      HasLocLiftPowerBounded (presheafValue D₀))
    (hA₀Noeth_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      letI : IsNoetherianRing (presheafValue D₀) := hNoeth_B
      IsNoetherianRing ↥((presheafValue_pairOfDefinition_concrete P D₀).A₀))
    (hA_complete_B : @CompleteSpace (presheafValue D₀)
      (IsTopologicalAddGroup.rightUniformSpace (presheafValue D₀)))
    (hnoeth_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      IsNoetherianRing ↥(TateAlgebra.pairSubring
        (IsTateRing.principalPair (presheafValue D₀)).toPairOfDefinition))
    (hcont_forward_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      letI : HasLocLiftPowerBounded (presheafValue D₀) := hLocLift_B
      letI : IsNoetherianRing (presheafValue D₀) := hNoeth_B
      letI P_B : PairOfDefinition (presheafValue D₀) :=
        presheafValue_pairOfDefinition_concrete P D₀
      letI : IsNoetherianRing ↥P_B.A₀ := hA₀Noeth_B
      @Continuous _ _
        (quotientPlusFSubXIdealTopology (presheafValue D₀) (D₀.canonicalMap f))
        (inferInstance : TopologicalSpace (presheafValue
          (trivialPlusDatum (presheafValue D₀) P_B (D₀.canonicalMap f))))
        (example638Plus_forwardHom (presheafValue D₀) P_B (D₀.canonicalMap f)))
    (hcont_eval_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      let D : RationalLocData (presheafValue D₀) := iteratedMinusDatum_B P D₀ f
      ∀ hb : TopologicalRing.IsPowerBounded (invS D),
        @Continuous _ _
          (TateAlgebra.quotientOneSubfXIdealTopology D.s)
          (inferInstance : TopologicalSpace (presheafValue D))
          (tateQuotientToPresheafHom D hb))
    (τ_preBiv : presheafValue (laurentOverlapDatum D₀ f) ≃+*
      (↥(TateAlgebra₂ (presheafValue D₀)) ⧸
        TateAlgebra.bivariateOverlapIdeal (D₀.canonicalMap f)))
    (τ_alg : (↥(TateAlgebra₂ (presheafValue D₀)) ⧸
        TateAlgebra.bivariateOverlapIdeal (D₀.canonicalMap f)) ≃+*
      LaurentCover.B₁₂_gen (D₀.canonicalMap f))
    (h_plus_compat : ∀ uplus : presheafValue (laurentPlusDatum D₀ f),
      τ_alg (τ_preBiv (restrictionMap (laurentPlusDatum D₀ f)
              (laurentOverlapDatum D₀ f)
              (laurentOverlap_subset_plus D₀ f) uplus)) =
        LaurentCover.posLift (D₀.canonicalMap f)
          (laurentPlusBridge P D₀ f hNoeth_B hLocLift_B hA₀Noeth_B hA_complete_B
            hnoeth_B hcont_forward_B uplus))
    (h_minus_compat : ∀ uminus : presheafValue (laurentMinusDatum D₀ f),
      τ_alg (τ_preBiv (restrictionMap (laurentMinusDatum D₀ f)
              (laurentOverlapDatum D₀ f)
              (laurentOverlap_subset_minus D₀ f) uminus)) =
        LaurentCover.negLift (D₀.canonicalMap f)
          (laurentMinusBridge P D₀ f hnoeth_B hcont_eval_B uminus))
    (hplus : rationalOpen (laurentPlusDatum D₀ f).T (laurentPlusDatum D₀ f).s ⊆
      rationalOpen D₀.T D₀.s)
    (hminus : rationalOpen (laurentMinusDatum D₀ f).T (laurentMinusDatum D₀ f).s ⊆
      rationalOpen D₀.T D₀.s)
    (uplus : presheafValue (laurentPlusDatum D₀ f))
    (uminus : presheafValue (laurentMinusDatum D₀ f))
    (hcompat : ∀ (D₃ : RationalLocData A)
      (h₃p : rationalOpen D₃.T D₃.s ⊆
        rationalOpen (laurentPlusDatum D₀ f).T (laurentPlusDatum D₀ f).s)
      (h₃m : rationalOpen D₃.T D₃.s ⊆
        rationalOpen (laurentMinusDatum D₀ f).T (laurentMinusDatum D₀ f).s),
      restrictionMap (laurentPlusDatum D₀ f) D₃ h₃p uplus =
        restrictionMap (laurentMinusDatum D₀ f) D₃ h₃m uminus) :
    ∃ x : presheafValue D₀,
      restrictionMap D₀ (laurentPlusDatum D₀ f) hplus x = uplus ∧
      restrictionMap D₀ (laurentMinusDatum D₀ f) hminus x = uminus :=
  laurentCover_gluing_presheaf_viaBridges P D₀ f hNoeth_B hLocLift_B
    hA₀Noeth_B hA_complete_B hnoeth_B hcont_forward_B hcont_eval_B
    τ_preBiv τ_alg h_plus_compat h_minus_compat
    hplus hminus uplus uminus hcompat

/-! ### Downstream Lane-C consumer tower: gluing from an explicit compatible bridge

The existing `laurentBridge_delta_eq_zero_of_compat` and
`laurentCover_gluing_presheaf_viaBridges` / `laurentCover_gluing_presheaf`
above all route through `laurentOverlapBridge_exists_compatible`
(LaurentRefinement.lean:3124, currently `sorry`, Lane-A target). Until
Lane A supplies that existence witness, downstream Lane-C consumers
wishing to invoke gluing cannot compile via the standard chain.

The theorems below **take the compatible overlap bridge as an explicit
hypothesis** `(τ₁₂, hcompat_bridge)` and discharge gluing **without**
routing through the Lane-A sorry. Intended for Lane C callers that have
independently obtained — or will downstream-supply — a compatible bridge
witness. Once Primary's Lane-A work closes
`laurentOverlapBridge_exists_compatible`, these become dischargeable
unconditionally by plugging Lane-A's existential unpacking.

**Caller tower** (in increasing level of abstraction; each uses the one
below, all accept the same single upstream witness `(τ₁₂, hcompat_bridge)`):

| Abstraction level | Theorem | Conclusion |
|---|---|---|
| algebraic δ | `laurentBridge_delta_eq_zero_via_compatible_bridge` | `deltaMap_gen (laurentPlusBridge uplus, laurentMinusBridge uminus) = 0` |
| Laurent-pair presheaf gluing | `laurentCover_gluing_presheaf_via_compatible_bridge` | `∃ x, restrictionMap D₀ plus x = uplus ∧ restrictionMap D₀ minus x = uminus` |
| V-cover presheaf gluing | `V_cover_gluing_from_laurentPair_via_compatible_bridge` | `∃ x, ∀ D ∈ V_covers, restrictionMap D₀ D x = fV D` |

**Typical Lane-C usage pattern** (V-cover level):

```lean
-- Lane C inductive step (schematic):
-- 1. Obtain compatible overlap bridge witness:
obtain ⟨τ₁₂, hcompat_bridge⟩ :=
  laurentOverlapBridge_exists_compatible P D₀ f … -- Primary's Lane-A theorem
-- 2. Apply the V-cover consumer directly:
exact V_cover_gluing_from_laurentPair_via_compatible_bridge P D₀ f …
  τ₁₂ hcompat_bridge
  V_covers hV_subset_base hrefine
  u_plus u_minus fV hfV_plus hfV_minus hcompat
```

Consumers who only need the Laurent-pair conclusion (not the full V-cover
shape) can use `laurentCover_gluing_presheaf_via_compatible_bridge`
directly, which returns both half-section recoveries in one existential.

**No new sorries introduced**: the three theorems share the pre-existing
T001 axiom leak (via `[HasLocLiftPowerBounded A]` → `restrictionMap`)
with every other `restrictionMap`-consuming theorem in the file. None
depend on the Lane-A existential sorry. -/

/-- **`delta = 0` via an explicit compatible bridge** — sorry-free analog
of `laurentBridge_delta_eq_zero_of_compat` that takes the bridge
`(τ₁₂, hcompat_bridge)` as caller-supplied hypotheses rather than
extracting them via `laurentOverlapBridge_exists_compatible` (the
Lane-A `sorry`).

Same conclusion as `laurentBridge_delta_eq_zero_of_compat`; same proof
body minus the `obtain ⟨τ₁₂, hcompat_bridge⟩ := …` step. -/
theorem laurentBridge_delta_eq_zero_via_compatible_bridge
    [IsTateRing A] [IsNoetherianRing A] [T2Space A]
    [NonarchimedeanRing A]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (D₀ : RationalLocData A) [IsNoetherianRing (locSubring D₀.P D₀.T D₀.s)]
    [LaurentNormalized D₀]
    (f : A)
    (hNoeth_B : IsNoetherianRing (presheafValue D₀))
    (hLocLift_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      HasLocLiftPowerBounded (presheafValue D₀))
    (hA₀Noeth_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      letI : IsNoetherianRing (presheafValue D₀) := hNoeth_B
      IsNoetherianRing ↥((presheafValue_pairOfDefinition_concrete P D₀).A₀))
    (hA_complete_B : @CompleteSpace (presheafValue D₀)
      (IsTopologicalAddGroup.rightUniformSpace (presheafValue D₀)))
    (hnoeth_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      IsNoetherianRing ↥(TateAlgebra.pairSubring
        (IsTateRing.principalPair (presheafValue D₀)).toPairOfDefinition))
    (hcont_forward_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      letI : HasLocLiftPowerBounded (presheafValue D₀) := hLocLift_B
      letI : IsNoetherianRing (presheafValue D₀) := hNoeth_B
      letI P_B : PairOfDefinition (presheafValue D₀) :=
        presheafValue_pairOfDefinition_concrete P D₀
      letI : IsNoetherianRing ↥P_B.A₀ := hA₀Noeth_B
      @Continuous _ _
        (quotientPlusFSubXIdealTopology (presheafValue D₀) (D₀.canonicalMap f))
        (inferInstance : TopologicalSpace (presheafValue
          (trivialPlusDatum (presheafValue D₀) P_B (D₀.canonicalMap f))))
        (example638Plus_forwardHom (presheafValue D₀) P_B (D₀.canonicalMap f)))
    (hcont_eval_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      let D : RationalLocData (presheafValue D₀) := iteratedMinusDatum_B P D₀ f
      ∀ hb : TopologicalRing.IsPowerBounded (invS D),
        @Continuous _ _
          (TateAlgebra.quotientOneSubfXIdealTopology D.s)
          (inferInstance : TopologicalSpace (presheafValue D))
          (tateQuotientToPresheafHom D hb))
    (τ₁₂ : presheafValue (laurentOverlapDatum D₀ f) ≃+*
      LaurentCover.B₁₂_gen (D₀.canonicalMap f))
    (hcompat_bridge : LaurentOverlapBridgeCompatible P D₀ f hNoeth_B hLocLift_B
      hA₀Noeth_B hA_complete_B hnoeth_B hcont_forward_B hcont_eval_B τ₁₂)
    (uplus : presheafValue (laurentPlusDatum D₀ f))
    (uminus : presheafValue (laurentMinusDatum D₀ f))
    (hcompat : ∀ (D₃ : RationalLocData A)
      (h₃p : rationalOpen D₃.T D₃.s ⊆
        rationalOpen (laurentPlusDatum D₀ f).T (laurentPlusDatum D₀ f).s)
      (h₃m : rationalOpen D₃.T D₃.s ⊆
        rationalOpen (laurentMinusDatum D₀ f).T (laurentMinusDatum D₀ f).s),
      restrictionMap (laurentPlusDatum D₀ f) D₃ h₃p uplus =
        restrictionMap (laurentMinusDatum D₀ f) D₃ h₃m uminus) :
    LaurentCover.deltaMap_gen (D₀.canonicalMap f)
      (laurentPlusBridge P D₀ f hNoeth_B hLocLift_B hA₀Noeth_B hA_complete_B
          hnoeth_B hcont_forward_B uplus,
        laurentMinusBridge P D₀ f hnoeth_B hcont_eval_B uminus) = 0 := by
  -- Step 1: Apply `hcompat` at the overlap datum.
  have h_restr_eq : restrictionMap (laurentPlusDatum D₀ f) (laurentOverlapDatum D₀ f)
        (laurentOverlap_subset_plus D₀ f) uplus =
      restrictionMap (laurentMinusDatum D₀ f) (laurentOverlapDatum D₀ f)
        (laurentOverlap_subset_minus D₀ f) uminus :=
    hcompat (laurentOverlapDatum D₀ f)
      (laurentOverlap_subset_plus D₀ f) (laurentOverlap_subset_minus D₀ f)
  -- Step 2: Transport through τ₁₂.
  have h_pos_eq_neg :
      LaurentCover.posLift (D₀.canonicalMap f)
        (laurentPlusBridge P D₀ f hNoeth_B hLocLift_B hA₀Noeth_B hA_complete_B
          hnoeth_B hcont_forward_B uplus) =
      LaurentCover.negLift (D₀.canonicalMap f)
        (laurentMinusBridge P D₀ f hnoeth_B hcont_eval_B uminus) := by
    have h1 := hcompat_bridge.plus_compat uplus
    have h2 := hcompat_bridge.minus_compat uminus
    rw [← h1, ← h2, h_restr_eq]
  -- Step 3: `deltaMap_gen (b₁, b₂) = posLift b₁ - negLift b₂`.
  show LaurentCover.posLift (D₀.canonicalMap f) _ -
    LaurentCover.negLift (D₀.canonicalMap f) _ = 0
  rw [h_pos_eq_neg]
  exact sub_self _

/-- **Lane-C consumer: Laurent-cover gluing via an explicit compatible bridge**
— sorry-free analog of `laurentCover_gluing_presheaf` that takes
`(τ₁₂, hcompat_bridge)` as caller-supplied hypotheses.

**Usage (Lane C)**: Lane C's refinement induction requires
`laurentCover_gluing_presheaf` at each Laurent split. That theorem
currently routes through `laurentOverlapBridge_exists_compatible`
(`sorry` at LaurentRefinement.lean:3124). Lane C callers that
independently supply a `(τ₁₂, hcompat_bridge)` witness can use this
version instead, avoiding the Lane-A sorry until Lane A's existential
is closed.

**Proof structure**: factored through
`laurentCover_gluing_presheaf_viaRow3` (parametric in the Route-B
bridges, sorry-free) plus the new
`laurentBridge_delta_eq_zero_via_compatible_bridge` for the delta-zero
step. -/
theorem laurentCover_gluing_presheaf_via_compatible_bridge
    [IsTateRing A] [IsNoetherianRing A] [T2Space A]
    [NonarchimedeanRing A]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (D₀ : RationalLocData A) [IsNoetherianRing (locSubring D₀.P D₀.T D₀.s)]
    [LaurentNormalized D₀]
    (f : A)
    (hNoeth_B : IsNoetherianRing (presheafValue D₀))
    (hLocLift_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      HasLocLiftPowerBounded (presheafValue D₀))
    (hA₀Noeth_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      letI : IsNoetherianRing (presheafValue D₀) := hNoeth_B
      IsNoetherianRing ↥((presheafValue_pairOfDefinition_concrete P D₀).A₀))
    (hA_complete_B : @CompleteSpace (presheafValue D₀)
      (IsTopologicalAddGroup.rightUniformSpace (presheafValue D₀)))
    (hnoeth_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      IsNoetherianRing ↥(TateAlgebra.pairSubring
        (IsTateRing.principalPair (presheafValue D₀)).toPairOfDefinition))
    (hcont_forward_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      letI : HasLocLiftPowerBounded (presheafValue D₀) := hLocLift_B
      letI : IsNoetherianRing (presheafValue D₀) := hNoeth_B
      letI P_B : PairOfDefinition (presheafValue D₀) :=
        presheafValue_pairOfDefinition_concrete P D₀
      letI : IsNoetherianRing ↥P_B.A₀ := hA₀Noeth_B
      @Continuous _ _
        (quotientPlusFSubXIdealTopology (presheafValue D₀) (D₀.canonicalMap f))
        (inferInstance : TopologicalSpace (presheafValue
          (trivialPlusDatum (presheafValue D₀) P_B (D₀.canonicalMap f))))
        (example638Plus_forwardHom (presheafValue D₀) P_B (D₀.canonicalMap f)))
    (hcont_eval_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      let D : RationalLocData (presheafValue D₀) := iteratedMinusDatum_B P D₀ f
      ∀ hb : TopologicalRing.IsPowerBounded (invS D),
        @Continuous _ _
          (TateAlgebra.quotientOneSubfXIdealTopology D.s)
          (inferInstance : TopologicalSpace (presheafValue D))
          (tateQuotientToPresheafHom D hb))
    (τ₁₂ : presheafValue (laurentOverlapDatum D₀ f) ≃+*
      LaurentCover.B₁₂_gen (D₀.canonicalMap f))
    (hcompat_bridge : LaurentOverlapBridgeCompatible P D₀ f hNoeth_B hLocLift_B
      hA₀Noeth_B hA_complete_B hnoeth_B hcont_forward_B hcont_eval_B τ₁₂)
    (hplus : rationalOpen (laurentPlusDatum D₀ f).T (laurentPlusDatum D₀ f).s ⊆
      rationalOpen D₀.T D₀.s)
    (hminus : rationalOpen (laurentMinusDatum D₀ f).T (laurentMinusDatum D₀ f).s ⊆
      rationalOpen D₀.T D₀.s)
    (uplus : presheafValue (laurentPlusDatum D₀ f))
    (uminus : presheafValue (laurentMinusDatum D₀ f))
    (hcompat : ∀ (D₃ : RationalLocData A)
      (h₃p : rationalOpen D₃.T D₃.s ⊆
        rationalOpen (laurentPlusDatum D₀ f).T (laurentPlusDatum D₀ f).s)
      (h₃m : rationalOpen D₃.T D₃.s ⊆
        rationalOpen (laurentMinusDatum D₀ f).T (laurentMinusDatum D₀ f).s),
      restrictionMap (laurentPlusDatum D₀ f) D₃ h₃p uplus =
        restrictionMap (laurentMinusDatum D₀ f) D₃ h₃m uminus) :
    ∃ x : presheafValue D₀,
      restrictionMap D₀ (laurentPlusDatum D₀ f) hplus x = uplus ∧
      restrictionMap D₀ (laurentMinusDatum D₀ f) hminus x = uminus :=
  laurentCover_gluing_presheaf_viaRow3 D₀ f hplus hminus
    (laurentPlusBridge P D₀ f hNoeth_B hLocLift_B hA₀Noeth_B hA_complete_B
        hnoeth_B hcont_forward_B)
    (laurentMinusBridge P D₀ f hnoeth_B hcont_eval_B)
    (laurentPlusBridge_restrictionMap P D₀ f hNoeth_B hLocLift_B hA₀Noeth_B
        hA_complete_B hnoeth_B hcont_forward_B hplus)
    (laurentMinusBridge_restrictionMap P D₀ f hnoeth_B hcont_eval_B hminus)
    rfl
    uplus uminus
    (laurentBridge_delta_eq_zero_via_compatible_bridge P D₀ f hNoeth_B hLocLift_B
      hA₀Noeth_B hA_complete_B hnoeth_B hcont_forward_B hcont_eval_B
      τ₁₂ hcompat_bridge uplus uminus hcompat)

/-- **V-cover Lane-C consumer from Laurent pair + explicit compatible bridge**.

**The high-level downstream API for Lane C's inductive step**. Takes:

* A Laurent-pair base `(D₀, f)` with the full 7-hypothesis Tate bundle.
* An **abstract** V-cover `V_covers : Finset (RationalLocData A)` refining
  `D₀`, with each piece lying in the plus or minus half.
* Half-sections `u_plus, u_minus` compatible on the overlap.
* Matching conditions `hfV_plus, hfV_minus` of the half-sections with the
  V-sections `fV` on their respective halves.
* The **explicit compatible overlap bridge** `(τ₁₂, hcompat_bridge)` — the
  single upstream Lane-A witness this theorem consumes.

Produces the V-cover gluing conclusion directly (no need for the caller to
unpack the Laurent gluing and then reshuffle via
`restrictionMap_comp`).

**Architectural note**: this theorem inlines the geometric content of
`standardCover_gluing_induction_step` (in `GeometricReduction.lean`)
but states it **parametric in abstract `V_covers`**, independent of
`standardCoverVCovers` / `StandardCover` infrastructure. This keeps the
caller-ready API self-contained in `LaurentRefinement.lean` and
immune to upstream in-flight edits in downstream-geometric files.

Downstream callers who work with standard-cover V-sets simply
instantiate `V_covers := C.standardCoverVCovers S` and derive
`hV_subset_base` / `hrefine` from the `standardCoverVCovers`
specializations (`standardCoverVCovers_subset_base`,
`refinedVCovers_plusMinus_dichotomy`, etc.). Other consumers
(e.g., ad-hoc Laurent induction variants) can supply any V-cover
Finset directly.

**Proof**: unpacks the Laurent pair gluing via
`laurentCover_gluing_presheaf_via_compatible_bridge`, then for each
`D ∈ V_covers` chooses plus/minus refinement via `hrefine` and applies
`restrictionMap_comp`. Pure structural composition; no new analytic
content. -/
theorem V_cover_gluing_from_laurentPair_via_compatible_bridge
    [IsTateRing A] [IsNoetherianRing A] [T2Space A]
    [NonarchimedeanRing A]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (D₀ : RationalLocData A) [IsNoetherianRing (locSubring D₀.P D₀.T D₀.s)]
    [LaurentNormalized D₀]
    (f : A)
    (hNoeth_B : IsNoetherianRing (presheafValue D₀))
    (hLocLift_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      HasLocLiftPowerBounded (presheafValue D₀))
    (hA₀Noeth_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      letI : IsNoetherianRing (presheafValue D₀) := hNoeth_B
      IsNoetherianRing ↥((presheafValue_pairOfDefinition_concrete P D₀).A₀))
    (hA_complete_B : @CompleteSpace (presheafValue D₀)
      (IsTopologicalAddGroup.rightUniformSpace (presheafValue D₀)))
    (hnoeth_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      IsNoetherianRing ↥(TateAlgebra.pairSubring
        (IsTateRing.principalPair (presheafValue D₀)).toPairOfDefinition))
    (hcont_forward_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      letI : HasLocLiftPowerBounded (presheafValue D₀) := hLocLift_B
      letI : IsNoetherianRing (presheafValue D₀) := hNoeth_B
      letI P_B : PairOfDefinition (presheafValue D₀) :=
        presheafValue_pairOfDefinition_concrete P D₀
      letI : IsNoetherianRing ↥P_B.A₀ := hA₀Noeth_B
      @Continuous _ _
        (quotientPlusFSubXIdealTopology (presheafValue D₀) (D₀.canonicalMap f))
        (inferInstance : TopologicalSpace (presheafValue
          (trivialPlusDatum (presheafValue D₀) P_B (D₀.canonicalMap f))))
        (example638Plus_forwardHom (presheafValue D₀) P_B (D₀.canonicalMap f)))
    (hcont_eval_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      let D : RationalLocData (presheafValue D₀) := iteratedMinusDatum_B P D₀ f
      ∀ hb : TopologicalRing.IsPowerBounded (invS D),
        @Continuous _ _
          (TateAlgebra.quotientOneSubfXIdealTopology D.s)
          (inferInstance : TopologicalSpace (presheafValue D))
          (tateQuotientToPresheafHom D hb))
    (τ₁₂ : presheafValue (laurentOverlapDatum D₀ f) ≃+*
      LaurentCover.B₁₂_gen (D₀.canonicalMap f))
    (hcompat_bridge : LaurentOverlapBridgeCompatible P D₀ f hNoeth_B hLocLift_B
      hA₀Noeth_B hA_complete_B hnoeth_B hcont_forward_B hcont_eval_B τ₁₂)
    (V_covers : Finset (RationalLocData A))
    (hV_subset_base : ∀ D ∈ V_covers,
      rationalOpen D.T D.s ⊆ rationalOpen D₀.T D₀.s)
    (hrefine : ∀ D : { D // D ∈ V_covers },
      (rationalOpen D.1.T D.1.s ⊆
        rationalOpen (laurentPlusDatum D₀ f).T (laurentPlusDatum D₀ f).s) ∨
      (rationalOpen D.1.T D.1.s ⊆
        rationalOpen (laurentMinusDatum D₀ f).T (laurentMinusDatum D₀ f).s))
    (u_plus : presheafValue (laurentPlusDatum D₀ f))
    (u_minus : presheafValue (laurentMinusDatum D₀ f))
    (fV : ∀ D : { D // D ∈ V_covers }, presheafValue D.1)
    (hfV_plus : ∀ (D : { D // D ∈ V_covers })
      (hD_plus : rationalOpen D.1.T D.1.s ⊆
        rationalOpen (laurentPlusDatum D₀ f).T (laurentPlusDatum D₀ f).s),
      restrictionMap (laurentPlusDatum D₀ f) D.1 hD_plus u_plus = fV D)
    (hfV_minus : ∀ (D : { D // D ∈ V_covers })
      (hD_minus : rationalOpen D.1.T D.1.s ⊆
        rationalOpen (laurentMinusDatum D₀ f).T (laurentMinusDatum D₀ f).s),
      restrictionMap (laurentMinusDatum D₀ f) D.1 hD_minus u_minus = fV D)
    (hcompat : ∀ (D₃ : RationalLocData A)
      (h₃p : rationalOpen D₃.T D₃.s ⊆
        rationalOpen (laurentPlusDatum D₀ f).T (laurentPlusDatum D₀ f).s)
      (h₃m : rationalOpen D₃.T D₃.s ⊆
        rationalOpen (laurentMinusDatum D₀ f).T (laurentMinusDatum D₀ f).s),
      restrictionMap (laurentPlusDatum D₀ f) D₃ h₃p u_plus =
        restrictionMap (laurentMinusDatum D₀ f) D₃ h₃m u_minus) :
    ∃ x : presheafValue D₀,
      ∀ D : { D // D ∈ V_covers },
        restrictionMap D₀ D.1 (hV_subset_base D.1 D.2) x = fV D := by
  -- Step 1: get the Laurent-pair gluing from the explicit bridge.
  obtain ⟨x, hx_plus, hx_minus⟩ :=
    laurentCover_gluing_presheaf_via_compatible_bridge P D₀ f
      hNoeth_B hLocLift_B hA₀Noeth_B hA_complete_B hnoeth_B
      hcont_forward_B hcont_eval_B τ₁₂ hcompat_bridge
      (laurentPlus_subset D₀ f) (laurentMinus_subset D₀ f)
      u_plus u_minus hcompat
  -- Step 2: check the V-cover condition via plus/minus refinement dichotomy.
  refine ⟨x, fun D => ?_⟩
  rcases hrefine D with hD_plus | hD_minus
  · -- D refines plus half: compose restrictionMap D₀ → plus → D.1.
    have hcomp := congr_fun
      (restrictionMap_comp D₀ (laurentPlusDatum D₀ f) D.1
        (laurentPlus_subset D₀ f) hD_plus) x
    simp only [Function.comp_apply] at hcomp
    rw [hx_plus, hfV_plus D hD_plus] at hcomp
    exact hcomp.symm
  · -- D refines minus half: symmetric.
    have hcomp := congr_fun
      (restrictionMap_comp D₀ (laurentMinusDatum D₀ f) D.1
        (laurentMinus_subset D₀ f) hD_minus) x
    simp only [Function.comp_apply] at hcomp
    rw [hx_minus, hfV_minus D hD_minus] at hcomp
    exact hcomp.symm

/-- **End-to-end smoke test** (CLEANUP-C2): compose the three-theorem caller
tower — `laurentBridge_delta_eq_zero_via_compatible_bridge` →
`laurentCover_gluing_presheaf_via_compatible_bridge` →
`V_cover_gluing_from_laurentPair_via_compatible_bridge` — into a single
invocation returning both the Laurent-pair witness and a named V-piece
restriction, to demonstrate the tower closes at a concrete call site.

Takes the single upstream Lane-A witness `(τ₁₂, hcompat_bridge)` plus the
standard Laurent-pair + V-cover data, and returns a combined existential
of the form `∃ x, <Laurent pair holds> ∧ <V-cover holds>`. Verifies that
the Laurent-pair and V-cover conclusions share a single witness `x`
(not two different ones).

**Content**: `V_cover_gluing_from_laurentPair_via_compatible_bridge`'s
proof already chooses `x` as the Laurent-pair-gluing witness, so the
Laurent-pair equations are recoverable from the same `x`. This smoke test
makes that recovery explicit in the theorem statement, as a sanity check
for callers. -/
theorem laurentAndVCover_gluing_unified_via_compatible_bridge
    [IsTateRing A] [IsNoetherianRing A] [T2Space A]
    [NonarchimedeanRing A]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (D₀ : RationalLocData A) [IsNoetherianRing (locSubring D₀.P D₀.T D₀.s)]
    [LaurentNormalized D₀]
    (f : A)
    (hNoeth_B : IsNoetherianRing (presheafValue D₀))
    (hLocLift_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      HasLocLiftPowerBounded (presheafValue D₀))
    (hA₀Noeth_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      letI : IsNoetherianRing (presheafValue D₀) := hNoeth_B
      IsNoetherianRing ↥((presheafValue_pairOfDefinition_concrete P D₀).A₀))
    (hA_complete_B : @CompleteSpace (presheafValue D₀)
      (IsTopologicalAddGroup.rightUniformSpace (presheafValue D₀)))
    (hnoeth_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      IsNoetherianRing ↥(TateAlgebra.pairSubring
        (IsTateRing.principalPair (presheafValue D₀)).toPairOfDefinition))
    (hcont_forward_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      letI : HasLocLiftPowerBounded (presheafValue D₀) := hLocLift_B
      letI : IsNoetherianRing (presheafValue D₀) := hNoeth_B
      letI P_B : PairOfDefinition (presheafValue D₀) :=
        presheafValue_pairOfDefinition_concrete P D₀
      letI : IsNoetherianRing ↥P_B.A₀ := hA₀Noeth_B
      @Continuous _ _
        (quotientPlusFSubXIdealTopology (presheafValue D₀) (D₀.canonicalMap f))
        (inferInstance : TopologicalSpace (presheafValue
          (trivialPlusDatum (presheafValue D₀) P_B (D₀.canonicalMap f))))
        (example638Plus_forwardHom (presheafValue D₀) P_B (D₀.canonicalMap f)))
    (hcont_eval_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      let D : RationalLocData (presheafValue D₀) := iteratedMinusDatum_B P D₀ f
      ∀ hb : TopologicalRing.IsPowerBounded (invS D),
        @Continuous _ _
          (TateAlgebra.quotientOneSubfXIdealTopology D.s)
          (inferInstance : TopologicalSpace (presheafValue D))
          (tateQuotientToPresheafHom D hb))
    (τ₁₂ : presheafValue (laurentOverlapDatum D₀ f) ≃+*
      LaurentCover.B₁₂_gen (D₀.canonicalMap f))
    (hcompat_bridge : LaurentOverlapBridgeCompatible P D₀ f hNoeth_B hLocLift_B
      hA₀Noeth_B hA_complete_B hnoeth_B hcont_forward_B hcont_eval_B τ₁₂)
    (V_covers : Finset (RationalLocData A))
    (hV_subset_base : ∀ D ∈ V_covers,
      rationalOpen D.T D.s ⊆ rationalOpen D₀.T D₀.s)
    (hrefine : ∀ D : { D // D ∈ V_covers },
      (rationalOpen D.1.T D.1.s ⊆
        rationalOpen (laurentPlusDatum D₀ f).T (laurentPlusDatum D₀ f).s) ∨
      (rationalOpen D.1.T D.1.s ⊆
        rationalOpen (laurentMinusDatum D₀ f).T (laurentMinusDatum D₀ f).s))
    (u_plus : presheafValue (laurentPlusDatum D₀ f))
    (u_minus : presheafValue (laurentMinusDatum D₀ f))
    (fV : ∀ D : { D // D ∈ V_covers }, presheafValue D.1)
    (hfV_plus : ∀ (D : { D // D ∈ V_covers })
      (hD_plus : rationalOpen D.1.T D.1.s ⊆
        rationalOpen (laurentPlusDatum D₀ f).T (laurentPlusDatum D₀ f).s),
      restrictionMap (laurentPlusDatum D₀ f) D.1 hD_plus u_plus = fV D)
    (hfV_minus : ∀ (D : { D // D ∈ V_covers })
      (hD_minus : rationalOpen D.1.T D.1.s ⊆
        rationalOpen (laurentMinusDatum D₀ f).T (laurentMinusDatum D₀ f).s),
      restrictionMap (laurentMinusDatum D₀ f) D.1 hD_minus u_minus = fV D)
    (hcompat : ∀ (D₃ : RationalLocData A)
      (h₃p : rationalOpen D₃.T D₃.s ⊆
        rationalOpen (laurentPlusDatum D₀ f).T (laurentPlusDatum D₀ f).s)
      (h₃m : rationalOpen D₃.T D₃.s ⊆
        rationalOpen (laurentMinusDatum D₀ f).T (laurentMinusDatum D₀ f).s),
      restrictionMap (laurentPlusDatum D₀ f) D₃ h₃p u_plus =
        restrictionMap (laurentMinusDatum D₀ f) D₃ h₃m u_minus) :
    ∃ x : presheafValue D₀,
      restrictionMap D₀ (laurentPlusDatum D₀ f)
          (laurentPlus_subset D₀ f) x = u_plus ∧
      restrictionMap D₀ (laurentMinusDatum D₀ f)
          (laurentMinus_subset D₀ f) x = u_minus ∧
      ∀ D : { D // D ∈ V_covers },
        restrictionMap D₀ D.1 (hV_subset_base D.1 D.2) x = fV D := by
  -- Step 1: Laurent-pair gluing via explicit bridge — pins `x`.
  obtain ⟨x, hx_plus, hx_minus⟩ :=
    laurentCover_gluing_presheaf_via_compatible_bridge P D₀ f
      hNoeth_B hLocLift_B hA₀Noeth_B hA_complete_B hnoeth_B
      hcont_forward_B hcont_eval_B τ₁₂ hcompat_bridge
      (laurentPlus_subset D₀ f) (laurentMinus_subset D₀ f)
      u_plus u_minus hcompat
  -- Step 2: extract the V-cover conclusion on the same `x` via refinement.
  refine ⟨x, hx_plus, hx_minus, fun D => ?_⟩
  rcases hrefine D with hD_plus | hD_minus
  · have hcomp := congr_fun
      (restrictionMap_comp D₀ (laurentPlusDatum D₀ f) D.1
        (laurentPlus_subset D₀ f) hD_plus) x
    simp only [Function.comp_apply] at hcomp
    rw [hx_plus, hfV_plus D hD_plus] at hcomp
    exact hcomp.symm
  · have hcomp := congr_fun
      (restrictionMap_comp D₀ (laurentMinusDatum D₀ f) D.1
        (laurentMinus_subset D₀ f) hD_minus) x
    simp only [Function.comp_apply] at hcomp
    rw [hx_minus, hfV_minus D hD_minus] at hcomp
    exact hcomp.symm

/-- **Tate acyclicity gluing via explicit refinement.**

Reduces the Part 2 (gluing) clause of `tateAcyclicity` to gluing on a *refinement*
`V_covers` of the same base, under the mild hypothesis that `τ : V → C` is
surjective (every `C`-piece has at least one `V`-piece landing inside it).

The surjectivity of `τ` is used to apply `restrictionMapHom_injective` (Wedhorn
Cor 8.32, currently `sorry`'d in `PresheafTateStructure`) for the local-separation
step: for each `E ∈ C.covers`, the chosen V-piece `d` with `τ d = E` gives an
injective restriction map `presheafValue E → presheafValue d.1`, which is all that
is needed to distinguish `restrictionMap C.base E _ x` from `fC E` (since they
agree on `d`).

This theorem is thus a *pure reshuffling* of the gluing statement: it converts
"gluing on `C`" into "gluing on `V`" + "surjective refinement map `τ`". The
intended use is the **standard-cover reduction** (Wedhorn Lemma 8.34 / Zavyalov §2)
— feed `RationalCovering.refines_by_standard_cover` to produce the refinement,
then Laurent-cover induction to discharge `hV_glue`. -/
theorem tateAcyclicity_gluing_via_refinement
    [IsTateRing A] [IsNoetherianRing A] [IsStronglyNoetherian A] [T2Space A]
    [NonarchimedeanRing A]
    (C : RationalCovering A)
    (V_covers : Finset (RationalLocData A))
    (hV_subset : ∀ D ∈ V_covers, rationalOpen D.T D.s ⊆
      rationalOpen C.base.T C.base.s)
    (τ : { D // D ∈ V_covers } → { E // E ∈ C.covers })
    (hτ : ∀ d : { D // D ∈ V_covers },
      rationalOpen d.1.T d.1.s ⊆ rationalOpen (τ d).1.T (τ d).1.s)
    (hτ_surj : Function.Surjective τ)
    (fC : ∀ E : { E // E ∈ C.covers }, presheafValue E.1)
    (hC_compat : ∀ (E₁ E₂ : { E // E ∈ C.covers }) (D₃ : RationalLocData A)
      (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen E₁.1.T E₁.1.s)
      (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen E₂.1.T E₂.1.s),
      restrictionMap E₁.1 D₃ h₃₁ (fC E₁) = restrictionMap E₂.1 D₃ h₃₂ (fC E₂))
    (hV_glue : ∀ (fV : ∀ D : { D // D ∈ V_covers }, presheafValue D.1),
      (∀ (D₁ D₂ : { D // D ∈ V_covers }) (D₃ : RationalLocData A)
        (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₁.1.T D₁.1.s)
        (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₂.1.T D₂.1.s),
        restrictionMap D₁.1 D₃ h₃₁ (fV D₁) = restrictionMap D₂.1 D₃ h₃₂ (fV D₂)) →
      ∃ x : presheafValue C.base, ∀ D : { D // D ∈ V_covers },
        restrictionMap C.base D.1 (hV_subset D.1 D.2) x = fV D) :
    ∃ x : presheafValue C.base, ∀ E : { E // E ∈ C.covers },
      restrictionMap C.base E.1 (C.hsubset E.1 E.2) x = fC E := by
  apply ValuationSpectrum.gluing_of_finer_rational C V_covers hV_subset τ hτ fC
    hC_compat hV_glue
  intro E a b hab
  -- T-INJ-1-CLEANUP NOTE (2026-05-11): the per-`E` separation here calls
  -- the retired-as-false single-map `restrictionMapHom_injective`. The
  -- correct route is to thread a per-`E` Cor 8.32 separation hypothesis
  -- (i.e. invoke `productRestriction_injective_tate_via_prime_extension_closed`
  -- applied at each `E`'s local covering). This refactor is non-trivial
  -- because the τ-based gluing currently consumes single-map injectivity;
  -- migrating it to the per-E direct assembly
  -- (`GeometricReduction.tateAcyclicity_Part2_direct_per_E`) is the
  -- intended cleanup. The reviewer confirmed (ChatGPT Pro, 2026-05-11)
  -- that the single-map dependency must be removed; the call site is
  -- preserved here until the τ-route is fully replaced.
  obtain ⟨d, hd⟩ := hτ_surj E
  have := hab d hd
  exact ValuationSpectrum.restrictionMapHom_injective E.1 d.1 (hd ▸ hτ d) this

/-- **Wedhorn Theorem 8.28(b)**: Tate acyclicity.

For a finite rational covering of a strongly noetherian Tate ring,
the presheaf satisfies the sheaf-of-abelian-groups conditions:
- **Separation** (zero kernel): `x` restricts to `0` everywhere implies `x = 0`.
- **Gluing**: compatible sections have a global pre-image.

**Status** (2026-04-08): reframed around the Wedhorn flatness route.

**Wedhorn's proof** (lecture notes `1910.05934v1.pdf`, pp. 81–85):

1. **Lemma 8.31** (`TateAlgebra.lean`): for noetherian complete Tate `A`,
   `A⟨X⟩`, `A⟨X⟩/(f-X)`, and `A⟨X⟩/(1-fX)` are all flat over `A`. **DONE**
   (`tateAlgebra_flat`, `flat_quotient_fSubX_general`, `flat_quotient_oneSubfX_general`).
2. **Example 6.38** (gap, Phase 2): `presheafValue D ≃+* A⟨X⟩/(closed ideal)`
   for strongly noetherian Tate `A`, via universal property + Wedhorn Prop 6.17
   (ideals in noetherian Tate are closed).
3. **Corollary 8.32** (Phase 3): the product restriction
   `presheafValue C.base → ∏ presheafValue D` is faithfully flat (in
   particular **injective** ⇒ Part 1 below).
4. **Lemma 8.33** (Phase 4): the 2-element Laurent cover exact sequence
   `0 → A → A⟨ζ⟩/(f-ζ) × A⟨η⟩/(1-fη) → A⟨ζ,ζ⁻¹⟩/(f-ζ) → 0` is exact
   (3×3 diagram chase; algebraic core in `LaurentCoverExact.row3_exact`).
5. **Lemma 8.34** (Phase 4): refinement transfer + Laurent-cover induction give
   acyclicity for every rational cover generated by `T·A = A` (⇒ Part 2 below).

See `docs/plans/2026-04-08-wedhorn-vs-zavyalov.md` for the full plan.

The earlier "strict exactness via Banach open mapping" framing of R2 was a
red herring: our `IsSheafy` only requires sheaf-of-sets, and Wedhorn's proof
gives exactly that via flatness — no topological embedding needed. -/
theorem tateAcyclicity
    [IsTateRing A] [IsNoetherianRing A] [IsStronglyNoetherian A] [T2Space A]
    [NonarchimedeanRing A]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (C : RationalCovering A) (hne : C.covers.Nonempty) :
    -- Part 1: Zero kernel (separation)
    (∀ x : presheafValue C.base,
      (∀ (D : RationalLocData A) (hD : D ∈ C.covers),
        restrictionMap C.base D (C.hsubset D hD) x = 0) → x = 0) ∧
    -- Part 2: Gluing
    (∀ (f : ∀ (D : ↥C.covers), presheafValue D.1),
      (∀ (D₁ D₂ : ↥C.covers) (D₃ : RationalLocData A)
        (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₁.1.T D₁.1.s)
        (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₂.1.T D₂.1.s),
        restrictionMap D₁.1 D₃ h₃₁ (f D₁) = restrictionMap D₂.1 D₃ h₃₂ (f D₂)) →
      ∃ x : presheafValue C.base, ∀ (D : ↥C.covers),
        restrictionMap C.base D.1 (C.hsubset D.1 D.2) x = f D) := by
  refine ⟨?_, ?_⟩
  · -- Part 1: Separation via Wedhorn Cor 8.32 (product-level faithful flatness,
    -- per reviewer (ChatGPT Pro, 2026-05-11) confirmation — single-map
    -- `restrictionMapHom_injective` is retired-as-false; only the cover-level
    -- product injectivity enters the critical path).
    --
    -- The proof here previously delegated to the retired single-map
    -- `restrictionMapHom_injective` applied to any one cover piece. That route
    -- is mathematically false in general (Conrad counterexample). The correct
    -- path is the product-level Cor 8.32 statement: faithful flatness of
    -- `presheafValue C.base → ∏ presheafValue D_i` from componentwise flatness
    -- (Lemma 8.31, available) + cover-level Spa/spec surjectivity (an R2a
    -- ingredient).
    --
    -- Current status (T-INJ-1-CLEANUP, 2026-05-11): the call site below
    -- maintains the existing dependency on `restrictionMapHom_injective`
    -- because the product-level wrapper that would discharge this sorry-free
    -- requires R2a to land first. The doc-block here is updated to reflect
    -- the reviewer's confirmation that THIS is the residual to close, not
    -- to revisit the single-map route.
    intro x hx
    obtain ⟨D, hD⟩ := hne
    exact ValuationSpectrum.restrictionMapHom_injective C.base D (C.hsubset D hD)
      ((hx D hD).trans (map_zero _).symm)
  · -- Part 2: Gluing via partition of unity (Wedhorn Prop 8.15 + Thm 8.28(b)).
    --
    -- Using `restrictionMap_isLocalization` (PresheafTateStructure.lean), each
    -- presheafValue D is a localization of presheafValue C.base. The standard
    -- partition-of-unity argument produces the global section.
    --
    -- Upstream sorry dependencies: `restrictionMapHom_surj` (Baire category,
    -- PresheafTateStructure:1307), `locLift_preimage_locNhd` (Artin-Rees,
    -- PresheafTateStructure:1143). The separation (Part 1) uses the same chain.
    -- Additional sorry: span-top needs Spa-point at non-open primes
    -- (`exists_spa_point_in_rationalOpen`, StructureSheaf:682).
    intro f hcompat
    -- **Reduction available** (2026-04-14): `tateAcyclicity_gluing_via_refinement`
    -- above provides a clean reduction of this gluing to gluing on a refinement
    -- `V_covers` with surjective `τ : V → C`. Concretely, feed
    -- `RationalCovering.refines_by_standard_cover` to produce the refinement (a
    -- plus-type cover at elements of a standard cover), then Laurent-cover
    -- induction (`laurentCover_gluing_presheaf`) to discharge `hV_glue` inductively
    -- on the size of the standard cover.
    --
    -- **Remaining obstructions to full closure**:
    -- - `refines_by_standard_cover` itself still has residual sorries
    --   (non-open-prime Spa-point construction; see
    --   `StandardCover.exists_nullstellensatz_refinement`).
    -- - `laurentCover_gluing_presheaf` routes through the Route B bridges
    --   (`laurentPlusBridge`, `laurentMinusBridge`) and their sub-sorries
    --   (`presheafValue_iteratedPlus_equiv`, `presheafValue_iteratedMinus_equiv`,
    --   overlap bridge intertwining lemmas).
    -- - `restrictionMapHom_injective` is itself a sorry pending Wedhorn Cor 8.32
    --   (faithful flatness of the product restriction).
    --
    -- **Alternative route (direct partition of unity)** (Wedhorn Theorem 8.28(b)):
    -- 1. Span-top: Ideal.span {canonicalMap(D.s)} = top in presheafValue C.base
    -- 2. Surj: f D is a fraction r_D / sD^n_D via IsLocalization.Away.surj
    -- 3. Uniform exponent: absorb n_D into a uniform N₀
    -- 4. Numerator compatibility: r'_D₁ * sD₂^N = r'_D₂ * sD₁^N (up to powers)
    -- 5-6. Power absorption: uniform K, exact compatibility after absorption
    -- 7. Partition of unity: ∑ c_D * sD^N = 1 from span-top
    -- 8. Global section: x = ∑ c_D * r''_D
    -- 9. Verification: restrictionMap(x) = f D via partition + compatibility
    sorry

omit [PlusSubring A] [IsHuberRing A] [HasLocLiftPowerBounded A] in
/-- When `D.s = 0`, the localization `Localization.Away D.s` is the zero ring,
hence its completion `presheafValue D` is also subsingleton. -/
theorem presheafValue_subsingleton_of_s_eq_zero (D : RationalLocData A)
    (hs : D.s = 0) : Subsingleton (presheafValue D) := by
  haveI : Subsingleton (Localization.Away D.s) := by
    apply IsLocalization.subsingleton (M := Submonoid.powers D.s)
    exact ⟨1, by simp [hs]⟩
  -- 0 = 1 in `Localization.Away D.s` (subsingleton), so 0 = 1 in `presheafValue D`.
  have h01 : (0 : presheafValue D) = 1 := by
    rw [← map_zero D.coeRingHom, ← map_one D.coeRingHom,
      Subsingleton.elim (0 : Localization.Away D.s) 1]
  exact subsingleton_of_zero_eq_one h01

/-- Separation extracted from `tateAcyclicity`. Handles empty coverings
directly: when `C.covers = ∅` and `C.base.s = 0`, `presheafValue C.base` is
subsingleton; when `C.covers = ∅` and `C.base.s ≠ 0`, `hSpa` applied to the
zero ideal (prime since `A` is a domain) produces a Spa-point in
`rationalOpen C.base.T C.base.s`, contradicting the vacuous cover condition.

The `hSpa` hypothesis is the Spa-point existence witness for primes avoiding
`C.base.s`; in practice it is supplied via Wedhorn Lemma 7.45 applied to the
completed pair of definition (non-open prime case) or the trivial-valuation
construction (open prime case). -/
theorem rationalCovering_hasSeparation
    [IsTateRing A] [IsNoetherianRing A] [IsStronglyNoetherian A] [T2Space A]
    [NonarchimedeanRing A] [IsDomain A]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (C : RationalCovering A)
    (hSpa : ∀ (p : Ideal A), p.IsPrime → C.base.s ∉ p →
      ∃ v ∈ rationalOpen C.base.T C.base.s, p ≤ v.supp) :
    ∀ x y : presheafValue C.base,
      (∀ (D : RationalLocData A) (hD : D ∈ C.covers),
        restrictionMap C.base D (C.hsubset D hD) x =
        restrictionMap C.base D (C.hsubset D hD) y) → x = y := by
  intro x y hxy
  by_cases hne : C.covers.Nonempty
  · have ⟨hzk, _⟩ := tateAcyclicity P C hne
    exact sub_eq_zero.mp (hzk (x - y) fun D hD => by
      change restrictionMapHom C.base D _ (x - y) = 0
      rw [map_sub, sub_eq_zero]; exact hxy D hD)
  · -- Empty covering edge case: split on whether `C.base.s = 0`.
    by_cases hs : C.base.s = 0
    · -- `C.base.s = 0`: `presheafValue C.base` is subsingleton, so `x = y` trivially.
      haveI := presheafValue_subsingleton_of_s_eq_zero C.base hs
      exact Subsingleton.elim x y
    · -- `C.base.s ≠ 0`: use `hSpa` applied to the zero ideal.
      -- Since `A` is a domain, `(0)` is prime and `C.base.s ∉ (0)`.
      -- `hSpa` then produces `v ∈ rationalOpen C.base.T C.base.s`, and
      -- `C.hcover v` gives `D ∈ C.covers = ∅`, a contradiction.
      haveI hprime : (⊥ : Ideal A).IsPrime := Ideal.isPrime_bot
      have hs_notin : C.base.s ∉ (⊥ : Ideal A) := fun h => hs (Ideal.mem_bot.mp h)
      obtain ⟨v, hv_rat, _⟩ := hSpa ⊥ hprime hs_notin
      obtain ⟨D, hD, _⟩ := C.hcover v hv_rat
      exact absurd ⟨D, hD⟩ hne

/-- Gluing extracted from `tateAcyclicity`. Handles empty coverings
directly (any element works since compatibility is vacuous). -/
theorem rationalCovering_hasGluing
    [IsTateRing A] [IsNoetherianRing A] [IsStronglyNoetherian A] [T2Space A]
    [NonarchimedeanRing A]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (C : RationalCovering A)
    (f : ∀ (D : ↥C.covers), presheafValue D.1)
    (hcompat : ∀ (D₁ D₂ : ↥C.covers) (D₃ : RationalLocData A)
       (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₁.1.T D₁.1.s)
       (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₂.1.T D₂.1.s),
       restrictionMap D₁.1 D₃ h₃₁ (f D₁) = restrictionMap D₂.1 D₃ h₃₂ (f D₂)) :
    ∃ x : presheafValue C.base, ∀ (D : ↥C.covers),
      restrictionMap C.base D.1 (C.hsubset D.1 D.2) x = f D := by
  by_cases hne : C.covers.Nonempty
  · exact (tateAcyclicity P C hne).2 f hcompat
  · -- Empty covering: any x works, pick 0.
    exact ⟨0, fun ⟨D, hD⟩ => absurd ⟨D, hD⟩ hne⟩

-- The embedding theorem (Topology.IsEmbedding) is stated in StructureSheaf.lean
-- since it uses `productRestrictionSub` defined there.

end ValuationSpectrum

end
