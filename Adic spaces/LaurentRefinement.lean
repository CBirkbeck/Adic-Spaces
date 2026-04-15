/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».RationalRefinement
import «Adic spaces».RationalSubsets
import «Adic spaces».TopologyComparison
import «Adic spaces».PresheafTateStructure
import «Adic spaces».LaurentCoverExact
import «Adic spaces».CompletionLocalization
import «Adic spaces».Example638
import «Adic spaces».IteratedRational
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors

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
  P := (presheafValue_pairOfDefinition P D₀).some
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
  P := (presheafValue_pairOfDefinition P D₀).some
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
    (f : A) :
    presheafValue (laurentPlusDatum D₀ f) ≃+*
      presheafValue (iteratedPlusDatum_B P D₀ f) := by
  -- Structural closure via the uncompleted-level infrastructure above.
  -- The hypotheses `hsub`, `hcont_fwd`, `hcont_bwd`, `h_fwd_back` are the
  -- specific residual obligations; they are discharged via `laurentPlus_subset`,
  -- two Wedhorn Prop 8.2 continuity facts (not yet in the project), and the
  -- dual uncompleted round-trip identity (which requires density of
  -- `canonicalMap a` in `B` — an `IsDomain`-free replacement for the deleted
  -- `IsLocalization.Away.lift` route). See `iteratedPlus_forwardLocHom` and
  -- `iteratedPlus_backwardLocHom` above for the uncompleted maps.
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
  have hsub := laurentPlus_subset D₀ f
  have hcont_fwd : @Continuous _ _ (laurentPlusDatum D₀ f).topology _
      (iteratedPlus_forwardToCompletion P D₀ f) := sorry
  have hcont_bwd : @Continuous _ _ (iteratedPlusDatum_B P D₀ f).topology _
      (iteratedPlus_backwardLocHom D₀ f hsub) := sorry
  let forwardHom : presheafValue (laurentPlusDatum D₀ f) →+*
      presheafValue (iteratedPlusDatum_B P D₀ f) :=
    UniformSpace.Completion.extensionHom
      (iteratedPlus_forwardToCompletion P D₀ f) hcont_fwd
  let backwardHom : presheafValue (iteratedPlusDatum_B P D₀ f) →+*
      presheafValue (laurentPlusDatum D₀ f) :=
    UniformSpace.Completion.extensionHom
      (iteratedPlus_backwardLocHom D₀ f hsub) hcont_bwd
  -- Round-trip 1: backward ∘ forward = id (proved via `ext'` + uncompleted identity).
  have h_back_fwd : backwardHom.comp forwardHom = RingHom.id _ := by
    apply RingHom.ext
    intro x
    show backwardHom (forwardHom x) = x
    refine @UniformSpace.Completion.ext' _ _ _ _ _ _ _
      ((UniformSpace.Completion.continuous_extension).comp
        UniformSpace.Completion.continuous_extension)
      continuous_id ?_ x
    intro a
    show backwardHom (forwardHom (UniformSpace.Completion.coeRingHom a)) =
      UniformSpace.Completion.coeRingHom a
    have hfwd : forwardHom (UniformSpace.Completion.coeRingHom a) =
        iteratedPlus_forwardToCompletion P D₀ f a :=
      UniformSpace.Completion.extensionHom_coe _ _ a
    rw [hfwd]
    show backwardHom ((iteratedPlusDatum_B P D₀ f).coeRingHom
      (iteratedPlus_forwardLocHom D₀ a)) = _
    have hbwd : backwardHom ((iteratedPlusDatum_B P D₀ f).coeRingHom
        (iteratedPlus_forwardLocHom D₀ a)) =
        iteratedPlus_backwardLocHom D₀ f hsub
          (iteratedPlus_forwardLocHom D₀ a) :=
      UniformSpace.Completion.extensionHom_coe _ _ _
    rw [hbwd]
    have := congr_fun (congrArg DFunLike.coe
      (iteratedPlus_backward_forward_locHom D₀ f hsub)) a
    simp only [RingHom.comp_apply] at this
    exact this
  -- Round-trip 2: forward ∘ backward = id. Needs the dual uncompleted identity,
  -- which in turn requires density of `canonicalMap a` in B. This is a genuinely
  -- hard residual obligation — recorded as a single `sorry` here.
  have h_fwd_back : forwardHom.comp backwardHom = RingHom.id _ := sorry
  exact {
    toFun := forwardHom
    invFun := backwardHom
    left_inv := fun x =>
      congr_fun (congrArg DFunLike.coe h_back_fwd) x
    right_inv := fun y =>
      congr_fun (congrArg DFunLike.coe h_fwd_back) y
    map_mul' := map_mul _
    map_add' := map_add _
  }

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
    (f : A) :
    presheafValue (laurentMinusDatum D₀ f) ≃+*
      presheafValue (iteratedMinusDatum_B P D₀ f) := by
  -- Structural closure via the uncompleted-level infrastructure above.
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
  have hsub := laurentMinus_subset D₀ f
  have hcont_fwd : @Continuous _ _ (laurentMinusDatum D₀ f).topology _
      (iteratedMinus_forwardToCompletion P D₀ f) := sorry
  have hcont_bwd : @Continuous _ _ (iteratedMinusDatum_B P D₀ f).topology _
      (iteratedMinus_backwardLocHom D₀ f hsub) := sorry
  let forwardHom : presheafValue (laurentMinusDatum D₀ f) →+*
      presheafValue (iteratedMinusDatum_B P D₀ f) :=
    UniformSpace.Completion.extensionHom
      (iteratedMinus_forwardToCompletion P D₀ f) hcont_fwd
  let backwardHom : presheafValue (iteratedMinusDatum_B P D₀ f) →+*
      presheafValue (laurentMinusDatum D₀ f) :=
    UniformSpace.Completion.extensionHom
      (iteratedMinus_backwardLocHom D₀ f hsub) hcont_bwd
  have h_back_fwd : backwardHom.comp forwardHom = RingHom.id _ := by
    apply RingHom.ext
    intro x
    show backwardHom (forwardHom x) = x
    refine @UniformSpace.Completion.ext' _ _ _ _ _ _ _
      ((UniformSpace.Completion.continuous_extension).comp
        UniformSpace.Completion.continuous_extension)
      continuous_id ?_ x
    intro a
    show backwardHom (forwardHom (UniformSpace.Completion.coeRingHom a)) =
      UniformSpace.Completion.coeRingHom a
    have hfwd : forwardHom (UniformSpace.Completion.coeRingHom a) =
        iteratedMinus_forwardToCompletion P D₀ f a :=
      UniformSpace.Completion.extensionHom_coe _ _ a
    rw [hfwd]
    show backwardHom ((iteratedMinusDatum_B P D₀ f).coeRingHom
      (iteratedMinus_forwardLocHom D₀ f a)) = _
    have hbwd : backwardHom ((iteratedMinusDatum_B P D₀ f).coeRingHom
        (iteratedMinus_forwardLocHom D₀ f a)) =
        iteratedMinus_backwardLocHom D₀ f hsub
          (iteratedMinus_forwardLocHom D₀ f a) :=
      UniformSpace.Completion.extensionHom_coe _ _ _
    rw [hbwd]
    have := congr_fun (congrArg DFunLike.coe
      (iteratedMinus_backward_forward_locHom D₀ f hsub)) a
    simp only [RingHom.comp_apply] at this
    exact this
  have h_fwd_back : forwardHom.comp backwardHom = RingHom.id _ := sorry
  exact {
    toFun := forwardHom
    invFun := backwardHom
    left_inv := fun x =>
      congr_fun (congrArg DFunLike.coe h_back_fwd) x
    right_inv := fun y =>
      congr_fun (congrArg DFunLike.coe h_fwd_back) y
    map_mul' := map_mul _
    map_add' := map_add _
  }

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
      IsNoetherianRing ↥((presheafValue_pairOfDefinition P D₀).some.A₀))
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
        (presheafValue_pairOfDefinition P D₀).some
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
    (presheafValue_pairOfDefinition P D₀).some
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
    (f : A)
    (hNoeth_B : IsNoetherianRing (presheafValue D₀))
    (hLocLift_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      HasLocLiftPowerBounded (presheafValue D₀))
    (hA₀Noeth_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      letI : IsNoetherianRing (presheafValue D₀) := hNoeth_B
      IsNoetherianRing ↥((presheafValue_pairOfDefinition P D₀).some.A₀))
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
        (presheafValue_pairOfDefinition P D₀).some
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

/-- **Sub-sorry: compatibility of `presheafValue_iteratedPlus_equiv` with
`canonicalMap`.**

This is the single residual fact blocking `laurentPlusBridge_restrictionMap`.
Morally, `presheafValue_iteratedPlus_equiv` identifies the two presheaf values
in a way that respects the canonical maps from `A` (via the tower
`A → presheafValue D₀ → presheafValue (iteratedPlusDatum_B P D₀ f)`, which
matches `A → presheafValue (laurentPlusDatum D₀ f)` under the identification).

Currently `presheafValue_iteratedPlus_equiv` is itself a sorry'd `noncomputable
def`; once it is defined concretely, this compatibility will be a straightforward
consequence of the definition. We expose it as a separate sub-sorry so that
`laurentPlusBridge_restrictionMap` can be proved modulo this precise claim
(parallel to the minus-branch sub-sorry). -/
theorem presheafValue_iteratedPlus_equiv_restrictionMap_canonicalMap
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (D₀ : RationalLocData A)
    [IsNoetherianRing (locSubring D₀.P D₀.T D₀.s)]
    (f : A)
    (hplus : rationalOpen (laurentPlusDatum D₀ f).T (laurentPlusDatum D₀ f).s ⊆
      rationalOpen D₀.T D₀.s) (x : presheafValue D₀) :
    presheafValue_iteratedPlus_equiv P D₀ f
        (restrictionMap D₀ (laurentPlusDatum D₀ f) hplus x) =
      (iteratedPlusDatum_B P D₀ f).canonicalMap x := by
  -- Reduce to the uncompleted-level identity via `Completion.ext'` on `x`.
  -- Both sides are ring-hom images of `x : presheafValue D₀` and the equation is
  -- closed when we check on `x = D₀.coeRingHom a'` for `a' : Loc_A(D₀.s)`:
  --   LHS(a') = forwardHom (restrictionMapHom _ _ _ (coeRingHom a'))
  --           = forwardHom (coeRingHom_{laurentPlus} (restrictionMapAlg a'))
  --           = forwardToCompletion (restrictionMapAlg a')
  --           = coeRingHom_B (forwardLocHom (restrictionMapAlg a'))
  --   RHS(a') = coeRingHom_B (algebraMap B _ (canonicalMap_A_to_B a_of_a'))
  -- These agree whenever `forwardLocHom ∘ restrictionMapAlg = algebraMap_B ∘ canonicalMap`,
  -- which is the uncompleted-level coherence. Verified via `IsLocalization.ringHom_ext`.
  -- However, this requires structural unfolding that tangles instances; we defer
  -- the full algebraic chase to a future closure and leave as sorry — noting it
  -- is now REDUCIBLE (no longer opaque) since `presheafValue_iteratedPlus_equiv`
  -- has a concrete `toFun = forwardHom` depending only on the continuity sorries.
  sorry

/-- **Route B bridge (plus compatibility)**: the plus bridge intertwines
`restrictionMap` and the first projection of `epsilonHom_gen`.

Proof structure: `laurentPlusBridge` is `(presheafValue_iteratedPlus_equiv).trans
(presheafValue_trivialPlus_fSubX_equiv ...)`. The second factor is
`(example638Plus_equiv ...).symm`, which maps
`(iteratedPlusDatum_B P D₀ f).canonicalMap x ↦ mk(algebraMap x)` by
`example638Plus_equiv_symm_canonicalMap` (via the definitional equality
`iteratedPlusDatum_B = trivialPlusDatum`). The first factor's action on
`restrictionMap ... x` is the content of
`presheafValue_iteratedPlus_equiv_restrictionMap_canonicalMap` (currently a
sub-sorry; it is the single residual fact blocking a full proof, parallel
to the minus-branch sub-sorry).

Modulo that sub-sorry, the theorem reduces by direct computation. -/
theorem laurentPlusBridge_restrictionMap
    [IsTateRing A] [IsNoetherianRing A] [T2Space A]
    [NonarchimedeanRing A]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (D₀ : RationalLocData A) [IsNoetherianRing (locSubring D₀.P D₀.T D₀.s)]
    (f : A)
    (hNoeth_B : IsNoetherianRing (presheafValue D₀))
    (hLocLift_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      HasLocLiftPowerBounded (presheafValue D₀))
    (hA₀Noeth_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      letI : IsNoetherianRing (presheafValue D₀) := hNoeth_B
      IsNoetherianRing ↥((presheafValue_pairOfDefinition P D₀).some.A₀))
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
        (presheafValue_pairOfDefinition P D₀).some
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
    (presheafValue_pairOfDefinition P D₀).some
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
    (f : A)
    (hminus : rationalOpen (laurentMinusDatum D₀ f).T (laurentMinusDatum D₀ f).s ⊆
      rationalOpen D₀.T D₀.s) (x : presheafValue D₀) :
    presheafValue_iteratedMinus_equiv P D₀ f
        (restrictionMap D₀ (laurentMinusDatum D₀ f) hminus x) =
      (iteratedMinusDatum_B P D₀ f).canonicalMap x := by
  -- Parallel to the plus branch: reduce to an uncompleted-level identity via
  -- `Completion.ext'` on `x`, then compute on the dense `coeRingHom` image
  -- using `iteratedMinus_forwardLocHom_algebraMap` +
  -- `iteratedMinus_backwardLocHom_algebraMap` + `restrictionMapHom_canonicalMap`.
  -- Deferred pending the same full algebraic chase as the plus branch.
  sorry

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
    (f : A)
    (hNoeth_B : IsNoetherianRing (presheafValue D₀))
    (hLocLift_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      HasLocLiftPowerBounded (presheafValue D₀))
    (hA₀Noeth_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      letI : IsNoetherianRing (presheafValue D₀) := hNoeth_B
      IsNoetherianRing ↥((presheafValue_pairOfDefinition P D₀).some.A₀))
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
        (presheafValue_pairOfDefinition P D₀).some
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

/-- **Sub-sorry: overlap bridge τ₁₂ existence.**

The ring isomorphism identifying the presheaf value at the Laurent overlap
with the algebraic overlap ring `B₁₂_gen (D₀.canonicalMap f)`, parallel to
`laurentPlusBridge` and `laurentMinusBridge` but at the overlap. The
statement `Nonempty (... ≃+* ...)` is enough for the downstream delta-
vanishing argument.

**Structural note.** As originally stated, this existence sorry produces an
arbitrary ring equiv; the intertwining theorems below then take this
equiv as input and attempt to prove identities about it. That's not
provable for a generic equiv — the intertwining identities determine the
equiv up to the image of the plus/minus restrictions, which generate a
dense subring. To obtain a proof path, one must either (a) replace this
sorry with the `Nonempty LaurentOverlapBridgeCompatible` variant, so the
intertwining theorems take the compatibility witness and extract the
desired identity directly, or (b) provide a CONCRETE construction for
`τ₁₂` (see the note above about the Laurent analog of Example 6.38).

The required new primitive (Laurent analog of Example 6.38) is: for a
strongly noetherian complete Tate base `B` with `b : B`, there is a ring
isomorphism
`LaurentTateAlgebra B ⧸ (algebraMap b − ζ) ≃+* presheafValue(D_overlap_B)`
where `D_overlap_B` is the "Laurent overlap datum" on `B`. This is not
yet available in the project. -/
theorem laurentOverlapBridge_exists
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (D₀ : RationalLocData A) [IsNoetherianRing (locSubring D₀.P D₀.T D₀.s)]
    (f : A) :
    Nonempty (presheafValue (laurentOverlapDatum D₀ f) ≃+*
      LaurentCover.B₁₂_gen (D₀.canonicalMap f)) := by
  sorry

/-- **Sub-sorry: overlap bridge intertwining with the plus side.**

The overlap bridge `τ₁₂` commutes with the plus restriction map via `posLift`:
`τ₁₂ ∘ restrictionMap(plus → overlap) = posLift ∘ laurentPlusBridge`. -/
theorem laurentOverlap_plus_intertwine
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (D₀ : RationalLocData A) [IsNoetherianRing (locSubring D₀.P D₀.T D₀.s)]
    (f : A)
    (hNoeth_B : IsNoetherianRing (presheafValue D₀))
    (hLocLift_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      HasLocLiftPowerBounded (presheafValue D₀))
    (hA₀Noeth_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      letI : IsNoetherianRing (presheafValue D₀) := hNoeth_B
      IsNoetherianRing ↥((presheafValue_pairOfDefinition P D₀).some.A₀))
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
        (presheafValue_pairOfDefinition P D₀).some
      letI : IsNoetherianRing ↥P_B.A₀ := hA₀Noeth_B
      @Continuous _ _
        (quotientPlusFSubXIdealTopology (presheafValue D₀) (D₀.canonicalMap f))
        (inferInstance : TopologicalSpace (presheafValue
          (trivialPlusDatum (presheafValue D₀) P_B (D₀.canonicalMap f))))
        (example638Plus_forwardHom (presheafValue D₀) P_B (D₀.canonicalMap f)))
    (τ₁₂ : presheafValue (laurentOverlapDatum D₀ f) ≃+*
      LaurentCover.B₁₂_gen (D₀.canonicalMap f))
    (uplus : presheafValue (laurentPlusDatum D₀ f)) :
    τ₁₂ (restrictionMap (laurentPlusDatum D₀ f) (laurentOverlapDatum D₀ f)
          (laurentOverlap_subset_plus D₀ f) uplus) =
      LaurentCover.posLift (D₀.canonicalMap f)
        (laurentPlusBridge P D₀ f hNoeth_B hLocLift_B hA₀Noeth_B hA_complete_B
          hnoeth_B hcont_forward_B uplus) := by
  sorry

/-- **Sub-sorry: overlap bridge intertwining with the minus side.**

The overlap bridge `τ₁₂` commutes with the minus restriction map via `negLift`:
`τ₁₂ ∘ restrictionMap(minus → overlap) = negLift ∘ laurentMinusBridge`. -/
theorem laurentOverlap_minus_intertwine
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (D₀ : RationalLocData A) [IsNoetherianRing (locSubring D₀.P D₀.T D₀.s)]
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
    (τ₁₂ : presheafValue (laurentOverlapDatum D₀ f) ≃+*
      LaurentCover.B₁₂_gen (D₀.canonicalMap f))
    (uminus : presheafValue (laurentMinusDatum D₀ f)) :
    τ₁₂ (restrictionMap (laurentMinusDatum D₀ f) (laurentOverlapDatum D₀ f)
          (laurentOverlap_subset_minus D₀ f) uminus) =
      LaurentCover.negLift (D₀.canonicalMap f)
        (laurentMinusBridge P D₀ f hnoeth_B hcont_eval_B uminus) := by
  sorry

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
    (f : A)
    (hNoeth_B : IsNoetherianRing (presheafValue D₀))
    (hLocLift_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      HasLocLiftPowerBounded (presheafValue D₀))
    (hA₀Noeth_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      letI : IsNoetherianRing (presheafValue D₀) := hNoeth_B
      IsNoetherianRing ↥((presheafValue_pairOfDefinition P D₀).some.A₀))
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
        (presheafValue_pairOfDefinition P D₀).some
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
          (tateQuotientToPresheafHom D hb)) :
    ∃ τ₁₂ : presheafValue (laurentOverlapDatum D₀ f) ≃+*
          LaurentCover.B₁₂_gen (D₀.canonicalMap f),
      LaurentOverlapBridgeCompatible P D₀ f hNoeth_B hLocLift_B hA₀Noeth_B
        hA_complete_B hnoeth_B hcont_forward_B hcont_eval_B τ₁₂ := by
  -- This theorem packages the three sub-sorries above into a single
  -- existence claim for a bridge satisfying both intertwining identities.
  -- The proof is equivalent in strength to filling all three original sorries:
  -- given such a τ₁₂, both intertwinings hold; conversely, a proof of this
  -- theorem provides the compatible τ₁₂ whose existence underlies all three.
  sorry

/-- **Consequence**: from a compatible bridge, the plus-side intertwining is
an immediate projection from the compatibility structure. This shows that
the original `laurentOverlap_plus_intertwine` holds when `τ₁₂` is chosen to
satisfy `LaurentOverlapBridgeCompatible` — which is the intended usage. -/
theorem laurentOverlap_plus_intertwine_of_compatible
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (D₀ : RationalLocData A) [IsNoetherianRing (locSubring D₀.P D₀.T D₀.s)]
    (f : A)
    (hNoeth_B : IsNoetherianRing (presheafValue D₀))
    (hLocLift_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      HasLocLiftPowerBounded (presheafValue D₀))
    (hA₀Noeth_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      letI : IsNoetherianRing (presheafValue D₀) := hNoeth_B
      IsNoetherianRing ↥((presheafValue_pairOfDefinition P D₀).some.A₀))
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
        (presheafValue_pairOfDefinition P D₀).some
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
    (f : A)
    (hNoeth_B : IsNoetherianRing (presheafValue D₀))
    (hLocLift_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      HasLocLiftPowerBounded (presheafValue D₀))
    (hA₀Noeth_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      letI : IsNoetherianRing (presheafValue D₀) := hNoeth_B
      IsNoetherianRing ↥((presheafValue_pairOfDefinition P D₀).some.A₀))
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
        (presheafValue_pairOfDefinition P D₀).some
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
    (f : A)
    (hNoeth_B : IsNoetherianRing (presheafValue D₀))
    (hLocLift_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      HasLocLiftPowerBounded (presheafValue D₀))
    (hA₀Noeth_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      letI : IsNoetherianRing (presheafValue D₀) := hNoeth_B
      IsNoetherianRing ↥((presheafValue_pairOfDefinition P D₀).some.A₀))
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
        (presheafValue_pairOfDefinition P D₀).some
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
  -- The strengthened existence theorem `laurentOverlapBridge_exists_compatible`
  -- produces a bridge together with a compatibility witness, packaging all
  -- three original sub-sorries (existence + two intertwinings) into one
  -- primitive that captures the actual algebraic content needed here.
  obtain ⟨τ₁₂, hcompat_bridge⟩ := laurentOverlapBridge_exists_compatible P D₀ f
    hNoeth_B hLocLift_B hA₀Noeth_B hA_complete_B hnoeth_B hcont_forward_B
    hcont_eval_B
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
    (f : A)
    (hNoeth_B : IsNoetherianRing (presheafValue D₀))
    (hLocLift_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      HasLocLiftPowerBounded (presheafValue D₀))
    (hA₀Noeth_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      letI : IsNoetherianRing (presheafValue D₀) := hNoeth_B
      IsNoetherianRing ↥((presheafValue_pairOfDefinition P D₀).some.A₀))
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
        (presheafValue_pairOfDefinition P D₀).some
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
      uplus uminus hcompat)

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
    (f : A)
    (hNoeth_B : IsNoetherianRing (presheafValue D₀))
    (hLocLift_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      HasLocLiftPowerBounded (presheafValue D₀))
    (hA₀Noeth_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      letI : IsNoetherianRing (presheafValue D₀) := hNoeth_B
      IsNoetherianRing ↥((presheafValue_pairOfDefinition P D₀).some.A₀))
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
        (presheafValue_pairOfDefinition P D₀).some
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
    hplus hminus uplus uminus hcompat

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
    [IsTateRing A] [IsNoetherianRing A] [T2Space A]
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
  -- Pick a d ∈ V_covers with τ d = E (from surjectivity); the restriction map
  -- E → d is injective (restrictionMapHom_injective), so the equation
  -- restrictionMap E d (hτ d) a = restrictionMap E d (hτ d) b gives a = b.
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
    [IsTateRing A] [IsNoetherianRing A] [T2Space A]
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
  · -- Part 1: Separation via Wedhorn Cor 8.32 (Phase 3 of the Wedhorn plan).
    -- The current bridge goes through `restrictionMapHom_injective` in
    -- `PresheafTateStructure.lean` (which still has its own sorry pending Phase 3
    -- — replacement by faithful-flatness-of-the-product-restriction).
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
    [IsTateRing A] [IsNoetherianRing A] [T2Space A]
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
    [IsTateRing A] [IsNoetherianRing A] [T2Space A]
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
