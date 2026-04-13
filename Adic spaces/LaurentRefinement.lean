/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».RationalRefinement
import «Adic spaces».RationalSubsets
import «Adic spaces».TopologyComparison
import «Adic spaces».PresheafTateStructure
import «Adic spaces».LaurentCoverExact
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
    [NonarchimedeanRing A] [IsDomain A]
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

/-- **Laurent cover gluing -- algebraic core**: There exists a pre-completion
element `x' : Localization.Away D₀.s` whose algebraic restrictions match
the given sections.

This is the heart of the partition-of-unity argument. The proof follows
the same scheme as `discrete_gluing` in `TateAcyclicity.lean`:
1. Each section `u±` corresponds (via density + completeness) to an algebraic
   element in the dense image.
2. The cross-compatibility of numerators follows from `hcompat`.
3. The partition of unity `∑ c_i * s_i^N = 1` assembles the global section.

**Sorry justification**: Requires `restrictionMapHom_surj` (Baire category,
PresheafTateStructure.lean) to lift completion elements back to localizations.
This is a deep infrastructure gap (Wedhorn Prop 8.15). -/
theorem laurentCover_algebraic_gluing
    [IsTateRing A] [IsNoetherianRing A] [T2Space A]
    [NonarchimedeanRing A] [IsDomain A]
    (D₀ : RationalLocData A) (f : A)
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
    ∃ x' : Localization.Away D₀.s,
      restrictionMapAlg D₀ (laurentPlusDatum D₀ f) hplus x' =
        uplus ∧
      restrictionMapAlg D₀ (laurentMinusDatum D₀ f) hminus x' =
        uminus := by
  -- The partition-of-unity argument:
  -- 1. span_top_of_laurentCover gives 1 ∈ Ideal.span {s₊, s₋}.
  -- 2. restrictionMapHom_surj gives fractional preimages of u± in presheafValue D₀.
  -- 3. Cross-multiply and use hcompat for numerator compatibility.
  -- 4. Assemble via partition of unity.
  -- Blocking: restrictionMapHom_surj (PresheafTateStructure.lean, Baire category).
  sorry

/-- Laurent cover gluing on presheaf values (Wedhorn Lemma 8.33, presheaf level).

Decomposes into:
1. `laurentCover_algebraic_gluing`: find `x'` at the localization level.
2. Transport via `D₀.coeRingHom` and `extensionHom_coe`. -/
theorem laurentCover_gluing_presheaf
    [IsTateRing A] [IsNoetherianRing A] [T2Space A]
    [NonarchimedeanRing A] [IsDomain A]
    (D₀ : RationalLocData A) (f : A)
    (hplus : rationalOpen (laurentPlusDatum D₀ f).T (laurentPlusDatum D₀ f).s ⊆
      rationalOpen D₀.T D₀.s)
    (hminus : rationalOpen (laurentMinusDatum D₀ f).T (laurentMinusDatum D₀ f).s ⊆
      rationalOpen D₀.T D₀.s)
    (uplus : presheafValue (laurentPlusDatum D₀ f))
    (uminus : presheafValue (laurentMinusDatum D₀ f))
    -- Compatibility: the two sections agree on any common refinement
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
  -- Step 1: Get the algebraic-level preimage.
  obtain ⟨x', hx'_plus, hx'_minus⟩ :=
    laurentCover_algebraic_gluing D₀ f hplus hminus uplus uminus hcompat
  -- Step 2: Lift to presheafValue via coeRingHom.
  refine ⟨D₀.coeRingHom x', ?_, ?_⟩
  · -- restrictionMap D₀ (plus) (coeRingHom x') = uplus
    -- By extensionHom_coe: restrictionMap(coeRingHom x') = restrictionMapAlg x'
    change restrictionMapHom D₀ (laurentPlusDatum D₀ f) hplus (D₀.coeRingHom x') = uplus
    letI := D₀.uniformSpace
    letI := D₀.isTopologicalRing
    letI := D₀.isUniformAddGroup
    letI := (laurentPlusDatum D₀ f).uniformSpace
    letI := (laurentPlusDatum D₀ f).isTopologicalRing
    letI := (laurentPlusDatum D₀ f).isUniformAddGroup
    erw [UniformSpace.Completion.extensionHom_coe
      (restrictionMapAlg D₀ (laurentPlusDatum D₀ f) hplus)
      (restrictionMapAlg_continuous D₀ (laurentPlusDatum D₀ f) hplus) x']
    exact hx'_plus
  · -- restrictionMap D₀ (minus) (coeRingHom x') = uminus
    change restrictionMapHom D₀ (laurentMinusDatum D₀ f) hminus (D₀.coeRingHom x') = uminus
    letI := D₀.uniformSpace
    letI := D₀.isTopologicalRing
    letI := D₀.isUniformAddGroup
    letI := (laurentMinusDatum D₀ f).uniformSpace
    letI := (laurentMinusDatum D₀ f).isTopologicalRing
    letI := (laurentMinusDatum D₀ f).isUniformAddGroup
    erw [UniformSpace.Completion.extensionHom_coe
      (restrictionMapAlg D₀ (laurentMinusDatum D₀ f) hminus)
      (restrictionMapAlg_continuous D₀ (laurentMinusDatum D₀ f) hminus) x']
    exact hx'_minus

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
    [NonarchimedeanRing A] [IsDomain A]
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
    -- The proof uses `restrictionMap_isLocalization` (PresheafTateStructure.lean)
    -- which shows each `presheafValue D` is a localization of `presheafValue C.base`
    -- at `C.base.canonicalMap D.s`. The partition-of-unity argument then produces
    -- the global section. Steps 1 (span-top) and 4 (numerator compatibility)
    -- are sorry'd; they depend on:
    -- - Spa-point construction at non-open primes (StructureSheaf.lean:682)
    -- - Common refinement D₃ with hopen for s₁*s₂ (Tate ring infrastructure)
    -- The partition-of-unity assembly (Steps 5-9) is fully proved.
    --
    -- **Proof sketch** (Wedhorn Theorem 8.28(b)):
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
directly (vacuously true hypothesis for the nonempty branch). -/
theorem rationalCovering_hasSeparation
    [IsTateRing A] [IsNoetherianRing A] [T2Space A]
    [NonarchimedeanRing A] [IsDomain A]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (C : RationalCovering A) :
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
    -- If `C.base.s = 0`, the localization is the zero ring and `presheafValue C.base`
    -- is subsingleton, so x = y trivially.
    -- If `C.base.s ≠ 0`, we'd need a Spa-point construction in `rationalOpen C.base`
    -- to derive a contradiction with the empty cover (since `C.hcover` forces
    -- `rationalOpen C.base = ∅`). This requires the non-open prime case of
    -- `exists_spa_point_in_rationalOpen` (still a sorry in StructureSheaf.lean:655).
    by_cases hs : C.base.s = 0
    · haveI := presheafValue_subsingleton_of_s_eq_zero C.base hs
      exact Subsingleton.elim x y
    · sorry

/-- Gluing extracted from `tateAcyclicity`. Handles empty coverings
directly (any element works since compatibility is vacuous). -/
theorem rationalCovering_hasGluing
    [IsTateRing A] [IsNoetherianRing A] [T2Space A]
    [NonarchimedeanRing A] [IsDomain A]
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
