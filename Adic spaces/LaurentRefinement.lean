/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».RationalRefinement
import «Adic spaces».RationalSubsets
import «Adic spaces».TopologyComparison
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

variable [IsHuberRing A]

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

/-- **Wedhorn Corollary 8.31 + Theorem 8.28**: Tate acyclicity.

For a finite rational covering of a strongly noetherian Tate ring,
the product restriction is faithfully flat. This gives both:
- **Separation** (zero kernel): x restricts to 0 everywhere → x = 0
- **Gluing**: compatible sections have a global pre-image

**Proof route** (Wedhorn):
1. By Prop 8.15, B = presheafValue C.base is a strongly noetherian Tate ring
2. Each presheafValue D is a rational localization of B (Prop 8.15)
3. Each restriction B → presheafValue D is flat (localization = flat)
4. Covering condition → Spec surjectivity: for each prime p of B, some D.s ∉ p
5. Flat + Spec surjective = faithfully flat (Mathlib: `FaithfullyFlat.of_comap_surjective`)
6. Faithfully flat → zero kernel (Mathlib: `FaithfullyFlat.injective`)
7. Laurent cover Čech exactness → gluing (discrete: `laurentCover_exact` part 4)

The central infrastructure is Prop 8.15 (localization principle). -/
theorem tateAcyclicity
    [IsTateRing A] [IsNoetherianRing A] [T2Space A]
    [NonarchimedeanRing A] [FirstCountableTopology A] [IsDomain A]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (C : RationalCovering A) :
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
  -- Prop 8.15: presheafValue C.base is a Tate ring and each cover piece
  -- is its rational localization. This gives faithful flatness via Cor 8.31.
  --
  -- Part 1 (separation): faithfully flat → zero kernel.
  -- Part 2 (gluing): the Čech complex is exact by faithfully flat descent.
  --
  -- Both parts require the localization principle (Prop 8.15) to identify
  -- restriction maps as rational localizations of the Tate ring
  -- B = presheafValue C.base.
  --
  -- Key infrastructure (from PresheafTateStructure.lean):
  -- - presheafValue_isTateRing: B is a Tate ring (Prop 8.15, partial)
  -- - presheafValue_pairOfDefinition: B has a pair of definition
  --
  -- What remains: identifying restriction maps as rational localizations of B
  -- (the full content of Prop 8.15), then applying faithful flatness.
  --
  -- The restriction B → presheafValue D makes canonicalMap(D.s) a unit
  -- (by isUnit_canonicalMap_s). If this is a LOCALIZATION at canonicalMap(D.s):
  -- then it's flat (Localization.flat). The covering condition gives Spec
  -- surjectivity (not all D.s land in any single prime of B). Then
  -- FaithfullyFlat.of_comap_surjective gives the result.
  --
  -- For gluing: faithfully flat descent gives the Čech complex is exact.
  -- Alternatively: use the Laurent cover exactness transferred via Prop 8.15.
  constructor
  · -- Part 1: Separation (zero kernel)
    -- STATUS: BLOCKED on Proposition 8.15 (localization principle).
    --
    -- Proof route (Wedhorn Corollary 8.31):
    -- (a) By Prop 8.15, B := presheafValue C.base is a strongly noetherian Tate ring
    --     and each restrictionMap B → presheafValue D is a rational localization of B.
    --     [MISSING: the localization identification. PresheafTateStructure.lean has
    --     presheafValue_isTateRing (B is Tate) and presheafValue_pairOfDefinition
    --     (B has a pair of definition), but NOT the identification of restrictionMap
    --     as an IsLocalization. This is the core of Prop 8.15.]
    -- (b) Each rational localization is flat over B.
    --     [AVAILABLE modulo (a): presheafValue_flat_of_tateQuotient in StructureSheaf.lean
    --     gives flatness of presheafValue D over A with TopologyComparison hypotheses.
    --     For flatness over B (not A), need the localization identification from (a).]
    -- (c) Covering condition → Spec surjectivity: for every prime p of B, some
    --     D.s does not land in p (because the cover pieces cover the base).
    --     [AVAILABLE once (a) gives the localization identification.]
    -- (d) Flat + Spec surjective = faithfully flat.
    --     [AVAILABLE in Mathlib: Module.FaithfullyFlat.of_comap_surjective]
    -- (e) Faithfully flat → zero kernel (the product algebra map B → ∏ presheafValue D
    --     is injective).
    --     [AVAILABLE in Mathlib: faithfully flat ring maps are injective]
    --
    -- With restrictionMap_isLocalization (Prop 8.15):
    -- Each restriction is a localization → injective (non-zero-divisor at a unit).
    -- So the product restriction is injective.
    intro x hx
    -- Pick any cover piece D (covering is nonempty for nontrivial base).
    by_cases hne : C.covers.Nonempty
    · obtain ⟨D, hD⟩ := hne
      -- The restriction to D is injective (localization at non-zero-divisor).
      have hx_D := hx D hD
      -- restrictionMap(x) = 0 at D.
      -- By IsLocalization: restrictionMap is injective (canonicalMap(D.s) is a unit
      -- in presheafValue D, hence a non-zero-divisor in presheafValue C.base).
      -- So x = 0.
      sorry -- Needs: IsLocalization.injective from restrictionMap_isLocalization
    · -- Empty covering: degenerate case.
      -- C.hcover + C.covers = ∅ implies rationalOpen C.base = ∅.
      -- For a domain Tate ring, this means C.base.s is nilpotent → unit in
      -- Localization.Away → presheafValue C.base = 0.
      -- Edge case; does not arise for coverings from IsSheafy (always nonempty).
      sorry -- Edge case: empty covering implies trivial presheafValue
  · -- Part 2: Gluing
    sorry -- Prop 8.15 → Čech descent / Laurent exactness transfer

/-- Separation extracted from `tateAcyclicity`. -/
theorem rationalCovering_hasSeparation
    [IsTateRing A] [IsNoetherianRing A] [T2Space A]
    [NonarchimedeanRing A] [FirstCountableTopology A] [IsDomain A]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (C : RationalCovering A) :
    ∀ x y : presheafValue C.base,
      (∀ (D : RationalLocData A) (hD : D ∈ C.covers),
        restrictionMap C.base D (C.hsubset D hD) x =
        restrictionMap C.base D (C.hsubset D hD) y) → x = y := by
  intro x y hxy
  have ⟨hzk, _⟩ := tateAcyclicity P C
  exact sub_eq_zero.mp (hzk (x - y) fun D hD => by
    change restrictionMapHom C.base D _ (x - y) = 0
    rw [map_sub, sub_eq_zero]; exact hxy D hD)

/-- Gluing extracted from `tateAcyclicity`. -/
theorem rationalCovering_hasGluing
    [IsTateRing A] [IsNoetherianRing A] [T2Space A]
    [NonarchimedeanRing A] [FirstCountableTopology A] [IsDomain A]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (C : RationalCovering A)
    (f : ∀ (D : ↥C.covers), presheafValue D.1)
    (hcompat : ∀ (D₁ D₂ : ↥C.covers) (D₃ : RationalLocData A)
       (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₁.1.T D₁.1.s)
       (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₂.1.T D₂.1.s),
       restrictionMap D₁.1 D₃ h₃₁ (f D₁) = restrictionMap D₂.1 D₃ h₃₂ (f D₂)) :
    ∃ x : presheafValue C.base, ∀ (D : ↥C.covers),
      restrictionMap C.base D.1 (C.hsubset D.1 D.2) x = f D :=
  (tateAcyclicity P C).2 f hcompat

-- The embedding theorem (Topology.IsEmbedding) is stated in StructureSheaf.lean
-- since it uses `productRestrictionSub` defined there.

end ValuationSpectrum

end
