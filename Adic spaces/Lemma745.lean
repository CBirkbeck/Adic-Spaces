/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».AnalyticPoints
import «Adic spaces».AffinoidRings
import «Adic spaces».ValuationCoarsening
import «Adic spaces».ValuationPrimeConvex
import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.GroupTheory.ArchimedeanDensely

/-!
# Lemma 7.45: Analytic Point Construction

Given a complete affinoid ring `(A, A⁺)` with pair of definition `(A₀, I)` and a
non-open prime `𝔭` of `A`, we construct `v ∈ Spa(A, A⁺)` with `supp(v) = 𝔭`.

This is the key surjectivity result for the support map
`supp : Spa(A, A⁺) → {non-open primes of A}` (Lemma 7.45 of Wedhorn).

## Main results

* `Valuation.isContinuous_of_ideal_pow_lt` : Continuity criterion for valuations on
  Huber rings: if `I^n`-elements have value `< γ` for every `γ > 0`, then `v` is continuous.

* `PairOfDefinition.exists_valuationSubring_of_nonOpen_prime` : The algebraic core of
  Lemma 7.45: given a non-open prime `𝔭`, construct a valuation subring `V` of
  `FractionRing (A ⧸ 𝔭)` such that `A₀/𝔭₀ ⊆ V` and `image(I) ⊆ nonunits(V)`.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn2019adic], Lemma 7.45
-/

open Filter Topology

/-! ### Section 1: Continuity criterion for valuations on Huber rings -/

namespace Valuation

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]

/-- **Continuity criterion for valuations on Huber rings.** A valuation `v` is
continuous if for every `γ > 0`, some power `I^n` maps into
`{ a | v(a) < γ }`. -/
theorem isContinuous_of_ideal_pow_lt
    (P : PairOfDefinition A) (v : Valuation A Γ₀)
    (h : ∀ (γ : Γ₀), 0 < γ → ∃ n : ℕ,
      ∀ (a : P.A₀), a ∈ P.I ^ n → v (P.A₀.subtype a) < γ) :
    v.IsContinuous := by
  intro γ
  by_cases hγ : γ = 0
  · subst hγ; simp [not_lt_zero']
  · have hγ_pos : (0 : Γ₀) < γ := zero_lt_iff.mpr hγ
    obtain ⟨n, hn⟩ := h γ hγ_pos
    have h_sub : P.A₀.subtype '' ((P.I ^ n : Ideal P.A₀) : Set P.A₀) ⊆ { a | v a < γ } := by
      rintro _ ⟨y, hy, rfl⟩
      exact hn y hy
    rw [show { a : A | v a < γ } =
      (v.ltAddSubgroup (Units.mk0 γ hγ) : Set A) from by ext; simp [ltAddSubgroup]]
    exact AddSubgroup.isOpen_of_mem_nhds _
      (Filter.mem_of_superset
        ((P.pow_image_isOpen n).mem_nhds (Set.mem_image_of_mem _ (P.I ^ n).zero_mem))
        h_sub)

/-- Continuity via cofinal powers of a bound `g < 1`. -/
theorem isContinuous_of_le_one_and_pow_cofinal
    (P : PairOfDefinition A) (v : Valuation A Γ₀)
    (h_le : ∀ (a : P.A₀), v (P.A₀.subtype a) ≤ 1)
    {g : Γ₀} (hg0 : g ≠ 0) (hg1 : g < 1)
    (h_gen : ∀ (a : P.A₀), a ∈ P.I → v (P.A₀.subtype a) ≤ g)
    (h_cofinal : ∀ (γ : Γ₀), 0 < γ → ∃ n : ℕ, g ^ n < γ) :
    v.IsContinuous := by
  apply isContinuous_of_ideal_pow_lt P
  intro γ hγ
  obtain ⟨n, hn⟩ := h_cofinal γ hγ
  suffices key : ∀ (m : ℕ) (a : P.A₀), a ∈ P.I ^ m → v (P.A₀.subtype a) ≤ g ^ m by
    exact ⟨n, fun a ha ↦ lt_of_le_of_lt (key n a ha) hn⟩
  intro m
  induction m with
  | zero => intro a _; simpa using h_le a
  | succ m ih =>
    intro a ha
    rw [pow_succ] at ha
    refine Submodule.mul_induction_on ha (fun x hx y hy ↦ ?_) (fun x y hx hy ↦ ?_)
    · calc v (P.A₀.subtype (x * y))
          = v (P.A₀.subtype x) * v (P.A₀.subtype y) := by simp [map_mul]
        _ ≤ g ^ m * g := mul_le_mul' (ih x hx) (h_gen y hy)
        _ = g ^ (m + 1) := (pow_succ g m).symm
    · calc v (P.A₀.subtype (x + y))
          ≤ max (v (P.A₀.subtype x)) (v (P.A₀.subtype y)) := by
            simp only [map_add]; exact v.map_add _ _
        _ ≤ g ^ (m + 1) := max_le hx hy

end Valuation

/-! ### Section 2: Algebraic construction for Lemma 7.45 -/

namespace PairOfDefinition

open ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A]
  [IsTopologicalRing A] [IsLinearTopology A A]

/-- The composition `A₀ → A → A/𝔭 → Frac(A/𝔭)` as a ring homomorphism. -/
noncomputable def toFractionQuotient (P : PairOfDefinition A)
    (𝔭 : Ideal A) : P.A₀ →+* FractionRing (A ⧸ 𝔭) :=
  ((algebraMap (A ⧸ 𝔭) (FractionRing (A ⧸ 𝔭))).comp (Ideal.Quotient.mk 𝔭)).comp P.A₀.subtype

omit [IsTopologicalRing A] [IsLinearTopology A A] in
/-- The kernel of `A₀ → Frac(A/𝔭)` equals `𝔭 ∩ A₀` when `𝔭` is prime. -/
theorem ker_toFractionQuotient (P : PairOfDefinition A)
    {𝔭 : Ideal A} [𝔭.IsPrime] :
    RingHom.ker (P.toFractionQuotient 𝔭) = Ideal.comap P.A₀.subtype 𝔭 := by
  ext a
  simp only [RingHom.mem_ker, toFractionQuotient, RingHom.comp_apply,
    Ideal.mem_comap, Subring.coe_subtype]
  constructor
  · intro h
    rwa [← Ideal.Quotient.eq_zero_iff_mem,
      ← (IsFractionRing.injective (A ⧸ 𝔭) (FractionRing (A ⧸ 𝔭))).eq_iff, map_zero]
  · intro h
    exact (congr_arg _ (Ideal.Quotient.eq_zero_iff_mem.mpr h)).trans (map_zero _)

omit [IsTopologicalRing A] [IsLinearTopology A A] in
/-- The image of `I` under the range-restricted map is proper. -/
theorem image_I_ne_top (P : PairOfDefinition A)
    [IsAdicComplete P.I P.A₀]
    {𝔭 : Ideal A} [𝔭.IsPrime] :
    Ideal.map (P.toFractionQuotient 𝔭).rangeRestrict P.I ≠ ⊤ := by
  haveI : (Ideal.comap P.A₀.subtype 𝔭).IsPrime := Ideal.IsPrime.comap P.A₀.subtype
  have h_ne := P.I_sup_prime_ne_top (𝔭₀ := Ideal.comap P.A₀.subtype 𝔭)
  intro htop
  apply h_ne; clear h_ne
  have hsurj := (P.toFractionQuotient 𝔭).rangeRestrict_surjective
  have hker : RingHom.ker (P.toFractionQuotient 𝔭).rangeRestrict =
      Ideal.comap P.A₀.subtype 𝔭 := by
    rw [RingHom.ker_rangeRestrict, P.ker_toFractionQuotient]
  rw [← Ideal.map_top (f := (P.toFractionQuotient 𝔭).rangeRestrict),
    Ideal.map_eq_iff_sup_ker_eq_of_surjective _ hsurj, top_sup_eq, hker] at htop
  exact htop

/-! ### The domination theorem applied to non-open primes -/

omit [IsTopologicalRing A] [IsLinearTopology A A] in
/-- **Algebraic core of Lemma 7.45.** The domination theorem produces
a `ValuationSubring V` with `image(A₀) ⊆ V` and `image(I) ⊆ V.nonunits`. -/
theorem exists_valuationSubring_of_prime (P : PairOfDefinition A)
    [IsAdicComplete P.I P.A₀]
    {𝔭 : Ideal A} [𝔭.IsPrime] :
    ∃ V : ValuationSubring (FractionRing (A ⧸ 𝔭)),
      (P.toFractionQuotient 𝔭).range ≤ V.toSubring ∧
      (P.toFractionQuotient 𝔭).range.subtype ''
        (Ideal.map (P.toFractionQuotient 𝔭).rangeRestrict P.I : Set _) ⊆ V.nonunits :=
  Ideal.image_subset_nonunits_valuationSubring _ P.image_I_ne_top

/-! ### Support computation -/

omit [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A] in
/-- Support of the pullback along `A → Frac(A/𝔭)` equals `𝔭`. -/
theorem supp_comap_quotient_fractionRing {𝔭 : Ideal A} [𝔭.IsPrime]
    {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
    (v : Valuation (FractionRing (A ⧸ 𝔭)) Γ₀) :
    (v.comap ((algebraMap (A ⧸ 𝔭) (FractionRing (A ⧸ 𝔭))).comp
      (Ideal.Quotient.mk 𝔭))).supp = 𝔭 := by
  ext a
  simp only [Valuation.mem_supp_iff, Valuation.comap_apply, RingHom.comp_apply]
  haveI : IsDomain (A ⧸ 𝔭) := Ideal.Quotient.isDomain 𝔭
  constructor
  · intro h
    by_contra ha
    have hq : (Ideal.Quotient.mk 𝔭) a ≠ 0 :=
      fun h0 ↦ ha (Ideal.Quotient.eq_zero_iff_mem.mp h0)
    have hk : (algebraMap (A ⧸ 𝔭) (FractionRing (A ⧸ 𝔭)))
        ((Ideal.Quotient.mk 𝔭) a) ≠ 0 := by
      rw [ne_eq, map_eq_zero_iff _
        (IsFractionRing.injective (A ⧸ 𝔭) (FractionRing (A ⧸ 𝔭)))]
      exact hq
    exact hk (v.zero_iff.mp h)
  · intro h
    simp [Ideal.Quotient.eq_zero_iff_mem.mpr h]

end PairOfDefinition

/-! ### Section 3: Concrete valuation from the domination theorem -/

namespace PairOfDefinition

open ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A]
  [IsTopologicalRing A] [IsLinearTopology A A]

/-- The pulled-back valuation from `V : ValuationSubring(Frac(A/𝔭))` to `A`. -/
noncomputable def pulledBackValuation (_P : PairOfDefinition A)
    {𝔭 : Ideal A} [𝔭.IsPrime]
    (V : ValuationSubring (FractionRing (A ⧸ 𝔭))) :
    Valuation A V.ValueGroup :=
  haveI : IsDomain (A ⧸ 𝔭) := Ideal.Quotient.isDomain 𝔭
  V.valuation.comap ((algebraMap (A ⧸ 𝔭) (FractionRing (A ⧸ 𝔭))).comp (Ideal.Quotient.mk 𝔭))

omit [IsTopologicalRing A] [IsLinearTopology A A] in
/-- The pulled-back valuation has support equal to `𝔭`. -/
theorem pulledBackValuation_supp (P : PairOfDefinition A)
    {𝔭 : Ideal A} [𝔭.IsPrime] (V : ValuationSubring (FractionRing (A ⧸ 𝔭))) :
    (P.pulledBackValuation V).supp = 𝔭 :=
  supp_comap_quotient_fractionRing V.valuation

omit [IsTopologicalRing A] [IsLinearTopology A A] in
/-- The pulled-back valuation relates to `V.valuation` via `toFractionQuotient`. -/
theorem pulledBackValuation_eq_valuation_toFractionQuotient (P : PairOfDefinition A)
    {𝔭 : Ideal A} [𝔭.IsPrime]
    (V : ValuationSubring (FractionRing (A ⧸ 𝔭))) (a : P.A₀) :
    P.pulledBackValuation V (P.A₀.subtype a) = V.valuation (P.toFractionQuotient 𝔭 a) := by
  simp only [pulledBackValuation, Valuation.comap_apply]
  rfl

omit [IsTopologicalRing A] [IsLinearTopology A A] in
/-- The pulled-back valuation has value `≤ 1` on `A₀`. -/
theorem pulledBackValuation_le_one (P : PairOfDefinition A)
    {𝔭 : Ideal A} [𝔭.IsPrime]
    {V : ValuationSubring (FractionRing (A ⧸ 𝔭))}
    (hV : (P.toFractionQuotient 𝔭).range ≤ V.toSubring) (a : P.A₀) :
    P.pulledBackValuation V (P.A₀.subtype a) ≤ 1 := by
  rw [pulledBackValuation_eq_valuation_toFractionQuotient]
  exact (ValuationSubring.valuation_le_one_iff V _).mpr (hV ⟨a, rfl⟩)

omit [IsTopologicalRing A] [IsLinearTopology A A] in
/-- The pulled-back valuation has value `< 1` on `I`. -/
theorem pulledBackValuation_lt_one (P : PairOfDefinition A)
    {𝔭 : Ideal A} [𝔭.IsPrime]
    {V : ValuationSubring (FractionRing (A ⧸ 𝔭))}
    (hnonunits : (P.toFractionQuotient 𝔭).range.subtype ''
      (Ideal.map (P.toFractionQuotient 𝔭).rangeRestrict P.I : Set _) ⊆ V.nonunits)
    {a : P.A₀} (ha : a ∈ P.I) :
    P.pulledBackValuation V (P.A₀.subtype a) < 1 := by
  rw [pulledBackValuation_eq_valuation_toFractionQuotient]
  exact (ValuationSubring.mem_nonunits_iff V).mp
    (hnonunits (Set.mem_image_of_mem _ (Ideal.mem_map_of_mem _ ha)))

end PairOfDefinition

/-! ### Section 4: Lemma 7.45 -- Analytic point construction -/

namespace PairOfDefinition

open ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A]
  [IsTopologicalRing A] [IsLinearTopology A A]

omit [IsTopologicalRing A] [IsLinearTopology A A] in
/-- **Lemma 7.45 (algebraic core).** Produces `v` with `supp(v) = 𝔭`,
`v ≤ 1` on `A₀`, and `v < 1` on `I`. -/
theorem exists_valuationSubring_and_properties (P : PairOfDefinition A)
    [IsAdicComplete P.I P.A₀]
    {𝔭 : Ideal A} [𝔭.IsPrime] (_h : ¬IsOpen (𝔭 : Set A)) :
    ∃ V : ValuationSubring (FractionRing (A ⧸ 𝔭)),
      (P.pulledBackValuation V).supp = 𝔭 ∧
      (∀ a : P.A₀, P.pulledBackValuation V (P.A₀.subtype a) ≤ 1) ∧
      (∀ a : P.A₀, a ∈ P.I → P.pulledBackValuation V (P.A₀.subtype a) < 1) := by
  obtain ⟨V, hrange, hnonunits⟩ := P.exists_valuationSubring_of_prime (𝔭 := 𝔭)
  exact ⟨V, P.pulledBackValuation_supp V,
    P.pulledBackValuation_le_one hrange,
    fun a ha ↦ P.pulledBackValuation_lt_one hnonunits ha⟩

/-! ### Section 5: Continuity via MulArchimedean -/

/-- Valuation bound on `I` follows from bound on generators. -/
theorem valuation_le_on_ideal_of_le_on_generators
    {R : Type*} [CommRing R]
    {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
    {A₀ : Subring R} (v : Valuation R Γ₀)
    (h_le : ∀ (a : A₀), v (A₀.subtype a) ≤ 1)
    {I : Ideal A₀} {S : Finset A₀}
    (hS : Ideal.span (↑S : Set A₀) = I)
    {g : Γ₀}
    (h_gen : ∀ s ∈ S, v (A₀.subtype s) ≤ g)
    {a : A₀} (ha : a ∈ I) :
    v (A₀.subtype a) ≤ g := by
  rw [← hS] at ha
  induction ha using Submodule.span_induction with
  | mem x hx => exact h_gen x (Finset.mem_coe.mp hx)
  | zero => simp only [map_zero]; exact zero_le'
  | add x y _ _ hx hy =>
    calc v (A₀.subtype (x + y))
        ≤ max (v (A₀.subtype x)) (v (A₀.subtype y)) := by
          rw [map_add]; exact v.map_add _ _
      _ ≤ g := max_le hx hy
  | smul r x _ hx =>
    calc v (A₀.subtype (r • x))
        = v (A₀.subtype r) * v (A₀.subtype x) := by
          simp only [smul_eq_mul, map_mul]
      _ ≤ 1 * g := mul_le_mul' (h_le r) hx
      _ = g := one_mul g

/-- The pulled-back valuation is continuous when `MulArchimedean`. -/
theorem pulledBackValuation_isContinuous
    (P : PairOfDefinition A) [IsAdicComplete P.I P.A₀]
    {𝔭 : Ideal A} [𝔭.IsPrime] (h𝔭 : ¬IsOpen (𝔭 : Set A))
    {V : ValuationSubring (FractionRing (A ⧸ 𝔭))}
    (hrange : (P.toFractionQuotient 𝔭).range ≤ V.toSubring)
    (hnonunits : (P.toFractionQuotient 𝔭).range.subtype ''
      (Ideal.map (P.toFractionQuotient 𝔭).rangeRestrict P.I : Set _) ⊆ V.nonunits)
    [MulArchimedean V.ValueGroup] :
    (P.pulledBackValuation V).IsContinuous := by
  haveI : IsDomain (A ⧸ 𝔭) := Ideal.Quotient.isDomain 𝔭
  set v := P.pulledBackValuation V with hv_def
  obtain ⟨S, hS⟩ := P.fg
  obtain ⟨a₀, ha₀_I, ha₀_notp⟩ := P.exists_mem_I_not_mem_of_not_isOpen h𝔭
  have hSne : S.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hS_eq
    have hI_bot : P.I = ⊥ := by rw [← hS, hS_eq, Finset.coe_empty, Ideal.span_empty]
    have ha₀_zero : a₀ = 0 := Ideal.mem_bot.mp (hI_bot ▸ ha₀_I)
    exact ha₀_notp (by rw [ha₀_zero, map_zero]; exact 𝔭.zero_mem)
  set g := S.sup' hSne (fun s ↦ v (P.A₀.subtype s)) with hg_def
  have hg1 : g < 1 := (Finset.sup'_lt_iff hSne).mpr fun s hs ↦
    P.pulledBackValuation_lt_one hnonunits
      (hS ▸ Ideal.subset_span (Finset.mem_coe.mpr hs))
  have h_gen : ∀ a : P.A₀, a ∈ P.I → v (P.A₀.subtype a) ≤ g :=
    fun a ha ↦ valuation_le_on_ideal_of_le_on_generators v
      (P.pulledBackValuation_le_one hrange) hS
      (fun s hs ↦ Finset.le_sup' (fun s ↦ v (P.A₀.subtype s)) hs) ha
  have hg0 : g ≠ 0 := ne_of_gt <|
    lt_of_lt_of_le (zero_lt_iff.mpr (show v (P.A₀.subtype a₀) ≠ 0 by
      rwa [ne_eq, ← Valuation.mem_supp_iff, P.pulledBackValuation_supp V]))
      (h_gen a₀ ha₀_I)
  exact Valuation.isContinuous_of_le_one_and_pow_cofinal P v
    (P.pulledBackValuation_le_one hrange) hg0 hg1 h_gen
    (fun γ hγ ↦ exists_pow_lt₀ hg1 (Units.mk0 γ hγ.ne'))

/-- **Lemma 7.45 (conditional on MulArchimedean).** -/
theorem exists_mem_spa_supp_eq_of_nonOpen_prime_mulArchimedean
    (P : PairOfDefinition A) [IsAdicComplete P.I P.A₀] [PlusSubring A]
    {𝔭 : Ideal A} [𝔭.IsPrime] (h𝔭 : ¬IsOpen (𝔭 : Set A))
    {V : ValuationSubring (FractionRing (A ⧸ 𝔭))}
    (hrange : (P.toFractionQuotient 𝔭).range ≤ V.toSubring)
    (hnonunits : (P.toFractionQuotient 𝔭).range.subtype ''
      (Ideal.map (P.toFractionQuotient 𝔭).rangeRestrict P.I : Set _) ⊆ V.nonunits)
    [MulArchimedean V.ValueGroup]
    (hAplus : ∀ f ∈ (A⁺ : Set A), P.pulledBackValuation V f ≤ 1) :
    ∃ v ∈ Spa A A⁺, v.supp = 𝔭 := by
  haveI : IsDomain (A ⧸ 𝔭) := Ideal.Quotient.isDomain 𝔭
  set w := P.pulledBackValuation V
  refine ⟨ofValuation w, ⟨?_, ?_⟩, ?_⟩
  · exact isContinuous_ofValuation_of w
      (P.pulledBackValuation_isContinuous h𝔭 hrange hnonunits)
  · intro f hf; change w f ≤ w 1; rw [map_one]; exact hAplus f hf
  · rw [supp_ofValuation]; exact P.pulledBackValuation_supp V

end PairOfDefinition

/-! ### Section 6: Coarsening to MulArchimedean value group

The valuation subring `V` from the domination theorem may not have a MulArchimedean
value group. We coarsen by the largest convex subgroup of `(V.ValueGroup)ˣ` that
avoids a chosen I-generator's value (§7.1 of Wedhorn). -/

section CoarsenByUnits

variable {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]

/-- The composition `Γ₀ → WithZero(Γ₀ˣ) → WithZero(Γ₀ˣ ⧸ H)` as a `MonoidWithZeroHom`. -/
noncomputable def coarsenMapOfValueGroup
    (H : ConvexSubgroup Γ₀ˣ) :
    Γ₀ →*₀ WithZero (Γ₀ˣ ⧸ H.toSubgroup) :=
  (WithZero.mapMonoidWithZeroHom (QuotientGroup.mk' H.toSubgroup)).comp
    (OrderMonoidIso.withZeroUnits (α := Γ₀)).symm.toMonoidWithZeroHom

theorem coarsenMapOfValueGroup_monotone
    (H : ConvexSubgroup Γ₀ˣ) :
    Monotone (coarsenMapOfValueGroup H) := by
  intro a b hab
  unfold coarsenMapOfValueGroup
  simp only [MonoidWithZeroHom.comp_apply]
  apply WithZero.mapMonoidWithZeroHom_monotone _ H.quotientMk_monotone
  exact (OrderMonoidIso.withZeroUnits (α := Γ₀)).symm.toOrderIso.monotone hab

theorem coarsenMapOfValueGroup_apply_zero (H : ConvexSubgroup Γ₀ˣ) :
    coarsenMapOfValueGroup H 0 = 0 := map_zero _

theorem coarsenMapOfValueGroup_apply_unit (H : ConvexSubgroup Γ₀ˣ) (g : Γ₀ˣ) :
    coarsenMapOfValueGroup H (g : Γ₀) =
    ↑(QuotientGroup.mk' H.toSubgroup g) := by
  unfold coarsenMapOfValueGroup
  simp only [MonoidWithZeroHom.comp_apply]
  have : (OrderMonoidIso.withZeroUnits (α := Γ₀)).symm.toMonoidWithZeroHom (g : Γ₀) =
      (g : WithZero Γ₀ˣ) := by
    show (WithZero.withZeroUnitsEquiv (G := Γ₀)).symm (g : Γ₀) = ↑g
    exact WithZero.withZeroUnitsEquiv_symm_apply_coe g
  rw [this, WithZero.mapMonoidWithZeroHom_apply_coe]

end CoarsenByUnits

namespace Valuation

variable {R : Type*} [CommRing R]
  {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]

/-- Coarsening a valuation by a convex subgroup of the units of its value group. -/
noncomputable def coarsenByUnits
    (v : Valuation R Γ₀) (H : ConvexSubgroup Γ₀ˣ) :
    Valuation R (WithZero (Γ₀ˣ ⧸ H.toSubgroup)) :=
  v.map (coarsenMapOfValueGroup H) (coarsenMapOfValueGroup_monotone H)

theorem coarsenByUnits_apply
    (v : Valuation R Γ₀) (H : ConvexSubgroup Γ₀ˣ) (r : R) :
    v.coarsenByUnits H r = coarsenMapOfValueGroup H (v r) :=
  Valuation.map_apply _ _ _ _

theorem coarsenByUnits_supp
    (v : Valuation R Γ₀) (H : ConvexSubgroup Γ₀ˣ) :
    (v.coarsenByUnits H).supp = v.supp := by
  ext r
  simp only [mem_supp_iff, coarsenByUnits_apply]
  constructor
  · intro h
    by_contra hr
    have hne : v r ≠ 0 := hr
    set u := Units.mk0 (v r) hne
    have : coarsenMapOfValueGroup H (v r) = ↑(QuotientGroup.mk' H.toSubgroup u) :=
      coarsenMapOfValueGroup_apply_unit H u
    rw [this] at h
    exact WithZero.coe_ne_zero h
  · intro h; rw [h, map_zero]

theorem coarsenByUnits_le_one_of_le_one
    (v : Valuation R Γ₀) (H : ConvexSubgroup Γ₀ˣ)
    {a : R} (ha : v a ≤ 1) :
    (v.coarsenByUnits H) a ≤ 1 := by
  rw [coarsenByUnits_apply]
  have h1 : coarsenMapOfValueGroup H 1 = 1 := map_one _
  rw [← h1]
  exact coarsenMapOfValueGroup_monotone H ha

/-- If `v(a) ≠ 0`, `Units.mk0 (v a) ∉ H`, and `v(a) ≤ 1`, then `(v.coarsenByUnits H)(a) < 1`.

The unit part of `v(a)` is not in `H` and `≤ 1`, hence `< 1` (since `1 ∈ H`).
The quotient projection then sends it strictly below `1`. -/
theorem coarsenByUnits_lt_one_of_not_mem
    (v : Valuation R Γ₀) (H : ConvexSubgroup Γ₀ˣ)
    {a : R} (ha_ne : v a ≠ 0)
    (ha_not_mem : Units.mk0 (v a) ha_ne ∉ H) (ha_le : v a ≤ 1) :
    v.coarsenByUnits H a < 1 := by
  set u := Units.mk0 (v a) ha_ne with hu_def
  -- u ≤ 1 from ha_le, and u ≠ 1 (since u ∉ H but 1 ∈ H), hence u < 1
  have hu_ne : u ≠ 1 :=
    fun h ↦ ha_not_mem (h ▸ H.toSubgroup.one_mem)
  have hu_lt : u < 1 :=
    lt_of_le_of_ne (Units.val_le_val.mp ha_le) (fun h ↦ hu_ne h)
  -- coarsenByUnits H a = coarsenMapOfValueGroup H (↑u) = ↑(π u)
  have hva_eq : v a = (u : Γ₀) := rfl
  rw [coarsenByUnits_apply, hva_eq, coarsenMapOfValueGroup_apply_unit H u]
  -- π(u) < 1 by quotientMk_lt_one_of_not_mem
  exact WithZero.coe_lt_one.mpr (H.quotientMk_lt_one_of_not_mem hu_lt ha_not_mem)

/-! ### Restriction of a valuation to a convex subgroup (Wedhorn's retraction 7.1.2) -/

open Classical in
/-- **Restriction of a valuation to a convex subgroup.**

For `v : Valuation R Γ₀` with `∀ r, v r ≤ 1` and a convex subgroup `H` of `Γ₀ˣ`,
the restricted valuation keeps values whose unit part is in `H` and zeros out the rest.

This is Wedhorn's retraction `r(v) = v_{|cΓ_v(I)}` from (7.1.2). Unlike coarsening
(which quotients by H), restriction KEEPS H as the value group. The cofinal property
holds automatically when `H = convexGenerated(y)` (by `exists_inv_pow_lt_of_mem_convexGenerated`).

**Requires:** `∀ r, v r ≤ 1` — without this, multiplicativity can fail. -/
noncomputable def restrictToConvex
    (v : Valuation R Γ₀) (H : ConvexSubgroup Γ₀ˣ)
    (hle : ∀ r : R, v r ≤ 1) :
    Valuation R (WithZero H.toSubgroup) where
  toFun r :=
    if h : v r = 0 then 0
    else if hm : Units.mk0 (v r) h ∈ H then some ⟨Units.mk0 (v r) h, hm⟩
    else 0
  map_zero' := by simp [map_zero]
  map_one' := by
    simp only [map_one]
    have h1 : (1 : Γ₀) ≠ 0 := one_ne_zero
    have hm : Units.mk0 (1 : Γ₀) h1 ∈ H := by
      have : Units.mk0 (1 : Γ₀) h1 = 1 := Units.ext rfl
      rw [this]; exact one_mem H
    simp [h1]; rfl
  map_mul' x y := by
    -- Helper: if u ∉ H and u ≤ 1 and w ≤ u, then w ∉ H (by convexity with 1 ∈ H)
    have not_mem_of_le' {u w : Γ₀ˣ} (hu : u ∉ H) (hu1 : u ≤ 1) (hw1 : w ≤ u) : w ∉ H :=
      fun hw_mem => hu (H.convex hw_mem (one_mem H) hw1 hu1)
    -- All unit parts are ≤ 1 (from hle)
    have unit_le_one' : ∀ (r : R) (hr : v r ≠ 0), Units.mk0 (v r) hr ≤ 1 :=
      fun r hr => Units.val_le_val.mp (hle r)
    -- Case: v x = 0
    by_cases hx : v x = 0
    · have hxy : v (x * y) = 0 := by rw [map_mul, hx, zero_mul]
      simp only [hxy, hx, dif_pos, zero_mul]
    -- Case: v y = 0
    by_cases hy : v y = 0
    · have hxy : v (x * y) = 0 := by rw [map_mul, hy, mul_zero]
      simp only [hxy, hy, dif_pos, mul_zero]
    -- Both nonzero. Set up unit parts.
    have hxy_ne : v (x * y) ≠ 0 := by rw [map_mul]; exact mul_ne_zero hx hy
    -- Key: Units.mk0 (v (x*y)) _ = Units.mk0 (v x) _ * Units.mk0 (v y) _
    have huxy_eq : Units.mk0 (v (x * y)) hxy_ne =
        Units.mk0 (v x) hx * Units.mk0 (v y) hy := Units.ext (map_mul v x y)
    -- Case analysis on membership in H
    by_cases hmx : Units.mk0 (v x) hx ∈ H <;> by_cases hmy : Units.mk0 (v y) hy ∈ H
    · -- Both in H: product in H
      have hmxy : Units.mk0 (v (x * y)) hxy_ne ∈ H := huxy_eq ▸ mul_mem hmx hmy
      simp only [hx, hy, hxy_ne, dif_neg, dif_pos hmx, dif_pos hmy, dif_pos hmxy, not_false_eq_true]
      -- Goal: some ⟨uxy, hmxy⟩ = some ⟨ux, hmx⟩ * some ⟨uy, hmy⟩
      -- In WithZero, (↑a : WithZero _) * ↑b = ↑(a * b)
      rw [show (some (⟨Units.mk0 (v x) hx, hmx⟩ : H.toSubgroup) : WithZero H.toSubgroup) =
        (↑(⟨Units.mk0 (v x) hx, hmx⟩ : H.toSubgroup) : WithZero H.toSubgroup) from rfl,
        show (some (⟨Units.mk0 (v y) hy, hmy⟩ : H.toSubgroup) : WithZero H.toSubgroup) =
        (↑(⟨Units.mk0 (v y) hy, hmy⟩ : H.toSubgroup) : WithZero H.toSubgroup) from rfl,
        ← WithZero.coe_mul]
      congr 1
      exact Subtype.ext huxy_eq
    · -- ux ∈ H, uy ∉ H: product ∉ H
      have hmxy : Units.mk0 (v (x * y)) hxy_ne ∉ H := by
        rw [huxy_eq]; intro hmem
        exact hmy (by have := mul_mem (inv_mem hmx) hmem; rwa [inv_mul_cancel_left] at this)
      simp only [hx, hy, hxy_ne, dif_neg, dif_pos hmx, dif_neg hmy, dif_neg hmxy, not_false_eq_true,
        mul_zero]
    · -- ux ∉ H, uy ∈ H: product ∉ H
      have hmxy : Units.mk0 (v (x * y)) hxy_ne ∉ H := by
        rw [huxy_eq]; intro hmem
        exact hmx (by have := mul_mem hmem (inv_mem hmy); rwa [mul_inv_cancel_right] at this)
      simp only [hx, hy, hxy_ne, dif_neg, dif_neg hmx, dif_pos hmy, dif_neg hmxy, not_false_eq_true,
        zero_mul]
    · -- Both ∉ H: product ∉ H (by convexity)
      have hmxy : Units.mk0 (v (x * y)) hxy_ne ∉ H := by
        rw [huxy_eq]
        intro hmem
        have hle_ux : Units.mk0 (v x) hx * Units.mk0 (v y) hy ≤ Units.mk0 (v x) hx :=
          Units.val_le_val.mp (show (v x) * (v y) ≤ v x from by
            calc v x * v y ≤ v x * 1 := mul_le_mul_right (hle y) (v x)
              _ = v x := mul_one _)
        exact not_mem_of_le' hmx (unit_le_one' x hx) hle_ux hmem
      simp only [hx, hy, hxy_ne, dif_neg, dif_neg hmx, dif_neg hmy, dif_neg hmxy, not_false_eq_true,
        mul_zero]
  map_add_le_max' x y := by
    -- We name the function for clarity.
    set f : R → WithZero H.toSubgroup := fun r =>
      if h : v r = 0 then 0
      else if hm : Units.mk0 (v r) h ∈ H then some ⟨Units.mk0 (v r) h, hm⟩
      else 0
    show f (x + y) ≤ max (f x) (f y)
    -- The key ultrametric from v
    have hv_add : v (x + y) ≤ max (v x) (v y) := v.map_add x y
    -- If f(x+y) = 0, we are done (0 ≤ anything)
    by_cases hxy : v (x + y) = 0
    · simp only [f, hxy, dif_pos]; exact bot_le
    by_cases hmxy : Units.mk0 (v (x + y)) hxy ∈ H
    · -- f(x+y) = some ⟨u_{x+y}, _⟩. Need to show this ≤ max (f x) (f y).
      -- Since v(x+y) ≤ max(v x, v y) and v(x+y) > 0, the max is > 0.
      -- We need: some ⟨u_{x+y}, _⟩ ≤ max(f x)(f y).
      -- It suffices to show that the max side has its unit in H, and that unit ≥ u_{x+y}.
      -- Use le_total to pick the dominant side.
      rcases le_total (v x) (v y) with hvxy | hvyx
      · -- v x ≤ v y, so max(v x, v y) = v y
        have hv_le : v (x + y) ≤ v y := hv_add.trans (max_eq_right hvxy).le
        suffices h : f (x + y) ≤ f y from h.trans (le_max_right _ _)
        have hy : v y ≠ 0 := ne_of_gt (lt_of_lt_of_le (zero_lt_iff.mpr hxy) hv_le)
        by_cases hmy : Units.mk0 (v y) hy ∈ H
        · simp only [f, hxy, hy, dif_neg, dif_pos hmxy, dif_pos hmy]
          exact WithZero.coe_le_coe.mpr (Subtype.mk_le_mk.mpr
            (Units.val_le_val.mp hv_le))
        · exfalso
          exact hmy (H.convex hmxy (one_mem H) (Units.val_le_val.mp hv_le)
            (Units.val_le_val.mp (hle y)))
      · -- v y ≤ v x: symmetric case
        have hv_le : v (x + y) ≤ v x := hv_add.trans (max_eq_left hvyx).le
        suffices h : f (x + y) ≤ f x from h.trans (le_max_left _ _)
        have hx' : v x ≠ 0 := ne_of_gt (lt_of_lt_of_le (zero_lt_iff.mpr hxy) hv_le)
        by_cases hmx : Units.mk0 (v x) hx' ∈ H
        · simp only [f, hxy, hx', dif_neg, dif_pos hmxy, dif_pos hmx]
          exact WithZero.coe_le_coe.mpr (Subtype.mk_le_mk.mpr
            (Units.val_le_val.mp hv_le))
        · exfalso
          exact hmx (H.convex hmxy (one_mem H) (Units.val_le_val.mp hv_le)
            (Units.val_le_val.mp (hle x)))
    · -- f(x+y) = 0 (unit not in H), so ≤ anything
      simp only [f, dif_neg hxy, dif_neg hmxy]; exact bot_le

end Valuation

/-! ### Section 7: Lemma 7.45 -- full proof -/

namespace PairOfDefinition

open ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A]
  [IsTopologicalRing A] [IsLinearTopology A A]

/-- **Existence of a MulArchimedean dominating valuation (algebraic core of Lemma 7.45).**

Given a non-open prime `𝔭` and the pair of definition `(A₀, I)` of a complete
Huber ring, there exists a valuation subring `V` of `Frac(A/𝔭)` such that:
1. `A₀/𝔭₀ ⊆ V` (range containment)
2. Image of I lands in nonunits of V (ideal condition)
3. `V.ValueGroup` is MulArchimedean (rank ≤ 1)

This combines the domination theorem (`exists_valuationSubring_of_prime`) with
a coarsening step: the V from the domination theorem may have higher rank.
We coarsen to a rank-1 overring using `ValuationSubring.ofPrime` applied to the
minimal prime of V lying over the I-images. The coarsened ring is rank-1 because
it is obtained by localizing at a prime, giving a quotient of the value group
by a convex subgroup with archimedean quotient.

The key algebraic input is that `image_I_ne_top` (from I-adic completeness)
prevents all I-generators from becoming units in the coarsened ring. -/
theorem exists_mulArchimedean_valuationSubring_of_prime
    (P : PairOfDefinition A) [IsAdicComplete P.I P.A₀]
    {𝔭 : Ideal A} [𝔭.IsPrime] (h𝔭 : ¬IsOpen (𝔭 : Set A)) :
    ∃ V : ValuationSubring (FractionRing (A ⧸ 𝔭)),
      (P.toFractionQuotient 𝔭).range ≤ V.toSubring ∧
      (P.toFractionQuotient 𝔭).range.subtype ''
        (Ideal.map (P.toFractionQuotient 𝔭).rangeRestrict P.I : Set _) ⊆ V.nonunits ∧
      MulArchimedean V.ValueGroup := by
  haveI : IsDomain (A ⧸ 𝔭) := Ideal.Quotient.isDomain 𝔭
  -- Step 1: Get V₀ from domination theorem (conditions 1-2 but not necessarily rank 1)
  obtain ⟨V₀, hrange₀, hnonunits₀⟩ := P.exists_valuationSubring_of_prime (𝔭 := 𝔭)
  -- Step 2: Build ring hom φ : A₀ →+* V₀ via the range containment
  have hφ : ∀ a : P.A₀, P.toFractionQuotient 𝔭 a ∈ V₀.toSubring :=
    fun a => hrange₀ ⟨a, rfl⟩
  let φ : P.A₀ →+* V₀ := (P.toFractionQuotient 𝔭).codRestrict V₀.toSubring hφ
  -- Key: φ a viewed in K is the same as P.toFractionQuotient 𝔭 a
  have hφ_coe : ∀ a : P.A₀, (φ a : FractionRing (A ⧸ 𝔭)) = P.toFractionQuotient 𝔭 a :=
    fun a => rfl
  -- Step 3: Elements of Ideal.map φ I are nonunits in V₀
  -- We prove: Ideal.map φ I ≤ maximalIdeal V₀
  have hJ_le_maximal : Ideal.map φ P.I ≤ IsLocalRing.maximalIdeal V₀ := by
    rw [Ideal.map, Ideal.span_le]
    rintro x ⟨a, ha, rfl⟩
    rw [SetLike.mem_coe, ← ValuationSubring.coe_mem_nonunits_iff]
    show (φ a : FractionRing (A ⧸ 𝔭)) ∈ V₀.nonunits
    rw [hφ_coe]
    exact hnonunits₀ ⟨⟨P.toFractionQuotient 𝔭 a, ⟨a, rfl⟩⟩,
      Ideal.mem_map_of_mem _ ha, rfl⟩
  -- Step 4: Find a₀ ∈ I with a₀ ∉ 𝔭 (so its image is nonzero in K)
  obtain ⟨a₀, ha₀_I, ha₀_notp⟩ := P.exists_mem_I_not_mem_of_not_isOpen h𝔭
  have hφa₀_ne : φ a₀ ≠ 0 := by
    intro h
    have : (φ a₀ : FractionRing (A ⧸ 𝔭)) = 0 := congr_arg Subtype.val h
    rw [hφ_coe] at this
    simp only [toFractionQuotient, RingHom.comp_apply, Subring.coe_subtype] at this
    rw [map_eq_zero_iff _ (IsFractionRing.injective (A ⧸ 𝔭) (FractionRing (A ⧸ 𝔭)))] at this
    exact ha₀_notp (Ideal.Quotient.eq_zero_iff_mem.mp this)
  -- Step 5: Ideal.map φ I is nonzero and proper
  have hJ_ne_bot : Ideal.map φ P.I ≠ ⊥ := by
    intro h; exact hφa₀_ne (Ideal.mem_bot.mp (h ▸ Ideal.mem_map_of_mem φ ha₀_I))
  have hJ_ne_top : Ideal.map φ P.I ≠ ⊤ :=
    ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal (R := V₀)).ne_top hJ_le_maximal
  -- Step 6: Get a minimal prime Q over Ideal.map φ I
  haveI : (IsLocalRing.maximalIdeal V₀).IsPrime :=
    (IsLocalRing.maximalIdeal.isMaximal (R := V₀)).isPrime
  obtain ⟨Q, hQ_min, hQ_le_max⟩ :=
    Ideal.exists_minimalPrimes_le (J := IsLocalRing.maximalIdeal V₀) hJ_le_maximal
  haveI : Q.IsPrime := Ideal.minimalPrimes_isPrime hQ_min
  have hJ_le_Q : Ideal.map φ P.I ≤ Q := hQ_min.1.2
  -- Step 7: V₀.ofPrime Q satisfies all three conditions
  refine ⟨V₀.ofPrime Q, ?_, ?_, ?_⟩
  -- Condition 1: Range containment (V₀ ≤ V₀.ofPrime Q)
  · exact le_trans hrange₀ (ValuationSubring.le_ofPrime V₀ Q)
  -- Condition 2: I-images are nonunits of V₀.ofPrime Q
  · -- An element of K is a nonunit of V₀.ofPrime Q iff its valuation is < 1.
    -- For x : V₀ with x ∈ Q, the valuation is ≠ 1 (by ofPrime_valuation_eq_one_iff)
    -- and ≤ 1 (since V₀ ≤ V₀.ofPrime Q), hence < 1.
    intro x hx
    obtain ⟨⟨y, hy_range⟩, hy_mem, rfl⟩ := hx
    obtain ⟨a, rfl⟩ := hy_range
    show (P.toFractionQuotient 𝔭 a : FractionRing (A ⧸ 𝔭)) ∈ (V₀.ofPrime Q).nonunits
    rw [← hφ_coe, ValuationSubring.mem_nonunits_iff]
    -- Need: (V₀.ofPrime Q).valuation (φ a : K) < 1
    -- We know φ a ∈ V₀ ≤ V₀.ofPrime Q, so valuation ≤ 1
    have hle : (V₀.ofPrime Q).valuation (φ a : FractionRing (A ⧸ 𝔭)) ≤ 1 :=
      (ValuationSubring.valuation_le_one_iff _ _).mpr
        (ValuationSubring.le_ofPrime V₀ Q (hφ a))
    -- And φ a ∈ Q means valuation ≠ 1
    have hne : (V₀.ofPrime Q).valuation (φ a : FractionRing (A ⧸ 𝔭)) ≠ 1 := by
      intro h1
      -- φ a ∈ Q means φ a ∉ Q.primeCompl
      have ha_in_Q : φ a ∈ Q := by
        -- a ∈ I follows from hy_mem (the map rangeRestrict a ∈ Ideal.map rangeRestrict I)
        -- and Ideal.mem_map_of_mem gives φ a ∈ Ideal.map φ I ≤ Q
        have : (P.toFractionQuotient 𝔭).rangeRestrict a ∈
            Ideal.map (P.toFractionQuotient 𝔭).rangeRestrict P.I := hy_mem
        rw [Ideal.mem_map_iff_of_surjective _
          (P.toFractionQuotient 𝔭).rangeRestrict_surjective] at this
        obtain ⟨b, hb_I, hb_eq⟩ := this
        have hab : φ a = φ b := by
          ext; simp only [hφ_coe]; exact congr_arg Subtype.val hb_eq.symm
        rw [hab]; exact hJ_le_Q (Ideal.mem_map_of_mem φ hb_I)
      have ha_in_Qc := (V₀.ofPrime_valuation_eq_one_iff_mem_primeCompl Q (φ a)).mp h1
      exact absurd ha_in_Qc (show φ a ∉ Q.primeCompl from
        Ideal.mem_primeCompl_iff.not.mpr (not_not.mpr ha_in_Q))
    exact lt_of_le_of_ne hle hne
  -- Condition 3: MulArchimedean (V₀.ofPrime Q).ValueGroup
  -- Use mulArchimedean_ofPrime_of_height_one: need Q ≠ ⊥ and Q height-1.
  · apply ValuationSubring.mulArchimedean_ofPrime_of_height_one
    -- Q ≠ ⊥ (since J ≠ ⊥ and J ≤ Q)
    · intro hQ_bot
      exact absurd (hQ_bot ▸ hJ_le_Q (Ideal.mem_map_of_mem φ ha₀_I))
        (Ideal.mem_bot.not.mpr hφa₀_ne)
    -- Height-1: ∀ P prime, P < Q → P = ⊥
    --
    -- **Status: sorry.** The claim "the minimal prime Q over a nonzero ideal
    -- J in a valuation ring is height-1" is FALSE in general valuation rings.
    -- Counterexample: a valuation ring with value group Z x Z (lex order) has
    -- primes ⊥ < P₁ < m. Taking J = m, the minimal prime over J is m itself,
    -- which has height 2. See `ValuationPrimeConvex.lean` lines 146-164 for
    -- a detailed discussion.
    --
    -- In our setting, J = Ideal.map φ P.I where P.I is finitely generated
    -- (the ideal of definition). In a valuation ring, finitely generated
    -- ideals are principal, so J = (j₀) for some j₀. For any prime P < Q
    -- with Q minimal over (j₀):
    --   (a) j₀ ∉ P (by `not_le_of_lt_minimalPrime`)
    --   (b) For p ∈ P: either j₀ ∣ p or p ∣ j₀ (by `dvd_or_dvd`)
    --   (c) If p ∣ j₀ then j₀ ∈ P, contradicting (a). So j₀ ∣ p.
    --   (d) p = j₀ · r with r ∈ P (since P prime and j₀ ∉ P)
    --   (e) Hence P = j₀ · P, and by iteration P ⊆ (j₀ⁿ) for all n
    --   (f) Need: ⋂ₙ (j₀ⁿ) = {0} in a valuation domain
    --
    -- Step (f) is the Krull intersection theorem, which holds in Noetherian
    -- domains but NOT in general valuation rings (fails when the value group
    -- has non-archimedean elements). The correct resolution requires either:
    --   (i)  A rank-1 domination argument (Bourbaki, Comm. Alg., Ch. VI),
    --        choosing a rank-1 valuation dominating V₀ from the start, or
    --   (ii) Showing ⋂ₙ (j₀ⁿ) = 0 using I-adic completeness of A₀ transferred
    --        through φ, or
    --   (iii) Restructuring to use the height-1 prime of V₀ directly (requires
    --         showing J ⊆ height-1 prime, which needs additional input).
    --
    -- References: Wedhorn, Adic Spaces, Lemma 7.45; Bourbaki, Comm. Alg.,
    -- Ch. VI, §4, No. 5 (prime-convex correspondence for valuation rings).
    · sorry

/-- **Lemma 7.45 of Wedhorn (direct coarsening approach).**
Non-open primes are supports in `Spa`.

This proof follows Wedhorn's Lemma 7.45 directly:
1. The domination theorem gives `V₀` with `A₀/𝔭₀ ⊆ V₀` and `I ↦ nonunits`.
2. The pulled-back valuation `v₀ : A → V₀.ValueGroup` has support `𝔭`.
3. Choose the I-generator `a₀` with the MAX `v₀`-value among those not in `𝔭`.
4. Coarsen `v₀` by `maxAvoid(u₀⁻¹)` (where `u₀` is the unit part of `v₀(a₀)`).
5. The coarsened valuation has support `𝔭`, is `≤ 1` on `A₀`, and `< 1` on `I`.
6. Continuity follows from cofinal powers of the bound (sorry: MulArchimedean).

This replaces the `exists_mulArchimedean_valuationSubring_of_prime` approach,
eliminating the height-1 prime sorry in favor of a more direct MulArchimedean sorry. -/
theorem exists_mem_spa_supp_eq_of_nonOpen_prime
    (P : PairOfDefinition A) [IsAdicComplete P.I P.A₀] [PlusSubring A]
    {𝔭 : Ideal A} [𝔭.IsPrime] (h𝔭 : ¬IsOpen (𝔭 : Set A))
    (hAplus_le_A₀ : (A⁺ : Set A) ⊆ P.A₀) :
    ∃ v ∈ Spa A A⁺, v.supp = 𝔭 := by
  classical
  haveI : IsDomain (A ⧸ 𝔭) := Ideal.Quotient.isDomain 𝔭
  -- ═══════════════════════════════════════════════════════════════════
  -- Step 1: Get V₀ from the domination theorem
  -- ═══════════════════════════════════════════════════════════════════
  obtain ⟨V₀, hrange₀, hnonunits₀⟩ := P.exists_valuationSubring_of_prime (𝔭 := 𝔭)
  -- ═══════════════════════════════════════════════════════════════════
  -- Step 2: The pulled-back valuation v₀ : A → V₀.ValueGroup
  -- ═══════════════════════════════════════════════════════════════════
  set v₀ := P.pulledBackValuation V₀ with hv₀_def
  -- ═══════════════════════════════════════════════════════════════════
  -- Step 3: Choose the I-generator with MAX value not in 𝔭
  -- ═══════════════════════════════════════════════════════════════════
  -- First get the finite generating set S of I.
  obtain ⟨S, hS⟩ := P.fg
  -- Partition S into those in 𝔭 and those not in 𝔭.
  -- At least one generator is not in 𝔭 (since I ⊄ 𝔭 by non-openness).
  set S' := S.filter (fun s ↦ (P.A₀.subtype s : A) ∉ 𝔭) with hS'_def
  -- S' is nonempty: if all generators were in 𝔭, then I ≤ 𝔭, contradicting non-openness.
  have hS'ne : S'.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]; intro hempty
    have hall : ∀ s ∈ S, (P.A₀.subtype s : A) ∈ 𝔭 := by
      intro s hs; by_contra hns
      have : s ∈ S' := Finset.mem_filter.mpr ⟨hs, hns⟩
      simp [hempty] at this
    -- All generators are in 𝔭, so I ≤ 𝔭 (via the comap characterization).
    have hI_le : P.I ≤ Ideal.comap P.A₀.subtype 𝔭 := by
      rw [← hS, Ideal.span_le]
      intro x hx; exact Ideal.mem_comap.mpr (hall x (Finset.mem_coe.mp hx))
    exact P.idealOfDefinition_not_le_of_not_isOpen h𝔭
      (Ideal.map_le_iff_le_comap.mpr hI_le)
  -- The MAX value among generators not in 𝔭.
  set g₀ := S'.sup' hS'ne (fun s ↦ v₀ (P.A₀.subtype s)) with hg₀_def
  -- g₀ ≠ 0 (pick any s ∈ S'; its value is > 0 ≤ g₀)
  have hg₀_ne : g₀ ≠ 0 := ne_of_gt <| by
    obtain ⟨s, hs⟩ := hS'ne
    have hs_notp : (P.A₀.subtype s : A) ∉ 𝔭 := (Finset.mem_filter.mp hs).2
    have hvs_ne : v₀ (P.A₀.subtype s) ≠ 0 := by
      rwa [ne_eq, ← Valuation.mem_supp_iff, P.pulledBackValuation_supp V₀]
    exact lt_of_lt_of_le (zero_lt_iff.mpr hvs_ne)
      (Finset.le_sup' (fun s ↦ v₀ (P.A₀.subtype s)) hs)
  -- g₀ < 1 (each generator not in 𝔭 has value < 1 by pulledBackValuation_lt_one)
  have hg₀_lt : g₀ < 1 := (Finset.sup'_lt_iff hS'ne).mpr fun s hs ↦
    P.pulledBackValuation_lt_one hnonunits₀
      (hS ▸ Ideal.subset_span (Finset.mem_coe.mpr (Finset.mem_filter.mp hs).1))
  -- ═══════════════════════════════════════════════════════════════════
  -- Step 4: Build the unit u₀ and H = maxAvoid(u₀⁻¹)
  -- ═══════════════════════════════════════════════════════════════════
  set u₀ := Units.mk0 g₀ hg₀_ne with hu₀_def
  -- u₀ < 1 (since g₀ < 1 and g₀ ≠ 0)
  have hu₀_lt : u₀ < 1 := by
    refine lt_of_le_of_ne ?_ ?_
    · exact Units.val_le_val.mp hg₀_lt.le
    · intro h; exact absurd (show (u₀ : V₀.ValueGroup) = 1 from by
        rw [show (1 : V₀.ValueGroupˣ) = Units.mk0 (1 : V₀.ValueGroup) one_ne_zero from
          Units.ext rfl] at h
        exact congr_arg Units.val h) (ne_of_lt hg₀_lt)
  -- u₀⁻¹ > 1, hence u₀⁻¹ ≠ 1
  have hu₀_inv_ne : u₀⁻¹ ≠ 1 :=
    ne_of_gt (one_lt_inv_of_inv hu₀_lt)
  set H := ConvexSubgroup.maxAvoid hu₀_inv_ne with hH_def
  -- ═══════════════════════════════════════════════════════════════════
  -- Step 5: Coarsen v₀ by H
  -- ═══════════════════════════════════════════════════════════════════
  set v' := v₀.coarsenByUnits H with hv'_def
  -- (a) Support: supp(v') = supp(v₀) = 𝔭
  have hsupp : v'.supp = 𝔭 := by
    rw [hv'_def, Valuation.coarsenByUnits_supp, P.pulledBackValuation_supp]
  -- (b) v' ≤ 1 on A₀
  have hle_one : ∀ (a : P.A₀), v' (P.A₀.subtype a) ≤ 1 :=
    fun a ↦ Valuation.coarsenByUnits_le_one_of_le_one v₀ H
      (P.pulledBackValuation_le_one hrange₀ a)
  -- (c) v' < 1 on ALL generators of I (the key step using maxAvoid convexity)
  have hlt_gen : ∀ s ∈ S, v' (P.A₀.subtype s) < 1 := by
    intro s hs
    -- Case 1: s ∈ 𝔭. Then v₀(s) = 0 (since supp(v₀) = 𝔭), so v'(s) = 0 < 1.
    by_cases hs𝔭 : (P.A₀.subtype s : A) ∈ 𝔭
    · have hv₀s : v₀ (P.A₀.subtype s) = 0 := by
        rwa [← Valuation.mem_supp_iff, P.pulledBackValuation_supp V₀]
      rw [hv'_def, Valuation.coarsenByUnits_apply, hv₀s, map_zero]
      exact zero_lt_one
    · -- Case 2: s ∉ 𝔭. The unit uₛ = Units.mk0(v₀(s)) satisfies uₛ ≤ u₀
      -- (since g₀ = MAX over generators not in 𝔭), hence uₛ ∉ H by convexity.
      have hs' : s ∈ S' := Finset.mem_filter.mpr ⟨hs, hs𝔭⟩
      have hvs_ne : v₀ (P.A₀.subtype s) ≠ 0 := by
        rwa [ne_eq, ← Valuation.mem_supp_iff, P.pulledBackValuation_supp V₀]
      have hvs_le : v₀ (P.A₀.subtype s) ≤ g₀ :=
        Finset.le_sup' (fun s ↦ v₀ (P.A₀.subtype s)) hs'
      set uₛ := Units.mk0 (v₀ (P.A₀.subtype s)) hvs_ne
      -- uₛ ≤ u₀ (from hvs_le)
      have huₛ_le : uₛ ≤ u₀ := Units.val_le_val.mp hvs_le
      -- uₛ⁻¹ ≥ u₀⁻¹ > 1. Since u₀⁻¹ ∉ H and u₀⁻¹ ≤ uₛ⁻¹: uₛ⁻¹ ∉ H.
      have huₛ_inv_ge : u₀⁻¹ ≤ uₛ⁻¹ := inv_le_inv' huₛ_le
      have hu₀_inv_gt : 1 < u₀⁻¹ := one_lt_inv_of_inv hu₀_lt
      have huₛ_not_mem : uₛ ∉ H := by
        -- uₛ ∈ H ↔ uₛ⁻¹ ∈ H (subgroup). And uₛ⁻¹ ∉ H by convexity.
        intro hmem
        exact ConvexSubgroup.not_mem_of_not_mem_of_one_lt_le H
          (ConvexSubgroup.not_mem_maxAvoid hu₀_inv_ne) hu₀_inv_gt huₛ_inv_ge
          (inv_mem hmem)
      exact Valuation.coarsenByUnits_lt_one_of_not_mem v₀ H hvs_ne huₛ_not_mem
        (P.pulledBackValuation_le_one hrange₀ s)
  -- ═══════════════════════════════════════════════════════════════════
  -- Step 6: Continuity of v'
  -- ═══════════════════════════════════════════════════════════════════
  -- Build the bound g = sup'(v'(sᵢ)) over generators.
  have hSne : S.Nonempty :=
    hS'ne.mono (Finset.filter_subset _ _)
  set g := S.sup' hSne (fun s ↦ v' (P.A₀.subtype s)) with hg_def
  have hg1 : g < 1 := (Finset.sup'_lt_iff hSne).mpr (fun s hs ↦ hlt_gen s hs)
  have h_gen : ∀ (a : P.A₀), a ∈ P.I → v' (P.A₀.subtype a) ≤ g :=
    fun a ha ↦ valuation_le_on_ideal_of_le_on_generators v' hle_one hS
      (fun s hs ↦ Finset.le_sup' (fun s ↦ v' (P.A₀.subtype s)) hs) ha
  -- g ≠ 0 (since v'(s) ≠ 0 for some generator s not in 𝔭, and v'(s) ≤ g)
  have hg0 : g ≠ 0 := ne_of_gt <| by
    obtain ⟨s, hs⟩ := hS'ne
    have hs_notp : (P.A₀.subtype s : A) ∉ 𝔭 := (Finset.mem_filter.mp hs).2
    have hvs_ne : v' (P.A₀.subtype s) ≠ 0 := by
      rwa [ne_eq, ← Valuation.mem_supp_iff, hsupp]
    exact lt_of_lt_of_le (zero_lt_iff.mpr hvs_ne)
      (h_gen s (hS ▸ Ideal.subset_span (Finset.mem_coe.mpr (Finset.mem_filter.mp hs).1)))
  -- ═══════════════════════════════════════════════════════════════════
  -- Cofinal property (sorry): g^n → 0 in the coarsened value group.
  --
  -- **Status: sorry.** This is equivalent to `MulArchimedean` of the quotient
  -- `V₀.ValueGroupˣ ⧸ maxAvoid(u₀⁻¹)`, which follows from the maxAvoid
  -- construction: every nontrivial convex subgroup of the quotient contains
  -- `[u₀⁻¹]` (by `maxAvoid_mem_of_nontrivial`). Establishing that the
  -- generated subgroup of `[u₀⁻¹]` is the full quotient requires either:
  -- (a) the Krull intersection property `⋂ₙ (j₀ⁿ) = {0}` in V₀, or
  -- (b) connecting I-adic completeness to archimedean properties of the
  --     value group quotient.
  --
  -- Both approaches require results not yet formalized.
  -- References: Wedhorn, Adic Spaces, Lemma 7.45; Bourbaki, Comm. Alg.,
  -- Ch. VI, §4, No. 5.
  -- ═══════════════════════════════════════════════════════════════════
  -- ═══════════════════════════════════════════════════════════════════
  -- The cofinal property for the quotient by `maxAvoid` is FALSE in general.
  -- The correct approach (Wedhorn's retraction 7.1.2) uses RESTRICTION to
  -- `convexGenerated(u₀⁻¹)` instead of coarsening by `maxAvoid(u₀⁻¹)`.
  --
  -- The restriction approach defines a new valuation v_r into
  -- `WithZero (convexGenerated(u₀⁻¹).toSubgroup)` that:
  -- (1) Keeps values whose unit part is in convexGenerated(u₀⁻¹)
  -- (2) Sends other values to 0
  -- (3) Has the cofinal property by `exists_inv_pow_lt_of_mem_convexGenerated`
  --
  -- The full implementation of `restrictToConvex` as a `Valuation` requires
  -- proving multiplicativity and the ultrametric property under the `∀ r, v r ≤ 1`
  -- hypothesis. The multiplicativity proof uses convexity: for values ≤ 1,
  -- elements outside H are BELOW H, so products/sums stay outside H.
  --
  -- For now, we assert the cofinal property and mark the restriction valuation
  -- construction as the remaining sorry.
  -- ═══════════════════════════════════════════════════════════════════
  have hcofinal : ∀ (γ : WithZero (V₀.ValueGroupˣ ⧸ H.toSubgroup)),
      0 < γ → ∃ n : ℕ, g ^ n < γ := by
    sorry -- Requires Wedhorn's restriction approach; see OrderedGroupConvex.convexGenerated
  have hcont : v'.IsContinuous :=
    Valuation.isContinuous_of_le_one_and_pow_cofinal P v' hle_one hg0 hg1 h_gen hcofinal
  -- ═══════════════════════════════════════════════════════════════════
  -- Step 7: Construct the Spa point
  -- ═══════════════════════════════════════════════════════════════════
  refine ⟨ofValuation v', ⟨?_, ?_⟩, ?_⟩
  -- v' is continuous
  · exact isContinuous_ofValuation_of v' hcont
  -- v' ≤ 1 on A⁺ (since A⁺ ⊆ A₀ and v' ≤ 1 on A₀)
  · intro f hf
    change v' f ≤ v' 1; rw [map_one]
    obtain ⟨a, rfl⟩ : ∃ a : P.A₀, P.A₀.subtype a = f := ⟨⟨f, hAplus_le_A₀ hf⟩, rfl⟩
    exact hle_one a
  -- supp(v') = 𝔭
  · rw [supp_ofValuation]; exact hsupp

end PairOfDefinition
