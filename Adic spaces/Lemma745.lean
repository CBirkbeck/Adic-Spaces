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
        · simp only [f, hxy, hy, dif_pos hmxy, dif_pos hmy]
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
        · simp only [f, hxy, hx', dif_pos hmxy, dif_pos hmx]
          exact WithZero.coe_le_coe.mpr (Subtype.mk_le_mk.mpr
            (Units.val_le_val.mp hv_le))
        · exfalso
          exact hmx (H.convex hmxy (one_mem H) (Units.val_le_val.mp hv_le)
            (Units.val_le_val.mp (hle x)))
    · -- f(x+y) = 0 (unit not in H), so ≤ anything
      simp only [f, dif_neg hxy, dif_neg hmxy]; exact bot_le

/-! ### API for `restrictToConvex` -/

section RestrictToConvexAPI

open Classical

-- Unfold `restrictToConvex` application to the underlying `dite` chain.
private theorem restrictToConvex_unfold
    (v : Valuation R Γ₀) (H : ConvexSubgroup Γ₀ˣ)
    (hle : ∀ r : R, v r ≤ 1) (r : R) :
    v.restrictToConvex H hle r =
      (if h : v r = 0 then (0 : WithZero H.toSubgroup)
       else if hm : Units.mk0 (v r) h ∈ H
            then (⟨Units.mk0 (v r) h, hm⟩ : H.toSubgroup)
            else 0) :=
  rfl

/-- The support of `restrictToConvex` contains the support of `v`. -/
theorem supp_le_restrictToConvex_supp
    (v : Valuation R Γ₀) (H : ConvexSubgroup Γ₀ˣ)
    (hle : ∀ r : R, v r ≤ 1) :
    v.supp ≤ (v.restrictToConvex H hle).supp := by
  intro r hr
  rw [mem_supp_iff] at hr ⊢
  rw [restrictToConvex_unfold, dif_pos hr]

/-- `restrictToConvex` is `≤ 1` on all elements. -/
theorem restrictToConvex_le_one
    (v : Valuation R Γ₀) (H : ConvexSubgroup Γ₀ˣ)
    (hle : ∀ r : R, v r ≤ 1) (r : R) :
    v.restrictToConvex H hle r ≤ 1 := by
  rw [restrictToConvex_unfold]
  split
  · exact bot_le
  next h =>
    split
    next hm =>
      rw [show (1 : WithZero H.toSubgroup) = ((1 : H.toSubgroup) : WithZero H.toSubgroup) from rfl]
      exact WithZero.coe_le_coe.mpr (Subtype.mk_le_mk.mpr (Units.val_le_val.mp (hle r)))
    · exact bot_le

/-- If `v(r) ≠ 0` and `Units.mk0 (v r) ∉ H`, then `restrictToConvex` sends `r` to `0`. -/
theorem restrictToConvex_eq_zero_of_not_mem
    (v : Valuation R Γ₀) (H : ConvexSubgroup Γ₀ˣ)
    (hle : ∀ r : R, v r ≤ 1) {r : R} (hr : v r ≠ 0)
    (hm : Units.mk0 (v r) hr ∉ H) :
    v.restrictToConvex H hle r = 0 := by
  rw [restrictToConvex_unfold, dif_neg hr, dif_neg hm]

/-- If `v(r) ≠ 0` and `Units.mk0 (v r) ∈ H`, then `restrictToConvex` sends `r` to a nonzero value. -/
theorem restrictToConvex_pos_of_mem
    (v : Valuation R Γ₀) (H : ConvexSubgroup Γ₀ˣ)
    (hle : ∀ r : R, v r ≤ 1) {r : R} (hr : v r ≠ 0)
    (hm : Units.mk0 (v r) hr ∈ H) :
    0 < v.restrictToConvex H hle r := by
  rw [restrictToConvex_unfold, dif_neg hr, dif_pos hm]
  exact WithZero.zero_lt_coe _

/-- If `v(r) ≠ 0`, `Units.mk0 (v r) ∈ H`, and `v r < 1`, then `restrictToConvex v H r < 1`. -/
theorem restrictToConvex_lt_one_of_mem
    (v : Valuation R Γ₀) (H : ConvexSubgroup Γ₀ˣ)
    (hle : ∀ r : R, v r ≤ 1) {r : R} (hr : v r ≠ 0)
    (hm : Units.mk0 (v r) hr ∈ H) (hlt : v r < 1) :
    v.restrictToConvex H hle r < 1 := by
  rw [restrictToConvex_unfold, dif_neg hr, dif_pos hm]
  rw [show (1 : WithZero H.toSubgroup) = ((1 : H.toSubgroup) : WithZero H.toSubgroup) from rfl]
  exact WithZero.coe_lt_coe.mpr (Subtype.mk_lt_mk.mpr (Units.val_lt_val.mp hlt))

/-- If `v(r) ≠ 0` and `Units.mk0 (v r) ∉ H`, then `restrictToConvex v H r < 1`
(trivially, since it equals 0). -/
theorem restrictToConvex_lt_one_of_not_mem
    (v : Valuation R Γ₀) (H : ConvexSubgroup Γ₀ˣ)
    (hle : ∀ r : R, v r ≤ 1) {r : R} (hr : v r ≠ 0)
    (hm : Units.mk0 (v r) hr ∉ H) :
    v.restrictToConvex H hle r < 1 := by
  rw [restrictToConvex_eq_zero_of_not_mem v H hle hr hm]
  exact zero_lt_one

/-- `restrictToConvex` is `< 1` at `r` whenever `v r < 1` (regardless of H-membership). -/
theorem restrictToConvex_lt_one_of_val_lt_one
    (v : Valuation R Γ₀) (H : ConvexSubgroup Γ₀ˣ)
    (hle : ∀ r : R, v r ≤ 1) {r : R} (hr : v r ≠ 0) (hlt : v r < 1) :
    v.restrictToConvex H hle r < 1 := by
  by_cases hm : Units.mk0 (v r) hr ∈ H
  · exact restrictToConvex_lt_one_of_mem v H hle hr hm hlt
  · exact restrictToConvex_lt_one_of_not_mem v H hle hr hm

end RestrictToConvexAPI

end Valuation

/-! ### Section 7: Lemma 7.45 -- full proof

## Proof strategy (Wedhorn)

Following Wedhorn's Lemma 7.45:
1. Get `V₀` from the domination theorem with `range(A₀) ≤ V₀` and I-images
   landing in `V₀.nonunits`.
2. Apply the retraction `r` from (7.1.2): `restrictToConvex` with
   `H = convexGenerated(u₀⁻¹)` where `u₀` is a specific I-generator value.
3. Extend from `A₀` to `A` using topological nilpotency (Lemma 7.44(3)).
4. The extended valuation has `supp = 𝔭` and is continuous with a value group
   that is automatically MulArchimedean (rank ≤ 1).

The extension `v_ext(a) = v_r(s^n * a) * v_r(s)^{-n}` (where `s ∈ I \ 𝔭` is
topologically nilpotent and `n` is chosen so `s^n * a ∈ A₀`) requires proving
well-definedness, multiplicativity, the ultrametric inequality, and support = 𝔭.
-/

namespace PairOfDefinition

open ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A]
  [IsTopologicalRing A] [IsLinearTopology A A]

/-! ### Helper (a): Topological nilpotency gives `s^n * a ∈ A₀`

If `s` is topologically nilpotent in `A` and `A₀` is open, then for any `a : A`,
there exists `n` such that `s ^ n * a ∈ A₀`. This is Wedhorn's Lemma 7.44(1)
applied to the extension construction. -/

omit [IsLinearTopology A A] in
/-- For `s` topologically nilpotent and `A₀` open in `A`, there exists `n`
with `s ^ n * a ∈ A₀` (used in the extension construction, Wedhorn Lemma 7.44). -/
theorem exists_pow_mul_mem_A₀ (P : PairOfDefinition A)
    {s : A} (hs : IsTopologicallyNilpotent s) (a : A) :
    ∃ n : ℕ, s ^ n * a ∈ P.A₀ := by
  -- The set U = {x : A | x * a ∈ A₀} is open (preimage of open A₀ under
  -- continuous (· * a)) and contains 0 (since 0 * a = 0 ∈ A₀).
  have h_cont : Continuous (· * a : A → A) := continuous_mul_const a
  have h_open : IsOpen {x : A | x * a ∈ P.A₀} :=
    P.isOpen.preimage h_cont
  have h_zero : (0 : A) ∈ {x : A | x * a ∈ P.A₀} := by
    simp [P.A₀.zero_mem]
  -- Since s^n → 0, eventually s^n ∈ U
  have h_nhds : {x : A | x * a ∈ P.A₀} ∈ nhds (0 : A) :=
    h_open.mem_nhds h_zero
  obtain ⟨n, hn⟩ := (hs.eventually h_nhds).exists
  exact ⟨n, hn⟩

omit [IsTopologicalRing A] [IsLinearTopology A A] in
/-- Monotonicity: if `s ^ n * a ∈ A₀` then `s ^ (n + k) * a ∈ A₀` for all `k`.
This follows because `s ^ (n + k) * a = s ^ k * (s ^ n * a)` and `A₀` is a subring. -/
theorem pow_mul_mem_A₀_of_le (P : PairOfDefinition A)
    {s : A} (hs : s ∈ P.A₀) {a : A} {n : ℕ} (hn : s ^ n * a ∈ P.A₀)
    (k : ℕ) : s ^ (n + k) * a ∈ P.A₀ := by
  rw [show n + k = k + n from by omega, pow_add, mul_assoc]
  exact P.A₀.mul_mem (P.A₀.pow_mem hs k) hn

/-! ### Helper (b)-(c): Extended valuation construction

The extension `v_ext : A → WithZero(H_gen.toSubgroup)` is defined by choosing
`n` such that `s^n * a ∈ A₀` and setting `v_ext(a) = v_r(s^n * a) * v_r(s)^{-n}`.

This requires proving:
- Well-definedness (independence of choice of `n`)
- Multiplicativity
- Ultrametric inequality
- v_ext(0) = 0, v_ext(1) = 1

These are stated as sorry lemmas below, to be filled as infrastructure is developed. -/

omit [IsTopologicalRing A] [IsLinearTopology A A] in
/-- **Well-definedness of the extended valuation.** If `s ^ n * a ∈ A₀` and
`s ^ m * a ∈ A₀`, then the two definitions of `v_ext(a)` agree:
`v_r(s^n * a) * v_r(s)^{-n} = v_r(s^m * a) * v_r(s)^{-m}`.

Proof sketch: WLOG `n ≤ m`. Then `s^m * a = s^{m-n} * (s^n * a)`, so
`v_r(s^m * a) = v_r(s)^{m-n} * v_r(s^n * a)`. Dividing by `v_r(s)^m`
gives the same result as dividing `v_r(s^n * a)` by `v_r(s)^n`. -/
theorem vExt_well_defined
    {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
    (v : Valuation A Γ₀)
    {s : A} (hs_ne : v s ≠ 0) {a : A}
    {n m : ℕ} (_hn : s ^ n * a ∈ (P : PairOfDefinition A).A₀)
    (_hm : s ^ m * a ∈ P.A₀) :
    v (s ^ n * a) * (v s)⁻¹ ^ n = v (s ^ m * a) * (v s)⁻¹ ^ m := by
  -- Both sides equal v(a) after simplification using v(s^k * a) = v(s)^k * v(a)
  -- and cancellation of v(s)^n (possible since v(s) ≠ 0).
  have h1 : v (s ^ n * a) = v s ^ n * v a := by rw [map_mul, map_pow]
  have h2 : v (s ^ m * a) = v s ^ m * v a := by rw [map_mul, map_pow]
  rw [h1, h2]
  have hs_inv : ∀ k : ℕ, v s ^ k * (v s)⁻¹ ^ k = 1 := by
    intro k
    rw [← mul_pow, mul_inv_cancel₀ hs_ne, one_pow]
  calc v s ^ n * v a * (v s)⁻¹ ^ n
      = v s ^ n * (v s)⁻¹ ^ n * v a := by rw [mul_assoc, mul_comm (v a), mul_assoc]
    _ = 1 * v a := by rw [hs_inv]
    _ = v a := one_mul _
    _ = 1 * v a := (one_mul _).symm
    _ = v s ^ m * (v s)⁻¹ ^ m * v a := by rw [hs_inv]
    _ = v s ^ m * v a * (v s)⁻¹ ^ m := by rw [mul_assoc, mul_comm ((v s)⁻¹ ^ m), ← mul_assoc]

/-! ### Helper (d): Support of the extended valuation

The support of `v_ext` equals `𝔭`. The key point is:
- `a ∈ 𝔭 ⟹ s^n * a ∈ 𝔭` (since 𝔭 is an ideal) and `v_r(s^n * a) = 0`
  (since `v_r` restricted to `A₀` has support containing `𝔭 ∩ A₀`)
- `a ∉ 𝔭 ⟹ s^n * a ∉ 𝔭` (since `s ∉ 𝔭` and `𝔭` is prime) and
  `v_r(s^n * a) ≠ 0` -/

/-- **Support of the extended valuation equals 𝔭.** This is the key property
needed to produce a Spa point with the correct support.

Proof: For `a ∈ 𝔭`, `s^n * a ∈ 𝔭` (ideal absorption). Since `supp(v_r) ⊇ 𝔭 ∩ A₀`
on `A₀`, `v_r(s^n * a) = 0`, hence `v_ext(a) = 0`. Conversely, for `a ∉ 𝔭`,
`s^n * a ∉ 𝔭` (since `s ∉ 𝔭` and `𝔭` prime), so `v_r(s^n * a) ≠ 0` and
`v_ext(a) ≠ 0` (after dividing by the nonzero `v_r(s)^n`). -/
theorem vExt_supp_eq
    (P : PairOfDefinition A) [IsAdicComplete P.I P.A₀]
    {𝔭 : Ideal A} [𝔭.IsPrime] (h𝔭 : ¬IsOpen (𝔭 : Set A))
    {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
    (v : Valuation A Γ₀) (hv_supp : v.supp = 𝔭)
    (v_ext : Valuation A Γ₀) (h_ext : ∀ a ∈ P.A₀, v_ext a = v a) :
    v_ext.supp = 𝔭 := by
  sorry

/-! ### Helper (e): Continuity of the extended valuation

The extended valuation is continuous when the restricted valuation on `A₀` is
continuous and `A₀` is open in `A`. This is Wedhorn's Lemma 7.44(2):
`v` on `A` is continuous iff `v|_{A₀}` is continuous on the open subring `A₀`. -/

omit [IsLinearTopology A A] in
/-- **Continuity transfer from open subring.** If `v` is a valuation on `A`,
`A₀` is an open subring, and `v|_{A₀}` (the restriction) is continuous
(in the subspace topology on `A₀`), then `v` is continuous on `A`.

This is Wedhorn's Lemma 7.44(2). The proof uses: for any `γ`, the set
`{a ∈ A | v(a) < γ}` is an additive subgroup containing the open set
`A₀.subtype '' {a ∈ A₀ | v(a) < γ}`, hence is open. -/
theorem isContinuous_of_restriction_isContinuous
    (P : PairOfDefinition A)
    {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
    (v : Valuation A Γ₀)
    (h_res : ∀ γ : Γ₀, IsOpen (P.A₀.subtype '' {a : P.A₀ | v (P.A₀.subtype a) < γ})) :
    v.IsContinuous := by
  intro γ
  by_cases hγ : γ = 0
  · subst hγ; simp [not_lt_zero']
  -- {a : A | v a < γ} is the underlying set of v.ltAddSubgroup (Units.mk0 γ hγ)
  rw [show { a : A | v a < γ } =
    (v.ltAddSubgroup (Units.mk0 γ hγ) : Set A) from by ext; simp [Valuation.ltAddSubgroup]]
  -- It suffices to show this additive subgroup contains an open neighborhood of 0
  apply AddSubgroup.isOpen_of_mem_nhds
  -- The image of {a ∈ A₀ | v(a) < γ} under subtype is open (by hypothesis)
  -- and contained in {a : A | v a < γ}, and contains 0.
  have h_sub : P.A₀.subtype '' {a : P.A₀ | v (P.A₀.subtype a) < γ} ⊆
      (v.ltAddSubgroup (Units.mk0 γ hγ) : Set A) := by
    rintro _ ⟨a, ha, rfl⟩
    simp only [Valuation.ltAddSubgroup, Units.val_mk0]
    exact ha
  have h_zero : (0 : A) ∈ P.A₀.subtype '' {a : P.A₀ | v (P.A₀.subtype a) < γ} := by
    exact ⟨0, by simp [zero_lt_iff.mpr hγ], rfl⟩
  exact Filter.mem_of_superset ((h_res γ).mem_nhds h_zero) h_sub

/-! ### Helper (f): A-plus boundedness

For `f ∈ A⁺ ⊆ A₀`, we have `v_ext(f) = v_r(f) ≤ 1` since `v_r ≤ 1` on `A₀`. -/

-- This helper is trivial given `h_ext` and `v_r ≤ 1`, so it is handled inline
-- in the main proof.

/-! ### The rank-1 extension (Wedhorn Lemma 7.44(3) + 7.45)

The key remaining sorry: produce a `ValuationSubring` of `Frac(A/𝔭)` with
MulArchimedean value group that dominates the image of `A₀` and sends I-images
to nonunits. This isolates all the hard parts (extension construction, well-
definedness, valuation axioms) into a single well-typed helper.

The proof sketch is:
1. Start with `V₀` from the domination theorem (arbitrary rank).
2. Choose `a₀ ∈ I \ 𝔭`, set `u₀ = Units.mk0(V₀.valuation(φ(a₀)))`.
3. Let `H = convexGenerated(u₀⁻¹)` and `v_r = V₀.valuation.restrictToConvex H`.
4. Extend `v_r` from `A₀` to `A` via `v_ext(a) = v_r(s^n * a) * v_r(s)^{-n}`.
5. Take `V = v_ext.valuationSubring`. The value group of `v_ext` lives in
   `WithZero(H.toSubgroup)` which is MulArchimedean by `convexGenerated`.
-/

/-- **Rank-1 domination (Wedhorn Lemma 7.45, Steps 3-4).**

Given the arbitrary-rank `V₀` from the domination theorem, produce a
MulArchimedean `V` satisfying the same range and nonunits conditions.

This encapsulates the full extension construction: retraction via
`restrictToConvex`, extension from `A₀` to `A` using topological
nilpotency (`exists_pow_mul_mem_A₀`), and verification of the
valuation axioms, support, and A-plus bound.

The proof requires ~150 lines of additional infrastructure:
- Well-definedness of `v_ext(a) = v_r(s^n * a) * v_r(s)^{-n}`
- Multiplicativity and ultrametric inequality for `v_ext`
- `supp(v_ext) = 𝔭`
- Continuity transfer (Lemma 7.44(2), now proved above)
- Correspondence between `v_ext` and a `ValuationSubring` of `Frac(A/𝔭)` -/
theorem exists_mulArchimedean_valuationSubring
    (P : PairOfDefinition A) [IsAdicComplete P.I P.A₀] [PlusSubring A]
    {𝔭 : Ideal A} [𝔭.IsPrime] (h𝔭 : ¬IsOpen (𝔭 : Set A))
    (hAplus_le_A₀ : (A⁺ : Set A) ⊆ P.A₀) :
    ∃ V : ValuationSubring (FractionRing (A ⧸ 𝔭)),
      (P.toFractionQuotient 𝔭).range ≤ V.toSubring ∧
      (P.toFractionQuotient 𝔭).range.subtype ''
        (Ideal.map (P.toFractionQuotient 𝔭).rangeRestrict P.I : Set _) ⊆ V.nonunits ∧
      MulArchimedean V.ValueGroup ∧
      (∀ f ∈ (A⁺ : Set A), P.pulledBackValuation V f ≤ 1) := by
  haveI : IsDomain (A ⧸ 𝔭) := Ideal.Quotient.isDomain 𝔭
  -- Step 1: Get V₀ from the domination theorem
  obtain ⟨V₀, hrange₀, hnonunits₀⟩ := P.exists_valuationSubring_of_prime (𝔭 := 𝔭)
  -- Step 2: Get a₀ ∈ I \ 𝔭 (exists since 𝔭 is non-open)
  obtain ⟨a₀, ha₀_I, ha₀_notp⟩ := P.exists_mem_I_not_mem_of_not_isOpen h𝔭
  set s := (P.A₀.subtype a₀ : A)
  -- s is topologically nilpotent and s ∉ 𝔭
  have hs_nil : IsTopologicallyNilpotent s := P.isTopologicallyNilpotent_of_mem ha₀_I
  -- For any a : A, there exists n with s^n * a ∈ A₀ (proved helper)
  have _h_pow_mul : ∀ a : A, ∃ n : ℕ, s ^ n * a ∈ P.A₀ :=
    P.exists_pow_mul_mem_A₀ hs_nil
  -- Step 3: Get the maximum V₀-value among I-generators (closest to 1).
  -- This determines the convex subgroup for coarsening.
  set φ := P.toFractionQuotient 𝔭
  -- Step 3a: Get finite generators for I
  obtain ⟨S, hS⟩ := P.fg
  -- a₀ ∈ I \ 𝔭 ensures S is nonempty and φ(a₀) ≠ 0
  have hSne : S.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]; intro hS_eq
    have hI_bot : P.I = ⊥ := by rw [← hS, hS_eq, Finset.coe_empty, Ideal.span_empty]
    have ha₀_zero : a₀ = 0 := Ideal.mem_bot.mp (hI_bot ▸ ha₀_I)
    exact ha₀_notp (by rw [show s = P.A₀.subtype a₀ from rfl, ha₀_zero, map_zero]
                       exact 𝔭.zero_mem)
  -- Step 3b: The maximum V₀-value among generators
  -- All generators that are in I have value ≤ 1, and those not in 𝔭 have value < 1.
  -- We take the sup of all V₀.valuation(φ(t)) for t ∈ S.
  set g_max := S.sup' hSne (fun t ↦ V₀.valuation (φ t)) with g_max_def
  -- g_max < 1: each generator has value < 1 (since generators ∈ I → image is nonunit of V₀)
  have hg_lt1 : g_max < 1 := by
    rw [Finset.sup'_lt_iff]
    intro t ht
    exact P.pulledBackValuation_lt_one hnonunits₀ (hS ▸ Ideal.subset_span (Finset.mem_coe.mpr ht))
  -- g_max ≠ 0: V₀.valuation(φ(a₀)) ≠ 0 and V₀.valuation(φ(a₀)) ≤ g_max
  have ha₀_val_ne : V₀.valuation (φ a₀) ≠ 0 := by
    rw [ne_eq, Valuation.zero_iff]; intro h
    exact ha₀_notp (by
      simp only [φ, toFractionQuotient, RingHom.comp_apply, Subring.coe_subtype] at h
      exact Ideal.Quotient.eq_zero_iff_mem.mp
        ((IsFractionRing.injective (A ⧸ 𝔭) (FractionRing (A ⧸ 𝔭))).eq_iff.mp
          (h.trans (map_zero _).symm)))
  -- V₀.valuation(φ(a₀)) ≤ g_max since a₀ ∈ I = span S and g_max bounds generators
  -- Use pulledBackValuation to view as a Valuation on A, then apply the bound.
  have hpb_eq : ∀ b : P.A₀, P.pulledBackValuation V₀ (P.A₀.subtype b) =
      V₀.valuation (φ b) := P.pulledBackValuation_eq_valuation_toFractionQuotient V₀
  -- Helper: the pulled-back valuation on A₀ is bounded by g_max on I
  have hpb_le_gmax : ∀ a : P.A₀, a ∈ P.I →
      P.pulledBackValuation V₀ (P.A₀.subtype a) ≤ g_max :=
    fun a ha ↦ valuation_le_on_ideal_of_le_on_generators (P.pulledBackValuation V₀)
      (P.pulledBackValuation_le_one hrange₀)
      hS (fun t ht ↦ hpb_eq t ▸ Finset.le_sup' (f := fun t ↦ V₀.valuation (φ t)) ht) ha
  have ha₀_val_le_gmax : V₀.valuation (φ a₀) ≤ g_max := by
    rw [← hpb_eq]; exact hpb_le_gmax a₀ ha₀_I
  have hg_ne0 : g_max ≠ 0 := ne_of_gt <|
    lt_of_lt_of_le (zero_lt_iff.mpr ha₀_val_ne) ha₀_val_le_gmax
  -- Step 4: Construct H = maxAvoid(u_max) where u_max is the unit of g_max
  set u_max := Units.mk0 g_max hg_ne0
  have hu_max_lt1 : (u_max : V₀.ValueGroup) < 1 := hg_lt1
  have hu_max_ne1 : u_max ≠ 1 := fun h ↦ ne_of_lt hg_lt1
    (show g_max = 1 from congr_arg Units.val h)
  set H := ConvexSubgroup.maxAvoid hu_max_ne1 with H_def
  -- Step 5: Coarsen V₀.valuation by H
  set v_c := V₀.valuation.coarsenByUnits H with v_c_def
  -- Step 6: V = valuationSubring of v_c
  set V := v_c.valuationSubring with V_def
  -- Key helper: v_c(x) ≤ 1 when V₀.valuation(x) ≤ 1
  have hvc_le_one : ∀ x, V₀.valuation x ≤ 1 → v_c x ≤ 1 := fun x hx ↦
    Valuation.coarsenByUnits_le_one_of_le_one _ _ hx
  -- Key helper: v_c(x) < 1 for I-generators (their unit parts are ≤ u_max, hence ∉ H)
  have hvc_lt_one_gen : ∀ t ∈ S, v_c (φ t) < 1 := by
    intro t ht
    have hval_le : V₀.valuation (φ t) ≤ g_max :=
      Finset.le_sup' (f := fun t ↦ V₀.valuation (φ t)) ht
    have hval_lt1 : V₀.valuation (φ t) < 1 :=
      lt_of_le_of_lt hval_le hg_lt1
    -- If V₀.valuation(φ(t)) = 0: v_c(φ(t)) = 0 < 1
    by_cases hne : V₀.valuation (φ t) = 0
    · rw [Valuation.coarsenByUnits_apply, hne, map_zero]; exact zero_lt_one
    -- Otherwise, unit part u_t ≤ u_max < 1
    · have hu_t_le : Units.mk0 (V₀.valuation (φ t)) hne ≤ u_max :=
        Units.val_le_val.mp hval_le
      -- u_max ∉ H (by not_mem_maxAvoid)
      have hu_max_not_H : u_max ∉ H := ConvexSubgroup.not_mem_maxAvoid hu_max_ne1
      -- u_t ≤ u_max < 1 and u_max ∉ H → u_t ∉ H (by not_mem_of_not_mem_of_le_lt_one)
      have hu_t_not_H : Units.mk0 (V₀.valuation (φ t)) hne ∉ H :=
        H.not_mem_of_not_mem_of_le_lt_one hu_max_not_H hu_max_lt1 hu_t_le
      exact Valuation.coarsenByUnits_lt_one_of_not_mem _ _ hne hu_t_not_H
        (le_of_lt hval_lt1)
  refine ⟨V, ?_, ?_, ?_, ?_⟩
  · -- Condition 1: range(φ) ≤ V
    -- φ(a) ∈ V iff v_c(φ(a)) ≤ 1, which follows from V₀.valuation(φ(a)) ≤ 1.
    intro x hx
    obtain ⟨a, rfl⟩ := hx
    change v_c (φ a) ≤ 1
    exact hvc_le_one _ ((ValuationSubring.valuation_le_one_iff V₀ _).mpr (hrange₀ ⟨a, rfl⟩))
  · -- Condition 2: I-images ⊆ V.nonunits
    intro x hx
    obtain ⟨y, hy_mem, rfl⟩ := hx
    -- We need φ.range.subtype y ∈ V.nonunits.
    -- By mem_nonunits_iff: V.valuation(x) < 1, which is iff v_c(x) < 1 (by equivalence).
    -- Use: x ∈ V.nonunits ↔ V.valuation x < 1 ↔ ¬(1 ≤ V.valuation x)
    -- and ¬(1 ≤ V.valuation x) ↔ ¬(v_c 1 ≤ v_c x) (by IsEquiv) ↔ ¬(1 ≤ v_c x) ↔ v_c x < 1
    suffices h : v_c (φ.range.subtype y) < 1 by
      -- v_c(x) < 1 means x ∉ V (as valuationSubring checks v ≤ 1 for inv)
      -- More precisely: v_c < 1 ↔ V.valuation < 1 ↔ nonunit of V
      -- Use: isEquiv_iff_val_le_one gives (V.val x ≤ 1 ↔ v_c x ≤ 1).
      -- So V.val x < 1 ↔ (V.val x ≤ 1 ∧ ¬(V.val x⁻¹ ≤ 1)) ↔ ... complicated.
      -- Simpler: x ∈ V.nonunits ↔ x = 0 ∨ x⁻¹ ∉ V
      show φ.range.subtype y ∈ V.nonunits
      rw [ValuationSubring.mem_nonunits_iff_or]
      -- v_c(x) < 1 → v_c(x⁻¹) > 1 (when x ≠ 0) → x⁻¹ ∉ V
      by_cases hne : φ.range.subtype y = 0
      · exact Or.inl hne
      · right; intro hmem
        rw [Valuation.mem_valuationSubring_iff] at hmem
        -- v_c(x⁻¹) ≤ 1, but v_c(x) < 1 and v_c(x) * v_c(x⁻¹) = 1 (since x ≠ 0)
        -- gives 1 = v_c(x) * v_c(x⁻¹) < 1 * 1 = 1, contradiction
        have h1 : v_c (φ.range.subtype y) * v_c (φ.range.subtype y)⁻¹ = 1 := by
          rw [← map_mul, mul_inv_cancel₀ hne, map_one]
        -- v_c(x) < 1 and v_c(x⁻¹) ≤ 1 but v_c(x) * v_c(x⁻¹) = 1: contradiction
        -- since 1 = v_c(x) * v_c(x⁻¹) ≤ v_c(x) * 1 = v_c(x) < 1
        have : 1 ≤ v_c (φ.range.subtype y) :=
          h1 ▸ mul_le_of_le_one_right zero_le' hmem
        exact absurd h (not_lt.mpr this)
    obtain ⟨a, ha_I, ha_eq⟩ := (Ideal.mem_map_iff_of_surjective _
      φ.rangeRestrict_surjective).mp hy_mem
    have : (φ.range.subtype y : FractionRing (A ⧸ 𝔭)) = φ a := by
      simp only [Subring.coe_subtype]; rw [← ha_eq]; rfl
    rw [this]
    -- a ∈ I, so V₀.valuation(φ(a)) ≤ g_max (the bound on I via generators)
    have hval_le_gen : V₀.valuation (φ a) ≤ g_max := by
      rw [← hpb_eq]; exact hpb_le_gmax a ha_I
    -- v_c preserves ≤ (monotone), and v_c(g_max) ≤ 1
    -- Actually, we need v_c(φ(a)) < 1, not just ≤ 1.
    -- Since V₀.valuation(φ(a)) ≤ g_max: the unit part is ≤ u_max (when nonzero).
    -- Then same argument as for generators applies.
    by_cases hne : V₀.valuation (φ a) = 0
    · rw [Valuation.coarsenByUnits_apply, hne, map_zero]; exact zero_lt_one
    · have hval_lt1 : V₀.valuation (φ a) < 1 :=
        lt_of_le_of_lt hval_le_gen hg_lt1
      have hu_a_le : Units.mk0 (V₀.valuation (φ a)) hne ≤ u_max :=
        Units.val_le_val.mp hval_le_gen
      have hu_a_not_H : Units.mk0 (V₀.valuation (φ a)) hne ∉ H :=
        H.not_mem_of_not_mem_of_le_lt_one
          (ConvexSubgroup.not_mem_maxAvoid hu_max_ne1) hu_max_lt1 hu_a_le
      exact Valuation.coarsenByUnits_lt_one_of_not_mem _ _ hne hu_a_not_H
        (le_of_lt hval_lt1)
  · -- Condition 3: MulArchimedean V.ValueGroup
    -- V.ValueGroup is isomorphic to a quotient of WithZero(V₀.ValueGroupˣ / H).
    -- This requires showing the quotient V₀.ValueGroupˣ / maxAvoid(u_max)
    -- is MulArchimedean. This is a nontrivial algebraic fact.
    sorry
  · -- Condition 4: A-plus bound
    intro f hf
    change V.valuation _ ≤ 1
    rw [ValuationSubring.valuation_le_one_iff]
    show v_c _ ≤ 1
    exact hvc_le_one _
      ((ValuationSubring.valuation_le_one_iff V₀ _).mpr
        (hrange₀ ⟨⟨f, hAplus_le_A₀ hf⟩, rfl⟩))

/-! ### Full proof assembly -/

/-- **Lemma 7.45 of Wedhorn.** Non-open primes are supports in `Spa`.

Given a complete affinoid ring `(A, A⁺)` with pair of definition `(A₀, I)` and
a non-open prime `𝔭` of `A`, there exists `v ∈ Spa(A, A⁺)` with `supp(v) = 𝔭`.

The proof uses `exists_mulArchimedean_valuationSubring` to produce a rank-1
valuation subring, then applies `exists_mem_spa_supp_eq_of_nonOpen_prime_mulArchimedean`.

References: Wedhorn, Adic Spaces, Lemma 7.45. -/
theorem exists_mem_spa_supp_eq_of_nonOpen_prime
    (P : PairOfDefinition A) [IsAdicComplete P.I P.A₀] [PlusSubring A]
    {𝔭 : Ideal A} [𝔭.IsPrime] (h𝔭 : ¬IsOpen (𝔭 : Set A))
    (hAplus_le_A₀ : (A⁺ : Set A) ⊆ P.A₀) :
    ∃ v ∈ Spa A A⁺, v.supp = 𝔭 := by
  haveI : IsDomain (A ⧸ 𝔭) := Ideal.Quotient.isDomain 𝔭
  -- Get the rank-1 valuation subring from the extension construction
  obtain ⟨V, hrange, hnonunits, harch, hAplus⟩ :=
    P.exists_mulArchimedean_valuationSubring h𝔭 hAplus_le_A₀
  -- Apply the conditional MulArchimedean version (already proved)
  exact P.exists_mem_spa_supp_eq_of_nonOpen_prime_mulArchimedean
    h𝔭 hrange hnonunits hAplus

end PairOfDefinition

/-! ### Section 8: Cofinal property for `WithZero` of `convexGenerated`

This lemma lifts the cofinal property from `convexGenerated` (the group) to
`WithZero(convexGenerated.toSubgroup)` (the value group). It is used in
`exists_mem_spa_supp_eq_of_nonOpen_prime` (Step 7) to establish that the
restricted valuation's bound `g_r` has cofinal powers in the value group.

Note: The `g_r ≠ 0` step (Step 6d) was resolved by using `Finset.exists_mem_eq_sup'`
to select the specific generator achieving the maximum value, for which membership
in `convexGenerated(u₀⁻¹)` follows directly from `self_mem_convexGenerated`. -/

namespace ConvexSubgroup

variable {Γ : Type*} [CommGroup Γ] [LinearOrder Γ] [IsOrderedMonoid Γ]

/-- **Cofinal property in `WithZero` of `convexGenerated` for the inverse generator.**

For `y > 1` in `Γ`, the element `y⁻¹ < 1` is in `convexGenerated(y)`, and its
powers are cofinal for `0` in `WithZero(convexGenerated(y).toSubgroup)`:
for every `γ > 0`, there exists `n` with `(y⁻¹)^n < γ`.

This is the `WithZero`-version of `exists_inv_pow_lt_of_mem_convexGenerated`,
specialized to the inverse of the generator. It is used in Step 6 of
`exists_mem_spa_supp_eq_of_nonOpen_prime` (Wedhorn's retraction 7.1.2). -/
theorem withZero_inv_pow_cofinal_of_convexGenerated
    {y : Γ} (hy : 1 < y) :
    ∀ (γ : WithZero (convexGenerated hy).toSubgroup), 0 < γ →
      ∃ n : ℕ,
        ((⟨y⁻¹, inv_mem (self_mem_convexGenerated hy)⟩ :
          (convexGenerated hy).toSubgroup) : WithZero _) ^ n < γ := by
  intro γ hγ
  obtain ⟨⟨δ, hδ_mem⟩, rfl⟩ := WithZero.ne_zero_iff_exists.mp (ne_of_gt hγ)
  obtain ⟨n, hn⟩ := exists_inv_pow_lt_of_mem_convexGenerated hy hδ_mem
  refine ⟨n, ?_⟩
  rw [← WithZero.coe_pow]
  exact WithZero.coe_lt_coe.mpr (Subtype.mk_lt_mk.mpr hn)

end ConvexSubgroup
