/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».AnalyticPoints
import «Adic spaces».AffinoidRings
import «Adic spaces».ValuationCoarsening
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
  -- Get V₀ from domination theorem (conditions 1-2 but not necessarily rank 1)
  obtain ⟨V₀, hrange₀, hnonunits₀⟩ := P.exists_valuationSubring_of_prime (𝔭 := 𝔭)
  -- We coarsen V₀ to a rank-1 (MulArchimedean) valuation subring.
  -- The construction uses ValuationSubring.ofPrime at a minimal prime of V₀
  -- containing the I-image elements. The key facts are:
  -- (a) V₀.ofPrime Q ≥ V₀, preserving range containment
  -- (b) Elements of Q are nonunits of V₀.ofPrime Q
  --     (by idealOfLE_ofPrime: the ideal of V₀ corresponding to V₀.ofPrime Q is Q)
  -- (c) Q minimal over the I-images gives V₀.ofPrime Q rank ≤ 1
  --     (the quotient value group has no proper nontrivial convex subgroups)
  --
  -- This requires formalizing the Galois correspondence between primes of a
  -- valuation ring and convex subgroups of its value group (not yet in Mathlib).
  -- Alternatively, one can construct a rank-1 dominating valuation directly via
  -- the composition A₀ → Frac(A/𝔭) with a rank-1 valuation existence theorem.
  sorry

/-- **Lemma 7.45 of Wedhorn.** Non-open primes are supports in `Spa`. -/
theorem exists_mem_spa_supp_eq_of_nonOpen_prime
    (P : PairOfDefinition A) [IsAdicComplete P.I P.A₀] [PlusSubring A]
    {𝔭 : Ideal A} [𝔭.IsPrime] (h𝔭 : ¬IsOpen (𝔭 : Set A))
    (hAplus_le_A₀ : (A⁺ : Set A) ⊆ P.A₀) :
    ∃ v ∈ Spa A A⁺, v.supp = 𝔭 := by
  haveI : IsDomain (A ⧸ 𝔭) := Ideal.Quotient.isDomain 𝔭
  -- Step 1: Get MulArchimedean V from the domination + coarsening
  obtain ⟨V, hrange, hnonunits, harch⟩ :=
    P.exists_mulArchimedean_valuationSubring_of_prime h𝔭
  -- Step 2: Verify A⁺ condition using A⁺ ⊆ A₀ and pulledBackValuation_le_one
  have hAplus : ∀ f ∈ (A⁺ : Set A), P.pulledBackValuation V f ≤ 1 := by
    intro f hf
    obtain ⟨a, rfl⟩ : ∃ a : P.A₀, P.A₀.subtype a = f := ⟨⟨f, hAplus_le_A₀ hf⟩, rfl⟩
    exact P.pulledBackValuation_le_one hrange a
  -- Step 3: Apply the conditional MulArchimedean theorem
  exact P.exists_mem_spa_supp_eq_of_nonOpen_prime_mulArchimedean
    h𝔭 hrange hnonunits hAplus

end PairOfDefinition
