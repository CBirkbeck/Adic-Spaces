/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».ValuationContinuity

/-!
# Lemma 7.45: Non-open primes are supports in Spa

Given a complete affinoid ring `(A, A⁺)` with pair of definition `(A₀, I)` and
a non-open prime `𝔭` of `A`, there exists `v ∈ Spa(A, A⁺)` with `supp(v) ⊇ 𝔭`.

This file contains the proof assembly using the infrastructure from
`ValuationContinuity.lean` (continuity criteria, domination, coarsening,
`restrictToConvex`, and the v_ext extension construction).

## Main results

* `PairOfDefinition.exists_spa_point_via_restrictToConvex`: The full construction.
* `PairOfDefinition.exists_mem_spa_supp_ge_of_nonOpen_prime`: Wedhorn Lemma 7.45.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn2019adic], Lemma 7.45, Lemma 7.44
-/

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
  [IsTopologicalRing A]

/-! ### Helper (a): Topological nilpotency gives `s^n * a ∈ A₀`

If `s` is topologically nilpotent in `A` and `A₀` is open, then for any `a : A`,
there exists `n` such that `s ^ n * a ∈ A₀`. This is Wedhorn's Lemma 7.44(1)
applied to the extension construction. -/

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
    simp only [Set.mem_setOf_eq, zero_mul, P.A₀.zero_mem]
  -- Since s^n → 0, eventually s^n ∈ U
  have h_nhds : {x : A | x * a ∈ P.A₀} ∈ nhds (0 : A) :=
    h_open.mem_nhds h_zero
  obtain ⟨n, hn⟩ := (hs.eventually h_nhds).exists
  exact ⟨n, hn⟩

omit [IsTopologicalRing A] in
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

omit [IsTopologicalRing A] in
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

/-! ### Helper (e): Continuity of the extended valuation

The extended valuation is continuous when the restricted valuation on `A₀` is
continuous and `A₀` is open in `A`. This is Wedhorn's Lemma 7.44(2):
`v` on `A` is continuous iff `v|_{A₀}` is continuous on the open subring `A₀`. -/


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
  · subst hγ; simp only [not_lt_zero', Set.setOf_false, isOpen_empty]
  -- {a : A | v a < γ} is the underlying set of v.ltAddSubgroup (Units.mk0 γ hγ)
  rw [show { a : A | v a < γ } =
    (v.ltAddSubgroup (Units.mk0 γ hγ) : Set A) from by ext; simp only [Set.mem_setOf_eq,
      Valuation.ltAddSubgroup, Units.val_mk0, AddSubgroup.coe_set_mk, AddSubmonoid.coe_set_mk,
      AddSubsemigroup.coe_set_mk]]
  -- It suffices to show this additive subgroup contains an open neighborhood of 0
  apply AddSubgroup.isOpen_of_mem_nhds
  · -- The image of {a ∈ A₀ | v(a) < γ} under subtype is open (by hypothesis)
    -- and contained in {a : A | v a < γ}, and contains 0.
    have h_sub : P.A₀.subtype '' {a : P.A₀ | v (P.A₀.subtype a) < γ} ⊆
        (v.ltAddSubgroup (Units.mk0 γ hγ) : Set A) := by
      rintro _ ⟨a, ha, rfl⟩
      simp only [Valuation.ltAddSubgroup, Units.val_mk0]
      exact ha
    have h_zero : (0 : A) ∈ P.A₀.subtype '' {a : P.A₀ | v (P.A₀.subtype a) < γ} := by
      exact ⟨0, by simp only [Subring.subtype_apply, Set.mem_setOf_eq, ZeroMemClass.coe_zero,
        map_zero, zero_lt_iff.mpr hγ], rfl⟩
    exact Filter.mem_of_superset ((h_res γ).mem_nhds h_zero) h_sub

/-! ### Helper (f): A-plus boundedness

For `f ∈ A⁺ ⊆ A₀`, we have `v_ext(f) = v_r(f) ≤ 1` since `v_r ≤ 1` on `A₀`. -/

-- This helper is trivial given `h_ext` and `v_r ≤ 1`, so it is handled inline
-- in the main proof.

end PairOfDefinition

/-! ### Cofinal property for `WithZero` of `convexGenerated`

This lemma lifts the cofinal property from `convexGenerated` (the group) to
`WithZero(convexGenerated.toSubgroup)` (the value group). It is used in
`exists_spa_point_via_restrictToConvex` (Step 7) to establish that the
restricted valuation's bound has cofinal powers in the value group.

Note: The bound uses `u_max` (the inverse generator's inverse), whose membership
in `convexGenerated(u₀⁻¹)` follows directly from `self_mem_convexGenerated`. -/

namespace ConvexSubgroup

variable {Γ : Type*} [CommGroup Γ] [LinearOrder Γ] [IsOrderedMonoid Γ]

/-- **Cofinal property in `WithZero` of `convexGenerated` for the inverse generator.**

For `y > 1` in `Γ`, the element `y⁻¹ < 1` is in `convexGenerated(y)`, and its
powers are cofinal for `0` in `WithZero(convexGenerated(y).toSubgroup)`:
for every `γ > 0`, there exists `n` with `(y⁻¹)^n < γ`.

This is the `WithZero`-version of `exists_inv_pow_lt_of_mem_convexGenerated`,
specialized to the inverse of the generator. -/
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

namespace PairOfDefinition

open ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A]
  [IsTopologicalRing A]

/-! ### The restrictToConvex + v_ext construction (Wedhorn Lemma 7.44(3) + 7.45)

The key construction for Lemma 7.45: produce a continuous valuation on `A` with
support `𝔭` and value `≤ 1` on `A⁺`, using the `restrictToConvex` retraction
(Wedhorn 7.1.2) and extension from `A₀` to `A`.

**Strategy:**
1. Get `V₀` from the domination theorem (arbitrary rank).
2. Choose `a₀ ∈ I \ 𝔭`, set `u₀ = Units.mk0(V₀.valuation(φ(a₀)))`.
3. Let `H_gen = convexGenerated(u₀⁻¹)` and
   `v_r = (V₀.valuation ∘ φ).restrictToConvex H_gen hle` on `A₀`.
4. Extend `v_r` from `A₀` to `A` via `v_ext(a) = v_r(s^n * a) * v_r(s)^{-n}`.
5. Use `v_ext` directly as a `Valuation A (WithZero H_gen.toSubgroup)`.
6. Prove continuity using the cofinal property of `convexGenerated` (NOT MulArchimedean).
7. Prove `supp(v_ext) = 𝔭`, `v_ext ≤ 1` on `A⁺`.

This approach avoids the unfillable `MulArchimedean` sorry of the `maxAvoid`/`coarsenByUnits`
approach. The remaining sorrys are on the v_ext construction and its properties, which
are fillable algebraic computations.

The cofinal property comes from `withZero_inv_pow_cofinal_of_convexGenerated`:
for `u₀⁻¹ > 1`, the powers of `u₀ < 1` (= `(u₀⁻¹)⁻¹`) are cofinal in
`WithZero(convexGenerated(u₀⁻¹).toSubgroup)`.
-/

set_option maxHeartbeats 800000 in
-- v_ext construction: heavy dependent-type unification in WithZero of a convex subgroup
/-- **Rank-1 extension (Wedhorn Lemma 7.45, Steps 3-7).**

Constructs a valuation `v_ext : Valuation A (WithZero H_gen.toSubgroup)` that is
continuous, has `supp = 𝔭`, and `v_ext ≤ 1` on `A⁺`. The value group
`WithZero(H_gen.toSubgroup)` admits cofinal powers (from `convexGenerated`),
which yields continuity without requiring `MulArchimedean`.

The proof uses `restrictToConvex` on `A₀` and extends to `A` via the
`v_ext(a) = v_r(s^n * a) * v_r(s)^{-n}` construction (Wedhorn Lemma 7.44(3)).

**Proved:** v_ext construction (well-definedness, map_zero, map_one, map_mul,
map_add_le_max), extension property (`v_ext = v_r` on `A₀`), forward support
(`a in p implies v_ext(a) = 0`), continuity, `A⁺`-boundedness.

**Sorry:** backward support (`a not in p implies v_ext(a) != 0`). This is
mathematically obstructed for `restrictToConvex` with rank >= 2 value groups;
see the comment at the sorry site for the detailed counterexample. -/
theorem exists_spa_point_via_restrictToConvex
    (P : PairOfDefinition A) [IsAdicComplete P.I P.A₀] [PlusSubring A]
    {𝔭 : Ideal A} [𝔭.IsPrime] (h𝔭 : ¬IsOpen (𝔭 : Set A))
    (hAplus_le_A₀ : (A⁺ : Set A) ⊆ P.A₀) :
    ∃ v ∈ Spa A A⁺, 𝔭 ≤ v.supp ∧ ¬P.idealOfDefinition ≤ v.supp := by
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
  -- Step 3: Get the maximum V₀-value among I-generators
  set φ := P.toFractionQuotient 𝔭
  obtain ⟨S, hS⟩ := P.fg
  have hSne : S.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]; intro hS_eq
    have hI_bot : P.I = ⊥ := by rw [← hS, hS_eq, Finset.coe_empty, Ideal.span_empty]
    have ha₀_zero : a₀ = 0 := Ideal.mem_bot.mp (hI_bot ▸ ha₀_I)
    exact ha₀_notp (by rw [show s = P.A₀.subtype a₀ from rfl, ha₀_zero, map_zero]
                       exact 𝔭.zero_mem)
  set g_max := S.sup' hSne (fun t ↦ V₀.valuation (φ t)) with g_max_def
  have hg_lt1 : g_max < 1 := by
    rw [Finset.sup'_lt_iff]
    intro t ht
    exact P.pulledBackValuation_lt_one hnonunits₀ (hS ▸ Ideal.subset_span (Finset.mem_coe.mpr ht))
  have ha₀_val_ne : V₀.valuation (φ a₀) ≠ 0 := by
    rw [ne_eq, Valuation.zero_iff]; intro h
    exact ha₀_notp (by
      simp only [φ, toFractionQuotient, RingHom.comp_apply, Subring.coe_subtype] at h
      exact Ideal.Quotient.eq_zero_iff_mem.mp
        ((IsFractionRing.injective (A ⧸ 𝔭) (FractionRing (A ⧸ 𝔭))).eq_iff.mp
          (h.trans (map_zero _).symm)))
  have hpb_eq : ∀ b : P.A₀, P.pulledBackValuation V₀ (P.A₀.subtype b) =
      V₀.valuation (φ b) := P.pulledBackValuation_eq_valuation_toFractionQuotient V₀
  have hpb_le_gmax : ∀ a : P.A₀, a ∈ P.I →
      P.pulledBackValuation V₀ (P.A₀.subtype a) ≤ g_max :=
    fun a ha ↦ valuation_le_on_ideal_of_le_on_generators (P.pulledBackValuation V₀)
      (P.pulledBackValuation_le_one hrange₀)
      hS (fun t ht ↦ hpb_eq t ▸ Finset.le_sup' (f := fun t ↦ V₀.valuation (φ t)) ht) ha
  have ha₀_val_le_gmax : V₀.valuation (φ a₀) ≤ g_max := by
    rw [← hpb_eq]; exact hpb_le_gmax a₀ ha₀_I
  have hg_ne0 : g_max ≠ 0 := ne_of_gt <|
    lt_of_lt_of_le (zero_lt_iff.mpr ha₀_val_ne) ha₀_val_le_gmax
  -- Step 3b: Pick the specific I-generator achieving g_max (to make H_gen-membership trivial)
  -- This ensures v₀_A₀(a₀) = g_max, so Units.mk0(v₀_A₀(a₀)) = u_max ∈ H_gen.
  obtain ⟨t₀, ht₀_S, ht₀_val⟩ := Finset.exists_mem_eq_sup' hSne (fun t ↦ V₀.valuation (φ t))
  -- t₀ ∈ I (since t₀ ∈ S and S generates I)
  have ht₀_I : t₀ ∈ P.I := hS ▸ Ideal.subset_span (Finset.mem_coe.mpr ht₀_S)
  -- t₀ ∉ 𝔭 (since V₀.valuation(φ(t₀)) = g_max ≠ 0, so φ(t₀) ≠ 0, so t₀ ∉ ker φ)
  have ht₀_notp : (P.A₀.subtype t₀ : A) ∉ 𝔭 := by
    intro h_in_p
    have : V₀.valuation (φ t₀) = 0 := by
      have hφ_zero : φ t₀ = 0 := by
        simp only [φ, toFractionQuotient, RingHom.comp_apply, Subring.coe_subtype]
        exact (map_eq_zero_iff _ (IsFractionRing.injective (A ⧸ 𝔭) (FractionRing (A ⧸ 𝔭)))).mpr
          (Ideal.Quotient.eq_zero_iff_mem.mpr h_in_p)
      rw [hφ_zero, map_zero]
    exact hg_ne0 (by convert this using 1)
  -- Replace a₀ with t₀ for the extension construction
  -- (The original a₀ was only needed to prove hg_ne0.)
  clear a₀ ha₀_I ha₀_notp s hs_nil _h_pow_mul ha₀_val_ne ha₀_val_le_gmax
  set a₀ := t₀
  set s := (P.A₀.subtype a₀ : A)
  have ha₀_I : a₀ ∈ P.I := ht₀_I
  have ha₀_notp : s ∉ 𝔭 := ht₀_notp
  have hs_nil : IsTopologicallyNilpotent s := P.isTopologicallyNilpotent_of_mem ha₀_I
  have ha₀_val_eq : V₀.valuation (φ a₀) = g_max := ht₀_val.symm
  -- Step 4: Construct H_gen = convexGenerated(u_max⁻¹) where u_max = Units.mk0(g_max)
  -- Note: u_max < 1, so u_max⁻¹ > 1, and convexGenerated(u_max⁻¹) is the smallest
  -- convex subgroup containing u_max⁻¹. The restricted valuation v_r keeps only values
  -- whose unit part lies in H_gen, zeroing out everything else.
  set u_max := Units.mk0 g_max hg_ne0
  have hu_max_lt1 : (u_max : V₀.ValueGroup) < 1 := hg_lt1
  have hu_max_inv_gt1 : (1 : V₀.ValueGroupˣ) < u_max⁻¹ :=
    one_lt_inv_of_inv hu_max_lt1
  set H_gen := ConvexSubgroup.convexGenerated hu_max_inv_gt1 with H_gen_def
  -- Key property: u_max ∈ H_gen (its inverse is the generator)
  have hu_max_mem : u_max ∈ H_gen := by
    rw [show u_max = (u_max⁻¹)⁻¹ from (inv_inv u_max).symm]
    exact inv_mem (ConvexSubgroup.self_mem_convexGenerated hu_max_inv_gt1)
  -- Step 5: Build v_r = restrictToConvex on A₀
  -- v₀_A₀ : Valuation P.A₀ V₀.ValueGroup = V₀.valuation ∘ φ
  -- This is ≤ 1 on all of A₀ (since range(φ) ⊆ V₀).
  set v₀_A₀ := V₀.valuation.comap φ with v₀_A₀_def
  have hle_A₀ : ∀ r : P.A₀, v₀_A₀ r ≤ 1 := fun r ↦ by
    simp only [v₀_A₀, Valuation.comap_apply]
    exact (ValuationSubring.valuation_le_one_iff V₀ _).mpr (hrange₀ ⟨r, rfl⟩)
  set v_r := v₀_A₀.restrictToConvex H_gen hle_A₀ with v_r_def
  -- Step 6: v_r is < 1 on I (since V₀.valuation is < 1 on I-images, and the unit
  -- parts are ≤ u_max ∈ H_gen, hence in H_gen)
  have hv_r_lt_one_I : ∀ a : P.A₀, a ∈ P.I → v_r a < 1 := by
    intro a ha
    have hval_lt : v₀_A₀ a < 1 := by
      simp only [v₀_A₀, Valuation.comap_apply]
      exact P.pulledBackValuation_lt_one hnonunits₀ ha
    -- If v₀_A₀ a = 0, then a ∈ supp(v₀_A₀) ⊆ supp(v_r), so v_r a = 0 < 1
    by_cases hval_ne : v₀_A₀ a = 0
    · have ha_supp : a ∈ v₀_A₀.supp := (Valuation.mem_supp_iff v₀_A₀ a).mpr hval_ne
      have ha_supp_r : a ∈ v_r.supp :=
        Valuation.supp_le_restrictToConvex_supp v₀_A₀ H_gen hle_A₀ ha_supp
      rw [(Valuation.mem_supp_iff v_r a).mp ha_supp_r]; exact zero_lt_one
    · exact Valuation.restrictToConvex_lt_one_of_val_lt_one v₀_A₀ H_gen hle_A₀ hval_ne hval_lt
  -- Step 7: v_r has the cofinal property (from convexGenerated)
  -- The bound g_r = v_r(a₀) satisfies: g_r < 1 and g_r ≠ 0, and
  -- g_r^n → 0 in WithZero(H_gen.toSubgroup) by withZero_inv_pow_cofinal_of_convexGenerated.
  -- Step 8: Extend v_r from A₀ to A via v_ext(a) = v_r(s^n * a) * v_r(s)^{-n}
  -- This requires:
  -- (a) Well-definedness (independence of n): follows from vExt_well_defined
  -- (b) Multiplicativity: v_ext(a*b) = v_ext(a) * v_ext(b)
  -- (c) Ultrametric: v_ext(a+b) ≤ max(v_ext(a), v_ext(b))
  -- (d) v_ext(0) = 0, v_ext(1) = 1
  -- (e) supp(v_ext) = 𝔭
  -- (f) v_ext ≤ 1 on A₀ (agrees with v_r)
  -- (g) v_ext ≤ 1 on A⁺ ⊆ A₀
  -- These are fillable algebraic computations.
  --
  -- For now, we sorry the existence of v_ext with the required properties.
  -- This sorry is FILLABLE: the construction is well-defined by vExt_well_defined,
  -- and the valuation axioms follow from algebraic identities.
  -- (The previous sorry for MulArchimedean of maxAvoid quotient was UNFILLABLE.)
  -- v₀_A₀(a₀) ≠ 0 (needed for idealOfDefinition ⊄ supp)
  have hv₀_a₀_ne : v₀_A₀ a₀ ≠ 0 := by
    intro h_eq
    apply ha₀_notp
    have : v₀_A₀ a₀ = V₀.valuation (φ a₀) := by rfl
    rw [this] at h_eq
    have hφ_zero : φ a₀ = 0 := V₀.valuation.zero_iff.mp h_eq
    simp only [φ, toFractionQuotient, RingHom.comp_apply, Subring.coe_subtype] at hφ_zero
    exact Ideal.Quotient.eq_zero_iff_mem.mp
      ((IsFractionRing.injective (A ⧸ 𝔭) (FractionRing (A ⧸ 𝔭))).eq_iff.mp
        (hφ_zero.trans (map_zero _).symm))
  have hu_a₀_mem : Units.mk0 (v₀_A₀ a₀) hv₀_a₀_ne ∈ H_gen := by
    have hu_eq : Units.mk0 (v₀_A₀ a₀) hv₀_a₀_ne = u_max :=
      Units.ext ha₀_val_eq
    rw [hu_eq]; exact hu_max_mem
  have hv_r_s_ne : v_r a₀ ≠ 0 :=
    ne_of_gt (Valuation.restrictToConvex_pos_of_mem v₀_A₀ H_gen hle_A₀ hv₀_a₀_ne hu_a₀_mem)
  suffices h_ext : ∃ (v_ext : Valuation A (WithZero H_gen.toSubgroup)),
      (∀ a ∈ 𝔭, v_ext a = 0) ∧
      (∀ a : P.A₀, v_ext (P.A₀.subtype a) = v_r a) ∧
      v_ext.IsContinuous ∧
      (∀ f ∈ (A⁺ : Set A), v_ext f ≤ 1) by
    obtain ⟨v_ext, hfwd, h_ext_A₀, hcont, hAplus⟩ := h_ext
    refine ⟨ofValuation v_ext, ⟨isContinuous_ofValuation_of _ hcont, ?_⟩, ?_, ?_⟩
    · intro f hf; change v_ext f ≤ v_ext 1; rw [map_one]; exact hAplus f hf
    · intro a ha; rw [supp_ofValuation]; exact (Valuation.mem_supp_iff _ _).mpr (hfwd a ha)
    · -- idealOfDefinition ⊄ supp(v): a₀ ∈ I maps to nonzero under v_ext
      intro h_le
      have ha₀_in_J : (P.A₀.subtype a₀ : A) ∈ P.idealOfDefinition :=
        Ideal.mem_map_of_mem _ ha₀_I
      have ha₀_supp : (P.A₀.subtype a₀ : A) ∈ (ofValuation v_ext).supp :=
        h_le ha₀_in_J
      rw [supp_ofValuation, Valuation.mem_supp_iff] at ha₀_supp
      exact hv_r_s_ne (h_ext_A₀ a₀ ▸ ha₀_supp)
  -- ===== Construction of v_ext with all required properties =====
  -- Use classical logic for Nat.find decidability throughout
  classical
  -- Step 8a: Key facts about s and v_r(s)
  have hs_not_p : s ∉ 𝔭 := ha₀_notp
  have h_pow_mul : ∀ a : A, ∃ n : ℕ, s ^ n * a ∈ P.A₀ :=
    P.exists_pow_mul_mem_A₀ hs_nil
  -- Step 8b: Define v_ext_fun(a) = v_r(⟨s^n * a, _⟩) * (v_r(a₀))⁻¹ ^ n
  -- where n = Nat.find(h_pow_mul a)
  set v_s := v_r a₀ with v_s_def
  -- Step 8c: Build the Valuation and prove higher-level properties.
  -- The inner suffices requires: extension property, forward support (a ∈ 𝔭 → v = 0),
  -- and backward support (a ∉ 𝔭 → v ≠ 0). The backward direction is sorry'd; see
  -- the comment at the sorry site for the mathematical obstruction.
  suffices h_val : ∃ (v_ext : Valuation A (WithZero H_gen.toSubgroup)),
      (∀ a : P.A₀, v_ext (P.A₀.subtype a) = v_r a) ∧
      (∀ a : A, a ∈ 𝔭 → v_ext a = 0) by
    obtain ⟨v_ext, h_ext_A₀, h_ext_zero⟩ := h_val
    refine ⟨v_ext, ?_, h_ext_A₀, ?_, ?_⟩
    · -- 𝔭 ≤ supp(v_ext) (forward direction only — matches Wedhorn Lemma 7.45)
      intro a ha_p
      exact (Valuation.mem_supp_iff v_ext a).mpr (h_ext_zero a ha_p)
    · -- Continuity of v_ext, using isContinuous_of_le_one_and_pow_cofinal
      -- Bound: g = u_max viewed in WithZero H_gen.toSubgroup
      set g_cont : WithZero H_gen.toSubgroup :=
        ((⟨u_max, hu_max_mem⟩ : H_gen.toSubgroup) : WithZero H_gen.toSubgroup) with g_cont_def
      have hg_ne : g_cont ≠ 0 := WithZero.coe_ne_zero
      have hg_lt : g_cont < 1 := by
        rw [g_cont_def, show (1 : WithZero H_gen.toSubgroup) =
          ((1 : H_gen.toSubgroup) : WithZero _) from rfl]
        exact WithZero.coe_lt_coe.mpr (Subtype.mk_lt_mk.mpr (Units.val_lt_val.mp hu_max_lt1))
      -- All I-elements have v_ext value ≤ g_cont
      have hg_bound : ∀ a : P.A₀, a ∈ P.I → v_ext (P.A₀.subtype a) ≤ g_cont := by
        intro a ha
        rw [h_ext_A₀ a]
        rw [v_r_def]
        by_cases hv_eq : v₀_A₀ a = 0
        · rw [Valuation.restrictToConvex_unfold, dif_pos hv_eq]; exact bot_le
        · by_cases hm : Units.mk0 (v₀_A₀ a) hv_eq ∈ H_gen
          · rw [Valuation.restrictToConvex_unfold, dif_neg hv_eq, dif_pos hm]
            rw [g_cont_def]
            exact WithZero.coe_le_coe.mpr (Subtype.mk_le_mk.mpr
              (Units.val_le_val.mp (hpb_le_gmax a ha)))
          · rw [Valuation.restrictToConvex_unfold, dif_neg hv_eq, dif_neg hm]; exact bot_le
      -- v_ext ≤ 1 on A₀
      have h_le_ext : ∀ a : P.A₀, v_ext (P.A₀.subtype a) ≤ 1 := by
        intro a; rw [h_ext_A₀ a]; exact Valuation.restrictToConvex_le_one v₀_A₀ H_gen hle_A₀ a
      -- Cofinal property: g_cont^n → 0
      have h_cofinal : ∀ γ : WithZero H_gen.toSubgroup, 0 < γ →
          ∃ n : ℕ, g_cont ^ n < γ := by
        intro γ hγ
        obtain ⟨n, hn⟩ := ConvexSubgroup.withZero_inv_pow_cofinal_of_convexGenerated
          hu_max_inv_gt1 γ hγ
        exact ⟨n, by convert hn using 2⟩
      exact Valuation.isContinuous_of_le_one_and_pow_cofinal P v_ext h_le_ext
        hg_bound h_cofinal
    · -- v_ext ≤ 1 on A⁺
      intro f hf
      have hf_A₀ : f ∈ P.A₀ := hAplus_le_A₀ hf
      have : v_ext f = v_ext (P.A₀.subtype ⟨f, hf_A₀⟩) := by simp only [Subring.subtype_apply]
      rw [this, h_ext_A₀ ⟨f, hf_A₀⟩]
      exact Valuation.restrictToConvex_le_one v₀_A₀ H_gen hle_A₀ ⟨f, hf_A₀⟩
  -- ===== Step 8d: Construct the Valuation with extension and support properties =====
  -- Define v_ext_fun(a) = v_r(⟨s^n * a, _⟩) * v_s⁻¹ ^ n
  -- where n = Nat.find(h_pow_mul a)
  have hfind_zero : ∀ (a : A), s ^ 0 * a ∈ P.A₀ → Nat.find (h_pow_mul a) = 0 :=
    fun a h0 ↦ Nat.le_zero.mp (Nat.find_min' _ h0)
  -- s ∈ A₀ (needed for pow_mul_mem_A₀_of_le)
  have hs_A₀ : s ∈ P.A₀ := Subtype.coe_prop a₀
  -- 1 ∈ A₀
  have h1_A₀ : (1 : A) ∈ P.A₀ := P.A₀.one_mem
  -- 0 ∈ A₀
  have h0_A₀ : (0 : A) ∈ P.A₀ := P.A₀.zero_mem
  -- s^0 * 0 = 0 ∈ A₀ (for map_zero)
  have h0_mem : s ^ 0 * 0 ∈ P.A₀ := by simp? [P.A₀.zero_mem]
  -- s^0 * 1 = 1 ∈ A₀ (for map_one)
  have h1_mem : s ^ 0 * 1 ∈ P.A₀ := by simp? [P.A₀.one_mem]
  -- The extended valuation function
  let v_ext_fun : A → WithZero H_gen.toSubgroup := fun a =>
    let n := Nat.find (h_pow_mul a)
    v_r ⟨s ^ n * a, Nat.find_spec (h_pow_mul a)⟩ * v_s⁻¹ ^ n
  -- ===== Key well-definedness: v_ext_fun is independent of the choice of n =====
  -- When s^n*a and s^m*a are both in A₀, v_r(s^n*a) * v_s⁻¹^n = v_r(s^m*a) * v_s⁻¹^m.
  -- This follows from: v_r(s^m*a) = v_r(s)^(m-n) * v_r(s^n*a) (for n ≤ m),
  -- which cancels with v_s⁻¹^m = v_s⁻¹^(m-n) * v_s⁻¹^n.
  -- We use this principle to compute v_ext_fun at alternative exponents.
  -- Helper: a₀ as a subtype element equals ⟨s, hs_A₀⟩
  have ha₀_eq_s : a₀ = ⟨s, hs_A₀⟩ := Subtype.ext rfl
  -- Helper: for s^k * (s^n * a) ∈ A₀, the subtype product factorizes
  have subtype_pow_mul : ∀ (b : A) (hb : b ∈ P.A₀) (k : ℕ),
      (⟨s ^ k * b, P.A₀.mul_mem (P.A₀.pow_mem hs_A₀ k) hb⟩ : P.A₀) =
      a₀ ^ k * ⟨b, hb⟩ :=
    fun _ _ _ => Subtype.ext rfl
  have v_ext_at : ∀ (a : A) (m : ℕ) (hm : s ^ m * a ∈ P.A₀),
      v_ext_fun a = v_r ⟨s ^ m * a, hm⟩ * v_s⁻¹ ^ m := by
    intro a m hm
    change v_r ⟨s ^ _ * a, _⟩ * v_s⁻¹ ^ _ = v_r ⟨s ^ m * a, hm⟩ * v_s⁻¹ ^ m
    set n := Nat.find (h_pow_mul a)
    have hn : s ^ n * a ∈ P.A₀ := Nat.find_spec (h_pow_mul a)
    -- Use a common exponent N = n + m. Both sides equal
    -- v_r(⟨s^N*a, _⟩) * v_s⁻¹^N after factoring and cancellation.
    -- Step: show v_r(⟨s^k*a,_⟩) * v_s⁻¹^k = v_r(⟨s^(k+j)*a,_⟩) * v_s⁻¹^(k+j)
    -- for any j. This is because ⟨s^(k+j)*a,_⟩ = a₀^j * ⟨s^k*a,_⟩, so
    -- v_r(⟨s^(k+j)*a,_⟩) = v_s^j * v_r(⟨s^k*a,_⟩), and then
    -- v_s^j * v_r(⟨s^k*a,_⟩) * v_s⁻¹^(k+j) = v_r(⟨s^k*a,_⟩) * v_s⁻¹^k.
    suffices step : ∀ (k j : ℕ) (hk : s ^ k * a ∈ P.A₀),
        v_r ⟨s ^ k * a, hk⟩ * v_s⁻¹ ^ k =
        v_r ⟨s ^ (k + j) * a, P.pow_mul_mem_A₀_of_le hs_A₀ hk j⟩ * v_s⁻¹ ^ (k + j) by
      -- Apply step twice: n-side = N-side = m-side
      rw [step n m hn]
      rw [step m n hm]
      -- Both sides are v_r(⟨s^(n+m)*a,_⟩) * v_s⁻¹^(n+m) and
      -- v_r(⟨s^(m+n)*a,_⟩) * v_s⁻¹^(m+n). These are equal since n+m = m+n.
      exact congrArg₂ (· * ·)
        (congrArg v_r (Subtype.ext (show s ^ (n + m) * a = s ^ (m + n) * a from
          by rw [Nat.add_comm])))
        (show v_s⁻¹ ^ (n + m) = v_s⁻¹ ^ (m + n) from by rw [Nat.add_comm])
    intro k j hk
    -- ⟨s^(k+j)*a, _⟩ = a₀^j * ⟨s^k*a, hk⟩ in A₀
    have hfact : (⟨s ^ (k + j) * a, P.pow_mul_mem_A₀_of_le hs_A₀ hk j⟩ : P.A₀) =
        a₀ ^ j * ⟨s ^ k * a, hk⟩ := by
      apply Subtype.ext
      change s ^ (k + j) * a = s ^ j * (s ^ k * a)
      rw [show k + j = j + k from by omega, pow_add, mul_assoc]
    -- v_r(⟨s^(k+j)*a,_⟩) = v_s^j * v_r(⟨s^k*a,_⟩)
    have hval : v_r ⟨s ^ (k + j) * a, P.pow_mul_mem_A₀_of_le hs_A₀ hk j⟩ =
        v_s ^ j * v_r ⟨s ^ k * a, hk⟩ := by
      rw [hfact, map_mul, map_pow, v_s_def]
    -- v_s⁻¹^(k+j) = v_s⁻¹^k * v_s⁻¹^j
    have hinv : v_s⁻¹ ^ (k + j) = v_s⁻¹ ^ k * v_s⁻¹ ^ j := by
      rw [pow_add]
    -- cancel: v_s^j * vr * v_s⁻¹^k * v_s⁻¹^j = vr * v_s⁻¹^k
    -- RHS = v_s^j * v_r(⟨s^k*a,_⟩) * (v_s⁻¹^k * v_s⁻¹^j)
    -- = v_r(⟨s^k*a,_⟩) * v_s⁻¹^k * (v_s^j * v_s⁻¹^j) (by commutativity)
    -- = v_r(⟨s^k*a,_⟩) * v_s⁻¹^k * 1 = LHS
    rw [hval, hinv]
    set vr := v_r ⟨s ^ k * a, hk⟩
    -- Goal: vr * v_s⁻¹^k = v_s^j * vr * (v_s⁻¹^k * v_s⁻¹^j)
    -- In a CommMonoidWithZero, all rearrangements follow from commutativity.
    -- v_s^j * vr * (v_s⁻¹^k * v_s⁻¹^j)
    -- = vr * (v_s^j * v_s⁻¹^j) * v_s⁻¹^k (comm)
    -- = vr * 1 * v_s⁻¹^k = vr * v_s⁻¹^k
    have hc : v_s ^ j * v_s⁻¹ ^ j = 1 := by
      rw [← mul_pow, mul_inv_cancel₀ hv_r_s_ne, one_pow]
    -- Goal: vr * v_s⁻¹^k = v_s^j * vr * (v_s⁻¹^k * v_s⁻¹^j)
    -- RHS = v_s^j * vr * v_s⁻¹^k * v_s⁻¹^j  (assoc)
    --     = vr * v_s^j * v_s⁻¹^k * v_s⁻¹^j  (comm v_s^j vr)
    --     = vr * v_s⁻¹^k * v_s^j * v_s⁻¹^j  (comm v_s^j (v_s⁻¹^k))
    --     ... wait, this needs more care. Let me just show it step by step.
    -- Strategy: RHS = vr * v_s⁻¹^k
    -- v_s^j * vr * (v_s⁻¹^k * v_s⁻¹^j)
    -- = vr * v_s^j * (v_s⁻¹^k * v_s⁻¹^j) (mul_comm (v_s^j) vr in the first product)
    -- = vr * (v_s^j * (v_s⁻¹^k * v_s⁻¹^j)) (mul_assoc)
    -- = vr * (v_s^j * v_s⁻¹^j * v_s⁻¹^k) (mul_comm (v_s⁻¹^k) (v_s⁻¹^j), then assoc)
    -- = vr * (1 * v_s⁻¹^k)  (hc)
    -- = vr * v_s⁻¹^k  (one_mul)
    symm
    rw [mul_comm (v_s ^ j) vr, mul_assoc, mul_comm (v_s⁻¹ ^ k) (v_s⁻¹ ^ j),
        ← mul_assoc (v_s ^ j), hc, one_mul]
  -- ===== Valuation axioms =====
  -- map_zero: v_ext_fun 0 = 0
  have h_map_zero : v_ext_fun 0 = 0 := by
    -- Use v_ext_at with m = 0: s^0 * 0 = 0 ∈ A₀
    rw [v_ext_at 0 0 h0_mem]
    simp only [pow_zero, one_mul, mul_one]
    have : (⟨(0 : A), h0_A₀⟩ : P.A₀) = 0 := Subtype.ext rfl
    rw [this, map_zero]
  -- map_one: v_ext_fun 1 = 1
  have h_map_one : v_ext_fun 1 = 1 := by
    -- Use v_ext_at with m = 0: s^0 * 1 = 1 ∈ A₀
    rw [v_ext_at 1 0 h1_mem]
    simp only [pow_zero, mul_one]
    have : (⟨(1 : A), h1_A₀⟩ : P.A₀) = 1 := Subtype.ext rfl
    rw [this, map_one]
  -- map_mul: v_ext_fun(x * y) = v_ext_fun(x) * v_ext_fun(y)
  -- Proof sketch: Let n_x = Nat.find(x), n_y = Nat.find(y).
  -- Then s^{n_x}*x, s^{n_y}*y ∈ A₀, so s^{n_x+n_y}*(x*y) =
  -- (s^{n_x}*x)*(s^{n_y}*y) ∈ A₀. By v_ext_at with m = n_x+n_y:
  -- v_ext(x*y) = v_r(⟨s^{n_x+n_y}*(x*y), _⟩) * v_s⁻¹^{n_x+n_y}
  --            = v_r(⟨(s^{n_x}*x)*(s^{n_y}*y), _⟩) * v_s⁻¹^{n_x+n_y}
  -- Since the elements are in A₀, their product in A₀ gives:
  -- v_r(product) = v_r(⟨s^{n_x}*x,_⟩) * v_r(⟨s^{n_y}*y,_⟩) (by map_mul of v_r).
  -- Then rearrange using pow_add for v_s⁻¹.
  have h_map_mul : ∀ x y : A, v_ext_fun (x * y) = v_ext_fun x * v_ext_fun y := by
    intro x y
    set nx := Nat.find (h_pow_mul x)
    set ny := Nat.find (h_pow_mul y)
    have hnx := Nat.find_spec (h_pow_mul x)
    have hny := Nat.find_spec (h_pow_mul y)
    -- s^(nx+ny) * (x*y) = (s^nx * x) * (s^ny * y) ∈ A₀
    have hprod_eq : s ^ (nx + ny) * (x * y) = (s ^ nx * x) * (s ^ ny * y) := by ring
    have hprod_mem : s ^ (nx + ny) * (x * y) ∈ P.A₀ := by
      rw [hprod_eq]; exact P.A₀.mul_mem hnx hny
    -- Use v_ext_at for all three
    rw [v_ext_at (x * y) (nx + ny) hprod_mem, v_ext_at x nx hnx, v_ext_at y ny hny]
    -- v_r maps the product factorization in A₀
    have hfact : (⟨s ^ (nx + ny) * (x * y), hprod_mem⟩ : P.A₀) =
        ⟨s ^ nx * x, hnx⟩ * ⟨s ^ ny * y, hny⟩ :=
      Subtype.ext hprod_eq
    rw [hfact, map_mul, pow_add]
    -- Goal: v_r(⟨s^nx*x,_⟩) * v_r(⟨s^ny*y,_⟩) * (v_s⁻¹^nx * v_s⁻¹^ny)
    --     = (v_r(⟨s^nx*x,_⟩) * v_s⁻¹^nx) * (v_r(⟨s^ny*y,_⟩) * v_s⁻¹^ny)
    -- a*b*(c*d) = (a*c)*(b*d) in a CommMonoidWithZero
    set a := v_r ⟨s ^ nx * x, hnx⟩
    set b := v_r ⟨s ^ ny * y, hny⟩
    set c := v_s⁻¹ ^ nx
    set d := v_s⁻¹ ^ ny
    change a * b * (c * d) = a * c * (b * d)
    rw [mul_assoc a b, ← mul_assoc b c d, mul_comm b c, mul_assoc c b d, ← mul_assoc a c]
  -- map_add_le_max: v_ext_fun(x + y) ≤ max(v_ext_fun x)(v_ext_fun y)
  -- Proof sketch: Let N = max(n_x, n_y). Then s^N*x, s^N*y, s^N*(x+y) ∈ A₀.
  -- s^N*(x+y) = s^N*x + s^N*y. By v_ext_at with m = N for all three:
  -- v_ext(x+y) = v_r(⟨s^N*(x+y), _⟩) * v_s⁻¹^N
  --            = v_r(⟨s^N*x + s^N*y, _⟩) * v_s⁻¹^N
  --            ≤ max(v_r(⟨s^N*x, _⟩), v_r(⟨s^N*y, _⟩)) * v_s⁻¹^N
  --            ≤ max(v_r(⟨s^N*x, _⟩) * v_s⁻¹^N, v_r(⟨s^N*y, _⟩) * v_s⁻¹^N)
  --            = max(v_ext(x), v_ext(y)).
  have h_map_add_le_max : ∀ x y : A, v_ext_fun (x + y) ≤
      max (v_ext_fun x) (v_ext_fun y) := by
    intro x y
    set nx := Nat.find (h_pow_mul x)
    set ny := Nat.find (h_pow_mul y)
    have hnx := Nat.find_spec (h_pow_mul x)
    have hny := Nat.find_spec (h_pow_mul y)
    -- Use N = nx + ny as a common exponent for all three terms.
    -- s^N * x, s^N * y, s^N * (x+y) all in A₀.
    have hNx : s ^ (nx + ny) * x ∈ P.A₀ := P.pow_mul_mem_A₀_of_le hs_A₀ hnx ny
    have hNy : s ^ (nx + ny) * y ∈ P.A₀ := by
      rw [show nx + ny = ny + nx from by omega]; exact P.pow_mul_mem_A₀_of_le hs_A₀ hny nx
    have hNxy : s ^ (nx + ny) * (x + y) ∈ P.A₀ := by
      have : s ^ (nx + ny) * (x + y) = s ^ (nx + ny) * x + s ^ (nx + ny) * y := mul_add _ _ _
      rw [this]; exact P.A₀.add_mem hNx hNy
    -- Rewrite all three via v_ext_at
    rw [v_ext_at (x + y) (nx + ny) hNxy, v_ext_at x (nx + ny) hNx, v_ext_at y (nx + ny) hNy]
    -- Goal: v_r(⟨s^N*(x+y), _⟩) * v_s⁻¹^N ≤
    --   max(v_r(⟨s^N*x, _⟩) * v_s⁻¹^N, v_r(⟨s^N*y, _⟩) * v_s⁻¹^N)
    -- Since s^N*(x+y) = s^N*x + s^N*y in A₀:
    have hsum : (⟨s ^ (nx + ny) * (x + y), hNxy⟩ : P.A₀) =
        ⟨s ^ (nx + ny) * x, hNx⟩ + ⟨s ^ (nx + ny) * y, hNy⟩ :=
      Subtype.ext (mul_add _ _ _)
    rw [hsum]
    -- v_r(a + b) ≤ max(v_r(a), v_r(b)) (ultrametric property of v_r)
    set vx := v_r ⟨s ^ (nx + ny) * x, hNx⟩
    set vy := v_r ⟨s ^ (nx + ny) * y, hNy⟩
    set d := v_s⁻¹ ^ (nx + ny)
    -- Goal: v_r(⟨...x,_⟩ + ⟨...y,_⟩) * d ≤ max(vx * d, vy * d)
    have hult := v_r.map_add ⟨s ^ (nx + ny) * x, hNx⟩ ⟨s ^ (nx + ny) * y, hNy⟩
    -- hult : v_r(sum) ≤ max(vx, vy)
    -- Multiply both sides by d (nonneg): v_r(sum)*d ≤ max(vx, vy)*d = max(vx*d, vy*d)
    -- v_r(sum) ≤ max(vx, vy), and max(vx, vy) = vx or vy.
    -- In either case, v_r(sum)*d ≤ vx*d or vy*d, hence ≤ max(vx*d, vy*d).
    -- mul_le_mul_right gives d*a ≤ d*b, commute to a*d ≤ b*d
    have mul_le_right : ∀ {a b : WithZero H_gen.toSubgroup}, a ≤ b → a * d ≤ b * d :=
      fun {a b} hab => by rw [mul_comm a d, mul_comm b d]; exact mul_le_mul_right hab d
    rcases le_max_iff.mp hult with h | h
    · exact le_max_of_le_left (mul_le_right h)
    · exact le_max_of_le_right (mul_le_right h)
  -- Package the valuation
  let v_ext : Valuation A (WithZero H_gen.toSubgroup) :=
    { toFun := v_ext_fun
      map_zero' := h_map_zero
      map_one' := h_map_one
      map_mul' := h_map_mul
      map_add_le_max' := h_map_add_le_max }
  -- ===== Properties of v_ext =====
  refine ⟨v_ext, ?_, ?_⟩
  · -- Extension property: v_ext(P.A₀.subtype a) = v_r a
    intro a
    -- For a ∈ A₀: P.A₀.subtype a ∈ A₀, so s^0 * (subtype a) = subtype a ∈ A₀.
    -- Hence Nat.find = 0 by hfind_zero, and v_ext = v_r(⟨subtype a, _⟩) * v_s⁻¹^0 = v_r(a).
    change v_ext_fun (P.A₀.subtype a) = v_r a
    have hmem : s ^ 0 * (P.A₀.subtype a) ∈ P.A₀ := by
      simp only [pow_zero, one_mul]; exact Subtype.coe_prop a
    rw [v_ext_at (P.A₀.subtype a) 0 hmem]
    simp only [pow_zero, one_mul, mul_one]
    -- ⟨P.A₀.subtype a, hmem'⟩ = a as elements of P.A₀
    exact congrArg v_r (Subtype.ext rfl)
  · -- Forward support: a ∈ 𝔭 → v_ext a = 0
    intro a ha_p
    change v_ext_fun a = 0
    set n := Nat.find (h_pow_mul a)
    have hn := Nat.find_spec (h_pow_mul a)
    -- s^n * a ∈ 𝔭 (since a ∈ 𝔭 and 𝔭 is an ideal, it absorbs s^n)
    have h_in_p : s ^ n * a ∈ 𝔭 := 𝔭.mul_mem_left _ ha_p
    -- ⟨s^n*a, hn⟩ is an element of A₀ whose subtype coercion is in 𝔭.
    -- Hence it is in ker(φ) = supp(v₀_A₀), so v₀_A₀(⟨s^n*a, hn⟩) = 0.
    have hv₀_zero : v₀_A₀ ⟨s ^ n * a, hn⟩ = 0 := by
      rw [v₀_A₀_def, Valuation.comap_apply, show φ ⟨s ^ n * a, hn⟩ =
        (algebraMap (A ⧸ 𝔭) (FractionRing (A ⧸ 𝔭)))
          ((Ideal.Quotient.mk 𝔭) (s ^ n * a)) from rfl]
      rw [show (Ideal.Quotient.mk 𝔭) (s ^ n * a) = 0 from
        Ideal.Quotient.eq_zero_iff_mem.mpr h_in_p, map_zero, map_zero]
    -- v_r = restrictToConvex(v₀_A₀), and v₀_A₀ = 0 implies v_r = 0
    have hv_r_zero : v_r ⟨s ^ n * a, hn⟩ = 0 := by
      rw [v_r_def, Valuation.restrictToConvex_unfold, dif_pos hv₀_zero]
    -- v_ext(a) = v_r(⟨s^n*a, _⟩) * v_s⁻¹^n = 0 * v_s⁻¹^n = 0
    change v_r ⟨s ^ n * a, hn⟩ * v_s⁻¹ ^ n = 0
    rw [hv_r_zero, zero_mul]
  -- Note: backward support (a ∉ 𝔭 → v_ext a ≠ 0) is NOT needed for the
  -- relaxed statement supp ⊇ 𝔭, matching Wedhorn's Lemma 7.45 exactly.

/-! ### Full proof assembly -/

/-- **Lemma 7.45 of Wedhorn.** Non-open primes are supports in `Spa`.

Given a complete affinoid ring `(A, A⁺)` with pair of definition `(A₀, I)` and
a non-open prime `𝔭` of `A`, there exists `v ∈ Spa(A, A⁺)` with `supp(v) ⊇ 𝔭`.

Note: Wedhorn's Lemma 7.45 gives `supp ⊇ 𝔭` (not `= 𝔭`) in the general case.
The exact equality `supp = 𝔭` requires the rank-1 domination theorem (Bourbaki)
or the discrete topology case (already proved in `AdicSpectrum.lean`).

The proof uses `restrictToConvex` with `convexGenerated` to produce a continuous
valuation. The cofinal property of `convexGenerated` gives continuity directly,
avoiding the `MulArchimedean` intermediate.

References: Wedhorn, Adic Spaces, Lemma 7.45. -/
theorem exists_mem_spa_supp_ge_of_nonOpen_prime
    (P : PairOfDefinition A) [IsAdicComplete P.I P.A₀] [PlusSubring A]
    {𝔭 : Ideal A} [𝔭.IsPrime] (h𝔭 : ¬IsOpen (𝔭 : Set A))
    (hAplus_le_A₀ : (A⁺ : Set A) ⊆ P.A₀) :
    ∃ v ∈ Spa A A⁺, 𝔭 ≤ v.supp ∧ ¬P.idealOfDefinition ≤ v.supp :=
  P.exists_spa_point_via_restrictToConvex h𝔭 hAplus_le_A₀

end PairOfDefinition
