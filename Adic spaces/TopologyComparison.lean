/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».PresheafIdentification
import «Adic spaces».TateAlgebraWedhorn

/-!
# Topology Comparison: Completion Isomorphism (Non-Discrete)

The key bridge: `presheafValue D ≃+* A⟨X⟩/(1-sX)` for non-discrete
strongly noetherian Tate rings.

## Strategy

1. Show `locToQuotientOneSubfX_gen : Localization.Away s →+* A⟨X⟩/(1-sX)`
   is continuous for localization topology → T-topology quotient.
2. Extend to `presheafValue D →+* A⟨X⟩/(1-sX)` via `extensionHom`.
3. The round-trip `Localization → Quotient → presheafValue` = `coeRingHom`.
4. Both composites are identity → isomorphism.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn2019adic], §5.6, §8.1
-/

namespace ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [PlusSubring A] [HasRestrictionMaps A] [NonarchimedeanRing A]

section CompletionIsomorphism

omit [PlusSubring A] [HasRestrictionMaps A] in
/-- The round-trip `Localization → Quotient → presheafValue` equals
`locLiftToPresheaf = coeRingHom`. -/
theorem tateQuotient_roundtrip_eq_locLift (D : RationalLocData A)
    (hb : TopologicalRing.IsPowerBounded (invS D)) :
    ((tateQuotientToPresheafHom D hb).comp (locToQuotientOneSubfX_gen D.s)) =
    locLiftToPresheaf D := by
  apply IsLocalization.ringHom_ext (Submonoid.powers D.s)
  ext b
  simp only [RingHom.comp_apply]
  rw [locToQuotientOneSubfX_gen_algebraMap, tateQuotientToPresheafHom_algebraMap,
    locLiftToPresheaf_algebraMap]

omit [PlusSubring A] [HasRestrictionMaps A] in
/-- The round-trip pointwise. -/
theorem tateQuotient_roundtrip_apply (D : RationalLocData A)
    (hb : TopologicalRing.IsPowerBounded (invS D))
    (a : Localization.Away D.s) :
    tateQuotientToPresheafHom D hb (locToQuotientOneSubfX_gen D.s a) =
    locLiftToPresheaf D a :=
  RingHom.congr_fun (tateQuotient_roundtrip_eq_locLift D hb) a

/-! ### Step 1: Continuity of locToQuotientOneSubfX_gen

For the localization topology on `Localization.Away D.s` and the
quotient of the T-topology on `A⟨X⟩/(1-sX)`, the map
`locToQuotientOneSubfX_gen` is continuous.

This is the Artin-Rees topology comparison: the localization neighborhoods
`{(I·D)^m}` eventually land inside the quotient neighborhoods
`{class(g) : coeff n g ∈ s^n · U for all n}`.

For the proof: an element of `locNhd m` has the form `b/s^k` with
`b ∈ I^m · A₀`. Its image in the quotient is `class(b · X^k)`.
The T-topology condition: `coeff n (b · X^k) ∈ s^n · U`.
Since `coeff n (b · X^k) = b` if `n = k`, 0 otherwise.
Condition: `b ∈ s^k · U`. Since `b ∈ I^m · A₀` and `s^k · U`
contains `I^m · A₀` for `m ≥ m₀(U, k)` (Artin-Rees), this holds.

**NOTE:** This step requires the T-topology (from TateAlgebraWedhorn.lean),
NOT the product topology. With the product topology, the condition would
be `b ∈ U` (no `s^k` factor), which is weaker and doesn't match.
-/

/-! ### Bridge lemma: T₀ localization → annihilation by powers of s

For sorry-elimination in StructureSheaf.lean: if the localization topology
is T₀ and `coeRingHom(algebraMap b) = 0`, then `∃ k, s^k * b = 0`.
This reduces deep sorries to a single clean T₀ hypothesis. -/

omit [PlusSubring A] [HasRestrictionMaps A] [NonarchimedeanRing A] in
/-- If the localization topology on `Localization.Away D.s` is T₀, then
`D.coeRingHom (algebraMap b) = 0` implies `∃ k, D.s ^ k * b = 0`.

Uses injectivity of the completion embedding for T₀ uniform spaces
(`UniformSpace.Completion.coe_injective`) and the localization
characterization (`IsLocalization.map_eq_zero_iff`). -/
theorem exists_pow_mul_eq_zero_of_coeRingHom_zero (D : RationalLocData A) (b : A)
    (ht0 : @T0Space (Localization.Away D.s)
      (@UniformSpace.toTopologicalSpace _ D.uniformSpace))
    (h : D.coeRingHom (algebraMap A (Localization.Away D.s) b) = 0) :
    ∃ k : ℕ, D.s ^ k * b = 0 := by
  have hinj : Function.Injective D.coeRingHom :=
    @UniformSpace.Completion.coe_injective _ D.uniformSpace ht0
  have hab : algebraMap A (Localization.Away D.s) b = 0 :=
    hinj (h.trans (map_zero D.coeRingHom).symm)
  rw [IsLocalization.map_eq_zero_iff (Submonoid.powers D.s)] at hab
  obtain ⟨⟨_, ⟨k, rfl⟩⟩, hk⟩ := hab
  exact ⟨k, hk⟩

/-! ### Step 1: Quotient T-topology on A⟨X⟩/(1-sX)

The quotient of the T-topology on `A⟨X⟩` by the ideal `(1-sX)` gives a
topological ring structure on `A⟨X⟩/(1-sX)`. This is the correct topology
for the comparison with the localization topology: the T-topology scales
coefficients by powers of `s`, matching the denominator structure in the
localization. -/

/-- Quotient T-topology on `A⟨X⟩/(1-sX)`: the quotient of `tateTopologyT f`
by the ideal `(1-fX)`. This is the topology used for the comparison with
the localization topology on `Localization.Away f` (Wedhorn, §5.48). -/
@[reducible]
noncomputable def quotientTTopology (f : A) :
    TopologicalSpace (↥(TateAlgebra A) ⧸ oneSubfXIdeal f) :=
  @topologicalRingQuotientTopology _ (TateAlgebraWedhorn.tateTopologyT f) _
    (oneSubfXIdeal f)

/-- The quotient of the T-topology is a topological ring
(from Mathlib's `topologicalRing_quotient`, applied with the T-topology). -/
noncomputable instance quotientTTopology_isTopologicalRing (f : A) :
    @IsTopologicalRing (↥(TateAlgebra A) ⧸ oneSubfXIdeal f)
      (quotientTTopology f) _ :=
  @topologicalRing_quotient ↥(TateAlgebra A)
    (TateAlgebraWedhorn.tateTopologyT f) _
    (oneSubfXIdeal f) (TateAlgebraWedhorn.tateTopologyT_isTopologicalRing f)

/-- The quotient T-topology on `A⟨X⟩/(1-fX)` is nonarchimedean:
inherited from the nonarchimedean T-topology on `A⟨X⟩` via the
quotient map (which is continuous and open). -/
noncomputable instance quotientTTopology_nonarchimedean (f : A) :
    @NonarchimedeanRing (↥(TateAlgebra A) ⧸ oneSubfXIdeal f)
      _ (quotientTTopology f) := by
  letI : TopologicalSpace ↥(TateAlgebra A) := TateAlgebraWedhorn.tateTopologyT f
  haveI : IsTopologicalRing ↥(TateAlgebra A) :=
    TateAlgebraWedhorn.tateTopologyT_isTopologicalRing f
  haveI : NonarchimedeanRing ↥(TateAlgebra A) :=
    TateAlgebraWedhorn.tateTopologyT_nonarchimedean f
  constructor
  intro U hU
  -- The preimage of U in A⟨X⟩ is a neighborhood of 0.
  have hcont : @Continuous _ _ (TateAlgebraWedhorn.tateTopologyT f)
      (quotientTTopology f) (Ideal.Quotient.mk (oneSubfXIdeal f)) :=
    continuous_quotient_mk'
  have hU' : (Ideal.Quotient.mk (oneSubfXIdeal f)) ⁻¹' (U : Set _) ∈
      nhds (0 : ↥(TateAlgebra A)) :=
    hcont.continuousAt.preimage_mem_nhds hU
  -- Find an open additive subgroup V inside the preimage.
  obtain ⟨V, hVU⟩ := NonarchimedeanRing.is_nonarchimedean _ hU'
  -- Push V forward via the quotient map.
  refine ⟨{
    toAddSubgroup := V.toAddSubgroup.map
      (Ideal.Quotient.mk (oneSubfXIdeal f)).toAddMonoidHom
    isOpen' := QuotientRing.isOpenMap_coe _ _ V.isOpen
  }, ?_⟩
  intro x hx
  obtain ⟨y, hy, rfl⟩ := hx
  exact hVU hy

omit [PlusSubring A] [HasRestrictionMaps A] [NonarchimedeanRing A] in
/-- Multiplication by `s * t` sends `I^(k+C)` into `I^k` (inside `A₀`):
for each `t`, continuity of `x ↦ s * t * x` yields `C` with
`s * t * Im(I^{k+C}) ⊆ Im(I^k)` for all `k`.  This is the Artin-Rees
shift constant for the T-topology self-preserving neighborhood. -/
private theorem mul_st_ideal_shift (P : PairOfDefinition A) (s t : A) :
    ∃ C : ℕ, ∀ (k : ℕ) (b : P.A₀), (b : P.A₀) ∈ P.I ^ (k + C) →
      s * t * (b : A) ∈ Subtype.val '' ((P.I ^ k : Ideal P.A₀) : Set P.A₀) := by
  -- Multiplication by s*t is continuous, so ∃ C with s*t * Im(I^C) ⊆ A₀.
  have hmul_cont : Continuous (fun x : A ↦ s * t * x) :=
    continuous_const.mul continuous_id
  have hA₀_nhds : (P.A₀ : Set A) ∈ nhds (0 : A) :=
    P.isOpen.mem_nhds P.A₀.zero_mem
  have h_pre : (s * t * ·) ⁻¹' (P.A₀ : Set A) ∈ nhds (0 : A) :=
    hmul_cont.continuousAt.preimage_mem_nhds (by simp [hA₀_nhds])
  obtain ⟨C, -, hC⟩ := P.hasBasis_nhds_zero.mem_iff.mp h_pre
  -- hC : ∀ x ∈ Im(I^C), s * t * x ∈ A₀.
  refine ⟨C, fun k b hb ↦ ?_⟩
  -- b ∈ I^(k+C) ⊆ I^C * I^k. Use Ideal.mul_le and span_induction.
  rw [show k + C = C + k from by omega, pow_add] at hb
  -- b ∈ I^C * I^k. Decompose via Ideal.mul_le / the ideal product.
  -- The result s * t * val(b) ∈ val '' I^k follows because:
  -- for generators c * a with c ∈ I^C, a ∈ I^k:
  --   s * t * val(c * a) = s * t * val(c) * val(a)
  --   s * t * val(c) ∈ A₀ (by hC), so = val(d) for d ∈ A₀
  --   val(d) * val(a) = val(d * a) ∈ val(I^k) since a ∈ I^k, d ∈ A₀.
  -- For sums: val '' I^k is closed under addition (I^k is an additive subgroup).
  -- b ∈ I^C * I^k. Reduce to products c * a via Submodule.mul_induction_on,
  -- then show s * t * val(c * a) ∈ val '' I^k for each generator.
  refine Submodule.mul_induction_on hb (fun c hc a ha ↦ ?_) (fun x y hx hy ↦ ?_)
  · -- Product case: c ∈ I^C, a ∈ I^k.
    have hca : (c * a : P.A₀).val = c.val * a.val := rfl
    rw [hca, show s * t * (c.val * a.val) = (s * t * c.val) * a.val from by ring]
    have hstc : s * t * c.val ∈ (P.A₀ : Set A) :=
      hC ⟨c, hc, rfl⟩
    exact ⟨⟨s * t * c.val, hstc⟩ * a, Ideal.mul_mem_left _ _ ha, rfl⟩
  · -- Sum case: s * t * val(x + y) = s * t * val(x) + s * t * val(y).
    rw [show (x + y : P.A₀).val = x.val + y.val from rfl, mul_add]
    obtain ⟨x', hx', hx_eq⟩ := hx; obtain ⟨y', hy', hy_eq⟩ := hy
    exact ⟨x' + y', (P.I ^ k).add_mem hx' hy',
      show (x' + y' : P.A₀).val = _ by
        change x'.val + y'.val = _; rw [hx_eq, hy_eq]⟩

-- Helper: `divByS t s = algebraMap t * invSelf s` in `Localization.Away s`.
omit [TopologicalSpace A] [IsTopologicalRing A] [PlusSubring A] [HasRestrictionMaps A]
  [NonarchimedeanRing A] in
private theorem divByS_eq_algebraMap_mul_invSelf (t s : A) :
    divByS t s = algebraMap A (Localization.Away s) t *
      IsLocalization.Away.invSelf (S := Localization.Away s) s := by
  unfold divByS IsLocalization.Away.invSelf
  rw [IsLocalization.mk'_eq_mul_mk'_one]

-- Helper: `φ(divByS t s) = mk(algebraMap t * X)`.
private theorem locToQuotientOneSubfX_gen_divByS (s t : A) :
    locToQuotientOneSubfX_gen s (divByS t s) =
      Ideal.Quotient.mk (oneSubfXIdeal s)
        (algebraMap A _ t * TateAlgebra.X) := by
  rw [divByS_eq_algebraMap_mul_invSelf, map_mul,
    locToQuotientOneSubfX_gen_algebraMap,
    locToQuotientOneSubfX_gen_invSelf, ← map_mul]

-- Helper: scaled coefficient of `algebraMap(a) * g`.
private theorem scaledCoeff_algebraMap_mul (f a : A)
    (g : ↥(TateAlgebra A)) (n : ℕ) :
    f ^ n * TateAlgebra.coeff n (algebraMap A _ a * g) =
      a * (f ^ n * TateAlgebra.coeff n g) := by
  rw [TateAlgebra.coeff_algebraMap_mul, ← mul_assoc, mul_comm (f ^ n) a, mul_assoc]

-- Helper: scaled coefficient of `algebraMap(t) * X * g` at n+1.
private theorem scaledCoeff_succ_tX_mul (f t : A)
    (g : ↥(TateAlgebra A)) (n : ℕ) :
    f ^ (n + 1) * TateAlgebra.coeff (n + 1) (algebraMap A _ t * TateAlgebra.X * g) =
      f * t * (f ^ n * TateAlgebra.coeff n g) := by
  rw [show algebraMap A _ t * TateAlgebra.X * g =
    algebraMap A _ t * (TateAlgebra.X * g) from by ring,
    TateAlgebra.coeff_algebraMap_mul, TateAlgebra.coeff_succ_X_mul, pow_succ]
  ring

-- Helper: scaled coefficient of `algebraMap(t) * X * g` at 0.
private theorem scaledCoeff_zero_tX_mul (f t : A) (g : ↥(TateAlgebra A)) :
    f ^ 0 * TateAlgebra.coeff 0 (algebraMap A _ t * TateAlgebra.X * g) = 0 := by
  rw [show algebraMap A _ t * TateAlgebra.X * g =
    algebraMap A _ t * (TateAlgebra.X * g) from by ring,
    TateAlgebra.coeff_algebraMap_mul, TateAlgebra.coeff_zero_X_mul, mul_zero, mul_zero]

/-- For any neighborhood W of 0 in the quotient T-topology, there exists m such that
for all r in locSubring and b in I^m, the product phi(r) * mk(algebraMap(b)) lands in W.

This is the generator case needed by the span_induction in the continuity proof.
The proof constructs a self-preserving T-topology neighborhood G inside mk^{-1}(W) using
Artin-Rees shift constants, shows algebraMap(I^m) maps into G for m large enough, then
uses Subring.closure_induction to show every locSubring element has a lift that
stabilizes G. -/
private theorem locToQuotient_mul_small_constant_mem (D : RationalLocData A)
    [T2Space A]
    (W : Set (↥(TateAlgebra A) ⧸ oneSubfXIdeal D.s))
    (hW_top : W ∈ @nhds _ (quotientTTopology D.s) 0) :
    ∃ m : ℕ,
      ∀ (r : locSubring D.P D.T D.s) (b : D.P.A₀),
        (b : D.P.A₀) ∈ D.P.I ^ m →
        locToQuotientOneSubfX_gen D.s
          ((locSubring D.P D.T D.s).subtype r *
            algebraMap A (Localization.Away D.s) (b : A)) ∈ W := by
  -- Setup topology instances.
  letI τT : TopologicalSpace ↥(TateAlgebra A) :=
    TateAlgebraWedhorn.tateTopologyT D.s
  letI τQ : TopologicalSpace (↥(TateAlgebra A) ⧸ oneSubfXIdeal D.s) :=
    quotientTTopology D.s
  haveI hTR_T : IsTopologicalRing ↥(TateAlgebra A) :=
    TateAlgebraWedhorn.tateTopologyT_isTopologicalRing D.s
  haveI hTR_Q : IsTopologicalRing (↥(TateAlgebra A) ⧸ oneSubfXIdeal D.s) :=
    quotientTTopology_isTopologicalRing D.s
  -- Abbreviations.
  let mk := Ideal.Quotient.mk (oneSubfXIdeal D.s)
  let P := D.P; let s := D.s; let T := D.T
  -- Step 1: Get Artin-Rees shift constant C (max over all t ∈ T).
  have hC_exists : ∀ t : T, ∃ C : ℕ, ∀ (k : ℕ) (b : P.A₀),
      (b : P.A₀) ∈ P.I ^ (k + C) →
        s * t * (b : A) ∈ Subtype.val '' ((P.I ^ k : Ideal P.A₀) : Set P.A₀) :=
    fun t => mul_st_ideal_shift P s t
  choose C_fn hC_fn using hC_exists
  let C := (T.attach.image C_fn).sup id
  have hC_bound : ∀ (t : T), C_fn t ≤ C := fun t =>
    Finset.le_sup (f := id) (Finset.mem_image_of_mem _ (Finset.mem_attach _ _))
  have hC_shift : ∀ (t : T) (k : ℕ) (b : P.A₀), (b : P.A₀) ∈ P.I ^ (k + C) →
      s * t * (b : A) ∈ Subtype.val '' ((P.I ^ k : Ideal P.A₀) : Set P.A₀) := by
    intro t k b hb
    have := hC_bound t
    exact hC_fn t k b (Ideal.pow_le_pow_right (by omega) hb)
  -- Step 2: Pull W back to T-topology via mk.
  have hmk_cont : @Continuous _ _ τT τQ mk := continuous_quotient_mk'
  have hmk_pre_W : mk ⁻¹' W ∈ @nhds _ τT 0 :=
    hmk_cont.continuousAt.preimage_mem_nhds (by rwa [map_zero])
  -- Step 3: Decompose the T-topology neighborhood.
  rw [@nhds_induced _ _ (MvPowerSeries.WithPiTopology.instTopologicalSpace A)
    (TateAlgebraWedhorn.scaleIncl s) 0, Filter.mem_comap] at hmk_pre_W
  obtain ⟨W_prod, hW_prod, hW_incl⟩ := hmk_pre_W
  rw [map_zero] at hW_prod
  change W_prod ∈ @nhds _ (@Pi.topologicalSpace (Fin 1 →₀ ℕ)
    (fun _ => A) (fun _ => ‹_›)) 0 at hW_prod
  rw [nhds_pi] at hW_prod
  simp only [show ∀ i : Fin 1 →₀ ℕ,
    (0 : (Fin 1 →₀ ℕ) → A) i = (0 : A) from fun _ => rfl] at hW_prod
  obtain ⟨Idx, t_set, ht_set, hIt⟩ := Filter.mem_pi'.mp hW_prod
  -- Step 4: For each index in Idx, find m_i with Im(I^{m_i}) ⊆ t_set(i).
  have hm_exists : ∀ i : Fin 1 →₀ ℕ,
      ∃ m : ℕ, Subtype.val '' ((P.I ^ m : Ideal P.A₀) : Set P.A₀) ⊆ t_set i :=
    fun i => by
      obtain ⟨m, _, hm⟩ := P.hasBasis_nhds_zero.mem_iff.mp (ht_set i)
      exact ⟨m, hm⟩
  choose m_fn hm_fn using hm_exists
  let N := (Idx.image (fun i : Fin 1 →₀ ℕ => i 0)).sup id
  let M := (Idx.image m_fn).sup id
  -- Step 5: Construct G — the self-preserving neighborhood.
  let G : Set ↥(TateAlgebra A) := fun g =>
    ∀ n : ℕ, n ≤ N →
      s ^ n * TateAlgebra.coeff n g ∈
        Subtype.val '' ((P.I ^ (M + (N - n) * C) : Ideal P.A₀) : Set P.A₀)
  -- Step 5a: G is contained in mk⁻¹(W).
  have hG_sub_W : G ⊆ mk ⁻¹' W := by
    intro g hg
    apply hW_incl
    apply hIt
    intro i hi
    have : i 0 ≤ N :=
      Finset.le_sup (f := id) (Finset.mem_image_of_mem (fun i : Fin 1 →₀ ℕ => i 0) hi)
    have hg_i := hg (i 0) this
    have hM_bound : m_fn i ≤ M :=
      Finset.le_sup (f := id) (Finset.mem_image_of_mem m_fn hi)
    have hpow_le : M + (N - i 0) * C ≥ m_fn i := by omega
    have hsub : Subtype.val '' ((P.I ^ (M + (N - i 0) * C) : Ideal P.A₀) : Set P.A₀) ⊆
        Subtype.val '' ((P.I ^ (m_fn i) : Ideal P.A₀) : Set P.A₀) :=
      Set.image_mono (Ideal.pow_le_pow_right hpow_le)
    -- scaleIncl s g i = s^(i 0) * g.val i = s^(i 0) * coeff(i 0) g
    -- For Fin 1, i = Finsupp.single 0 (i 0), and TateAlgebra.coeff (i 0) g = g.val i.
    have hi_eq : i = Finsupp.single 0 (i 0) := by
      apply Finsupp.ext; intro j; fin_cases j; simp
    change TateAlgebraWedhorn.scaleIncl s g i ∈ t_set i
    rw [TateAlgebraWedhorn.scaleIncl_apply]
    -- Goal: s ^ (i 0) * g.val i ∈ t_set i
    -- hg_i : s ^ (i 0) * TateAlgebra.coeff (i 0) g ∈ val(I^{M+(N-i 0)*C})
    -- TateAlgebra.coeff (i 0) g = MvPowerSeries.coeff A (Finsupp.single 0 (i 0)) g
    --                            = g.val (Finsupp.single 0 (i 0)) = g.val i
    -- So the result follows from hg_i + hsub + hm_fn.
    -- We use hi_eq to convert: g.val i = g.val (Finsupp.single 0 (i 0))
    -- which equals TateAlgebra.coeff (i 0) g.
    -- g.val i = TateAlgebra.coeff (i 0) g since i = Finsupp.single 0 (i 0).
    -- So scaleIncl = s^(i 0) * TateAlgebra.coeff (i 0) g.
    have hscale : s ^ i 0 * g.val i =
        s ^ i 0 * TateAlgebra.coeff (i 0) g := by
      congr 1; change g.val i = g.val (Finsupp.single 0 (i 0)); rw [← hi_eq]
    rw [hscale]
    exact hm_fn i (hsub hg_i)
  -- Step 5b: G is an additive subgroup.
  have hG_zero : (0 : ↥(TateAlgebra A)) ∈ G := by
    intro n _
    have : TateAlgebra.coeff n (0 : ↥(TateAlgebra A)) = 0 := map_zero _
    rw [this, mul_zero]
    exact ⟨0, (P.I ^ _).zero_mem, rfl⟩
  have hG_add : ∀ {a b}, a ∈ G → b ∈ G → a + b ∈ G := by
    intro a b ha hb n hn
    have hcoeff_add : TateAlgebra.coeff n (a + b) =
        TateAlgebra.coeff n a + TateAlgebra.coeff n b := map_add _ _ _
    rw [hcoeff_add, mul_add]
    obtain ⟨x, hx, hx_eq⟩ := ha n hn
    obtain ⟨y, hy, hy_eq⟩ := hb n hn
    exact ⟨x + y, (P.I ^ _).add_mem hx hy,
      by rw [Subring.coe_add, ← hx_eq, ← hy_eq]⟩
  have hG_neg : ∀ {a}, a ∈ G → -a ∈ G := by
    intro a ha n hn
    have hcoeff_neg : TateAlgebra.coeff n (-a) = -TateAlgebra.coeff n a := map_neg _ _
    rw [hcoeff_neg, mul_neg]
    obtain ⟨x, hx, hx_eq⟩ := ha n hn
    exact ⟨-x, (P.I ^ _).neg_mem hx, by rw [NegMemClass.coe_neg, ← hx_eq]⟩
  -- Step 5c: G ∈ nhds 0 in the T-topology.
  have hG_eq : G = ⋂ (i : Fin (N + 1)), {g | s ^ (i : ℕ) * TateAlgebra.coeff (i : ℕ) g ∈
      Subtype.val '' ((P.I ^ (M + (N - (i : ℕ)) * C) : Ideal P.A₀) : Set P.A₀)} := by
    ext g; simp only [Set.mem_iInter, Set.mem_setOf_eq]
    constructor
    · intro hg ⟨i, hi⟩; exact hg i (by omega)
    · intro hg n hn; exact hg ⟨n, by omega⟩
  have hG_nhds : G ∈ @nhds _ τT 0 := by
    rw [mem_nhds_iff]
    refine ⟨G, le_refl _, ?_, hG_zero⟩
    rw [hG_eq]
    exact isOpen_iInter_of_finite fun ⟨n, _⟩ =>
      (P.pow_image_isOpen _).preimage
        (TateAlgebraWedhorn.tateTopologyT_continuous_scaledCoeff s n)
  -- Step 6: G is stable under algebraMap(a₀) * · for a₀ ∈ A₀.
  have hG_stable_alg : ∀ (a₀ : P.A₀) (g : ↥(TateAlgebra A)),
      g ∈ G → algebraMap A _ (a₀ : A) * g ∈ G := by
    intro a₀ g hg n hn
    have hrw : s ^ n * TateAlgebra.coeff n (algebraMap A _ (a₀ : A) * g) =
        (a₀ : A) * (s ^ n * TateAlgebra.coeff n g) := scaledCoeff_algebraMap_mul _ _ _ _
    rw [hrw]
    obtain ⟨b, hb, hb_eq⟩ := hg n hn
    exact ⟨a₀ * b, Ideal.mul_mem_left _ _ hb, by rw [MulMemClass.coe_mul, ← hb_eq]⟩
  -- Step 7: G is stable under algebraMap(t)*X * · for t ∈ T.
  have hG_stable_tX : ∀ (t : T) (g : ↥(TateAlgebra A)),
      g ∈ G → algebraMap A _ (t : A) * TateAlgebra.X * g ∈ G := by
    intro t g hg n hn
    by_cases hn0 : n = 0
    · subst hn0
      have hrw0 : s ^ 0 * TateAlgebra.coeff 0
          (algebraMap A _ (t : A) * TateAlgebra.X * g) = 0 :=
        scaledCoeff_zero_tX_mul _ _ _
      rw [hrw0]; exact ⟨0, (P.I ^ _).zero_mem, rfl⟩
    · obtain ⟨n', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn0
      have hrw_succ : s ^ (n' + 1) * TateAlgebra.coeff (n' + 1)
          (algebraMap A _ (t : A) * TateAlgebra.X * g) =
          s * t * (s ^ n' * TateAlgebra.coeff n' g) :=
        scaledCoeff_succ_tX_mul _ _ _ _
      rw [hrw_succ]
      have hn' : n' ≤ N := by omega
      obtain ⟨b, hb, hb_eq⟩ := hg n' hn'
      rw [← hb_eq]
      have hkey : M + (N - n') * C = (M + (N - (n' + 1)) * C) + C := by
        have : N - n' = N - (n' + 1) + 1 := by omega
        rw [this, add_mul, one_mul]; omega
      exact hC_shift t (M + (N - (n' + 1)) * C) b (hkey ▸ hb)
  -- Step 8: Find m such that algebraMap(I^m) maps into G.
  -- Use continuity of mk ∘ algebraMap: preimage of G (which is a nhd of 0 in
  -- the T-topology) under algebraMap gives a nhd of 0 in A.
  have halg_cont : @Continuous A _ _ τT (algebraMap A ↥(TateAlgebra A)) :=
    TateAlgebraWedhorn.tateTopologyT_continuous_algebraMap D.s
  have h_pre_G : (algebraMap A ↥(TateAlgebra A)) ⁻¹' G ∈ nhds (0 : A) :=
    halg_cont.continuousAt.preimage_mem_nhds (by rwa [map_zero])
  obtain ⟨m, -, hm_G⟩ := P.hasBasis_nhds_zero.mem_iff.mp h_pre_G
  -- hm_G : val(I^m) maps into the preimage of G under algebraMap.
  -- I.e., for b ∈ I^m, algebraMap(b.val) ∈ G.
  refine ⟨m, fun r b hb ↦ ?_⟩
  -- We need: φ(subtype(r) * algebraMap(b.val)) ∈ W.
  -- Rewrite as: φ(subtype(r)) * mk(algebraMap(b.val)) = mk(r') * mk(algebraMap(b.val))
  --           = mk(r' * algebraMap(b.val))
  -- where r' is a lift of r in A⟨X⟩ such that r' stabilizes G.
  -- Since algebraMap(b.val) ∈ G, r' * algebraMap(b.val) ∈ G ⊆ mk⁻¹(W).
  --
  -- Use Subring.closure_induction on r ∈ locSubring = Subring.closure(generators).
  -- Predicate: P(r) = ∃ r' : A⟨X⟩, mk(r') = φ(subtype(r)) ∧ ∀ g ∈ G, r' * g ∈ G.
  have hb_in_G : algebraMap A ↥(TateAlgebra A) (b : A) ∈ G :=
    hm_G ⟨b, hb, rfl⟩
  -- The predicate we prove by closure_induction.
  -- For each r in locSubring, there exists r' in A⟨X⟩ such that:
  --   (1) mk(r') = φ(subtype(r))
  --   (2) ∀ g ∈ G, r' * g ∈ G
  -- For each element x ∈ locSubring = Subring.closure(generators), prove
  -- there exists a lift r' ∈ A⟨X⟩ with mk(r') = φ(x) and r' stabilizes G.
  -- Then the conclusion follows: φ(r) * mk(algebraMap(b)) = mk(r' * algebraMap(b)) ∈ W.
  have hlift : ∀ (x : Localization.Away D.s),
      x ∈ locSubring D.P D.T D.s → ∃ r' : ↥(TateAlgebra A),
        mk r' = locToQuotientOneSubfX_gen D.s x ∧ ∀ g ∈ G, r' * g ∈ G := by
    intro x hx
    induction hx using Subring.closure_induction with
    | mem x hx =>
      rcases hx with ⟨a₀, ha₀, rfl⟩ | ⟨⟨t, ht⟩, rfl⟩
      · -- Case: x = algebraMap(a₀) with a₀ ∈ A₀.
        refine ⟨algebraMap A _ a₀, ?_, ?_⟩
        · rw [← locToQuotientOneSubfX_gen_algebraMap]
        · exact hG_stable_alg ⟨a₀, ha₀⟩
      · -- Case: x = divByS(t, s) with t ∈ T.
        refine ⟨algebraMap A _ t * TateAlgebra.X, ?_, ?_⟩
        · rw [← locToQuotientOneSubfX_gen_divByS]
        · exact hG_stable_tX ⟨t, ht⟩
    | zero =>
      exact ⟨0, by simp [map_zero], fun g _ ↦ by simp [zero_mul, hG_zero]⟩
    | one =>
      exact ⟨1, by simp [map_one], fun g hg ↦ by simp [one_mul, hg]⟩
    | add x y _ _ ihx ihy =>
      obtain ⟨rx, hrx_eq, hrx_stab⟩ := ihx
      obtain ⟨ry, hry_eq, hry_stab⟩ := ihy
      exact ⟨rx + ry, by rw [map_add, hrx_eq, hry_eq, map_add],
        fun g hg ↦ by rw [add_mul]; exact hG_add (hrx_stab g hg) (hry_stab g hg)⟩
    | neg x _ ihx =>
      obtain ⟨rx, hrx_eq, hrx_stab⟩ := ihx
      exact ⟨-rx, by rw [map_neg, hrx_eq, map_neg],
        fun g hg ↦ by rw [neg_mul]; exact hG_neg (hrx_stab g hg)⟩
    | mul x y _ _ ihx ihy =>
      obtain ⟨rx, hrx_eq, hrx_stab⟩ := ihx
      obtain ⟨ry, hry_eq, hry_stab⟩ := ihy
      exact ⟨rx * ry, by rw [map_mul, hrx_eq, hry_eq, map_mul],
        fun g hg ↦ by rw [mul_assoc]; exact hrx_stab _ (hry_stab g hg)⟩
  obtain ⟨r', hr'_eq, hr'_stab⟩ := hlift r.val r.property
  -- Goal: φ(subtype(r) * algebraMap(b.val)) ∈ W
  -- Rewrite to: mk(r' * algebraMap(b.val)) ∈ W
  -- φ(subtype(r) * algebraMap(b)) = φ(subtype(r)) * φ(algebraMap(b))
  --   = φ(subtype(r)) * mk(algebraMap(b))     [locToQuotientOneSubfX_gen_algebraMap]
  --   = mk(r') * mk(algebraMap(b))            [← hr'_eq]
  --   = mk(r' * algebraMap(b))                [← map_mul]
  -- And r' * algebraMap(b) ∈ G ⊆ mk⁻¹(W), so mk(r' * algebraMap(b)) ∈ W.
  -- φ(subtype(r) * algebraMap(b)) = mk(r' * algebraMap_Tate(b)) ∈ mk(G) ⊆ W
  -- The subtype coercion and r.val are the same:
  have hr_val : (locSubring D.P D.T D.s).subtype r = r.val := rfl
  rw [hr_val, map_mul, locToQuotientOneSubfX_gen_algebraMap, ← hr'_eq, ← map_mul]
  exact hG_sub_W (hr'_stab _ hb_in_G)

/-! ### Step 1b: Continuity of locToQuotientOneSubfX_gen

The continuity proof requires connecting `locNhd` to the T-topology
quotient neighborhoods via the Artin-Rees comparison. The key insight:
an element of `locNhd m` has the form `b/s^k` with `b ∈ I^m * A₀`.
Its image in the quotient is `class(algebraMap(b) * X^k)`.
The T-topology via `scaleIncl` requires `s^n * coeff_n(g) ∈ U` for all `n`.
For `g = algebraMap(b) * X^k`, the only nonzero coefficient is at `n = k`,
giving `s^k * b ∈ U`. Since `b ∈ I^m` and the topology on `A` is nonarchimedean,
`s^k * I^m ⊆ U` for `m` large enough (continuity of scalar multiplication). -/

/-- The map `locToQuotientOneSubfX_gen D.s` is continuous from the localization
topology on `Localization.Away D.s` to the quotient T-topology on
`A⟨X⟩/(1-sX)`.

**Proof sketch (Wedhorn §8.1):** The localization neighborhoods `locNhd(n)`
map into quotient T-topology neighborhoods because elements `b/s^k` with
`b ∈ I^n` get sent to `class(algebraMap(b) * X^k)` whose scaled coefficients
`s^k * b ∈ s^k * I^n` lie in any target neighborhood for `n` sufficiently large.

This is the key continuity result bridging the localization topology with
the T-topology, enabling the completion extension. -/
theorem locToQuotientOneSubfX_gen_continuous (D : RationalLocData A)
    [T2Space A] :
    @Continuous _ _ D.topology (quotientTTopology D.s)
      (locToQuotientOneSubfX_gen D.s) := by
  -- Set up instances for the source and target topologies.
  letI : TopologicalSpace (Localization.Away D.s) := D.topology
  letI : IsTopologicalRing (Localization.Away D.s) := D.isTopologicalRing
  letI : IsTopologicalAddGroup (Localization.Away D.s) := D.isTopologicalAddGroup
  letI τQ : TopologicalSpace (↥(TateAlgebra A) ⧸ oneSubfXIdeal D.s) :=
    quotientTTopology D.s
  letI : IsTopologicalRing (↥(TateAlgebra A) ⧸ oneSubfXIdeal D.s) :=
    quotientTTopology_isTopologicalRing D.s
  haveI : IsTopologicalAddGroup (↥(TateAlgebra A) ⧸ oneSubfXIdeal D.s) :=
    @IsTopologicalRing.to_topologicalAddGroup _ _
      (quotientTTopology D.s) (quotientTTopology_isTopologicalRing D.s)
  -- Step 1: Reduce to continuity at 0 using additive group structure.
  apply continuous_of_continuousAt_zero (locToQuotientOneSubfX_gen D.s)
  rw [ContinuousAt, map_zero, Filter.tendsto_def]
  intro S hS
  -- Step 2: Get a basis neighborhood from the localization topology.
  have hbasis := locBasis D.P D.T D.s D.hopen
  let hb := hbasis.toRingFilterBasis.toAddGroupFilterBasis
  -- Step 3: The target neighborhood S contains an open additive subgroup.
  -- Use the nonarchimedean property of the quotient.
  haveI : NonarchimedeanRing (↥(TateAlgebra A) ⧸ oneSubfXIdeal D.s) :=
    quotientTTopology_nonarchimedean D.s
  obtain ⟨W, hWS⟩ := NonarchimedeanRing.is_nonarchimedean S hS
  -- Step 4: It suffices to show locToQuotientOneSubfX_gen maps some
  -- locNhd n into W.
  suffices ∃ n, ∀ x ∈ locNhd D.P D.T D.s n,
      locToQuotientOneSubfX_gen D.s x ∈ (W : Set _) by
    obtain ⟨n, hn⟩ := this
    apply Filter.mem_of_superset
      (hb.nhds_zero_hasBasis.mem_iff.mpr
        ⟨locNhd D.P D.T D.s n, ⟨n, rfl⟩, le_refl _⟩)
    intro x hx
    exact hWS (hn x hx)
  -- Step 5: Use locToQuotient_mul_small_constant_mem to find m such that
  -- for all r ∈ locSubring and b ∈ I^m, φ(subtype(r) * algebraMap(b)) ∈ W.
  have hW_nhds : (W : Set _) ∈ @nhds _ τQ 0 :=
    W.isOpen.mem_nhds (W.zero_mem)
  obtain ⟨m, hm_helper⟩ :=
    locToQuotient_mul_small_constant_mem D (W : Set _) hW_nhds
  -- Step 6: Show locNhd(m) maps into W.
  -- We use Submodule.span_induction with the STRENGTHENED predicate:
  -- P(d) = "for all r ∈ locSubring, φ(subtype(r * d)) ∈ W".
  -- This handles the scalar case because r * (s * d) = (r * s) * d.
  -- Then P(d) with r = 1 gives φ(subtype(d)) ∈ W.
  refine ⟨m, ?_⟩
  rintro x ⟨d, hd, rfl⟩
  rw [locIdeal, ← Ideal.map_pow] at hd
  suffices ∀ (r : locSubring D.P D.T D.s),
      locToQuotientOneSubfX_gen D.s
        ((locSubring D.P D.T D.s).subtype (r * d)) ∈ (W : Set _) by
    specialize this 1; simp [one_mul] at this; exact this
  intro r₀
  revert r₀
  refine Submodule.span_induction (p := fun d _ ↦
      ∀ (r : locSubring D.P D.T D.s),
        locToQuotientOneSubfX_gen D.s
          ((locSubring D.P D.T D.s).subtype (r * d)) ∈
            (W : Set _)) ?_ ?_ ?_ ?_ hd
  · -- Generator: d = algebraMapD(b) for b ∈ I^m.
    rintro d ⟨b, hb, rfl⟩ r
    exact hm_helper r b hb
  · -- Zero
    intro r; simp [mul_zero, map_zero]
  · -- Addition: d₁ + d₂
    intro d₁ d₂ _ _ h₁ h₂ r
    have : (locSubring D.P D.T D.s).subtype (r * (d₁ + d₂)) =
        (locSubring D.P D.T D.s).subtype (r * d₁) +
        (locSubring D.P D.T D.s).subtype (r * d₂) := by
      simp [mul_add]
    rw [this, map_add]
    exact W.toAddSubgroup.add_mem (h₁ r) (h₂ r)
  · -- Scalar: s • d for s ∈ locSubring.
    intro s d _ hd r
    have : (locSubring D.P D.T D.s).subtype (r * (s • d)) =
        (locSubring D.P D.T D.s).subtype ((r * s) * d) := by
      simp [mul_assoc]
    rw [this]
    exact hd (r * s)

/-! ### Step 2: Extension to completion via extensionHom

Once continuity is established, `UniformSpace.Completion.extensionHom`
extends `locToQuotientOneSubfX_gen` to the completion, giving:
`presheafValueToQuotient : presheafValue D →+* A⟨X⟩/(1-sX)` -/

/-- The `IsTopologicalAddGroup` instance for the quotient T-topology. -/
noncomputable instance quotientTTopology_isTopologicalAddGroup (f : A) :
    @IsTopologicalAddGroup (↥(TateAlgebra A) ⧸ oneSubfXIdeal f)
      (quotientTTopology f) _ :=
  @IsTopologicalRing.to_topologicalAddGroup _ _
    (quotientTTopology f) (quotientTTopology_isTopologicalRing f)

/-- The `UniformSpace` on the quotient T-topology. -/
@[reducible]
noncomputable def quotientTUniformSpace (f : A) :
    UniformSpace (↥(TateAlgebra A) ⧸ oneSubfXIdeal f) :=
  @IsTopologicalAddGroup.rightUniformSpace _ _
    (quotientTTopology f) (quotientTTopology_isTopologicalAddGroup f)

/-- The `IsUniformAddGroup` instance for the quotient T-topology. -/
noncomputable instance quotientTTopology_isUniformAddGroup (f : A) :
    @IsUniformAddGroup (↥(TateAlgebra A) ⧸ oneSubfXIdeal f)
      (quotientTUniformSpace f) _ :=
  @isUniformAddGroup_of_addCommGroup _ _ (quotientTTopology f)
    (quotientTTopology_isTopologicalAddGroup f)

/-- The ring homomorphism `presheafValue D →+* A⟨X⟩/(1-sX)` extending
`locToQuotientOneSubfX_gen` to the completion.

Given that `locToQuotientOneSubfX_gen D.s` is continuous from the localization
topology to the quotient T-topology, `UniformSpace.Completion.extensionHom`
extends it to a ring homomorphism from the completion `presheafValue D`
to `A⟨X⟩/(1-sX)` (Wedhorn, Proposition 8.30).

The hypotheses `hcs` (completeness) and `ht0` (T0) on the quotient with the
T-topology hold for strongly noetherian Tate rings (Wedhorn Theorem 6.37). -/
noncomputable def presheafValueToQuotient (D : RationalLocData A)
    [T2Space A]
    (_hb : TopologicalRing.IsPowerBounded (invS D))
    (hcs : @CompleteSpace _ (quotientTUniformSpace D.s))
    (ht0 : @T0Space _ (quotientTTopology D.s)) :
    presheafValue D →+*
      (↥(TateAlgebra A) ⧸ oneSubfXIdeal D.s) := by
  letI : UniformSpace (Localization.Away D.s) := D.uniformSpace
  letI : IsTopologicalRing (Localization.Away D.s) := D.isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away D.s) := D.isUniformAddGroup
  letI : TopologicalSpace (↥(TateAlgebra A) ⧸ oneSubfXIdeal D.s) :=
    quotientTTopology D.s
  letI : IsTopologicalRing (↥(TateAlgebra A) ⧸ oneSubfXIdeal D.s) :=
    quotientTTopology_isTopologicalRing D.s
  letI : IsTopologicalAddGroup (↥(TateAlgebra A) ⧸ oneSubfXIdeal D.s) :=
    quotientTTopology_isTopologicalAddGroup D.s
  letI : UniformSpace (↥(TateAlgebra A) ⧸ oneSubfXIdeal D.s) :=
    quotientTUniformSpace D.s
  letI : IsUniformAddGroup (↥(TateAlgebra A) ⧸ oneSubfXIdeal D.s) :=
    quotientTTopology_isUniformAddGroup D.s
  exact @UniformSpace.Completion.extensionHom _ _ _ _ _ _
    (quotientTUniformSpace D.s) _ (quotientTTopology_isUniformAddGroup D.s)
    (quotientTTopology_isTopologicalRing D.s)
    (locToQuotientOneSubfX_gen D.s)
    (locToQuotientOneSubfX_gen_continuous D) hcs ht0

/-- `presheafValueToQuotient` on the dense image agrees with
`locToQuotientOneSubfX_gen`. -/
theorem presheafValueToQuotient_coe (D : RationalLocData A)
    [T2Space A]
    (hb : TopologicalRing.IsPowerBounded (invS D))
    (hcs : @CompleteSpace _ (quotientTUniformSpace D.s))
    (ht0 : @T0Space _ (quotientTTopology D.s))
    (a : Localization.Away D.s) :
    presheafValueToQuotient D hb hcs ht0 (D.coeRingHom a) =
      locToQuotientOneSubfX_gen D.s a := by
  letI : UniformSpace (Localization.Away D.s) := D.uniformSpace
  letI : IsTopologicalRing (Localization.Away D.s) := D.isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away D.s) := D.isUniformAddGroup
  letI : TopologicalSpace (↥(TateAlgebra A) ⧸ oneSubfXIdeal D.s) :=
    quotientTTopology D.s
  letI : IsTopologicalRing (↥(TateAlgebra A) ⧸ oneSubfXIdeal D.s) :=
    quotientTTopology_isTopologicalRing D.s
  letI : IsTopologicalAddGroup (↥(TateAlgebra A) ⧸ oneSubfXIdeal D.s) :=
    quotientTTopology_isTopologicalAddGroup D.s
  letI : UniformSpace (↥(TateAlgebra A) ⧸ oneSubfXIdeal D.s) :=
    quotientTUniformSpace D.s
  letI : IsUniformAddGroup (↥(TateAlgebra A) ⧸ oneSubfXIdeal D.s) :=
    quotientTTopology_isUniformAddGroup D.s
  exact @UniformSpace.Completion.extensionHom_coe _ _ _ _ _ _
    (quotientTUniformSpace D.s) _ (quotientTTopology_isUniformAddGroup D.s)
    (quotientTTopology_isTopologicalRing D.s)
    (locToQuotientOneSubfX_gen D.s)
    (locToQuotientOneSubfX_gen_continuous D) hcs ht0 a

/-! ### Step 3: The round-trip composites are identity

Using the round-trip lemma `tateQuotient_roundtrip_eq_locLift` (already proved)
and T2 uniqueness of continuous extensions, we show both composites are identity. -/

/-- The composite `tateQuotientToPresheafHom ∘ presheafValueToQuotient` is the
identity on `presheafValue D`.

On the dense image `coeRingHom(a)`:
  `tateQuotientToPresheafHom (presheafValueToQuotient (coeRingHom a))`
  `= tateQuotientToPresheafHom (locToQuotientOneSubfX_gen a)`
  `= locLiftToPresheaf a`   (by round-trip)
  `= coeRingHom a`          (by `locLiftToPresheaf_eq_coeRingHom`)

By T2 density, this extends to all of `presheafValue D`. -/
theorem tateQuotientToPresheaf_comp_presheafToQuotient (D : RationalLocData A)
    [T2Space A]
    (hb : TopologicalRing.IsPowerBounded (invS D))
    (hcs : @CompleteSpace _ (quotientTUniformSpace D.s))
    (ht0 : @T0Space _ (quotientTTopology D.s))
    (hcont_eval : @Continuous _ _
      (quotientTTopology D.s)
      (inferInstance : TopologicalSpace (presheafValue D))
      (tateQuotientToPresheafHom D hb))
    (x : presheafValue D) :
    tateQuotientToPresheafHom D hb
      (presheafValueToQuotient D hb hcs ht0 x) = x := by
  letI : UniformSpace (Localization.Away D.s) := D.uniformSpace
  letI : IsTopologicalRing (Localization.Away D.s) := D.isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away D.s) := D.isUniformAddGroup
  letI : TopologicalSpace (↥(TateAlgebra A) ⧸ oneSubfXIdeal D.s) :=
    quotientTTopology D.s
  letI : UniformSpace (↥(TateAlgebra A) ⧸ oneSubfXIdeal D.s) :=
    quotientTUniformSpace D.s
  -- Use T2 density: the composite and id agree on the dense image.
  refine @UniformSpace.Completion.ext' _ D.uniformSpace
    (presheafValue D) _ _ _ _
    (hcont_eval.comp UniformSpace.Completion.continuous_extension)
    continuous_id ?_ x
  -- On the dense image: show agreement pointwise.
  intro a
  simp only [Function.comp, id]
  change tateQuotientToPresheafHom D hb
    (presheafValueToQuotient D hb hcs ht0 (D.coeRingHom a)) = D.coeRingHom a
  rw [presheafValueToQuotient_coe D hb hcs ht0 a,
    tateQuotient_roundtrip_apply D hb a,
    locLiftToPresheaf_eq_coeRingHom D]

/-- The composite `presheafValueToQuotient ∘ tateQuotientToPresheafHom` is the
identity on `A⟨X⟩/(1-sX)`.

For `q = mk(g)` in the quotient:
  `presheafValueToQuotient (tateQuotientToPresheafHom (mk g))`
  `= presheafValueToQuotient (∑ canonicalMap(aₙ) · (invS)ⁿ)`

This requires showing the evaluation is the inverse of the localization map
on the quotient. By the universal property, it suffices to check on generators:
  - `mk(algebraMap a) ↦ canonicalMap a ↦ mk(algebraMap a)`
  - `mk(X) ↦ invS ↦ mk(X)`

The full proof uses density of the localization image in `presheafValue D`
and the round-trip on generators. -/
theorem presheafToQuotient_comp_tateQuotientToPresheaf (D : RationalLocData A)
    [T2Space A]
    (hb : TopologicalRing.IsPowerBounded (invS D))
    (hcs : @CompleteSpace _ (quotientTUniformSpace D.s))
    (ht0 : @T0Space _ (quotientTTopology D.s))
    (hcont_eval : @Continuous _ _
      (quotientTTopology D.s)
      (inferInstance : TopologicalSpace (presheafValue D))
      (tateQuotientToPresheafHom D hb))
    (hdense : @DenseRange (↥(TateAlgebra A) ⧸ oneSubfXIdeal D.s)
      (quotientTTopology D.s) (Localization.Away D.s)
      (locToQuotientOneSubfX_gen D.s))
    (q : ↥(TateAlgebra A) ⧸ oneSubfXIdeal D.s) :
    presheafValueToQuotient D hb hcs ht0
      (tateQuotientToPresheafHom D hb q) = q := by
  -- Setup instances for the quotient T-topology and localization.
  letI : UniformSpace (Localization.Away D.s) := D.uniformSpace
  letI : IsTopologicalRing (Localization.Away D.s) := D.isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away D.s) := D.isUniformAddGroup
  letI τQ : TopologicalSpace (↥(TateAlgebra A) ⧸ oneSubfXIdeal D.s) :=
    quotientTTopology D.s
  letI : UniformSpace (↥(TateAlgebra A) ⧸ oneSubfXIdeal D.s) :=
    quotientTUniformSpace D.s
  letI : IsTopologicalRing (↥(TateAlgebra A) ⧸ oneSubfXIdeal D.s) :=
    quotientTTopology_isTopologicalRing D.s
  letI : IsTopologicalAddGroup (↥(TateAlgebra A) ⧸ oneSubfXIdeal D.s) :=
    quotientTTopology_isTopologicalAddGroup D.s
  letI : IsUniformAddGroup (↥(TateAlgebra A) ⧸ oneSubfXIdeal D.s) :=
    quotientTTopology_isUniformAddGroup D.s
  -- T₀ uniform space is T₂ (uniform → regular → R1, and R1 + T₀ → T₂).
  haveI hT2 : @T2Space _ τQ := by
    haveI : @RegularSpace _ τQ :=
      @UniformSpace.to_regularSpace _ (quotientTUniformSpace D.s)
    exact inferInstance
  -- The composites agree on the dense image of locToQuotientOneSubfX_gen.
  have hagree : ∀ (a : Localization.Away D.s),
      presheafValueToQuotient D hb hcs ht0
        (tateQuotientToPresheafHom D hb (locToQuotientOneSubfX_gen D.s a)) =
        locToQuotientOneSubfX_gen D.s a := by
    intro a
    rw [tateQuotient_roundtrip_apply D hb a,
      locLiftToPresheaf_eq_coeRingHom D,
      presheafValueToQuotient_coe D hb hcs ht0 a]
  -- Use DenseRange.equalizer: two continuous maps agreeing on a dense
  -- subset of a T₂ space must be equal.
  -- g = presheafValueToQuotient ∘ tateQuotientToPresheafHom
  -- h = id
  -- Both are continuous; g ∘ locToQuotientOneSubfX_gen = h ∘ locToQuotientOneSubfX_gen.
  have h_eq : (fun q ↦ presheafValueToQuotient D hb hcs ht0
      (tateQuotientToPresheafHom D hb q)) =
    (fun q ↦ q) :=
    hdense.equalizer
      (UniformSpace.Completion.continuous_extension.comp hcont_eval)
      continuous_id
      (funext hagree)
  exact congr_fun h_eq q

/-! ### Step 4: Package as RingEquiv -/

/-- **The completion isomorphism** `presheafValue D ≃+* A⟨X⟩/(1-sX)`
(Wedhorn Proposition 8.30, Remark 7.55).

For a strongly noetherian Tate ring `A` and rational localization datum `D`,
the presheaf value (completion of `Localization.Away D.s`) is ring-isomorphic
to the Tate algebra quotient `A⟨X⟩/(1-sX)` equipped with the T-topology.

Both composites are identity:
- `tateQuotientToPresheafHom ∘ presheafValueToQuotient = id` (by T2 density)
- `presheafValueToQuotient ∘ tateQuotientToPresheafHom = id` (by round-trip on generators) -/
noncomputable def presheafValueTateQuotientEquiv (D : RationalLocData A)
    [T2Space A]
    (hb : TopologicalRing.IsPowerBounded (invS D))
    (hcs : @CompleteSpace _ (quotientTUniformSpace D.s))
    (ht0 : @T0Space _ (quotientTTopology D.s))
    (hcont_eval : @Continuous _ _
      (quotientTTopology D.s)
      (inferInstance : TopologicalSpace (presheafValue D))
      (tateQuotientToPresheafHom D hb))
    (hdense : @DenseRange (↥(TateAlgebra A) ⧸ oneSubfXIdeal D.s)
      (quotientTTopology D.s) (Localization.Away D.s)
      (locToQuotientOneSubfX_gen D.s)) :
    presheafValue D ≃+*
      (↥(TateAlgebra A) ⧸ oneSubfXIdeal D.s) where
  toFun := presheafValueToQuotient D hb hcs ht0
  invFun := tateQuotientToPresheafHom D hb
  left_inv :=
    tateQuotientToPresheaf_comp_presheafToQuotient D hb hcs ht0 hcont_eval
  right_inv :=
    presheafToQuotient_comp_tateQuotientToPresheaf D hb hcs ht0 hcont_eval hdense
  map_mul' := map_mul _
  map_add' := map_add _

/-- The isomorphism sends `canonicalMap(a)` to `mk(algebraMap a)`. -/
theorem presheafValueTateQuotientEquiv_canonicalMap (D : RationalLocData A)
    [T2Space A]
    (hb : TopologicalRing.IsPowerBounded (invS D))
    (hcs : @CompleteSpace _ (quotientTUniformSpace D.s))
    (ht0 : @T0Space _ (quotientTTopology D.s))
    (hcont_eval : @Continuous _ _
      (quotientTTopology D.s)
      (inferInstance : TopologicalSpace (presheafValue D))
      (tateQuotientToPresheafHom D hb))
    (hdense : @DenseRange (↥(TateAlgebra A) ⧸ oneSubfXIdeal D.s)
      (quotientTTopology D.s) (Localization.Away D.s)
      (locToQuotientOneSubfX_gen D.s))
    (a : A) :
    presheafValueTateQuotientEquiv D hb hcs ht0 hcont_eval hdense
      (D.canonicalMap a) =
      (Ideal.Quotient.mk _) (algebraMap A _ a) := by
  change presheafValueToQuotient D hb hcs ht0
    (D.coeRingHom (algebraMap A _ a)) = _
  rw [presheafValueToQuotient_coe, locToQuotientOneSubfX_gen_algebraMap]

/-- The inverse sends `mk(algebraMap a)` back to `canonicalMap(a)`. -/
theorem presheafValueTateQuotientEquiv_symm_algebraMap (D : RationalLocData A)
    [T2Space A]
    (hb : TopologicalRing.IsPowerBounded (invS D))
    (hcs : @CompleteSpace _ (quotientTUniformSpace D.s))
    (ht0 : @T0Space _ (quotientTTopology D.s))
    (hcont_eval : @Continuous _ _
      (quotientTTopology D.s)
      (inferInstance : TopologicalSpace (presheafValue D))
      (tateQuotientToPresheafHom D hb))
    (hdense : @DenseRange (↥(TateAlgebra A) ⧸ oneSubfXIdeal D.s)
      (quotientTTopology D.s) (Localization.Away D.s)
      (locToQuotientOneSubfX_gen D.s))
    (a : A) :
    (presheafValueTateQuotientEquiv D hb hcs ht0 hcont_eval hdense).symm
      ((Ideal.Quotient.mk _) (algebraMap A _ a)) =
      D.canonicalMap a := by
  simp only [presheafValueTateQuotientEquiv, RingEquiv.symm_mk,
    RingEquiv.coe_mk, Equiv.coe_fn_mk]
  exact tateQuotientToPresheafHom_algebraMap D hb a

end CompletionIsomorphism

end ValuationSpectrum
