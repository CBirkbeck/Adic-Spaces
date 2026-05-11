/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.RingTheory.Filtration
import Mathlib.RingTheory.AdicCompletion.Topology
import Mathlib.RingTheory.Ideal.Quotient.Noetherian
import «Adic spaces».GeometricSeries

/-!
# Closedness of Ideals in the I-adic Topology

For a Noetherian commutative ring `R` equipped with the `I`-adic topology, every
ideal `q ⊆ R` is **closed** provided `I` is contained in the Jacobson radical
of `R` (e.g., if `R` is `I`-adically complete, or if `I` is a Tate pair's ideal
of definition containing a topologically nilpotent unit).

The proof combines:
1. The topological characterization of closure in the `I`-adic topology:
   `x ∈ closure q ↔ ∀ n, x ∈ q + I^n` (since the basic open neighborhoods
   of `x` are the cosets `x + I^n`).
2. **Krull's intersection theorem** for Noetherian rings with ideals contained
   in the Jacobson radical: `⋂ n, I^n • (R/q) = 0` in the quotient `R/q`,
   which translates to `⋂ n, (q + I^n) = q` in `R`.

## Main results

* `Ideal.isClosed_of_le_jacobson` — the core closedness lemma.

## References

This is a topological consequence of Artin–Rees / Krull (Stacks 00IN / 00IP).
Used downstream by the Tate-acyclicity `coeRingHom_preserves_proper` chain
(`Cor832.lean`).
-/

open Topology

universe u

namespace ValuationSpectrum

variable {R : Type u} [CommRing R] [IsNoetherianRing R]

omit [IsNoetherianRing R] in
/-- Characterization of closure in the `I`-adic topology: `x ∈ closure q`
iff `x ∈ q + I^n` for every `n`. -/
theorem mem_closure_iff_of_isAdic
    [TopologicalSpace R] [IsTopologicalRing R]
    {I : Ideal R} (hI : IsAdic I) (q : Ideal R) (x : R) :
    x ∈ closure (q : Set R) ↔ ∀ n : ℕ, x ∈ (q + I ^ n : Ideal R) := by
  rw [mem_closure_iff_nhds]
  constructor
  · intro hx n
    -- Basic neighborhood `x + I^n` of `x`, viewed as the image of `I^n` under `(x + ·)`.
    have hmem : (x + ·) '' ((I ^ n : Ideal R) : Set R) ∈ 𝓝 x :=
      (hI.hasBasis_nhds x).mem_of_mem (i := n) trivial
    obtain ⟨y, hy_nhd, hy_q⟩ := hx _ hmem
    -- `y ∈ x + I^n`, i.e., `y = x + z` for some `z ∈ I^n`.
    obtain ⟨z, hz_In, rfl⟩ := hy_nhd
    -- `x + z ∈ q`, `z ∈ I^n`, so `x = (x + z) - z = (x + z) + (-z) ∈ q + I^n`.
    have hx_eq : x = (x + z) + (-z) := by ring
    rw [hx_eq]
    exact (q + I ^ n).add_mem
      (Submodule.mem_sup_left hy_q)
      (Submodule.mem_sup_right ((I ^ n).neg_mem hz_In))
  · intro hx U hU
    -- Take `n` with `x + I^n ⊆ U`.
    rw [(hI.hasBasis_nhds x).mem_iff] at hU
    obtain ⟨n, -, hn⟩ := hU
    -- From `hx n : x ∈ q + I^n`, write `x = a + b` with `a ∈ q`, `b ∈ I^n`.
    obtain ⟨a, ha_q, b, hb_In, hab⟩ := Submodule.mem_sup.mp (hx n)
    -- `a = x - b = x + (-b) ∈ x + I^n ⊆ U`; also `a ∈ q`.
    refine ⟨a, ?_, ha_q⟩
    apply hn
    refine ⟨-b, (I ^ n).neg_mem hb_In, ?_⟩
    show x + (-b) = a
    rw [← hab]; ring

/-- **Closedness of ideals in the `I`-adic topology under the Jacobson
hypothesis.** For a Noetherian commutative ring `R` equipped with the `I`-adic
topology and `I ⊆ Jacobson(⊥)`, every ideal `q ⊆ R` is closed.

Proof: by `mem_closure_iff_of_isAdic`, `closure q = ⋂ n, (q + I^n)`. Krull's
intersection theorem applied to the finitely generated `R`-module `R/q` gives
`⋂ n, I^n • (R/q) = 0`, which translates to `⋂ n, (q + I^n) = q`. -/
theorem Ideal.isClosed_of_le_jacobson
    [TopologicalSpace R] [IsTopologicalRing R]
    {I : Ideal R} (hI : IsAdic I)
    (h_jac : I ≤ Ideal.jacobson ⊥)
    (q : Ideal R) : IsClosed (q : Set R) := by
  rw [← closure_subset_iff_isClosed]
  intro x hx
  rw [mem_closure_iff_of_isAdic hI] at hx
  -- Apply Krull's intersection theorem to the R-module `R ⧸ q`.
  have hKrull : (⨅ n : ℕ, I ^ n • (⊤ : Submodule R (R ⧸ q))) = ⊥ :=
    Ideal.iInf_pow_smul_eq_bot_of_le_jacobson I h_jac
  set π := Ideal.Quotient.mk q
  -- Show `π x ∈ ⋂ n, I^n • ⊤` in `R ⧸ q`.
  have hπx_inter : π x ∈ (⨅ n : ℕ, I ^ n • (⊤ : Submodule R (R ⧸ q))) := by
    rw [Submodule.mem_iInf]
    intro n
    -- From `hx n : x ∈ q + I^n`, `π x` equals `π b` for some `b ∈ I^n`.
    obtain ⟨a, ha_q, b, hb_In, hab⟩ := Submodule.mem_sup.mp (hx n)
    have hπa : π a = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr ha_q
    have hπx : π x = π b := by
      rw [show x = a + b from hab.symm, map_add, hπa]; exact zero_add _
    rw [hπx]
    -- `π b ∈ I^n • ⊤` in `R ⧸ q`. Via `Submodule.Quotient.mk_smul`:
    -- `π b = π (b • 1) = b • π 1 = b • (1 : R/q)`, and `b • 1 ∈ I^n • ⊤`.
    have hπb_mem : (b : R) • (1 : R ⧸ q) ∈
        I ^ n • (⊤ : Submodule R (R ⧸ q)) :=
      Submodule.smul_mem_smul hb_In Submodule.mem_top
    convert hπb_mem using 1
    -- Goal: `π b = b • (1 : R ⧸ q)`.
    -- Uses `Submodule.Quotient.mk_smul`: `mk (r • x) = r • mk x`.
    show (Submodule.Quotient.mk b : R ⧸ (q : Submodule R R)) =
      b • (Submodule.Quotient.mk (1 : R) : R ⧸ (q : Submodule R R))
    rw [← Submodule.Quotient.mk_smul]
    congr 1
    exact (mul_one b).symm
  -- `hKrull` gives `π x = 0`, i.e., `x ∈ q`.
  rw [hKrull, Submodule.mem_bot] at hπx_inter
  exact Ideal.Quotient.eq_zero_iff_mem.mp hπx_inter

/-- **Closedness of ideals in the `I`-adic topology for `I`-adically complete
Noetherian rings.** Corollary of `Ideal.isClosed_of_le_jacobson` using
`IsAdicComplete.le_jacobson_bot`. -/
theorem Ideal.isClosed_of_isAdicComplete
    [TopologicalSpace R] [IsTopologicalRing R]
    (I : Ideal R) (hI : IsAdic I) [IsAdicComplete I R]
    (q : Ideal R) : IsClosed (q : Set R) :=
  Ideal.isClosed_of_le_jacobson hI (IsAdicComplete.le_jacobson_bot I) q

/-- **Pointwise Jacobson closedness.** Sharper analog of
`Ideal.isClosed_of_le_jacobson` taking a pointwise Jacobson containment
`I ≤ Ideal.jacobson q` at the **specific** ideal `q`, rather than the
global `I ≤ Ideal.jacobson ⊥`.

Strategy (suggested by the T007 plan): work in the quotient ring `R ⧸ q`.
The pointwise `R`-Jacobson hypothesis at `q` translates to a **global**
`R ⧸ q`-Jacobson hypothesis at `⊥`, via the maximal-ideal correspondence
between maximals of `R` above `q` and maximals of `R ⧸ q`. Mathlib's
existing Krull theorem then closes the quotient-ring intersection, which
pulls back to `⋂ n, (q + I^n) = q` in `R`.

This is strictly more general than `Ideal.isClosed_of_le_jacobson`:
`I ≤ Ideal.jacobson ⊥` implies `I ≤ Ideal.jacobson q` for every `q`
(monotonicity of `Ideal.jacobson`), but not conversely (non-Henselian
rings typically have `Ideal.jacobson ⊥ ⊊ Ideal.jacobson q` for specific
`q`). Useful for the Tate-acyclicity Cor 8.32 route where the global
containment fails in degenerate `locSubring` cases but the pointwise
containment at prime extensions holds unconditionally. -/
theorem Ideal.isClosed_of_le_jacobson_pointwise
    [TopologicalSpace R] [IsTopologicalRing R]
    {I : Ideal R} (hI : IsAdic I)
    (q : Ideal R) (h_jac : I ≤ Ideal.jacobson q) :
    IsClosed (q : Set R) := by
  rw [← closure_subset_iff_isClosed]
  intro x hx
  rw [mem_closure_iff_of_isAdic hI] at hx
  -- Step 1: Set up quotient ring R ⧸ q.
  set π : R →+* R ⧸ q := Ideal.Quotient.mk q with hπ_def
  set J : Ideal (R ⧸ q) := Ideal.map π I with hJ_def
  -- Step 2: J ≤ Ideal.jacobson ⊥ in R ⧸ q via the maximal-ideal correspondence.
  have hJ_jac : J ≤ Ideal.jacobson (⊥ : Ideal (R ⧸ q)) := by
    rw [Ideal.jacobson, le_sInf_iff]
    rintro m ⟨-, hm_max⟩
    -- Lift `m ⊂ R ⧸ q` max to `comap π m ⊂ R`, also max (and ⊃ q).
    haveI : m.IsMaximal := hm_max
    have hm'_max : (Ideal.comap π m).IsMaximal :=
      Ideal.comap_isMaximal_of_surjective π Ideal.Quotient.mk_surjective
    have hq_le_m' : q ≤ Ideal.comap π m := by
      intro y hy
      change π y ∈ m
      rw [show π y = 0 from Ideal.Quotient.eq_zero_iff_mem.mpr hy]
      exact m.zero_mem
    -- I ≤ Ideal.jacobson q ≤ comap π m (m' above is one of the maximals defining `jacobson q`).
    have hI_le : I ≤ Ideal.comap π m := by
      refine h_jac.trans ?_
      rw [Ideal.jacobson]
      exact sInf_le ⟨hq_le_m', hm'_max⟩
    rwa [hJ_def, Ideal.map_le_iff_le_comap]
  -- Step 3: Krull in R ⧸ q as self-module. Provide the quotient-noetherian instance.
  haveI : IsNoetherianRing (R ⧸ q) := Ideal.Quotient.isNoetherianRing q
  have hKrull : (⨅ n : ℕ, J ^ n • (⊤ : Submodule (R ⧸ q) (R ⧸ q))) = ⊥ :=
    Ideal.iInf_pow_smul_eq_bot_of_le_jacobson J hJ_jac
  -- Step 4: Pull x from `closure q` back. It suffices to show `π x = 0`.
  suffices h : π x = 0 by
    exact (Ideal.Quotient.eq_zero_iff_mem (I := q)).mp h
  -- `π x ∈ ⋂ J^n • ⊤`, then Krull gives `π x = 0`.
  have hπx_mem : π x ∈ (⨅ n : ℕ, J ^ n • (⊤ : Submodule (R ⧸ q) (R ⧸ q))) := by
    rw [Submodule.mem_iInf]
    intro n
    -- From `hx n : x ∈ q + I^n`, decompose `x = a + b` with `a ∈ q`, `b ∈ I^n`.
    obtain ⟨a, ha_q, b, hb_In, hab⟩ := Submodule.mem_sup.mp (hx n)
    have hπa : π a = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr ha_q
    have hπx_eq : π x = π b := by
      have hxeq : x = a + b := hab.symm
      rw [hxeq, map_add, hπa]
      exact zero_add _
    rw [hπx_eq]
    -- `π b ∈ J^n`: `b ∈ I^n` so `π b ∈ map π (I^n) = (map π I)^n = J^n`.
    have hπb : π b ∈ J ^ n := by
      have h1 : π b ∈ Ideal.map π (I ^ n) := Ideal.mem_map_of_mem π hb_In
      rwa [Ideal.map_pow] at h1
    -- `π b ∈ J^n • ⊤`: use `π b = π b • 1` and `Submodule.smul_mem_smul`.
    change π b ∈ J ^ n • (⊤ : Submodule (R ⧸ q) (R ⧸ q))
    have hπb_eq : π b = π b • (1 : R ⧸ q) := (mul_one (π b)).symm
    rw [hπb_eq]
    exact Submodule.smul_mem_smul hπb Submodule.mem_top
  rw [hKrull, Submodule.mem_bot] at hπx_mem
  exact hπx_mem

/-! ### Bridge: closedness in an open subring lifts to the ambient ring

For an open subring `S` of a topological ring `R`, `S` is automatically
clopen (open subgroups are clopen, `AddSubgroup.isClosed_of_isOpen`), and
hence subsets of `S` that are closed in the subspace topology are also
closed in `R`. This is the abstract ingredient for lifting closedness from
the ring of definition `locSubring` to `Localization.Away D.s`. -/

omit [IsNoetherianRing R] in
/-- **Clopen subspace bridge for closedness.** For a subring `S` that is open
in a topological ring `R` (equivalently clopen, since `AddSubgroup.isOpen`
implies `IsClosed`), any subset `C ⊆ S` closed in the subspace topology of `S`
is closed in `R`. -/
theorem IsClosed.of_isClosed_subspace_of_isOpen_subring
    [TopologicalSpace R] [IsTopologicalRing R]
    {S : Subring R} (hS_open : IsOpen (S : Set R))
    {C : Set R} (hC_sub : C ⊆ (S : Set R))
    (hC_closed_sub : IsClosed ((S.subtype) ⁻¹' C : Set S)) :
    IsClosed C := by
  -- `S` is clopen: open hypothesis + `AddSubgroup.isClosed_of_isOpen`.
  have hS_closed : IsClosed (S : Set R) :=
    S.toAddSubgroup.isClosed_of_isOpen hS_open
  -- Closed in subspace = preimage of some closed set under inclusion.
  -- Using `Topology.IsInducing.isClosed_iff` for `S.subtype` (an embedding).
  have h_inducing : Topology.IsInducing (S.subtype : S → R) :=
    Topology.IsEmbedding.subtypeVal.isInducing
  obtain ⟨C', hC'_closed, hC'_preimage⟩ := h_inducing.isClosed_iff.mp hC_closed_sub
  -- `C = C' ∩ S` (since `C ⊆ S`).
  have hC_eq : C = C' ∩ (S : Set R) := by
    ext x
    constructor
    · intro hxC
      refine ⟨?_, hC_sub hxC⟩
      -- `x ∈ C ⊆ S`, so `x = S.subtype ⟨x, hx_S⟩`, and we need `x ∈ C'`.
      have hx_S : x ∈ (S : Set R) := hC_sub hxC
      have := hC'_preimage
      -- `S.subtype ⁻¹' C' = (S.subtype) ⁻¹' C` (preimage of C = preimage of C' via inducing).
      have : (S.subtype ⁻¹' C' : Set S) = S.subtype ⁻¹' C := hC'_preimage
      have hmem : (⟨x, hx_S⟩ : S) ∈ (S.subtype ⁻¹' C' : Set S) := by
        rw [this]; exact hxC
      exact hmem
    · rintro ⟨hxC', hxS⟩
      have hmem : (⟨x, hxS⟩ : S) ∈ (S.subtype ⁻¹' C : Set S) := by
        rw [← hC'_preimage]; exact hxC'
      exact hmem
  rw [hC_eq]
  exact hC'_closed.inter hS_closed

/-! ### Topologically nilpotent elements and the Jacobson radical

**Generic algebraic machinery** (no `locSubring`/`Tate` specialization; pure
topological-ring facts). These lemmas produce the `I ≤ Ideal.jacobson ⊥`
hypothesis consumed by `Ideal.isClosed_of_le_jacobson` above, under a
`complete Hausdorff nonarchimedean` setup on the ambient ring.

The path used in S-IDEAL-JAC is:
1. `isTopologicallyNilpotent_of_mem_of_isAdic` — in an `I`-adic topology,
   every element of `I` is topologically nilpotent (no completeness needed).
2. `Ideal.le_jacobson_bot_of_forall_isTopologicallyNilpotent` — if every
   element of `I` is topologically nilpotent, then `I ≤ Ideal.jacobson ⊥`
   (via `IsTopologicallyNilpotent.isUnit_one_sub`, Wedhorn Prop 5.38).

Combined:
3. `Ideal.le_jacobson_bot_of_isAdic_complete` — for a complete Hausdorff
   nonarchimedean ring with the `I`-adic topology, `I ≤ Ideal.jacobson ⊥`. -/

section TopologicallyNilpotentJacobson

omit [IsNoetherianRing R] in
/-- **In an `I`-adic topology, every element of `I` is topologically nilpotent.**
For `x ∈ I`, the powers `x^n ∈ I^n` eventually land in any `I^m` neighborhood
of `0` (whenever `n ≥ m`). No completeness or Hausdorff hypothesis needed. -/
theorem isTopologicallyNilpotent_of_mem_of_isAdic
    [TopologicalSpace R] [IsTopologicalRing R]
    {I : Ideal R} (hI : IsAdic I) {x : R} (hx : x ∈ I) :
    IsTopologicallyNilpotent x := by
  intro U hU
  rw [hI.hasBasis_nhds_zero.mem_iff] at hU
  obtain ⟨m, -, hU_sub⟩ := hU
  refine Filter.eventually_atTop.mpr ⟨m, fun n hn => hU_sub ?_⟩
  exact Ideal.pow_le_pow_right hn (Ideal.pow_mem_pow hx n)

omit [IsNoetherianRing R] in
/-- **Generic Jacobson containment from topological nilpotence.** In a
complete Hausdorff nonarchimedean commutative topological ring, if every
element of an ideal `I` is topologically nilpotent, then `I ≤ Ideal.jacobson ⊥`.

**Proof.** For `x ∈ I` and `y : R`, the product `x * y ∈ I` is topologically
nilpotent, so `1 - (-(x*y)) = 1 + x*y = x*y + 1` is a unit by
`IsTopologicallyNilpotent.isUnit_one_sub` (Wedhorn Prop 5.38). This is the
characterization `Ideal.mem_jacobson_bot`. -/
theorem Ideal.le_jacobson_bot_of_forall_isTopologicallyNilpotent
    [UniformSpace R] [T2Space R] [CompleteSpace R]
    [IsTopologicalRing R] [IsUniformAddGroup R] [NonarchimedeanAddGroup R]
    {I : Ideal R} (hI : ∀ x ∈ I, IsTopologicallyNilpotent x) :
    (I : Ideal R) ≤ Ideal.jacobson ⊥ := by
  intro x hx
  rw [Ideal.mem_jacobson_bot]
  intro y
  have hxy_tn : IsTopologicallyNilpotent (x * y) :=
    hI _ (I.mul_mem_right y hx)
  have hrewrite : x * y + 1 = 1 - (-(x * y)) := by ring
  rw [hrewrite]
  exact hxy_tn.neg.isUnit_one_sub

omit [IsNoetherianRing R] in
/-- **Jacobson containment for `I`-adic complete Hausdorff nonarchimedean rings.**
Combines `IsAdic.isTopologicallyNilpotent_of_mem` with
`Ideal.le_jacobson_bot_of_forall_isTopologicallyNilpotent`. This is the
conclusion of Mathlib's `IsAdicComplete.le_jacobson_bot` re-derived along the
topological-nilpotence route (which stays inside the adic-topology world).

The `IsAdicComplete` hypothesis of Mathlib decomposes as
`IsPrecomplete + IsHausdorff`, equivalent (under `IsAdic I`) to
`CompleteSpace + T2Space`; `NonarchimedeanAddGroup` and `IsUniformAddGroup`
are automatic for the `I`-adic topology. -/
theorem Ideal.le_jacobson_bot_of_isAdic_complete
    [UniformSpace R] [T2Space R] [CompleteSpace R]
    [IsTopologicalRing R] [IsUniformAddGroup R] [NonarchimedeanAddGroup R]
    {I : Ideal R} (hI : IsAdic I) :
    I ≤ Ideal.jacobson (⊥ : Ideal R) :=
  Ideal.le_jacobson_bot_of_forall_isTopologicallyNilpotent
    (fun _ hx => isTopologicallyNilpotent_of_mem_of_isAdic hI hx)

end TopologicallyNilpotentJacobson

end ValuationSpectrum
