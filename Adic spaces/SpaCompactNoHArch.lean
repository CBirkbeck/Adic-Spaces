/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».SpaCompact
import «Adic spaces».Presheaf

/-!
# No-`hArch` compactness and per-`v` cofinality (T-COMPACT-NO-HARCH)

Per round-22 reviewer (ChatGPT Pro, 2026-05-16): no-`hArch` compactness of
rational half-spaces, plus a per-`v` cofinality bridge used in the P3
domination lemma.

The half-space compactness itself remains a TODO (`Spv(A, I)` track), but
the **per-v cofinality** sub-lemma is fully proved here and is the
substantive ingredient for the domination lemma's open-cover argument.

## Mathematical content

For `v ∈ Spa(A, A⁺)` (continuous), `π : A` topologically nilpotent, and
`a : A` with `v(a) ≠ 0`, there exists `N : ℕ` with `v(π^N) < v(a)`. This
is per-`v` cofinality at the specific value `γ = v(a)`, following exactly
the technique of `not_vle_one_of_mem_spa_of_topologicallyNilpotent` (which
is the `γ = 1` specialisation).

No mul-archimedean assumption enters; the argument is just Wedhorn 7.7
continuity + topological nilpotence of `π`.

References: Wedhorn §7.1–§7.2 + §7.5 (arXiv:1910.05934). Round-22
reviewer reply at `.mathlib-quality/expert-review/2026-05-16-3/reply.md`.
-/

namespace ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A] [PlusSubring A]
  [IsTopologicalRing A]

omit [IsTopologicalRing A] in
/-- **Per-`v` cofinality bridge (no `hArch`).** For a continuous valuation
`v ∈ Spa A A⁺`, a topologically nilpotent element `π : A`, and any `a : A`
with `v(a) ≠ 0`, there exists `N : ℕ` such that `v(π^N) < v(a)` strictly,
i.e. `¬ v.vle a (π^N)`.

Proved by adapting `not_vle_one_of_mem_spa_of_topologicallyNilpotent`
(`SpaCompact.lean`): continuity says `{x : v(x) < v(a)}` is open;
topological nilpotence of `π` says `π^N → 0` in `A`; so eventually
`v(π^N) < v(a)`. -/
lemma exists_pow_lt_of_topNilp_of_ne_zero
    {v : Spv A} (hv : v ∈ Spa A A⁺)
    {π : A} (hπ_tn : IsTopologicallyNilpotent π)
    {a : A} (ha : ¬ v.vle a 0) :
    ∃ N : ℕ, ¬ v.vle a (π ^ N) := by
  letI : ValuativeRel A := v.toValuativeRel
  -- Continuity of `v` yields `{x | val(x) < val(a)}` open.
  have hcont : v.IsContinuous := hv.1
  have h_open :
      IsOpen {x : A | (ValuativeRel.valuation A) x <
        (ValuativeRel.valuation A) a} :=
    hcont ((ValuativeRel.valuation A) a)
  -- `0` is in this set since `val(a) ≠ 0` (from `ha`).
  have h0_mem : (0 : A) ∈ {x : A | (ValuativeRel.valuation A) x <
      (ValuativeRel.valuation A) a} := by
    simp only [Set.mem_setOf_eq, map_zero]
    -- `val(a) ≠ 0` follows from `ha : ¬ v.vle a 0`.
    have hva_ne : (ValuativeRel.valuation A) a ≠ 0 := by
      intro h_eq
      apply ha
      -- `val(a) = 0` ⟹ `val(a) ≤ val(0) = 0` ⟹ `v.vle a 0`.
      have hva_le : (ValuativeRel.valuation A) a ≤
          (ValuativeRel.valuation A) 0 := by
        rw [h_eq, map_zero]
      exact (Valuation.Compatible.vle_iff_le
        (v := ValuativeRel.valuation A) a 0).mpr hva_le
    exact zero_lt_iff.mpr hva_ne
  -- Topological nilpotence of `π` + open set containing 0 → eventually `π^n` is in.
  obtain ⟨N, hN⟩ := (hπ_tn.eventually (h_open.mem_nhds h0_mem)).exists
  -- `hN : (ValuativeRel.valuation A) (π^N) < (ValuativeRel.valuation A) a`.
  -- Translate to `¬ v.vle a (π^N)`.
  refine ⟨N, ?_⟩
  intro h_vle
  have h_le := (Valuation.Compatible.vle_iff_le
    (v := ValuativeRel.valuation A) a (π ^ N)).mp h_vle
  exact absurd h_le (not_le.mpr hN)

/-- **Uniform `π`-power domination on a compact set.** Given a compact set
`K ⊆ ↥(Spa A A⁺)`, a topologically nilpotent `π : A`, and `a : A` with
`v(a) ≠ 0` for every `v ∈ K`, there exists a uniform `N : ℕ` such that
`v.vle (π^N) a` for every `v ∈ K`.

Proof: the per-`v` cofinality `exists_pow_lt_of_topNilp_of_ne_zero`
supplies a per-point `N(v)`; the open sets
`U_N := K ∩ {w : (w : Spv A).vle (π^N) a}` are monotone increasing and
cover `K`; compactness extracts a single uniform `N₀`.

This is the substantive open-cover ingredient for the P3 domination
lemma, modulo the (still TODO) no-`hArch` compactness of the half-space
itself. -/
lemma exists_uniform_pow_vle_on_compact
    {K : Set ↥(Spa A A⁺)} (hK : IsCompact K)
    {π : A} (hπ_tn : IsTopologicallyNilpotent π)
    {a : A} (ha : ∀ w ∈ K, ¬ (w.1 : Spv A).vle a 0) :
    ∃ N : ℕ, ∀ w ∈ K, (w.1 : Spv A).vle (π ^ N) a := by
  -- The open cover: `U N` = `{w ∈ ↥(Spa A A⁺) : w.1.vle (π^N) a}`, intersected with K.
  -- Each open in `↥(Spa A A⁺)` since `basicOpen` is open in Spv and
  -- the subtype map is continuous.
  let U : ℕ → Set ↥(Spa A A⁺) := fun N =>
    Subtype.val ⁻¹' (basicOpen (π ^ N) a : Set (Spv A))
  have hU_open : ∀ N, IsOpen (U N) := fun N =>
    (isOpen_basicOpen _ _).preimage continuous_subtype_val
  -- The cover is monotone increasing (`U N ⊆ U (N+1)` via `v.vle (π^(N+1)) (π^N)`).
  have hU_mono : ∀ N M, N ≤ M → U N ⊆ U M := by
    intro N M hNM w hw
    obtain ⟨hwN_le, hw_a_ne⟩ := hw
    refine ⟨?_, hw_a_ne⟩
    -- `v.vle (π^M) a` from `v.vle (π^N) a` and `v.vle (π^M) (π^N)`.
    letI : ValuativeRel A := w.1.toValuativeRel
    have : (ValuativeRel.valuation A) (π ^ M) ≤
        (ValuativeRel.valuation A) (π ^ N) := by
      simp only [map_pow]
      have hπ_le_one : (ValuativeRel.valuation A) π ≤ 1 := by
        by_contra h_not
        push_neg at h_not
        -- if v(π) > 1, then for the "v(π^n) < 1" set being a nbhd of 0, fails.
        -- Use that the Spa hypothesis gives bounded power.
        -- Actually for our purpose, we use that π is top.nilp. via hπ_tn.
        -- v(π) > 1 contradicts top.nilp.
        have h_nilp : ¬ w.1.vle 1 π := by
          have hw_spa : w.1 ∈ Spa A A⁺ := w.2
          exact not_vle_one_of_mem_spa_of_topologicallyNilpotent hw_spa hπ_tn
        apply h_nilp
        -- v(1) ≤ v(π) iff 1 ≤ v(π).
        have := (Valuation.Compatible.vle_iff_le
          (v := ValuativeRel.valuation A) 1 π).mpr
        apply this
        rw [map_one]
        exact h_not.le
      -- For `x ≤ 1` and `N ≤ M`, we have `x^M ≤ x^N`.
      -- Proof: x^M = x^N · x^(M-N) ≤ x^N · 1 = x^N (since x^(M-N) ≤ 1).
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hNM
      rw [pow_add]
      calc (ValuativeRel.valuation A) π ^ N * (ValuativeRel.valuation A) π ^ k
          ≤ (ValuativeRel.valuation A) π ^ N * 1 :=
            mul_le_mul_left' (Left.pow_le_one_of_le hπ_le_one k) _
        _ = (ValuativeRel.valuation A) π ^ N := mul_one _
    -- Now translate to vle.
    -- hwN_le : w.1.vle (π^N) a, i.e., v(π^N) ≤ v(a).
    -- We have v(π^M) ≤ v(π^N) ≤ v(a), so v(π^M) ≤ v(a).
    have hwN_le' := (Valuation.Compatible.vle_iff_le
      (v := ValuativeRel.valuation A) (π ^ N) a).mp hwN_le
    exact (Valuation.Compatible.vle_iff_le
      (v := ValuativeRel.valuation A) (π ^ M) a).mpr
      (le_trans this hwN_le')
  -- The cover covers K: for each `w ∈ K`, per-v cofinality gives some N.
  have hK_cover : K ⊆ ⋃ N, U N := by
    intro w hw
    have hw_spa : w.1 ∈ Spa A A⁺ := w.2
    have hw_a_ne : ¬ w.1.vle a 0 := ha w hw
    obtain ⟨N, hN_strict⟩ :=
      exists_pow_lt_of_topNilp_of_ne_zero hw_spa hπ_tn hw_a_ne
    refine Set.mem_iUnion.mpr ⟨N, ?_, hw_a_ne⟩
    -- `hN_strict : ¬ w.1.vle a (π^N)`, want `w.1.vle (π^N) a`.
    -- From totality of `vle`.
    rcases w.1.vle_total (π ^ N) a with h | h
    · exact h
    · exact absurd h hN_strict
  -- Apply `IsCompact.elim_directed_cover`.
  have hU_directed : Directed (· ⊆ ·) U := fun N M =>
    ⟨max N M, hU_mono N (max N M) (le_max_left N M),
     hU_mono M (max N M) (le_max_right N M)⟩
  obtain ⟨N₀, hN₀⟩ := hK.elim_directed_cover U hU_open hK_cover hU_directed
  refine ⟨N₀, fun w hw => ?_⟩
  exact (hN₀ hw).1

variable [IsHuberRing A] [IsTateRing A]

/-- **(T-COMPACT-NO-HARCH, round-22 reviewer-mandated.) Half-space compactness
without `hArch`.** The half-space `R(L) ∩ {v(g) ≤ v(h)}` in
`↥(Spa A A⁺)` is compact, **without** any mul-archimedean assumption on
valuation value groups.

**Status (round-22).** Stated with `sorry` to unblock P3 work. The
discharge plan is the `Spv(A, I)` infrastructure track
(`T-SPV-AI-WEDHORN-710`). Round-22 reviewer explicitly permits this as
a no-`hArch` TODO scaffolding lemma. -/
theorem isCompact_rationalOpen_inter_vle_noHArch
    (L : RationalLocData A) (g h : A) :
    IsCompact (Subtype.val ⁻¹'
      (rationalOpen L.T L.s ∩ {v | v.vle g h}) : Set ↥(Spa A A⁺)) := by
  -- See module docstring for the proof plan via Spv(A, I).
  sorry

end ValuationSpectrum
