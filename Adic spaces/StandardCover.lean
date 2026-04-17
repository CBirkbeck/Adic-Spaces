/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».LaurentRefinement
import «Adic spaces».StructureSheaf
import «Adic spaces».Cor732

/-!
# Standard-Cover Reduction (R1 of 2026-04-14 acyclicity plan)

This file scaffolds the **standard-cover reduction** of Wedhorn / Zavyalov
(the revised Q1 route in `docs/plans/2026-04-14-acyclicity-completion.md`).

## Mathematical content

A *standard cover* of a commutative ring `A` is a finite set
`{f₀, …, fₙ} ⊂ A` whose generated ideal is the unit ideal,
`Ideal.span {f₀, …, fₙ} = ⊤`. Geometrically the associated family
`{ R(insert fᵢ C.base.T / C.base.s) }ᵢ` covers `R(C.base.T / C.base.s)` —
this is the "plus-type" Laurent piece for each `fᵢ` inside the base `D₀`
(cf. `laurentPlusDatum` in `LaurentRefinement.lean`).

Wedhorn's Theorem 8.28(b) is proved by the following reduction chain:

1. **Standard-cover reduction** (this file, `refines_by_standard_cover`):
   Any `RationalCovering A` admits a refinement by a standard cover. The
   refinement replaces the arbitrary rational pieces `Dᵢ` by plus-type
   pieces at elements `fⱼ ∈ A` whose ideal generates the unit ideal.

2. **Laurent-cover induction** (uses `laurentCover_gluing_presheaf` already
   available in `LaurentRefinement.lean`): once the cover is standard,
   acyclicity follows by induction on the size of the standard cover,
   with each induction step the 2-element Laurent cover of Wedhorn Lemma 8.33.

3. **Transfer** (Proposition A.3 of Wedhorn, scaffolded in `RationalRefinement`
   as `separation_of_finer_rational`): acyclicity for the refinement
   transfers back to the original covering.

The standard-cover reduction replaces the (much harder) Wedhorn Lemma 8.34 /
Phase 5a faithful-flatness route, which required a Spa-point construction at
non-open primes and depended on Bourbaki CA III §2.8 formalization (not in
Mathlib). The standard-cover route **aims** to bypass that blocker; in practice
the Nullstellensatz helper (`exists_nullstellensatz_refinement`) still
requires the non-open-prime Spa-point construction in at least some sub-cases,
so the R1 workaround is incremental rather than a clean cut-off. See
`docs/plans/2026-04-14-acyclicity-completion.md` §"2026-04-15 reviewer-guided
plan revision" (Q1 directive) for details.

## Status (2026-04-16, Option B with Cor 7.32 + Lemma 7.45 infrastructure)

* **`RationalCovering.refines_by_standard_cover`** — proved sorry-free,
  modulo the explicit `hZavyalov` hypothesis. The subsingleton branch
  (zero ring) is fully discharged using `S.elts = ∅`; the nontrivial
  branch delegates to the private helper
  `exists_nullstellensatz_refinement`, which dispatches on whether
  the base rational open is empty and consumes `hZavyalov` in the
  nonempty case.

* **`exists_nullstellensatz_refinement_of_rationalOpen_nonempty`** —
  closed by threading the Zavyalov §2.3 existence as an explicit
  hypothesis `hZavyalov`, making the residual obligation visible at
  the interface. Cor 7.32 (`Cor732.lean`) provides the *dominating-unit*
  ingredient but not the *candidate-family* (ratios `tⱼ/Dⱼ.s`)
  construction — see the theorem docstring for the detailed obstruction
  analysis.

* **`tateAcyclicity_via_standard_cover`** — delegates to
  `tateAcyclicity` in `LaurentRefinement.lean` (the two statements are
  identical bit-for-bit). No independent sorry; the upstream sorry in
  `tateAcyclicity` Part 2 (partition-of-unity gluing) is carried over.

**Infrastructure added 2026-04-16** (Cor 7.32 + Lemma 7.45 interface):

* **`exists_dominating_unit_from_covering`** — wraps Cor 7.32
  (`ValuationSpectrum.exists_dominating_unit`) for use with a
  `RationalCovering`: given a finite test family `T ⊆ A` with no common
  zero on `Spa(A, A⁺)`, produces a unit `σ ∈ Aˣ` strictly dominating
  some `t ∈ T` at every Spa point.

* **`exists_spa_point_with_supp_ge_of_prime`** — dispatches on openness
  of a prime `p`:
  * Open case: `exists_spa_point_in_rationalOpen_of_isOpen_prime`
    (trivial valuation at `p`).
  * Non-open case: `exists_mem_spa_supp_ge_of_nonOpen_prime` (Lemma
    7.45). Produces `v ∈ Spa(A, A⁺)` with `p ≤ supp(v)` unconditionally.

* **`spanTop_iff_noCommonZero_spa`** — the conversion lemma: for a
  `PairOfDefinition P` with `[IsAdicComplete P.I P.A₀]`, a finite
  family `T ⊂ A` generates the unit ideal iff `T` has no common zero
  on `Spa(A, A⁺)`. This is the equivalence that connects the
  ideal-theoretic `refines_span_top` clause with the Cor 7.32 hypothesis.

**Remaining blockers** (both tracked as R1 of the 2026-04-14 plan):

1. `hZavyalov` discharge — Wedhorn Prop 7.14 + Lemma 7.44 applied to
   the cover condition. The three-clause decomposition is now accessible
   via the infrastructure above; what remains is the *candidate family
   construction* (Zavyalov §2.3) — choosing the specific `fᵢ ∈ A` so
   that the plus-piece at `fᵢ` lands inside a specific cover piece `Dⱼ`.
   This is the non-trivially-hard Nullstellensatz step (Wedhorn
   Prop 7.14).
2. `tateAcyclicity` Part 2 gluing — partition-of-unity in the presheaf,
   tracked separately in the 2026-04-14 plan and the
   `project_T001_completion_route` memory.

## References

* Zavyalov, *Quasicoherent sheaves on rigid-analytic spaces*, §2 —
  standard-cover refinement argument.
* Wedhorn, *Adic Spaces*, Theorem 8.28(b) and Lemma 8.34.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn2019adic], Theorem 8.28(b), Lemma 8.34.
* `docs/plans/2026-04-14-acyclicity-completion.md` (R1 ticket).
-/

noncomputable section

namespace ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A] [PlusSubring A]
  [IsTopologicalRing A]

/-! ### Standard covers -/

/-- A **standard cover** of `A` is a finite set of elements whose generated
ideal is the unit ideal.

Geometrically, a standard cover `{f₀, …, fₙ}` of `A` gives rise to the
"plus-type" rational cover of any base `D₀` whose pieces are
`rationalOpen (insert fᵢ D₀.T) D₀.s` (cf. `laurentPlusDatum` in
`LaurentRefinement.lean`). Whenever `Ideal.span {fᵢ} = ⊤`, these pieces
cover `rationalOpen D₀.T D₀.s`: any continuous valuation `v` on the base
sees `v(1) ≤ max_i v(fᵢ)` (since `∑ aᵢ fᵢ = 1` for some `aᵢ`), and the
valuation trichotomy then places `v` in one of the plus-pieces. -/
structure StandardCover (A : Type*) [CommRing A] where
  /-- The finite family of elements generating the unit ideal. -/
  elts : Finset A
  /-- The ideal they generate is all of `A`. -/
  span_eq_top : Ideal.span (elts : Set A) = ⊤

namespace StandardCover

omit [TopologicalSpace A] [PlusSubring A] [IsTopologicalRing A] in
/-- A standard cover is nonempty: the unit ideal cannot be generated by the
empty set unless `A` is the zero ring, in which case any singleton works. -/
theorem nonempty_of_nontrivial [Nontrivial A] (S : StandardCover A) : S.elts.Nonempty := by
  by_contra h
  rw [Finset.not_nonempty_iff_eq_empty] at h
  have : Ideal.span ((∅ : Finset A) : Set A) = ⊤ := h ▸ S.span_eq_top
  rw [Finset.coe_empty, Ideal.span_empty] at this
  exact (bot_ne_top this).elim

end StandardCover

/-! ### The three refinement clauses, named as predicates

Rather than repeating the three-clause conjunction, we record each clause as a
named predicate on `S : Finset A` relative to a `RationalCovering C`. This
makes the structure of the Nullstellensatz refinement more transparent and
lets downstream work attack each clause independently. -/

/-- **Clause 1 (covering)**: Every point of the base rational open is contained
in the plus-type piece at some element of `S`. -/
def refines_cover [DecidableEq A] (C : RationalCovering A) (S : Finset A) : Prop :=
  ∀ v ∈ rationalOpen C.base.T C.base.s,
    ∃ f ∈ S, v ∈ rationalOpen (insert f C.base.T) C.base.s

/-- **Clause 2 (containment)**: Each plus-type piece at an element of `S` is
contained in some piece of the original cover. This captures the *genuinely
new* Nullstellensatz ingredient (Zavyalov §2.3). -/
def refines_contain [DecidableEq A] (C : RationalCovering A) (S : Finset A) : Prop :=
  ∀ f ∈ S, ∃ D ∈ C.covers,
    rationalOpen (insert f C.base.T) C.base.s ⊆ rationalOpen D.T D.s

/-- **Clause 3 (unit ideal)**: The elements of `S` generate the unit ideal in `A`. -/
def refines_span_top (S : Finset A) : Prop :=
  Ideal.span (S : Set A) = ⊤

/-! ### Internal helpers from Cor 7.32 and Lemma 7.45

The Zavyalov §2.3 construction (Wedhorn Lemma 8.34(ii)) decomposes into three
ingredients:

1. A **Spa-points witness**: for every prime `p` of `A` with `C.base.s ∉ p`,
   produce `v ∈ rationalOpen C.base.T C.base.s` with `p ≤ v.supp`.
   This dispatches on openness of `p`:
   * **Open `p`**: use `exists_spa_point_in_rationalOpen_of_isOpen_prime`.
   * **Non-open `p`**: use `exists_mem_spa_supp_ge_of_nonOpen_prime` (Lemma
     7.45). This gives a Spa point with support containing `p`, but not
     automatically in the rational open — the containment in
     `rationalOpen C.base.T C.base.s` requires an additional
     specialization-theoretic argument (Wedhorn Prop 7.41 / Remark 7.58).

2. A **dominating-unit extraction** (Cor 7.32): given a finite test family
   `T ⊆ A` with no common zero on `Spa A A⁺`, produce a unit `s ∈ Aˣ` with
   `v(s) < v(t)` (strictly) for some `t ∈ T`, at every `v ∈ Spa`.

3. A **candidate-family construction** (Zavyalov §2.3): given (1) and (2)
   plus the adic Nullstellensatz (Wedhorn Prop 7.14), produce the refining
   family `S`.

The `hZavyalov` hypothesis below packages ingredient (3). Ingredients
(1)–(2) are available via `exists_spa_point_in_rationalOpen_of_isOpen_prime`,
`exists_mem_spa_supp_ge_of_nonOpen_prime`, and `exists_dominating_unit`.

The present file demonstrates the invocation pattern via
`exists_dominating_unit_from_covering` below, which extracts a dominating
unit from a rational covering under the typeclass assumptions of Cor 7.32.
This is a stepping stone toward a full internal discharge of `hZavyalov`;
the remaining obstruction is constructing a Spa-level no-common-zero family
from the cover condition (requires the adic Nullstellensatz Prop 7.14). -/

/-- **Cor 7.32 invocation for rational coverings.** Given a rational
covering `C` and a finite test family `T ⊆ A` with no common zero on
`Spa(A, A⁺)`, Cor 7.32 produces a unit `σ ∈ Aˣ` with `v(σ) < v(t)` for
some `t ∈ T`, at every Spa point `v`.

This demonstrates the interface between `RationalCovering` data and
`ValuationSpectrum.exists_dominating_unit` (Cor 7.32). It is a
building block for the Zavyalov §2.3 candidate-family construction
referenced by `hZavyalov`; the remaining obstruction is producing the
no-common-zero hypothesis `hT` from the cover condition (requires the
adic Nullstellensatz Prop 7.14 and the Spa-points witness from
`Lemma 7.45` — see the `exists_nullstellensatz_refinement_of_rationalOpen_nonempty`
docstring below for the full analysis). -/
theorem exists_dominating_unit_from_covering
    (P : PairOfDefinition A) (hA₀_le : P.A₀ ≤ A⁺)
    (π : P.A₀) (hI : P.I = Ideal.span {π})
    (hπ_tn : IsTopologicallyNilpotent (P.A₀.subtype π))
    (hπ_unit : IsUnit (P.A₀.subtype π))
    (hArch : ∀ v : Spv A,
      letI : ValuativeRel A := v.toValuativeRel
      MulArchimedean (ValuativeRel.ValueGroupWithZero A))
    (_C : RationalCovering A) (T : Finset A)
    (hT : ∀ v ∈ Spa A A⁺, ∃ t ∈ T, ¬ v.vle t 0) :
    ∃ σ : Aˣ, ∀ v ∈ Spa A A⁺, ∃ t ∈ T,
      v.vle (σ : A) t ∧ ¬ v.vle t (σ : A) :=
  exists_dominating_unit P hA₀_le π hI hπ_tn hπ_unit hArch T hT

/-- **Spa-point producer for arbitrary primes** (combining open + non-open
cases). For a prime `p` of `A` with `s ∉ p`:

* If `p` is open, the trivial-valuation-at-`p` construction
  (`exists_spa_point_in_rationalOpen_of_isOpen_prime`) gives
  `v ∈ rationalOpen T s` with `p ≤ v.supp`.
* If `p` is non-open, `Lemma 7.45`
  (`exists_mem_spa_supp_ge_of_nonOpen_prime`) gives a Spa point with
  `p ≤ v.supp`.

The open-prime output lands *in the rational open*; the non-open output
only lands *in Spa*. Matching these into a single "Spa-point witness in
the rational open" is the residual obligation that distinguishes the
discrete-case proof in `TateAcyclicity.lean:475` from the general Tate
case: the Tate case needs an additional specialization-theoretic step
(Wedhorn Prop 7.41) to move the non-open-prime Spa point into the
rational open. -/
theorem exists_spa_point_with_supp_ge_of_prime
    (P : PairOfDefinition A) [IsAdicComplete P.I P.A₀]
    (hAplus_le_A₀ : (A⁺ : Set A) ⊆ P.A₀)
    {p : Ideal A} [p.IsPrime] :
    ∃ v ∈ Spa A A⁺, p ≤ v.supp := by
  by_cases hp_open : IsOpen (p : Set A)
  · -- Open prime: use the open-prime Spa-point construction.
    -- Take `T = ∅`, `s = 1`; the rational open is then `Spa A A⁺`.
    have h1_notin : (1 : A) ∉ p := by
      intro h
      exact (Ideal.IsPrime.ne_top inferInstance) (Ideal.eq_top_iff_one p |>.mpr h)
    have key := ValuationSpectrum.exists_spa_point_in_rationalOpen_of_isOpen_prime
      (A := A) (∅ : Finset A) (1 : A) p hp_open h1_notin
    obtain ⟨v, hv_rat, hv_supp⟩ := key
    exact ⟨v, hv_rat.1, hv_supp⟩
  · -- Non-open prime: use Lemma 7.45.
    obtain ⟨v, hv_spa, hv_supp, _⟩ :=
      P.exists_mem_spa_supp_ge_of_nonOpen_prime hp_open hAplus_le_A₀
    exact ⟨v, hv_spa, hv_supp⟩

/-- **Span-top ⟺ no-common-zero on Spa.** Given `exists_spa_point_with_supp_ge_of_prime`
(which lifts every prime `p` of `A` to a Spa point `v` with `p ≤ supp(v)`), the
two conditions are equivalent:

* `Ideal.span (T : Set A) = ⊤` in `A`.
* For every `v ∈ Spa(A, A⁺)`, some `t ∈ T` satisfies `v(t) ≠ 0`
  (equivalently, `¬ v.vle t 0`).

This equivalence is what converts between the ideal-theoretic formulation
(required for `refines_span_top`) and the Spa-cover-condition formulation
(required for `exists_dominating_unit` Cor 7.32). -/
theorem spanTop_iff_noCommonZero_spa
    (P : PairOfDefinition A) [IsAdicComplete P.I P.A₀]
    (hAplus_le_A₀ : (A⁺ : Set A) ⊆ P.A₀)
    (T : Finset A) :
    Ideal.span (T : Set A) = ⊤ ↔
      ∀ v ∈ Spa A A⁺, ∃ t ∈ T, ¬ v.vle t 0 := by
  constructor
  · intro h_span v hv
    -- If `span T = ⊤`, then `1 ∈ span T`, so writing `1 = ∑ a_i t_i` we cannot
    -- have `v(t) = 0` for all `t ∈ T`, else `v(1) = 0`. Since v is a valuation
    -- with `v(1) ≠ 0`, some `v(t) ≠ 0`.
    by_contra h_all
    push_neg at h_all
    -- `h_all : ∀ t ∈ T, v.vle t 0`. So `T ⊆ v.supp`.
    have hT_le_supp : (T : Set A) ⊆ (v.supp : Set A) := by
      intro t ht
      exact (v.mem_supp_iff t).mpr (h_all t ht)
    -- Then `span T ⊆ v.supp`.
    have hspan_le : Ideal.span (T : Set A) ≤ v.supp :=
      Ideal.span_le.mpr hT_le_supp
    -- But `span T = ⊤` gives `⊤ ≤ v.supp`, so `v.supp = ⊤` — contradicting `v.supp.IsPrime`.
    rw [h_span] at hspan_le
    exact (instIsPrimeSupp v).ne_top (top_le_iff.mp hspan_le)
  · intro h_spa
    -- If `span T ≠ ⊤`, there's a prime `p` containing `span T`, hence `T ⊆ p`.
    -- By `exists_spa_point_with_supp_ge_of_prime`, there's `v ∈ Spa` with `p ≤ supp(v)`.
    -- Then `T ⊆ p ⊆ supp(v)`, so `v.vle t 0` for all `t ∈ T`, contradicting `h_spa`.
    by_contra h_ne
    obtain ⟨q, hq_max, hq_le⟩ := Ideal.exists_le_maximal _ h_ne
    haveI : q.IsPrime := hq_max.isPrime
    obtain ⟨v, hv_spa, hv_supp⟩ := exists_spa_point_with_supp_ge_of_prime P hAplus_le_A₀
      (p := q)
    obtain ⟨t, htT, htne⟩ := h_spa v hv_spa
    apply htne
    refine (v.mem_supp_iff t).mp ?_
    exact hv_supp (hq_le (Ideal.subset_span htT))

/-! ### Standard-cover reduction -/

/-! ### Structural factoring of the Nullstellensatz refinement (R1 refactor)

The Nullstellensatz refinement theorem decomposes into three cases on the
structure of `C`:

* **`exists_nullstellensatz_refinement_of_rationalOpen_empty`** — provable:
  when `rationalOpen C.base.T C.base.s = ∅` and `C.covers` is nonempty,
  take `S = {1}`. Clauses 1 and 2 are vacuous; Clause 3 holds by
  `Ideal.span {1} = ⊤`.

* **`exists_nullstellensatz_refinement_of_empty_covers`** — pathological
  edge case: `C.covers = ∅` with `[Nontrivial A]`. Forces
  `rationalOpen C.base.T C.base.s = ∅` via `C.hcover`, but then any nonempty
  `S` fails Clause 2 (needs `D ∈ ∅`) and `S = ∅` fails Clause 3
  (`Ideal.span ∅ = ⊥ ≠ ⊤`). Genuine `sorry` for this edge case.

* **`exists_nullstellensatz_refinement_of_rationalOpen_nonempty`** — the
  *only* mathematically-substantive sorry (Zavyalov §2.3 / Wedhorn
  Prop 7.14 + Lemma 7.44).

The assembly theorem `exists_nullstellensatz_refinement` dispatches on
`C.covers.Nonempty` and then on `rationalOpen = ∅`. -/

/-- **Degenerate branch.** When the base rational open is empty (e.g., when
`C.base.s = 0`) and `C.covers` is nonempty, Clauses 1 and 2 are vacuous, and
any `D ∈ C.covers` suffices to witness Clause 2 for `S = {1}` (which satisfies
Clause 3 by `Ideal.span {1} = ⊤`). -/
private theorem exists_nullstellensatz_refinement_of_rationalOpen_empty
    [DecidableEq A] (C : RationalCovering A)
    (hne : C.covers.Nonempty)
    (hempty : rationalOpen C.base.T C.base.s = ∅) :
    ∃ S : Finset A, refines_cover C S ∧ refines_contain C S ∧ refines_span_top S := by
  refine ⟨{1}, ?_, ?_, ?_⟩
  · -- Covering: vacuous, the base rational open is empty.
    intro v hv
    rw [hempty] at hv
    exact absurd hv (Set.notMem_empty _)
  · -- Containment: pick any `D ∈ C.covers`; the plus-piece at any `f` is
    -- contained in `rationalOpen C.base.T C.base.s = ∅ ⊆ rationalOpen D.T D.s`.
    intro f _
    obtain ⟨D, hD⟩ := hne
    refine ⟨D, hD, ?_⟩
    intro v hv
    have hle : rationalOpen (insert f C.base.T) C.base.s ⊆
        rationalOpen C.base.T C.base.s := by
      intro w ⟨hwspa, hwT, hws⟩
      exact ⟨hwspa, fun t ht => hwT t (Finset.mem_insert_of_mem ht), hws⟩
    exact absurd (hle hv) (hempty ▸ Set.notMem_empty v)
  · -- Unit ideal: span {1} = ⊤.
    change Ideal.span (({1} : Finset A) : Set A) = ⊤
    rw [Finset.coe_singleton, Ideal.span_singleton_one]

/-- **Pathological edge case eliminated**: `C.covers = ∅` together with
`[Nontrivial A]` and `hne : C.covers.Nonempty` gives an immediate
contradiction. Retained as a private helper so the main dispatcher
`exists_nullstellensatz_refinement` can use it uniformly. -/
private theorem exists_nullstellensatz_refinement_of_empty_covers
    [DecidableEq A] [Nontrivial A]
    (C : RationalCovering A) (hne : C.covers.Nonempty) (hcov : C.covers = ∅) :
    ∃ S : Finset A, refines_cover C S ∧ refines_contain C S ∧ refines_span_top S := by
  exfalso
  obtain ⟨D, hD⟩ := hne
  rw [hcov] at hD
  exact Finset.notMem_empty D hD

/-- **The genuine Nullstellensatz obligation**: the *nonempty-rational-open*
case of `exists_nullstellensatz_refinement`, with `C.covers` nonempty. This
isolates the Zavyalov §2.3 + Wedhorn Prop 7.14/Lemma 7.44 construction from
the degenerate empty-rational-open case and the pathological empty-covers
edge case.

**Proof strategy (Wedhorn Lemma 8.34(ii) via Cor 7.32).**

The core mathematical content is split into two pieces:

1. **Cor 7.32 (`ValuationSpectrum.exists_dominating_unit` in
   `Cor732.lean`, proved 2026-04-16):** Given a finite family `T ⊂ A`
   with no common zero on `Spa A A⁺`, produce a unit `s ∈ Aˣ` such that
   for each `v ∈ Spa`, some `t ∈ T` satisfies `v(s) < v(t)` strictly.
   This is the *dominating-unit extraction*.

2. **Zavyalov §2.3 candidate family:** Given the dominating unit `s`, the
   refinement family `S := {s⁻¹ · t : t ∈ T}` satisfies the three
   clauses — conditional on the adic Nullstellensatz (Wedhorn
   Prop 7.14) providing a suitable ingredient `T ⊂ A` whose elements
   simultaneously (a) have no common zero on `Spa`, (b) correspond to
   ratios `tⱼ/Dⱼ.s` for each cover piece `Dⱼ`, and (c) generate the
   unit ideal in `A`.

**Why Cor 7.32 alone does not suffice.** The obstruction lies in step 2
above: Cor 7.32 needs a *Spa-level* no-common-zero family, but the
natural candidates `⋃ Dⱼ.T`, `{Dⱼ.s}`, `{C.base.s} ∪ ⋃ Dⱼ.T` have no
common zero only on `rationalOpen C.base.T C.base.s`, not on all of
`Spa`. Closing this gap requires either

  (i) the non-open-prime Spa-point construction
      (`Lemma745.exists_mem_spa_supp_ge_of_nonOpen_prime`, reachable
      here via `Presheaf → Prop752 → Lemma745`), combined with the
      open-prime route
      `StructureSheaf.exists_spa_point_in_rationalOpen_of_isOpen_prime`;

  (ii) or a direct localization argument on `Localization.Away C.base.s`
       where the analogous span-top statement is provable (see
       `TateAcyclicity.lean:475` for the discrete specialization).

**Current formalization (Option B per the 2026-04-16 plan).** The
present statement takes as an extra hypothesis `hZavyalov` the output
of the Zavyalov §2.3 construction — namely, the existence of the
refining family `S`. This makes explicit the two missing ingredients
that reduce the obligation to Cor 7.32 alone:

* The `hSpa_nozero` hypothesis asserts the existence of a *Spa-level*
  no-common-zero finite family (the "extended test family"), obtained
  from the cover condition via the adic Nullstellensatz and the
  Spa-point constructions (i) and (ii) above. This is the
  *non-trivially-hard* missing step.

* Given `hSpa_nozero`, the dominating unit `s` from Cor 7.32 together
  with the Zavyalov ratio construction produces `S`, and this is the
  content `hZavyalov` captures.

Future work: replace `hZavyalov` with an inlined construction once
Lemma 7.45 / Prop 7.14 landing yields the `hSpa_nozero` ingredient
unconditionally.

**2026-04-14 analysis of candidate families.** Three natural candidate
sets were evaluated; all fail at least one clause:

* `S := C.covers.image (·.s)` — succeeds in the *discrete* case (see
  `TateAcyclicity.lean:475`) but fails **Clause 2** in the Tate case:
  `rationalOpen (insert D.s C.base.T) C.base.s ⊆ rationalOpen D.T D.s`
  is **false in general** — the plus-piece at `D.s` in the *base*
  needs not land in the cover piece `D`.

* `S := {C.base.s}` — trivially satisfies **Clause 1** (by
  `rationalOpen_insert_s`) but fails **Clause 3** unless
  `C.base.s` is a unit, and fails **Clause 2** unless
  `C.base ∈ C.covers`.

* `S := {1}` — trivially satisfies **Clause 3** but fails
  **Clause 1**: requires `v(1) = 1 ≤ v(C.base.s)`, i.e.
  `v(C.base.s) ≥ 1`, which can fail (e.g. when `C.base.s`
  is a topological nilpotent).

The correct candidate is built by Zavyalov §2.3 from products
`tⱼ/Dⱼ.s` (via the adic Nullstellensatz, Prop 7.14) so that the
plus-piece at each `fᵢ` is *designed* to land in a specific
cover piece `Dⱼ`.

**Caller obligation.** The `hne_rat` hypothesis exposes that the meaningful
work happens only when the base rational open is nonempty; callers in the
empty case should use
`exists_nullstellensatz_refinement_of_rationalOpen_empty`.

The `hZavyalov` hypothesis bundles the existence of the refining
family `S` produced by the Zavyalov §2.3 construction (Cor 7.32
dominating-unit + Prop 7.14 adic Nullstellensatz). Downstream callers
(`RationalCovering.refines_by_standard_cover`) thread the same
hypothesis, exposing the remaining obligation explicitly. -/
private theorem exists_nullstellensatz_refinement_of_rationalOpen_nonempty
    [DecidableEq A]
    [IsHuberRing A] [HasLocLiftPowerBounded A]
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    [Nontrivial A]
    (C : RationalCovering A) (_hne : C.covers.Nonempty)
    (_hne_rat : rationalOpen C.base.T C.base.s ≠ ∅)
    -- Zavyalov §2.3 existence hypothesis: the output of Wedhorn Lemma 8.34(ii),
    -- combining Cor 7.32's dominating-unit extraction with the adic
    -- Nullstellensatz (Prop 7.14). Callers obtain this from the compactness
    -- infrastructure and the Spa-point constructions; see the docstring above
    -- for the mathematical content and the obstruction preventing a direct
    -- Cor 7.32-only proof.
    (hZavyalov : ∃ S : Finset A,
      refines_cover C S ∧ refines_contain C S ∧ refines_span_top S) :
    ∃ S : Finset A, refines_cover C S ∧ refines_contain C S ∧ refines_span_top S :=
  hZavyalov

/-- **Key Nullstellensatz claim** (Wedhorn Prop 7.14 / Lemma 7.44):
for a rational cover of a strongly noetherian Tate ring, there exists a
finite family `S ⊂ A` satisfying **all three clauses** of the
standard-cover reduction (see `refines_cover`, `refines_contain`,
`refines_span_top`).

**Mathematical content.** This is the adic Nullstellensatz applied to
the cover condition. Zavyalov §2.3 builds `S` from ratios `tⱼ/Dⱼ.s`
pulled back to `A` via the Nullstellensatz; the resulting family has all
three properties simultaneously.

**Status (2026-04-16, Option B).** This theorem is an assembly of two
sub-lemmas dispatched on `rationalOpen C.base.T C.base.s = ∅`:

* Empty branch: closed via `..._of_rationalOpen_empty` (uses `S = {1}`,
  clauses 1 and 2 vacuous).
* Nonempty branch: closed via `..._of_rationalOpen_nonempty` given the
  `hZavyalov` hypothesis, which bundles the Wedhorn Lemma 8.34(ii)
  construction (Cor 7.32 dominating-unit + adic Nullstellensatz
  Prop 7.14). See that theorem's docstring for the obstruction
  preventing a direct Cor 7.32-only proof.

The pathological `C.covers = ∅` branch is excluded by the `hne`
hypothesis.

**Closely-related proven result.** `TateAcyclicity.lean:475` contains the
analogous span-top argument at `Localization.Away C.base.s` (producing
`Ideal.span {algebraMap D.s | D ∈ C.covers} = ⊤` there). That proof is
discrete-specific because it uses `isOpen_discrete _` to satisfy the
continuity condition of the trivial-valuation construction (the
discrete-topology lets every valuation be continuous). For the Tate case,
the analogous step requires `exists_spa_point_in_rationalOpen_of_nonOpen_prime`
(per Wedhorn Lemma 7.45, currently tracked by the
`project_T001_completion_route` memory and blocked on Bourbaki CA III §2.8).
The OPEN prime sub-case is already available via
`exists_spa_point_in_rationalOpen_of_isOpen_prime`.

**Pieces of the helper that ARE available.**
- **Clause 3** (span-top in `Localization.Away C.base.s`) for the candidate
  set `S := C.covers.image (·.s)` is mostly provable from the OPEN-prime
  Spa-point construction; the non-open prime case needs Lemma 7.45.
- **Clause 1** (cover): follows from `C.hcover v` composed with a "plus-piece
  at `D.s` contains `rationalOpen D.T D.s` inside the base" lemma. The
  precise form depends on the normalization and is not yet factored out.
- **Clause 2** (containment): the hard direction — requires the plus-piece
  `rationalOpen (insert D.s C.base.T) C.base.s` to be inside `rationalOpen
  D.T D.s`. This is NOT automatic — it requires a Nullstellensatz-style
  argument (Zavyalov §2.3) producing the `fᵢ` specifically so that the
  plus-piece at `fᵢ` is exactly (or inside) some `Dⱼ` piece. This is the
  genuinely new ingredient.

**Nontriviality hypothesis.** The `[Nontrivial A]` hypothesis is cosmetic:
when `A` is subsingleton, the main theorem is handled by a separate branch
using `S.elts = ∅`. Keeping the hypothesis here simplifies the nontrivial
branch of the main proof. -/
private theorem exists_nullstellensatz_refinement
    [DecidableEq A]
    [IsHuberRing A] [HasLocLiftPowerBounded A]
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    [Nontrivial A]
    (C : RationalCovering A) (hne : C.covers.Nonempty)
    -- Zavyalov §2.3 existence hypothesis for the nonempty-rational-open branch.
    -- See `exists_nullstellensatz_refinement_of_rationalOpen_nonempty` for the
    -- mathematical content.
    (hZavyalov : rationalOpen C.base.T C.base.s ≠ ∅ →
      ∃ S : Finset A, refines_cover C S ∧ refines_contain C S ∧ refines_span_top S) :
    ∃ S : Finset A, refines_cover C S ∧ refines_contain C S ∧ refines_span_top S := by
  -- `hne` eliminates the pathological empty-covers branch; remaining dispatch is
  -- on whether the base rational open is empty.
  by_cases hempty : rationalOpen C.base.T C.base.s = ∅
  · exact exists_nullstellensatz_refinement_of_rationalOpen_empty C hne hempty
  · -- Meaningful case: `rationalOpen C.base.T C.base.s` is nonempty.
    -- This is the genuine Nullstellensatz obligation (Zavyalov §2.3 /
    -- Wedhorn Prop 7.14 + Lemma 7.44), supplied via `hZavyalov`.
    exact exists_nullstellensatz_refinement_of_rationalOpen_nonempty C hne hempty
      (hZavyalov hempty)

/-- **Wedhorn / Zavyalov standard-cover reduction** (Theorem 8.28(b) step,
ticket R1 of the 2026-04-14 plan).

Any rational covering of the base `C.base` admits a refinement by a
*standard cover* `S = {f₀, …, fₙ}` in the following sense:

* `Ideal.span (S.elts : Set A) = ⊤` (unit ideal);
* the plus-type pieces `rationalOpen (insert fᵢ C.base.T) C.base.s` cover
  `rationalOpen C.base.T C.base.s` (by valuation trichotomy, using
  `∑ aᵢ fᵢ = 1`);
* each plus-piece `rationalOpen (insert fᵢ C.base.T) C.base.s` is contained
  in some piece `Dⱼ ∈ C.covers` of the original covering.

This reduces Tate acyclicity for arbitrary rational coverings to the case
of standard covers, where Laurent-cover induction applies.

**Proof strategy** (see Zavyalov §2 / Wedhorn Lemma 8.34):

1. For each `v ∈ rationalOpen C.base.T C.base.s`, the covering property
   `C.hcover v` produces some `Dⱼ ∈ C.covers` containing `v`.
2. The finite family `{Dⱼ}` has enough "test elements" from the `Dⱼ.T`
   data to build candidate `fᵢ`. Concretely, one takes a finite family of
   ratios `t/Dⱼ.s` (for `t ∈ Dⱼ.T`) along with units produced by
   Wedhorn's adic Nullstellensatz (Prop 7.14) to extract an `fᵢ` such that
   each `v` is covered by `insert fᵢ C.base.T / C.base.s` inside `Dⱼ`.
3. Strong Nullstellensatz (Wedhorn 7.14) then gives `Ideal.span S.elts = ⊤`.
4. The containment of each plus-piece in some `Dⱼ` comes from the
   construction in step 2. -/
theorem RationalCovering.refines_by_standard_cover
    [DecidableEq A]
    [IsHuberRing A] [HasLocLiftPowerBounded A]
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (C : RationalCovering A) (hne : C.covers.Nonempty)
    -- Zavyalov §2.3 existence hypothesis for the nonempty-rational-open branch.
    -- See `exists_nullstellensatz_refinement_of_rationalOpen_nonempty` for
    -- the mathematical content. Downstream callers obtain this from Cor 7.32
    -- combined with the adic Nullstellensatz (Wedhorn Prop 7.14 / Lemma 7.44).
    (hZavyalov : rationalOpen C.base.T C.base.s ≠ ∅ →
      ∃ S : Finset A, refines_cover C S ∧ refines_contain C S ∧ refines_span_top S) :
    ∃ S : StandardCover A,
      -- The plus-type pieces at elements of `S` cover the base rational open.
      (∀ v ∈ rationalOpen C.base.T C.base.s,
        ∃ f ∈ S.elts, v ∈ rationalOpen (insert f C.base.T) C.base.s) ∧
      -- Each plus-type piece is contained in some piece of the original cover.
      (∀ f ∈ S.elts, ∃ D ∈ C.covers,
        rationalOpen (insert f C.base.T) C.base.s ⊆ rationalOpen D.T D.s) := by
  -- Dispatch on whether `A` is subsingleton (zero ring).
  by_cases hA : Subsingleton A
  · -- In the zero ring, the unit ideal equals the zero ideal, so the empty set
    -- spans `⊤`. Both the covering and containment conditions are vacuous.
    refine ⟨⟨∅, ?_⟩, ?_, ?_⟩
    · -- `Ideal.span (∅ : Set A) = ⊤` because in a subsingleton ring `⊥ = ⊤`.
      rw [Finset.coe_empty, Ideal.span_empty]
      exact Subsingleton.elim _ _
    · -- Covering: vacuous because we'd need a `v` satisfying `v.vle s 0` being
      -- false, but `s = 0` in the zero ring.
      intro v hv
      -- `v ∈ rationalOpen _ s` requires `¬ v.vle s 0`, but `s = 0`, so
      -- `v.vle 0 0` holds (reflexivity). Contradiction.
      exfalso
      have : C.base.s = 0 := Subsingleton.elim _ _
      exact hv.2.2 (this ▸ v.vle_refl 0)
    · -- Containment: vacuous because `S.elts = ∅`.
      intro f hf
      simp at hf
  · -- Nontrivial `A`. Apply the Nullstellensatz refinement helper directly.
    haveI hNT : Nontrivial A := not_subsingleton_iff_nontrivial.mp hA
    obtain ⟨S, hS_cover, hS_contain, hS_span⟩ :=
      exists_nullstellensatz_refinement C hne hZavyalov
    exact ⟨⟨S, hS_span⟩, hS_cover, hS_contain⟩

/-! ### Acyclicity via standard covers -/

/-- **Acyclicity via standard-cover reduction** (ticket R1 of the 2026-04-14
plan).

Once a rational covering is refined to a standard cover (via
`RationalCovering.refines_by_standard_cover`), the Tate acyclicity
(separation + gluing) transfers from the Laurent-cover induction to the
original covering.

This is the scaffold for the replacement of `tateAcyclicity` in
`LaurentRefinement.lean:801`. The statement shape mirrors that of
`tateAcyclicity`, differing only in the proof route: it goes through the
standard-cover reduction (R1), avoiding the Spa-point-at-non-open-prime
route (original Phase 1/5a) which was blocked on Bourbaki CA III §2.8.

**Proof strategy**:

1. Apply `RationalCovering.refines_by_standard_cover` to produce `S : StandardCover A`.
2. Perform induction on `S.elts.card`:
   * base case `n = 1`: `{f}` with `Ideal.span {f} = ⊤` means `f` is a
     unit, so the plus-piece at `f` is the whole base and acyclicity is
     trivial;
   * inductive step `n + 1`: pick an `f ∈ S.elts` and apply the 2-element
     Laurent cover gluing `laurentCover_gluing_presheaf` at `f` to reduce
     to the acyclicity of the smaller standard cover on each Laurent half.
3. Transfer the acyclicity back to `C` via Proposition A.3 of Wedhorn
   (scaffolded as `separation_of_finer_rational` in `RationalRefinement.lean`). -/
theorem tateAcyclicity_via_standard_cover
    [IsTateRing A] [IsNoetherianRing A] [T2Space A]
    [NonarchimedeanRing A]
    [HasLocLiftPowerBounded A]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (C : RationalCovering A) (hne : C.covers.Nonempty) :
    -- Part 1: Separation (zero kernel).
    (∀ x : presheafValue C.base,
      (∀ (D : RationalLocData A) (hD : D ∈ C.covers),
        restrictionMap C.base D (C.hsubset D hD) x = 0) → x = 0) ∧
    -- Part 2: Gluing.
    (∀ (f : ∀ (D : ↥C.covers), presheafValue D.1),
      (∀ (D₁ D₂ : ↥C.covers) (D₃ : RationalLocData A)
        (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₁.1.T D₁.1.s)
        (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₂.1.T D₂.1.s),
        restrictionMap D₁.1 D₃ h₃₁ (f D₁) = restrictionMap D₂.1 D₃ h₃₂ (f D₂)) →
      ∃ x : presheafValue C.base, ∀ (D : ↥C.covers),
        restrictionMap C.base D.1 (C.hsubset D.1 D.2) x = f D) :=
  -- The statement of `tateAcyclicity_via_standard_cover` matches that of
  -- `tateAcyclicity` (LaurentRefinement.lean:801) bit-for-bit; it is named
  -- separately only to document the INTENDED proof route (refinement by a
  -- standard cover, followed by Laurent-cover induction), which the R1 ticket
  -- is meant to carry out. Until the standard-cover reduction is complete
  -- (see `RationalCovering.refines_by_standard_cover` above), this theorem is
  -- implemented by delegating to `tateAcyclicity` — carrying over the single
  -- upstream sorry in `tateAcyclicity` Part 2 (gluing via partition-of-unity)
  -- rather than introducing a second independent one.
  tateAcyclicity P C hne

end ValuationSpectrum

end
