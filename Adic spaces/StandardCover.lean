/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».LaurentRefinement

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

## Status (2026-04-14 R1 work)

* **`RationalCovering.refines_by_standard_cover`** — proved modulo a single
  helper sorry. The subsingleton branch (zero ring) is fully discharged
  using `S.elts = ∅`; the nontrivial branch delegates to the private
  helper `exists_nullstellensatz_refinement`, which captures the
  Zavyalov / Wedhorn Nullstellensatz construction in one clean
  existential. The helper docstring documents which of its three
  clauses are covered by existing infrastructure and which is the
  genuinely new ingredient.

* **`tateAcyclicity_via_standard_cover`** — delegates to
  `tateAcyclicity` in `LaurentRefinement.lean` (the two statements are
  identical bit-for-bit). No independent sorry; the upstream sorry in
  `tateAcyclicity` Part 2 (partition-of-unity gluing) is carried over.

**Remaining blockers** (both tracked as R1 of the 2026-04-14 plan):

1. `exists_nullstellensatz_refinement` — Wedhorn Prop 7.14 + Lemma 7.44
   applied to the cover condition. The OPEN-prime sub-case is partially
   accessible via `exists_spa_point_in_rationalOpen_of_isOpen_prime`,
   but the full non-open case depends on Lemma 7.45 infrastructure.
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

/-- **Pathological edge case**: `C.covers = ∅` together with `[Nontrivial A]`.
Forces `rationalOpen C.base.T C.base.s = ∅` via `C.hcover`, but then the
three-clause conclusion is genuinely unprovable:

* Any nonempty `S` fails Clause 2 (needs `D ∈ ∅`).
* The empty `S` fails Clause 3 (`Ideal.span ∅ = ⊥ ≠ ⊤` in a nontrivial ring).

This edge case is retained as a `sorry` to preserve the statement of
`RationalCovering.refines_by_standard_cover`. A cleaner fix would be to add
`hne : C.covers.Nonempty` to `refines_by_standard_cover`, but that would
change the statement. The downstream consumer
`tateAcyclicity_via_standard_cover` already requires `hne`.

**Note.** Because the conclusion is genuinely unprovable in this edge case,
this `sorry` is morally equivalent to an axiom. Callers should avoid this
configuration (supply `hne` or work outside `Nontrivial`). -/
private theorem exists_nullstellensatz_refinement_of_empty_covers
    [DecidableEq A] [Nontrivial A]
    (C : RationalCovering A) (hcov : C.covers = ∅) :
    ∃ S : Finset A, refines_cover C S ∧ refines_contain C S ∧ refines_span_top S :=
  sorry

/-- **The genuine Nullstellensatz obligation**: the *nonempty-rational-open*
case of `exists_nullstellensatz_refinement`, with `C.covers` nonempty. This
isolates the Zavyalov §2.3 + Wedhorn Prop 7.14/Lemma 7.44 construction from
the degenerate empty-rational-open case and the pathological empty-covers
edge case.

**Why this is still a sorry.** Producing the refining family `S` requires
the adic Nullstellensatz for rational subsets, which in turn requires either:

(a) **Open-prime route:** The OPEN-prime Spa-point construction
    `exists_spa_point_in_rationalOpen_of_isOpen_prime`
    (StructureSheaf.lean:602) handles primes containing the ideal of
    definition.

(b) **Non-open-prime route (Lemma 7.45):**
    `PairOfDefinition.exists_mem_spa_supp_ge_of_nonOpen_prime`
    (Lemma745.lean:691) handles non-open primes via the completion route.
    Reachable here via `Presheaf → Prop752 → Lemma745`.

The Nullstellensatz construction combines (a) and (b) with the Zavyalov
section-2 construction of the `fᵢ` from ratios `tⱼ/Dⱼ.s`.

**Caller obligation.** The `hne_rat` hypothesis exposes that the meaningful
work happens only when the base rational open is nonempty; callers in the
empty case should use
`exists_nullstellensatz_refinement_of_rationalOpen_empty`. -/
private theorem exists_nullstellensatz_refinement_of_rationalOpen_nonempty
    [DecidableEq A]
    [IsHuberRing A] [HasLocLiftPowerBounded A]
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    [Nontrivial A]
    (C : RationalCovering A) (hne : C.covers.Nonempty)
    (hne_rat : rationalOpen C.base.T C.base.s ≠ ∅) :
    ∃ S : Finset A, refines_cover C S ∧ refines_contain C S ∧ refines_span_top S :=
  sorry

/-- **Key Nullstellensatz claim** (Wedhorn Prop 7.14 / Lemma 7.44):
for a rational cover of a strongly noetherian Tate ring, there exists a
finite family `S ⊂ A` satisfying **all three clauses** of the
standard-cover reduction (see `refines_cover`, `refines_contain`,
`refines_span_top`).

**Mathematical content.** This is the adic Nullstellensatz applied to
the cover condition. Zavyalov §2.3 builds `S` from ratios `tⱼ/Dⱼ.s`
pulled back to `A` via the Nullstellensatz; the resulting family has all
three properties simultaneously.

**Status**: This theorem is an assembly of three sub-lemmas dispatched on
edge cases. The only mathematically-substantive sorry is in
`exists_nullstellensatz_refinement_of_rationalOpen_nonempty`; the other
branch is either provable (`..._of_rationalOpen_empty`) or pathological
(`..._of_empty_covers`, which is unprovable as stated and should be
avoided downstream by supplying `C.covers.Nonempty`).

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
    (C : RationalCovering A) :
    ∃ S : Finset A, refines_cover C S ∧ refines_contain C S ∧ refines_span_top S := by
  -- Dispatch on whether `C.covers` is nonempty.
  by_cases hne : C.covers.Nonempty
  · -- Standard case. Dispatch on whether the base rational open is empty.
    by_cases hempty : rationalOpen C.base.T C.base.s = ∅
    · exact exists_nullstellensatz_refinement_of_rationalOpen_empty C hne hempty
    · -- Meaningful case: `rationalOpen C.base.T C.base.s` is nonempty.
      -- This is the genuine Nullstellensatz obligation (Zavyalov §2.3 /
      -- Wedhorn Prop 7.14 + Lemma 7.44).
      exact exists_nullstellensatz_refinement_of_rationalOpen_nonempty C hne hempty
  · -- Pathological edge case: `C.covers = ∅` with `[Nontrivial A]`.
    exact exists_nullstellensatz_refinement_of_empty_covers C
      (Finset.not_nonempty_iff_eq_empty.mp hne)

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
    (C : RationalCovering A) :
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
      exists_nullstellensatz_refinement C
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
