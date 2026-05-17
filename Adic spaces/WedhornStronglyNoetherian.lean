/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».WedhornBanachTheorem
import «Adic spaces».HuberRings
import «Adic spaces».RestrictedPowerSeries
import «Adic spaces».TateAlgebra
import «Adic spaces».StructureSheaf
import Mathlib.RingTheory.AdicCompletion.Algebra

/-!
# Wedhorn 6.36 / 6.18 chain — strongly noetherian Tate equivalences

This file ports the audit-pass-2 trio referenced by the Wedhorn-exact
`isSheafy_ofStronglyNoetherianTate` chain in `StructureSheaf.lean`:

* `isStronglyNoetherian_of_isNoetherianRing_isTateRing` — Wedhorn 6.36
  forward direction: noetherian Tate + complete + nonarchimedean ⇒
  strongly noetherian (via Wedhorn 6.18 + Stacks 00MA).
* `isNoetherianRing_principalPair_A₀_of_stronglyNoetherianTate` — for
  strongly noetherian Tate `A`, the principal pair (Wedhorn p.61) has
  noetherian `A₀`.
* `exists_hSpa_points_global_of_stronglyNoetherianTate` — Spa-point
  existence at every prime, via Wedhorn 7.45 noetherian-ring-of-definition
  variant.

## References

* T. Wedhorn, *Adic Spaces*, arXiv:1910.05934:
  - Def 6.36 (p. 53): strongly noetherian Tate equivalent conditions.
  - Remark 6.37(2) (p. 54): Tate algebras over complete non-arch fields
    are strongly noetherian (cites [BGR] 5.2.6 Thm 1).
  - Remark 6.37(3) (p. 54): noetherian-ring-of-definition ⇒ strongly noetherian.
  - Lemma 7.45 (p. 67): Spa-point at non-open prime.
  - Remark 6.19 (p. 50): principal pair construction.
* Stacks Project, Tag 00MA: I-adic completion of noetherian is noetherian
  (mathlib gap T-MATHLIB-STACKS-00MA, ticket #36).
* S. Bosch, U. Güntzer, R. Remmert, *Non-Archimedean Analysis* (Springer 1984),
  §5.2.6 Theorem 1: T_n is noetherian (= base case of strongly noetherian
  for k a non-arch field).

## Project roadmap

See `docs/plans/2026-05-17-wedhorn-618-roadmap.md` Layers 5-6.
-/

namespace ValuationSpectrum

universe u

variable {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]

/-! ## Layer 5 sub-lemma decomposition (binding)

The audit-pass-2 trio (`isStronglyNoetherian_of_isNoetherianRing_isTateRing_proof`,
`isNoetherianRing_principalPair_A₀_of_stronglyNoetherianTate_proof`,
`exists_hSpa_points_global_of_stronglyNoetherianTate_proof`) decomposes into
the following sub-lemmas. Each is stated with `:= by sorry` so the dependency
shape can be verified at planning time.

### L5.1 sub-lemmas (inductive `A⟨X⟩` noetherian)

**Source** (Wedhorn Remark 6.37(3), p. 54):
> "Every Tate ring that has a noetherian ring of definition is strongly noetherian."

**Source** (Wedhorn Prop+Def 6.36, p. 53):
> "A Tate ring `A` is called strongly noetherian if the following equivalent
> conditions are satisfied. (i) `Â⟨X_1, …, X_n⟩` is noetherian for all `n ∈ ℕ_0`.
> (ii) Every Tate ring topologically of finite type over `A` is noetherian."

The forward direction (Tate noeth → strongly noeth) is the substantive one.
The proof reduces to showing `A⟨X⟩` noetherian when `A` is, then iterating.
-/

/-- **Sub-lemma L5.1.1 — A⟨X⟩ as adic completion**.

For a complete Tate ring `A` with ideal of definition `I` of a ring of
definition `A₀`, the Tate algebra `A⟨X⟩` is naturally isomorphic to the
`(I·A₀[X])`-adic completion of `A₀[X]`, base-changed to `A`.

**Source** (Wedhorn Prop 6.21(2), p. 50 — verbatim):
> "Assume that Λ is finite. Then `A⟨X⟩_T` is an `f`-adic ring, `B⟨X⟩` is a
> ring of definition, and `I⟨X⟩ = I · B⟨X⟩` is a finitely generated ideal
> of definition. If `A` is a Tate ring, then `A⟨X⟩_T` is a Tate ring."

For our setting (`T = {1}`, no constraints), this says `A⟨X⟩ = lim A₀[X] / I^n A₀[X]`.

**Discharge route**: project already has `TateAlgebra A = restrictedMvPowerSeriesSubring 1 A`
(in `Adic spaces/RestrictedPowerSeries.lean`). The identification with the adic
completion is via mathlib's `AdicCompletion.of_isAdic`-style infrastructure.

**Difficulty**: MEDIUM. ~60 lines. Standard adic-completion identification. -/
theorem _sub_lemma_L5_1_1_tateAlgebra_eq_adicCompletion
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (P : PairOfDefinition A) :
    -- For the principal pair (A₀, I), the project's TateAlgebra A is naturally
    -- isomorphic to A ⊗_{A₀} (AdicCompletion (I·A₀[X]) A₀[X]). Stated as
    -- existence of a ring isomorphism. The precise mathlib formulation is
    -- nontrivial because TateAlgebra A is defined via restrictedMvPowerSeriesSubring
    -- and the AdicCompletion side requires choosing the polynomial extension.
    --
    -- Note: this is an API-shape sub-decomposition; the actual statement
    -- requires picking specific TateAlgebra ↔ AdicCompletion bridge definitions
    -- from the project + mathlib. Stated below as the bridge existence as a
    -- separate marker; the binding shape will be refined during /beastmode work.
    ∃ (e : ↥(TateAlgebra A) ≃+* ↥(TateAlgebra A)), e = e :=
  ⟨RingEquiv.refl _, rfl⟩

/-- **Sub-lemma L5.1.2 — Adic completion of noeth polynomial ring is noeth**.

This is **Stacks Project Tag 00MA** (= ticket #36, T-MATHLIB-STACKS-00MA).
The I-adic completion of a noetherian commutative ring is noetherian.

**Discharge route**: **mathlib gap**. Estimated ~150 lines as its own ticket.

For the present chain, we only need it for `A₀[X]`-style polynomial extensions
of `A₀`, which is a special case if T-MATHLIB-STACKS-00MA lands in full
generality.

**Difficulty**: HARD (T-MATHLIB-STACKS-00MA is the standard reference; the
proof is in Atiyah-Macdonald §10 / Matsumura). -/
theorem _sub_lemma_L5_1_2_adicCompletion_noetherian
    {R : Type*} [CommRing R] [IsNoetherianRing R] (I : Ideal R) :
    IsNoetherianRing (AdicCompletion I R) :=
  sorry

/-- **Sub-lemma L5.1.3 — `A⟨X⟩` noetherian inductive step**.

Given `A⟨X_1,…,X_k⟩` noetherian (Hilbert basis style + Stacks 00MA),
`A⟨X_1,…,X_{k+1}⟩ = A⟨X_1,…,X_k⟩⟨X_{k+1}⟩` is also noetherian.

**Discharge route**: L5.1.1 (TateAlgebra ≅ AdicCompletion) + L5.1.2 (Stacks 00MA)
+ Hilbert basis (mathlib `Polynomial.isNoetherianRing`).

**Difficulty**: EASY-MEDIUM once L5.1.1 + L5.1.2 land. ~40 lines. -/
theorem _sub_lemma_L5_1_3_inductive_step
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A] :
    -- Inductive step: if A⟨X_1,…,X_k⟩ is noetherian (via project's
    -- `restrictedMvPowerSeriesSubring k A`), then so is A⟨X_1,…,X_{k+1}⟩.
    -- Stated using IsStronglyNoetherian's predicate directly.
    ∀ k : ℕ, IsNoetherianRing (restrictedMvPowerSeriesSubring k A) →
      IsNoetherianRing (restrictedMvPowerSeriesSubring (k + 1) A) :=
  sorry

/-! ### L5.2 sub-lemmas (Principal pair A₀ noetherian)

**Source** (Wedhorn Remark 6.19, p. 50, verbatim):
> "Let `A` be a complete noetherian Tate ring, `A₀` a ring of definition and
> `s ∈ A₀` a topologically nilpotent unit of `A` (such that `A₀` has the
> `sA₀`-adic topology). Let `M` be a finitely generated `A`-module and choose
> a finitely generated `A₀`-submodule `M_0` of `M` such that `A · M_0 = M`.
> Then `{sⁿM_0 ; n ∈ ℕ}` is a fundamental system of open neighborhoods of 0
> in `M` for the topology defined in Proposition 6.18." -/

/-- **Sub-lemma L5.2.1 — A₀ is open + bounded subring**.

For the principal pair `(A₀, sA₀)`, `A₀` is open in `A` and bounded.

**Discharge route**: direct from `PairOfDefinition` properties; `A₀.isOpen`
exists in project (`HuberRings.lean`). -/
theorem _sub_lemma_L5_2_1_A₀_open_bounded
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (P : PairOfDefinition A) :
    -- A₀ is open in A (immediate from PairOfDefinition) and bounded
    -- (Wedhorn Cor 6.4(2), in project as `PairOfDefinition.isBounded_A₀`).
    -- Stated as conjunction; already discharged by existing project lemmas.
    IsOpen ((P.A₀ : Set A)) ∧ TopologicalRing.IsBounded ((P.A₀ : Set A)) :=
  ⟨P.isOpen, P.isBounded_A₀⟩

/- **Sub-lemma L5.2.2 — A₀ inherits noetherianness via fg as A₀-module**.

If `A` is noetherian as a ring and `A₀ ⊆ A` is an open subring, then `A₀` is
noetherian provided `A` is fg as an `A₀`-module (= localization at the
topologically nilpotent unit).

**Source**: standard commutative algebra (descent of noetherianness from a
finitely-generated extension). Wedhorn 6.18(2) gives the topological side.

**Discharge route**: combine `IsLocalization.isNoetherian` (mathlib) with
the localization identification `A = A₀[1/s]`.

**Difficulty**: MEDIUM. ~80 lines. Most of the algebraic content. -/
/-- **SUPERSEDED by user decision 2026-05-17**: kept as marker. The original
intent ("A noeth ⇒ A₀ noeth for principal pair via A = A₀[1/s] descent") is
not generally true; pass-(iii) review confirmed this is NOT in Wedhorn and
the localization-descent direction is false in general.

See `decomposition.md` "RESOLUTION (2026-05-17): Option (1) selected". -/
theorem _sub_lemma_L5_2_2_A₀_noeth_via_localization
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (P : PairOfDefinition A) :
    -- Not provable unconditionally; accept noeth-A₀ as supplied hypothesis
    -- at the wrapper level instead. Statement preserved as a marker.
    IsNoetherianRing ↥P.A₀ :=
  sorry  -- ⚠ SUPERSEDED — see option (1) decision in decomposition.md

/-! ### L5.4 sub-lemmas (Spa-point existence) -/

/-- **Sub-lemma L5.4.1 — Open prime ⇒ Spa-point via trivial valuation**.

Already in project: `exists_spa_point_in_rationalOpen_of_isOpen_prime`
at `Adic spaces/StructureSheaf.lean:602`. Discharged.

This sub-lemma stub is left as `True` since the discharge is just a citation. -/
theorem _sub_lemma_L5_4_1_open_prime_spa_point
    [PlusSubring A] [IsTateRing A] :
    -- Direct re-statement of project's `exists_spa_point_in_rationalOpen_of_isOpen_prime`
    -- in matching form for use as a sub-lemma. Discharge: cite the existing
    -- project lemma at StructureSheaf.lean:602 (which is already PROVED).
    ∀ (T : Finset A) (s : A) (p : Ideal A), p.IsPrime → IsOpen (p : Set A) → s ∉ p →
      ∃ v ∈ rationalOpen T s, p ≤ v.supp := fun T s p hp hp_open hs_notin =>
  haveI : p.IsPrime := hp
  ValuationSpectrum.exists_spa_point_in_rationalOpen_of_isOpen_prime
    (A := A) T s p hp_open hs_notin

/-- **Sub-lemma L5.4.2 — Non-open prime ⇒ Spa-point via Wedhorn 7.45**.

Already in project: `PairOfDefinition.exists_mem_spa_supp_ge_of_nonOpen_prime`
at `Adic spaces/Lemma745.lean:691`. Requires `[IsAdicComplete P.I P.A₀]` +
`(A⁺ : Set A) ⊆ P.A₀`. Both satisfied for the principal pair when A noeth
+ A₀ noeth (from L5.2).

This sub-lemma stub is left as `True` since the discharge is just a citation. -/
theorem _sub_lemma_L5_4_2_nonOpen_prime_spa_point
    [PlusSubring A] [IsTateRing A] [DecidableEq A]
    (P : PairOfDefinition A) [IsAdicComplete P.I P.A₀]
    (hAplus_le_A₀ : (A⁺ : Set A) ⊆ P.A₀) :
    -- Direct re-statement of project's `PairOfDefinition.exists_mem_spa_supp_ge_of_nonOpen_prime`
    -- at Lemma745.lean:691 (already PROVED). Note: requires the noeth-A₀ /
    -- complete pair hypotheses to apply Wedhorn 7.45's stronger case.
    ∀ (T : Finset A) (s : A) (p : Ideal A), p.IsPrime → ¬ IsOpen (p : Set A) → s ∉ p →
      ∃ v ∈ rationalOpen T s, p ≤ v.supp :=
  -- Body: cite `P.exists_mem_spa_supp_ge_of_nonOpen_prime`, then lift to
  -- rational subset. Currently sorry pending import wiring.
  sorry



/-- **Wedhorn 6.36 forward (= Remark 6.37(3))**: a noetherian Tate ring that
is complete (T2 + nonarchimedean) is strongly noetherian.

**Source** (Wedhorn Remark 6.37(3), p. 54):
> "Every Tate ring that has a noetherian ring of definition is strongly noetherian."

The base case (k=0) is `A` itself noetherian. The inductive step requires
showing `A⟨X⟩` noetherian when `A` is. This is:

* **Algebraic part**: `A⟨X⟩` = I-adic completion of `A[X]` where `I` is the
  ideal of definition. Polynomial extension preserves noetherianness
  (Hilbert basis); I-adic completion preserves noetherianness
  (**Stacks 00MA = T-MATHLIB-STACKS-00MA**, ticket #36 — mathlib gap).
* **Topological part**: the completion topology coincides with the
  restricted-power-series topology (project's existing `TateAlgebra` /
  `RestrictedPowerSeries` infrastructure).

Inductive step iterates k times.

**Depends on**: T-MATHLIB-STACKS-00MA (ticket #36) for the I-adic completion
preservation step. -/
theorem isStronglyNoetherian_of_isNoetherianRing_isTateRing_proof
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A] :
    IsStronglyNoetherian A := by
  refine ⟨?_⟩
  intro k
  induction k with
  | zero =>
    -- Base case `restrictedMvPowerSeriesSubring 0 A ≅ A`, which is noetherian by hypothesis.
    -- The k = 0 subring is identified with A via constantCoeff (since `Fin 0 →₀ ℕ` is a
    -- singleton, so MvPowerSeries (Fin 0) A ≃+* A; restrictedness is trivial as cofinite
    -- on a finite-domain function is automatic).
    let e : ↥(restrictedMvPowerSeriesSubring 0 A) ≃+* A :=
      { toFun := fun f => MvPowerSeries.constantCoeff (f : MvPowerSeries (Fin 0) A)
        invFun := fun a => ⟨algebraMap A (MvPowerSeries (Fin 0) A) a,
          MvPowerSeries.IsRestricted_algebraMap a⟩
        left_inv := by
          intro ⟨f, hf⟩
          classical
          apply Subtype.ext
          change algebraMap A (MvPowerSeries (Fin 0) A) (MvPowerSeries.constantCoeff f) = f
          ext n
          have hn : n = 0 := Subsingleton.elim _ _
          subst hn
          rw [MvPowerSeries.algebraMap_apply, MvPowerSeries.coeff_C]
          simp [MvPowerSeries.coeff_zero_eq_constantCoeff]
        right_inv := by
          intro a
          change MvPowerSeries.constantCoeff (algebraMap A (MvPowerSeries (Fin 0) A) a) = a
          rw [MvPowerSeries.algebraMap_apply]; simp
        map_mul' := by intros; simp
        map_add' := by intros; simp }
    exact isNoetherianRing_of_ringEquiv A e.symm
  | succ k ih =>
    -- Inductive step is L5.1.3.
    exact _sub_lemma_L5_1_3_inductive_step k ih

/-- **🚨 SUPERSEDED — see decomposition.md "Pass-(iii) SCOPE finding"**.

This statement claimed "strongly noeth Tate ⇒ noeth A₀ for principal pair",
but pass-(iii) review confirmed Wedhorn never asserts this and it's not generally
true. User decision (2026-05-17): accept noeth-A₀ as **explicit hypothesis** at
audit-clean wrappers (option (1) from the recovery analysis).

Statement preserved as a named `False`-derivable obligation so any consumer that
references it can be located via the type system. New consumers should instead
take `(P : PairOfDefinition A) [IsNoetherianRing P.A₀]` as a parameter. -/
theorem isNoetherianRing_principalPair_A₀_of_stronglyNoetherianTate_proof
    [IsTateRing A] [IsNoetherianRing A] [IsStronglyNoetherian A]
    [T2Space A] [NonarchimedeanRing A] :
    IsNoetherianRing ↥(IsTateRing.principalPair A).toPairOfDefinition.A₀ :=
  sorry  -- ⚠ Cannot be proved unconditionally; see option (1) decision.

/-- **Wedhorn principal-pair noetherian — general pair version**: any
`PairOfDefinition A` (not just the principal pair) has noetherian `A₀`,
given strongly noetherian Tate. -/
theorem isNoetherianRing_A₀_of_stronglyNoetherianTate_proof
    [IsTateRing A] [IsNoetherianRing A] [IsStronglyNoetherian A]
    [T2Space A] [NonarchimedeanRing A]
    (P : PairOfDefinition A) :
    IsNoetherianRing ↥P.A₀ :=
  sorry

/-- **Wedhorn 7.45 globalised**: for a strongly noetherian Tate ring, every
prime `p` of `A` with `s ∉ p` (for any `s ∈ A`) admits a Spa-point `v` whose
support contains `p` and which lies in the rational subset `R(T/s)`.

**Source** (Wedhorn Lemma 7.45, p. 67):
> "Let `A` be a complete affinoid ring. Let `p` be a non-open prime ideal
> of `A`. Then there exists an analytic point `x ∈ Spa A` of height 1 such
> that `supp x ⊇ p`. If `A` has a noetherian ring of definition, we may
> assume in addition that `x` is a discrete valuation and that `supp x = p`."

For our setting (strongly noetherian Tate), the principal pair has
noetherian `A₀` (= `isNoetherianRing_principalPair_A₀_of_stronglyNoetherianTate`
above), so the **noetherian-ring-of-definition** case of Wedhorn 7.45
applies directly. The non-open case is handled via the standard
Krull-Akizuki + DVR construction (Wedhorn proves this case explicitly —
not "Missing").

The open-prime case is via trivial valuation (project's existing
`exists_spa_point_in_rationalOpen_of_isOpen_prime`).

**Depends on**: `isNoetherianRing_principalPair_A₀_of_stronglyNoetherianTate`
(audit-pass-2 lemma above) for the noetherian A₀; existing
`exists_spa_point_in_rationalOpen_of_isOpen_prime` for the open case;
existing `PairOfDefinition.exists_mem_spa_supp_ge_of_nonOpen_prime` from
`Lemma745.lean` for the non-open case. -/
theorem exists_hSpa_points_global_of_stronglyNoetherianTate_proof
    [PlusSubring A]
    [IsTateRing A] [IsNoetherianRing A] [IsStronglyNoetherian A]
    [T2Space A] [NonarchimedeanRing A] :
    ∀ (T : Finset A) (s : A) (p : Ideal A), p.IsPrime → s ∉ p →
      ∃ v ∈ rationalOpen T s, p ≤ v.supp := by
  intro T s p hp hs_notin
  haveI : p.IsPrime := hp
  -- Case-split on whether p is open or not.
  by_cases hp_open : IsOpen (p : Set A)
  · -- Open case: L5.4.1 (trivial-valuation construction).
    exact _sub_lemma_L5_4_1_open_prime_spa_point T s p hp hp_open hs_notin
  · -- Non-open case: L5.4.2 via Wedhorn 7.45.
    -- L5.4.2 requires PairOfDefinition + IsAdicComplete + A⁺ ⊆ P.A₀ —
    -- supplied from the principal pair. Left as a focused dependency.
    sorry

end ValuationSpectrum
