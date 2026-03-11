/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.RingTheory.AdicCompletion.Basic
import «Adic spaces».HuberRings
import «Adic spaces».OpenIdeals

/-!
# Analytic Points of the Adic Spectrum

We define *analytic points* of the valuation spectrum and prove that every point
of `Spa(A, A⁺)` is analytic when `A` is a Tate ring.

## Main definitions

* `ValuationSpectrum.IsAnalytic v` : A point `v : Spv A` is *analytic* if its support
  `supp(v)` is not an open ideal of `A` (Definition 8.35 of Wedhorn).

## Main results

* `IsTateRing.isAnalytic` : If `A` is a Tate ring, then every `v : Spv A` is analytic
  (Proposition 8.36 of Wedhorn).

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn2019adic], Definition 8.35, Proposition 8.36
-/

namespace ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A]

/-- A point `v : Spv A` is *analytic* if its support `supp(v)` is not an open ideal
(Definition 8.35 of Wedhorn). -/
def IsAnalytic (v : Spv A) : Prop :=
  ¬IsOpen (v.supp : Set A)

/-- **Proposition 8.36 of Wedhorn.** If `A` is a Tate ring, then every point of `Spv A`
is analytic: the support ideal is never open.

*Proof.* Let `u` be a topologically nilpotent unit (from `IsTateRing`). Since `u` is a
unit, `u ∉ supp(v)`. If `supp(v)` were open, then since `u` is topologically nilpotent,
`u ∈ supp(v).radical = supp(v)` (the radical equals itself because `supp(v)` is prime),
contradicting `u ∉ supp(v)`. -/
theorem IsTateRing.isAnalytic [IsTateRing A] (v : Spv A) : IsAnalytic v := by
  obtain ⟨u, hu_nil⟩ := ‹IsTateRing A›.exists_topologicallyNilpotent_unit
  intro h_open
  exact (v.mem_supp_iff _).not.mpr (not_vle_zero_of_isUnit u.isUnit v)
    ((instIsPrimeSupp v).radical ▸ hu_nil.mem_ideal_radical h_open)

end ValuationSpectrum

/-! ### Non-open primes and the ideal of definition -/

namespace PairOfDefinition

variable {A : Type*} [CommRing A] [TopologicalSpace A]
  [IsTopologicalRing A] [IsLinearTopology A A]

/-- In a Huber ring with linear topology, if a prime ideal `𝔭` contains the ideal
of definition, then `𝔭` is open. The ideal of definition generates the topological
nilradical (up to radical), so `𝔭 ⊇ topologicalNilradical A`, and the backward
direction of Lemma 6.6 gives openness. -/
theorem isOpen_of_idealOfDefinition_le
    (P : PairOfDefinition A) {𝔭 : Ideal A} [𝔭.IsPrime]
    (h : P.idealOfDefinition ≤ 𝔭) : IsOpen (𝔭 : Set A) :=
  ideal_isOpen_of_topologicalNilradical_le_radical
    P.exists_fg_le_topologicalNilradical
    (P.topologicalNilradical_le_idealOfDefinition_radical.trans (Ideal.radical_mono h))

/-- Contrapositive: in a Huber ring, a non-open prime does not contain the ideal of
definition. This is the key fact for Lemma 7.45 (Wedhorn). -/
theorem idealOfDefinition_not_le_of_not_isOpen
    (P : PairOfDefinition A) {𝔭 : Ideal A} [𝔭.IsPrime]
    (h : ¬IsOpen (𝔭 : Set A)) : ¬P.idealOfDefinition ≤ 𝔭 :=
  fun hle => h (P.isOpen_of_idealOfDefinition_le hle)

/-- A non-open prime ideal does not contain the ideal of definition `I` (as ideal of `A₀`):
there exists an element of `I` that maps outside `𝔭`. -/
theorem exists_mem_I_not_mem_of_not_isOpen
    (P : PairOfDefinition A) {𝔭 : Ideal A} [𝔭.IsPrime]
    (h : ¬IsOpen (𝔭 : Set A)) : ∃ a ∈ P.I, (P.A₀.subtype a : A) ∉ 𝔭 := by
  by_contra h_all
  push_neg at h_all
  exact P.idealOfDefinition_not_le_of_not_isOpen h
    (Ideal.map_le_iff_le_comap.mpr fun a ha => h_all a ha)

/-! ### Jacobson radical and I-adic completeness

When the ring of definition `A₀` is `I`-adically complete, every element of `I`
lies in the Jacobson radical of `A₀`, i.e., in every maximal ideal of `A₀`.
This is the algebraic heart of Lemma 7.45 (Wedhorn): it connects the ideal of
definition to the domination properties of valuation rings. -/

omit [IsTopologicalRing A] [IsLinearTopology A A] in
/-- If `A₀` is `I`-adically complete, then `I` is in every maximal ideal of `A₀`.
This follows from `IsAdicComplete.le_jacobson_bot` which gives `I ≤ Jac(A₀)`. -/
theorem I_le_maximal_of_isAdicComplete
    (P : PairOfDefinition A) [IsAdicComplete P.I P.A₀]
    {𝔪 : Ideal P.A₀} (h𝔪 : 𝔪.IsMaximal) : P.I ≤ 𝔪 :=
  (IsAdicComplete.le_jacobson_bot (I := P.I)).trans (sInf_le ⟨bot_le, h𝔪⟩)

omit [IsTopologicalRing A] [IsLinearTopology A A] in
/-- If `A₀` is `I`-adically complete and `𝔭₀` is a prime of `A₀` with `I ⊄ 𝔭₀`,
then `𝔭₀` is not maximal. This is because `I ⊆ 𝔪` for all maximal `𝔪`. -/
theorem not_isMaximal_of_I_not_le
    (P : PairOfDefinition A) [IsAdicComplete P.I P.A₀]
    {𝔭₀ : Ideal P.A₀} (h : ¬P.I ≤ 𝔭₀) : ¬𝔭₀.IsMaximal :=
  fun h𝔪 => h (P.I_le_maximal_of_isAdicComplete h𝔪)

end PairOfDefinition
