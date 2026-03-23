/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.RingTheory.MvPowerSeries.PiTopology
import «Adic spaces».TateAlgebra
import «Adic spaces».HuberRings

/-!
# Topology on the Tate Algebra A⟨X⟩

The Tate algebra `A⟨X⟩` inherits the **product topology** from `MvPowerSeries (Fin 1) A`,
where we view power series as functions `(Fin 1 →₀ ℕ) → A` and equip the codomain with
the topology of `A`. The subring `TateAlgebra A ⊂ MvPowerSeries (Fin 1) A` gets the
induced (subspace) topology.

This topology makes `A⟨X⟩` a topological ring (via `Subring.instIsTopologicalRing`)
and is the topology of coefficient-wise convergence: a net of restricted power series
converges iff each coefficient converges in `A`.

## I-adic topology and Huber ring structure

Given a pair of definition `(A₀, I)` for `A`, we construct:

* `TateAlgebra.pairSubring P` : The subring `A₀⟨X⟩ ⊆ A⟨X⟩` of restricted power series
  with coefficients in `A₀`.
* `TateAlgebra.pairConstantHom P` : The constant series embedding `A₀ →+* A₀⟨X⟩`.
* `TateAlgebra.pairIdeal P` : The ideal `I · A₀⟨X⟩` inside `A₀⟨X⟩`.
* `TateAlgebra.pairIdeal_fg P` : Finite generation of `I · A₀⟨X⟩`.
* `TateAlgebra.pairSubring_isHuberRing P` : `A₀⟨X⟩` with the `(I · A₀⟨X⟩)`-adic
  topology is a Huber ring.

The Huber ring structure on `A₀⟨X⟩` uses the pair `(⊤, idealToTop (pairIdeal P))`
where the ring of definition is the whole ring `A₀⟨X⟩` itself, equipped with the
`(pairIdeal P)`-adic topology.

## General results

* `idealToTop I` : Transfer an ideal from `R` to `↥(⊤ : Subring R)`.
* `isAdic_idealToTop I` : The subspace topology on `↥⊤` from the `I`-adic topology
  on `R` is `(idealToTop I)`-adic.
* `pairOfDefinition_ofAdic I hI` : Any ring with finitely generated `I`-adic topology
  admits a pair of definition `(⊤, idealToTop I)`.
* `isHuberRing_ofAdic I hI` : A ring with finitely generated `I`-adic topology is Huber.

## Main results (product topology)

* `TateAlgebra.continuous_coeff` : Each coefficient function `coeff n` is continuous.
* `TateAlgebra.continuous_evalZeroHom` : The evaluation-at-zero map is continuous.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn2019adic], §6, §8
-/

open MvPowerSeries.WithPiTopology Filter Topology

namespace TateAlgebra

variable {A : Type*} [CommRing A] [TopologicalSpace A] [NonarchimedeanRing A]

/-! ### Topology instances -/

/-- The topology on `A⟨X⟩` is the subspace topology from `MvPowerSeries (Fin 1) A`
with the product topology. This makes coefficient extraction continuous. -/
example : TopologicalSpace ↥(TateAlgebra A) := inferInstance

/-- `A⟨X⟩` is a topological ring with the subspace topology. -/
example : IsTopologicalRing ↥(TateAlgebra A) := inferInstance

/-! ### Continuity of coefficient extraction -/

/-- The `n`-th coefficient function `coeff n : A⟨X⟩ → A` is continuous
(it's the composition of the continuous embedding into `MvPowerSeries` and
the continuous coefficient projection). -/
theorem continuous_coeff (n : ℕ) :
    Continuous (fun f : ↥(TateAlgebra A) => coeff n f) := by
  apply Continuous.comp
  · exact MvPowerSeries.WithPiTopology.continuous_coeff A (toIndex n)
  · exact continuous_subtype_val

/-- `evalZeroHom` is continuous (it extracts the 0-th coefficient). -/
theorem continuous_evalZeroHom :
    Continuous (evalZeroHom : ↥(TateAlgebra A) → A) := by
  exact continuous_coeff 0

end TateAlgebra

/-! ### Transfer ideals to ↥⊤ and adic pair of definition

These results show that any commutative ring equipped with a finitely generated
`I`-adic topology admits a canonical pair of definition `(⊤, idealToTop I)`,
making it a Huber ring. This is used to construct the Huber ring structure
on `A₀⟨X⟩`.
-/

section IdealTopTransfer

variable {R : Type*} [CommRing R] (I : Ideal R)

/-- Transfer an ideal `I` of `R` to an ideal of `↥(⊤ : Subring R)` via the
inverse of `Subring.topEquiv`. This allows us to work with `PairOfDefinition`,
which requires an ideal of a subring. -/
noncomputable def idealToTop : Ideal ↥(⊤ : Subring R) :=
  I.map (Subring.topEquiv (R := R)).symm.toRingHom

/-- Powers of the transferred ideal equal preimages of the original
powers under `Subtype.val`. -/
theorem idealToTop_pow_eq_preimage (n : ℕ) :
    ((idealToTop I ^ n : Ideal ↥(⊤ : Subring R)) :
      Set ↥(⊤ : Subring R)) =
    Subtype.val ⁻¹' ((I ^ n : Ideal R) : Set R) := by
  unfold idealToTop
  rw [← Ideal.map_pow,
    show (I ^ n).map (Subring.topEquiv (R := R)).symm.toRingHom =
      (I ^ n).map (Subring.topEquiv (R := R)).symm from rfl,
    ← Ideal.comap_symm]
  ext x
  simp only [RingEquiv.symm_symm, Ideal.mem_comap,
    SetLike.mem_coe, Set.mem_preimage]
  rfl

/-- The transferred ideal is finitely generated when the original is. -/
theorem idealToTop_fg (hI : I.FG) : (idealToTop I).FG :=
  hI.map _

/-- When `R` carries the `I`-adic topology, the subspace topology on
`↥(⊤ : Subring R)` is `(idealToTop I)`-adic. This is the key topological
result: the subspace topology on the whole ring (viewed as ↥⊤) correctly
inherits the adic structure. -/
theorem isAdic_idealToTop :
    @IsAdic ↥(⊤ : Subring R) _
      (@instTopologicalSpaceSubtype R (· ∈ (⊤ : Subring R))
        I.adicTopology)
      (idealToTop I) := by
  letI : TopologicalSpace R := I.adicTopology
  letI : IsTopologicalRing R :=
    I.ringFilterBasis.isTopologicalRing
  have hadic : @IsAdic R _ I.adicTopology I := rfl
  rw [@isAdic_iff _ _ _
    (Subring.instIsTopologicalRing (⊤ : Subring R))]
  exact ⟨fun n => by
      rw [idealToTop_pow_eq_preimage I n]
      exact (isAdic_iff.mp hadic).1 n |>.preimage
        continuous_subtype_val,
    fun s hs => by
      rw [nhds_subtype_eq_comap] at hs
      obtain ⟨U, hU, hsU⟩ := Filter.mem_comap.mp hs
      rw [show (0 : ↥(⊤ : Subring R)).val = (0 : R)
        from rfl] at hU
      obtain ⟨n, -, hn⟩ :=
        hadic.hasBasis_nhds_zero.mem_iff.mp hU
      exact ⟨n, (idealToTop_pow_eq_preimage I n ▸
        Set.preimage_mono hn).trans hsU⟩⟩

/-- For a ring `R` with the `I`-adic topology (where `I` is finitely generated),
the pair `(⊤, idealToTop I)` is a pair of definition. -/
noncomputable def pairOfDefinition_ofAdic (hI : I.FG) :
    @PairOfDefinition R _ I.adicTopology := by
  letI : TopologicalSpace R := I.adicTopology
  exact
    { A₀ := ⊤
      I := idealToTop I
      isOpen := isOpen_univ
      fg := idealToTop_fg I hI
      isAdic := isAdic_idealToTop I }

/-- A ring with a finitely generated `I`-adic topology is a Huber ring.
The pair of definition is `(⊤, idealToTop I)`. -/
theorem isHuberRing_ofAdic (hI : I.FG) :
    @IsHuberRing R _ I.adicTopology := by
  letI : TopologicalSpace R := I.adicTopology
  exact ⟨⟨pairOfDefinition_ofAdic I hI⟩⟩

end IdealTopTransfer

/-! ### Ring of definition and ideal for A₀⟨X⟩

Given a pair of definition `(A₀, I)` for a nonarchimedean topological ring `A`,
we construct the algebraic data needed for the Huber ring structure on `A₀⟨X⟩`:
the subring of restricted power series with coefficients in `A₀`, the ideal
generated by constant series from `I`, and finite generation.
-/

namespace TateAlgebra

variable {A : Type*} [CommRing A] [TopologicalSpace A]
  [NonarchimedeanRing A] [IsTopologicalRing A]

/-- The subring of `A⟨X⟩` consisting of restricted power series whose
coefficients all lie in `P.A₀`. This is the "ring of definition"
`A₀⟨X⟩` for the Tate algebra (Wedhorn, §8). -/
noncomputable def pairSubring (P : PairOfDefinition A) :
    Subring ↥(TateAlgebra A) where
  carrier := {f | ∀ s : Fin 1 →₀ ℕ,
    MvPowerSeries.coeff s f.val ∈ P.A₀}
  mul_mem' {f g} hf hg s := by
    simp only [Subring.coe_mul, MvPowerSeries.coeff_mul]
    exact P.A₀.toSubsemiring.sum_mem
      fun p _ => P.A₀.mul_mem (hf p.1) (hg p.2)
  one_mem' s := by
    simp only [OneMemClass.coe_one, MvPowerSeries.coeff_one]
    split
    · exact P.A₀.one_mem
    · exact P.A₀.zero_mem
  add_mem' {f g} hf hg s := by
    simp only [Subring.coe_add, map_add]
    exact P.A₀.add_mem (hf s) (hg s)
  zero_mem' s := by
    simp only [ZeroMemClass.coe_zero, map_zero]
    exact P.A₀.zero_mem
  neg_mem' {f} hf s := by
    simp only [NegMemClass.coe_neg, map_neg]
    exact P.A₀.neg_mem (hf s)

omit [IsTopologicalRing A] in
/-- Membership in `pairSubring P` means all coefficients lie in `P.A₀`. -/
theorem mem_pairSubring (P : PairOfDefinition A)
    (f : ↥(TateAlgebra A)) :
    f ∈ pairSubring P ↔
      ∀ s, MvPowerSeries.coeff s f.val ∈ P.A₀ :=
  Iff.rfl

/-- The constant power series embedding `P.A₀ →+* A₀⟨X⟩`.
Sends `a ∈ A₀` to the constant restricted power series `C(a)`. -/
noncomputable def pairConstantHom (P : PairOfDefinition A) :
    P.A₀ →+* pairSubring P where
  toFun a := ⟨⟨MvPowerSeries.C a.val,
      MvPowerSeries.IsRestricted_algebraMap a.val⟩, by
    intro s; classical
    simp only [MvPowerSeries.coeff_C]
    split
    · exact a.2
    · exact P.A₀.zero_mem⟩
  map_one' := Subtype.ext (Subtype.ext (map_one _))
  map_mul' x y :=
    Subtype.ext (Subtype.ext (by
      simp [Subring.coe_mul, map_mul]))
  map_zero' := Subtype.ext (Subtype.ext (map_zero _))
  map_add' x y :=
    Subtype.ext (Subtype.ext (by
      simp [Subring.coe_add, map_add]))

/-- The ideal `I · A₀⟨X⟩` inside `A₀⟨X⟩`, defined as the image of `P.I`
under the constant power series embedding. This is the ideal of
definition for `A₀⟨X⟩` (Wedhorn, §8). -/
noncomputable def pairIdeal (P : PairOfDefinition A) :
    Ideal (pairSubring P) :=
  Ideal.map (pairConstantHom P) P.I

omit [IsTopologicalRing A] in
/-- The ideal `I · A₀⟨X⟩` is finitely generated (because `I` is). -/
theorem pairIdeal_fg (P : PairOfDefinition A) :
    (pairIdeal P).FG :=
  P.fg.map _

/-! ### Huber ring structure on A₀⟨X⟩ -/

omit [IsTopologicalRing A] in
/-- The ring `A₀⟨X⟩ = pairSubring P`, equipped with the
`(I · A₀⟨X⟩)`-adic topology, is a Huber ring. The pair of definition
is `(⊤, idealToTop (pairIdeal P))`, i.e., the whole ring `A₀⟨X⟩` serves
as its own ring of definition with the ideal `I · A₀⟨X⟩` (Wedhorn, §8). -/
theorem pairSubring_isHuberRing (P : PairOfDefinition A) :
    @IsHuberRing ↥(pairSubring P) _
      (pairIdeal P).adicTopology :=
  isHuberRing_ofAdic _ (pairIdeal_fg P)

omit [IsTopologicalRing A] in
/-- The `(pairIdeal P)`-adic topology on `A₀⟨X⟩` is a ring topology. -/
theorem pairSubring_isTopologicalRing
    (P : PairOfDefinition A) :
    @IsTopologicalRing ↥(pairSubring P)
      (pairIdeal P).adicTopology _ :=
  (pairIdeal P).ringFilterBasis.isTopologicalRing

omit [IsTopologicalRing A] in
/-- The `(pairIdeal P)`-adic topology on `A₀⟨X⟩` is nonarchimedean. -/
theorem pairSubring_nonarchimedean
    (P : PairOfDefinition A) :
    @NonarchimedeanRing ↥(pairSubring P) _
      (pairIdeal P).adicTopology :=
  Ideal.nonarchimedean (pairIdeal P)

omit [IsTopologicalRing A] in
/-- The `pairIdeal P` is `I`-adic on `A₀⟨X⟩` by construction. -/
theorem pairIdeal_isAdic (P : PairOfDefinition A) :
    @IsAdic ↥(pairSubring P) _
      (pairIdeal P).adicTopology (pairIdeal P) :=
  rfl

end TateAlgebra
