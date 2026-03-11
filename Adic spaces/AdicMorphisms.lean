/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».AnalyticPoints
import «Adic spaces».AdicSpectrum

/-!
# Adic Morphisms

We prove Lemma 7.46 and develop the theory of adic morphisms,
following §7.5 and §8.4 of [Wedhorn, *Adic Spaces*].

## Main results

* `ValuationSpectrum.supp_comap` : `supp(comap φ v) = φ⁻¹(supp v)`.
* `ValuationSpectrum.nonAnalytic_comap_of_continuous` : Continuous maps preserve non-analytic
  points (Lemma 7.46(1), first part).

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn2019adic], §7.5, §8.4
-/

namespace ValuationSpectrum

variable {A B : Type*} [CommRing A] [CommRing B]
  [TopologicalSpace A] [TopologicalSpace B]

/-! ### Support and comap -/

omit [TopologicalSpace A] [TopologicalSpace B] in
/-- The support of `comap φ v` equals the preimage ideal `φ⁻¹(supp v)`.
This is the ideal-level consequence of `suppFun_comap`. -/
theorem supp_comap (φ : A →+* B) (v : Spv B) :
    (comap φ v).supp = Ideal.comap φ v.supp := by
  have h := congr_arg PrimeSpectrum.asIdeal (suppFun_comap φ v)
  simpa using h

omit [TopologicalSpace A] [TopologicalSpace B] in
/-- The support of `comap φ v` as a set equals `φ ⁻¹' (supp v : Set B)`. -/
theorem supp_comap_coe (φ : A →+* B) (v : Spv B) :
    ((comap φ v).supp : Set A) = φ ⁻¹' (v.supp : Set B) := by
  ext x; simp [supp_comap]

/-! ### Lemma 7.46(1): Non-analytic preservation -/

/-- **Lemma 7.46(1), first part.** Continuous ring homomorphisms preserve non-analytic
points: if `supp(v)` is open (i.e., `v` is non-analytic) and `φ` is continuous,
then `supp(comap φ v)` is open (i.e., `comap φ v` is non-analytic).

This is immediate: `supp(comap φ v) = φ⁻¹(supp v)` is open by continuity. -/
theorem nonAnalytic_comap_of_continuous {φ : A →+* B} (hφ : Continuous φ)
    {v : Spv B} (hv : ¬IsAnalytic v) : ¬IsAnalytic (comap φ v) := by
  simp only [IsAnalytic, not_not] at hv ⊢
  rw [supp_comap_coe]
  exact hφ.isOpen_preimage _ hv

/-! ### Lemma 7.46(1): Adic homomorphisms preserve analytic points -/

section AdicPreservesAnalytic

variable [IsTopologicalRing A] [IsTopologicalRing B]
  [IsLinearTopology A A] [IsHuberRing A] [IsHuberRing B]

omit [IsHuberRing B] in
/-- If a support ideal `supp(v)` contains the ideal of definition (as a subset of `B`),
then `supp(v)` is open. -/
private theorem supp_isOpen_of_idealOfDefinition_le
    (PB : PairOfDefinition B) (v : Spv B)
    (h : PB.idealOfDefinition ≤ v.supp) : IsOpen (v.supp : Set B) := by
  change IsOpen (v.supp.toAddSubgroup : Set B)
  exact AddSubgroup.isOpen_of_mem_nhds _
    (Filter.mem_of_superset
      ((PB.pow_image_isOpen 1).mem_nhds
        (Set.mem_image_of_mem _ (PB.I ^ 1).zero_mem))
      (by
        intro b hb
        rw [Submodule.coe_toAddSubgroup]
        obtain ⟨y, hy, rfl⟩ := hb
        exact h (Ideal.mem_map_of_mem _ (pow_one PB.I ▸ hy))))

omit [IsTopologicalRing A] [IsTopologicalRing B] [IsLinearTopology A A]
  [IsHuberRing A] [IsHuberRing B] in
/-- If the ideal of definition I of A maps into `supp(comap φ v)` (which equals `φ⁻¹(supp v)`),
and φ is adic with pairs (A₀,I) and (B₀,J), then `PB.idealOfDefinition ≤ supp v`. -/
private theorem idealOfDefinition_le_supp_of_adic
    (PA : PairOfDefinition A) (PB : PairOfDefinition B)
    (φ : A →+* B) (hAB : ∀ a ∈ PA.A₀, φ a ∈ PB.A₀)
    (hrad : (Ideal.map (PA.restrictRingHom PB φ hAB) PA.I).radical = PB.I.radical)
    (v : Spv B)
    (hI : PA.idealOfDefinition ≤ (comap φ v).supp) :
    PB.idealOfDefinition ≤ v.supp := by
  -- Step 1: PA.I maps into Ideal.comap PB.A₀.subtype (supp v) via φ_res
  have hI_comap : PA.I ≤ Ideal.comap PA.A₀.subtype (comap φ v).supp := by
    rwa [PairOfDefinition.idealOfDefinition, Ideal.map_le_iff_le_comap] at hI
  -- Step 2: φ_res maps PA.I into supp(v) ∩ B₀
  have hmap_le : Ideal.map (PA.restrictRingHom PB φ hAB) PA.I ≤
      Ideal.comap PB.A₀.subtype v.supp := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    have ha' : (PA.A₀.subtype a : A) ∈ (comap φ v).supp := hI_comap ha
    rw [supp_comap] at ha'
    exact ha'
  -- Step 3: radical containment via adic condition
  have hJ_le : PB.I ≤ Ideal.comap PB.A₀.subtype v.supp := by
    calc PB.I ≤ PB.I.radical := Ideal.le_radical
    _ = (Ideal.map (PA.restrictRingHom PB φ hAB) PA.I).radical := hrad.symm
    _ ≤ (Ideal.comap PB.A₀.subtype v.supp).radical := Ideal.radical_mono hmap_le
    _ = Ideal.comap PB.A₀.subtype v.supp :=
        (Ideal.IsPrime.comap PB.A₀.subtype).radical
  -- Step 4: idealOfDefinition ≤ supp v
  rwa [PairOfDefinition.idealOfDefinition, Ideal.map_le_iff_le_comap]

omit [IsTopologicalRing A] in
/-- **Lemma 7.46(1), second part.** If `φ : A →+* B` is adic, then `Spv(φ)` preserves
analytic points: if `v ∈ Spv B` is analytic, then `comap φ v` is analytic.

*Proof (contrapositive).* If `supp(comap φ v) = φ⁻¹(supp v)` is open, the topological
nilradical of `A` lies in it. Since the ideal of definition `I` consists of topologically
nilpotent elements, `I ⊆ φ⁻¹(supp v)`, so `φ(I) ⊆ supp v`. The adic condition
`rad(φ(I)·B₀) = rad(J)` then gives `J ⊆ supp v ∩ B₀`, making `supp v` open. -/
theorem analytic_comap_of_isAdicHom {φ : A →+* B}
    (hφ : IsAdicHom φ) {v : Spv B}
    (hv : IsAnalytic v) : IsAnalytic (comap φ v) := by
  -- By contrapositive: assume comap φ v is non-analytic
  intro hna
  apply hv; clear hv
  -- hna : IsOpen ↑(comap φ v).supp, goal : IsOpen ↑v.supp
  obtain ⟨PA, PB, hAB, hrad⟩ := hφ
  -- I_A ⊆ supp(comap φ v) because supp(comap φ v) is open and I_A is topologically nilpotent
  have hI_le : PA.idealOfDefinition ≤ (comap φ v).supp := by
    have h_nilrad := topologicalNilradical_le_radical_of_isOpen hna
    have h_id_le := PA.idealOfDefinition_le_topologicalNilradical
    calc PA.idealOfDefinition ≤ topologicalNilradical A := h_id_le
    _ ≤ ((comap φ v).supp).radical := h_nilrad
    _ = (comap φ v).supp := (instIsPrimeSupp _).radical
  -- From adic condition: J_B ⊆ supp v
  have hPB := idealOfDefinition_le_supp_of_adic PA PB φ hAB hrad v hI_le
  -- supp v is open since it contains the ideal of definition
  exact supp_isOpen_of_idealOfDefinition_le PB v hPB

end AdicPreservesAnalytic

/-! ### Tate ring specializations of Lemma 7.46

In a Tate ring, every Spa point is analytic (`IsTateRing.isAnalytic`). This simplifies
Lemma 7.46 considerably:
* (1) becomes: if `φ` is adic from a Tate ring, then all comap points are analytic
  (automatic from `analytic_comap_of_isAdicHom`).
* (2) becomes: Proposition 6.25 — every continuous ring hom from a Tate ring is adic.
  The converse direction (continuous ⟹ adic) means adic = continuous for Tate sources.
-/

section TateSpecialization

variable [IsTopologicalRing A] [IsTopologicalRing B]
  [IsLinearTopology A A] [IsHuberRing A] [IsHuberRing B]

omit [IsTopologicalRing A] in
/-- In a Tate source ring, adic homomorphisms produce analytic comap points for
every continuous valuation (not just analytic ones), since all points of a Tate
ring are analytic. -/
theorem analytic_comap_of_isAdicHom_tate [IsTateRing B]
    {φ : A →+* B} (hφ : IsAdicHom φ) (v : Spv B) :
    IsAnalytic (comap φ v) :=
  analytic_comap_of_isAdicHom hφ (IsTateRing.isAnalytic v)

end TateSpecialization

end ValuationSpectrum
