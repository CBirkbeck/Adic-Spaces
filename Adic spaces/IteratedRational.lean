/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».PresheafTateStructure
import «Adic spaces».TopologyComparison
import «Adic spaces».CompletionLocalization

/-!
# Iterated Rational Localization (Wedhorn Lemma 2.13): helpers

Helper lemmas about `canonicalMap` and `restrictionMapHom` that feed into the
iterated rational identification and the Laurent bridges. The Wedhorn
Example 6.38 machinery used to live here under the name `Example638`; that
block now lives in `«Adic spaces».Example638` (extracted to break the cycle
with `LaurentRefinement`).

## References
* [T. Wedhorn, *Adic Spaces*][wedhorn2019adic], Lemma 2.13, Prop 8.7.
-/

namespace ValuationSpectrum

open UniformSpace

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [PlusSubring A] [IsHuberRing A] [HasLocLiftPowerBounded A]

/-! ### Helpers -/

section Helpers

variable [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]

/-- `D₀.canonicalMap D₀.s` is a unit in `presheafValue D₀`, because `D₀.s`
becomes a unit under `algebraMap A (Localization.Away D₀.s)` (definition of
localization) and `D₀.coeRingHom` preserves units. -/
theorem canonicalMap_s_isUnit (D₀ : RationalLocData A) :
    IsUnit (D₀.canonicalMap D₀.s) := by
  unfold RationalLocData.canonicalMap
  simp only [RingHom.coe_comp, Function.comp_apply]
  exact RingHom.isUnit_map D₀.coeRingHom
    (IsLocalization.Away.algebraMap_isUnit D₀.s)

/-- Compatibility: `restrictionMapHom D₀ D' hsub ∘ D₀.canonicalMap = D'.canonicalMap`.
Follows directly from `UniformSpace.Completion.extensionHom_coe` + the
`IsLocalization.Away.lift_eq` identity for the underlying alg map. -/
theorem restrictionMapHom_canonicalMap (D₀ D' : RationalLocData A)
    (h : rationalOpen D'.T D'.s ⊆ rationalOpen D₀.T D₀.s) (a : A) :
    restrictionMapHom D₀ D' h (D₀.canonicalMap a) = D'.canonicalMap a := by
  letI := D₀.uniformSpace
  letI := D₀.isTopologicalRing
  letI := D₀.isUniformAddGroup
  letI := D'.uniformSpace
  letI := D'.isTopologicalRing
  letI := D'.isUniformAddGroup
  change restrictionMapHom D₀ D' h
      (D₀.coeRingHom (algebraMap A (Localization.Away D₀.s) a)) =
      D'.coeRingHom (algebraMap A (Localization.Away D'.s) a)
  -- `D₀.coeRingHom = UniformSpace.Completion.coeRingHom` and `restrictionMapHom = extensionHom`.
  -- Apply `extensionHom_coe` to collapse `extensionHom f (coeRingHom x)` to `f x`.
  -- Then `restrictionMapAlg = IsLocalization.Away.lift D₀.s witness` with witness
  -- for the ring hom `D'.canonicalMap`; `IsLocalization.Away.lift_eq` finishes.
  have h_ext :
      restrictionMapHom D₀ D' h
        (D₀.coeRingHom (algebraMap A (Localization.Away D₀.s) a)) =
      restrictionMapAlg D₀ D' h (algebraMap A (Localization.Away D₀.s) a) :=
    UniformSpace.Completion.extensionHom_coe (restrictionMapAlg D₀ D' h)
      (restrictionMapAlg_continuous D₀ D' h)
      (algebraMap A (Localization.Away D₀.s) a)
  rw [h_ext, restrictionMapAlg, IsLocalization.Away.lift_eq]
  rfl

end Helpers

/-! ## Hidden-obligation audit pass 3 (2026-05-17): Wedhorn 7.55 reduction

Item 4 from the audit. Wedhorn Prop 8.30 (page 81) reduces to Lemma
8.31(1)/(2) via:
1. Example 6.38: WLOG U = Spa A (the bigger rational is again strong-noeth Tate);
2. Remark 7.55: any rational `V = R(T/s) ⊆ Spa A` admits a description
   `O_X(V) ≅ A⟨X_1, …, X_n⟩ / (s·X_1 - t_1, …, s·X_n - t_n)` where `T = {t_1, …, t_n}`;
3. Each generator `(s·X_i - t_i)` is the "Laurent pair" form, flat by 8.31(2).

The intermediate step is the explicit ring isomorphism that's the missing
audit lemma. -/

section AuditPass3

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [PlusSubring A] [IsHuberRing A] [IsTateRing A] [IsNoetherianRing A]
  [T2Space A] [NonarchimedeanRing A]

/-- **(Wedhorn Remark 7.55, clean ring-iso form — STATEMENT BUG, 2026-05-18)**

⚠ **B2 (b2_log entry 6, 2026-05-18):** the Lean statement below uses
`MvPolynomial D.T A` (algebraic polynomial ring) which gives quotient
`A[X_t]/(s·X_t = t) ≅ A[1/s]` — the *algebraic* localization, no topology.
But `presheafValue D = Completion(Localization.Away D.s)` in the
localization topology. The two coincide only when `A[1/s]` is already
complete (e.g., `A` discrete). Counterexample: `A = ℤ` with `p`-adic
topology, `D.s = p`, `D.T = ∅`. RHS = `MvPolynomial ∅ ℤ ≅ ℤ`. LHS =
`Completion(ℤ[1/p]) = ℚ_p ≠ ℤ`.

The intended statement (per docstring `A⟨X⟩` notation) uses the **Tate
algebra** in `|D.T|` variables (project's `restrictedMvPowerSeriesSubring`),
not `MvPolynomial`. With Tate algebra, the equivalence is Wedhorn 7.55
exactly. Fix: replace `MvPolynomial` with `restrictedMvPowerSeriesSubring`
(or equivalent Tate-algebra encoding) and quotient by the same ideal.

Discharge plan (for the *corrected* statement using `A⟨X⟩`): induction on
`n`. The base case `n = 0` is `R(∅/s) = R(s) = Spa(A[1/s])` and
`presheafValue ≃+* completion of A[1/s]` already exists in the project
(`PresheafIdentification.lean`). The inductive step adjoins one more
variable via the "Wedhorn 7.55" `Localization.Away` identification
applied to `A → A⟨X_1⟩/(s·X_1 - t_1)`.

**Note**: stated for arbitrary finset; the package shape returns the
ring iso bundled with a `HasLocLiftPowerBounded`-style continuity assertion
(omitted here for brevity; project's `presheafValue` API handles it). -/
theorem presheafValue_eq_quotient_AlangleX_iterated
    (D : RationalLocData A) :
    Nonempty (presheafValue D ≃+*
      MvPolynomial D.T A ⧸ Ideal.span
        (Set.range (fun t : D.T =>
          MvPolynomial.X (R := A) t * MvPolynomial.C D.s
            - MvPolynomial.C (t : A)))) :=
  sorry

end AuditPass3

end ValuationSpectrum
