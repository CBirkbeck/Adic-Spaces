/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Topology.Sets.Opens
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.GroupWithZero.Action
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Ring

/-!
# Čech Cohomology for Finite Covers

We define the Čech complex for finite open covers and prove `d ∘ d = 0`,
define acyclicity of the augmented complex, cover refinements with
induced cochain maps, cover restriction, product covers, and the
degree-zero acyclicity condition (separation + gluing).

## Main definitions

* `FiniteCover`: A finite open cover of a topological space.
* `FiniteCover.inter`: Multi-intersection `U_{σ(0)} ∩ ⋯ ∩ U_{σ(q)}`.
* `CechCochain`: The `q`-cochains `Č^q(U, F)`.
* `cechDiff`: The differential `d^q : Č^q → Č^{q+1}`.
* `cechAug`: The augmentation `ε : F(X) → Č^0(U, F)`.
* `IsSeparating`: The augmentation is injective.
* `HasGluing`: Compatible 0-cochains glue to a global section.
* `IsAcyclic`: The augmented Čech complex is exact at every degree.
* `Refinement`: A refinement of one cover by another.
* `Refinement.cochainMap`: Induced cochain map from a refinement.
* `FiniteCover.restrict`: Restriction of a cover to an open subset.
* `FiniteCover.prod`: Product of two covers.
* `IsDegreeZeroAcyclic`: Separation + gluing (sheaf condition).

## Main results

* `cechDiff_comp_cechDiff`: `d^{q+1} ∘ d^q = 0`.
* `cechDiff_comp_cechAug`: `d^0 ∘ ε = 0`.
* `Refinement.cochainMap_comm_diff`: The cochain map commutes with `d`.
* `single_isSeparating_and_hasGluing`: Single-set cover is degree-zero acyclic.
* `FiniteCover.prod_inter_eq`: Multi-intersections of product covers decompose.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn2019adic], Appendix A
-/

universe u v

/-! ### Finite covers -/

/-- A finite open cover of `X` indexed by `ι`. -/
structure FiniteCover (X : Type u) [TopologicalSpace X] (ι : Type v) [Fintype ι] where
  /-- The open sets forming the cover. -/
  sets : ι → Set X
  /-- Each set is open. -/
  isOpen : ∀ i, IsOpen (sets i)
  /-- The sets cover `X`. -/
  isCover : ⋃ i, sets i = Set.univ

namespace FiniteCover

variable {X : Type u} [TopologicalSpace X] {ι : Type v} [Fintype ι]

/-- Multi-intersection `U_{σ(0)} ∩ ⋯ ∩ U_{σ(q)}`. -/
def inter (U : FiniteCover X ι) {q : ℕ} (σ : Fin (q + 1) → ι) : Set X :=
  ⋂ k, U.sets (σ k)

/-- Multi-intersections are open. -/
theorem inter_isOpen (U : FiniteCover X ι) {q : ℕ}
    (σ : Fin (q + 1) → ι) : IsOpen (U.inter σ) :=
  isOpen_iInter_of_finite fun k => U.isOpen (σ k)

/-- Multi-intersection is contained in each component. -/
theorem inter_subset_sets (U : FiniteCover X ι) {q : ℕ}
    (σ : Fin (q + 1) → ι) (k : Fin (q + 1)) : U.inter σ ⊆ U.sets (σ k) :=
  Set.iInter_subset _ k

/-- Face map: remove the `j`-th index from `σ : Fin (q+2) → ι`. -/
def face {q : ℕ} (j : Fin (q + 2)) (σ : Fin (q + 2) → ι) : Fin (q + 1) → ι :=
  σ ∘ j.succAbove

/-- Multi-intersection of `σ` refines multi-intersection of `face j σ`. -/
theorem inter_face_subset (U : FiniteCover X ι) {q : ℕ} (j : Fin (q + 2))
    (σ : Fin (q + 2) → ι) : U.inter σ ⊆ U.inter (face j σ) :=
  Set.iInter_mono' fun k => ⟨j.succAbove k, le_refl _⟩

/-- Multi-intersection is contained in `Set.univ`. -/
theorem inter_subset_univ (U : FiniteCover X ι) {q : ℕ}
    (σ : Fin (q + 1) → ι) : U.inter σ ⊆ Set.univ :=
  Set.subset_univ _

end FiniteCover

/-! ### Presheaves of abelian groups -/

/-- A presheaf of additive abelian groups on subsets of `X`, with restriction maps. -/
structure AbPresheaf (X : Type u) where
  /-- The value on a subset. -/
  obj : Set X → Type u
  /-- Restriction maps. -/
  res : ∀ {U V : Set X}, V ⊆ U → obj U → obj V
  /-- Each value is an additive commutative group. -/
  instAddCommGroup : ∀ (U : Set X), AddCommGroup (obj U)
  /-- Restriction preserves zero. -/
  res_zero : ∀ {U V : Set X} (h : V ⊆ U),
    res h (instAddCommGroup U).toZero.zero = (instAddCommGroup V).toZero.zero
  /-- Restriction preserves addition. -/
  res_add : ∀ {U V : Set X} (h : V ⊆ U) (x y : obj U),
    res h ((instAddCommGroup U).toAdd.add x y) =
    (instAddCommGroup V).toAdd.add (res h x) (res h y)
  /-- Restriction preserves negation. -/
  res_neg : ∀ {U V : Set X} (h : V ⊆ U) (x : obj U),
    res h ((instAddCommGroup U).toNeg.neg x) = (instAddCommGroup V).toNeg.neg (res h x)
  /-- Restriction is functorial: identity. -/
  res_id : ∀ {U : Set X} (x : obj U), res (Set.Subset.refl U) x = x
  /-- Restriction is functorial: composition. -/
  res_comp : ∀ {U V W : Set X} (hWV : W ⊆ V) (hVU : V ⊆ U) (x : obj U),
    res hWV (res hVU x) = res (hWV.trans hVU) x

attribute [instance] AbPresheaf.instAddCommGroup

namespace AbPresheaf

variable {X : Type u}

/-- Restriction as an `AddMonoidHom`. -/
def resHom (F : AbPresheaf X) {U V : Set X} (h : V ⊆ U) : F.obj U →+ F.obj V where
  toFun := F.res h
  map_zero' := F.res_zero h
  map_add' := F.res_add h

/-- Restriction commutes with finite sums. -/
theorem res_sum (F : AbPresheaf X) {U V : Set X} (h : V ⊆ U)
    {α : Type*} (s : Finset α) (g : α → F.obj U) :
    F.res h (∑ x ∈ s, g x) = ∑ x ∈ s, F.res h (g x) :=
  map_sum (F.resHom h) g s

/-- Restriction preserves integer scalar multiplication. -/
theorem res_zsmul (F : AbPresheaf X) {U V : Set X} (h : V ⊆ U) (n : ℤ) (x : F.obj U) :
    F.res h (n • x) = n • F.res h x :=
  map_zsmul (F.resHom h) n x

/-- Restriction of a dependent section at equal arguments gives equal results. -/
theorem res_section_eq (F : AbPresheaf X) {α : Type*} {P : α → Set X} {W : Set X}
    (f : ∀ σ, F.obj (P σ)) {σ₁ σ₂ : α} (h₁ : W ⊆ P σ₁) (h₂ : W ⊆ P σ₂)
    (heq : σ₁ = σ₂) : F.res h₁ (f σ₁) = F.res h₂ (f σ₂) := by
  subst heq; rfl

/-- If `V = Set.univ`, restriction by `h : V ⊆ Set.univ` is a cast. -/
theorem res_eq_of_eq_univ (F : AbPresheaf X) {V : Set X} (hV : V = Set.univ)
    (h : V ⊆ Set.univ) (x : F.obj Set.univ) : F.res h x = hV ▸ x := by
  subst hV; exact F.res_id x

/-- If `V = U`, then `F.res h x = cast (...) x`. -/
theorem res_cast (F : AbPresheaf X) {U V : Set X} (hVU : V ⊆ U) (hUV : U = V)
    (x : F.obj U) : F.res hVU x = hUV ▸ x := by
  subst hUV; exact F.res_id x

end AbPresheaf

/-! ### Čech complex -/

section CechComplex

variable {X : Type u} [TopologicalSpace X] {ι : Type v} [Fintype ι]

/-- `q`-cochains: `Č^q(U, F) = ∏_{σ : Fin(q+1) → ι} F(U_σ)`. -/
def CechCochain (F : AbPresheaf X) (U : FiniteCover X ι) (q : ℕ) : Type (max v u) :=
  ∀ (σ : Fin (q + 1) → ι), F.obj (U.inter σ)

instance CechCochain.addCommGroup (F : AbPresheaf X) (U : FiniteCover X ι) (q : ℕ) :
    AddCommGroup (CechCochain F U q) :=
  @Pi.addCommGroup _ _ fun σ => F.instAddCommGroup (U.inter σ)

/-- Extensionality for cochains. -/
@[ext]
theorem CechCochain.ext {F : AbPresheaf X} {U : FiniteCover X ι} {q : ℕ}
    {f g : CechCochain F U q} (h : ∀ σ, f σ = g σ) : f = g :=
  funext h

/-- The Čech differential `d^q : Č^q(U, F) → Č^{q+1}(U, F)`. -/
def cechDiff (F : AbPresheaf X) (U : FiniteCover X ι) (q : ℕ) :
    CechCochain F U q → CechCochain F U (q + 1) :=
  fun f σ => ∑ j : Fin (q + 2),
    (-1 : ℤ) ^ (j : ℕ) • F.res (U.inter_face_subset j σ) (f (FiniteCover.face j σ))

/-- The augmentation `ε : F(X) → Č^0(U, F)`. -/
def cechAug (F : AbPresheaf X) (U : FiniteCover X ι) :
    F.obj Set.univ → CechCochain F U 0 :=
  fun x σ => F.res (U.inter_subset_univ σ) x

/-! ### The key identity d ∘ d = 0 -/

omit [Fintype ι] in
/-- Simplicial identity for `k < j`: composing face maps gives
`face k ∘ face j = face (j.pred) ∘ face (k.castSucc)`. -/
private theorem face_face_lt {q : ℕ} (j : Fin (q + 3)) (k : Fin (q + 2))
    (hjk : (k : ℕ) < j) (σ : Fin (q + 3) → ι) (hj : j ≠ 0 := by omega) :
    FiniteCover.face k (FiniteCover.face j σ) =
    FiniteCover.face (j.pred hj) (FiniteCover.face k.castSucc σ) := by
  funext m
  simp only [FiniteCover.face, Function.comp_apply]
  congr 1
  ext
  simp only [Fin.succAbove, Fin.lt_def, Fin.val_castSucc, Fin.val_succ,
    apply_ite Fin.val, Fin.val_pred]
  split_ifs <;> omega

omit [Fintype ι] in
/-- Simplicial identity for `j ≤ k`: composing face maps gives
`face k ∘ face j = face j' ∘ face (k.succ)` where `j' = ⟨j.val, ...⟩ : Fin (q+2)`. -/
private theorem face_face_ge {q : ℕ} (j : Fin (q + 3)) (k : Fin (q + 2))
    (hjk : (j : ℕ) ≤ k) (σ : Fin (q + 3) → ι)
    (hj : j.val < q + 2 := by omega) :
    FiniteCover.face k (FiniteCover.face j σ) =
    FiniteCover.face ⟨j.val, hj⟩ (FiniteCover.face k.succ σ) := by
  funext m
  simp only [FiniteCover.face, Function.comp_apply]
  congr 1
  ext
  simp only [Fin.succAbove, Fin.lt_def, Fin.val_castSucc, Fin.val_succ,
    apply_ite Fin.val]
  split_ifs <;> omega

/-- `d^{q+1} ∘ d^q = 0` (Appendix A of Wedhorn).

The proof expands the double sum, uses linearity and functoriality of restriction,
then applies `Finset.sum_involution` with the pairing `(j, k) ↦ (k↑, j-1)` (when `k < j`)
and `(j, k) ↦ (k+1, j↓)` (when `j ≤ k`). The simplicial face identities ensure the
underlying values match while the signs differ by `(-1)`. -/
theorem cechDiff_comp_cechDiff (F : AbPresheaf X) (U : FiniteCover X ι) (q : ℕ)
    (f : CechCochain F U q) : cechDiff F U (q + 1) (cechDiff F U q f) = 0 := by
  ext σ
  simp only [cechDiff]
  change ∑ j : Fin (q + 3), (-1 : ℤ) ^ (j : ℕ) •
    F.res (U.inter_face_subset j σ) (∑ k : Fin (q + 2),
      (-1 : ℤ) ^ (k : ℕ) • F.res (U.inter_face_subset k (FiniteCover.face j σ))
        (f (FiniteCover.face k (FiniteCover.face j σ)))) = 0
  -- Step 1: Push restriction through the inner sum and zsmul (keep res_comp separate)
  simp_rw [F.res_sum, F.res_zsmul]
  -- Helper: if two face compositions are equal, the corresponding T values
  -- (restriction applied to f) are equal
  -- Helper: if two face compositions are equal, the res(res(f(...))) terms agree
  have T_eq_of_face_eq : ∀ (j j' : Fin (q + 3)) (k k' : Fin (q + 2)),
      FiniteCover.face k' (FiniteCover.face j' σ) =
      FiniteCover.face k (FiniteCover.face j σ) →
      F.res (U.inter_face_subset j' σ)
        (F.res (U.inter_face_subset k' (FiniteCover.face j' σ))
          (f (FiniteCover.face k' (FiniteCover.face j' σ)))) =
      F.res (U.inter_face_subset j σ)
        (F.res (U.inter_face_subset k (FiniteCover.face j σ))
          (f (FiniteCover.face k (FiniteCover.face j σ)))) := by
    intro j j' k k' heq
    rw [F.res_comp, F.res_comp]
    exact F.res_section_eq f _ _ heq
  -- Step 2: Push (-1)^j • through the inner sum, then flatten to sum over pairs
  simp_rw [Finset.smul_sum]
  rw [← Finset.sum_product' Finset.univ Finset.univ]
  -- Step 3: Define the term function explicitly and use sum_involution
  -- Each term is T(j,k) = (-1)^j • (-1)^k • res(f(face k (face j σ)))
  set T : Fin (q + 3) × Fin (q + 2) → F.obj (U.inter σ) :=
    fun ⟨j, k⟩ => (-1 : ℤ) ^ (j : ℕ) • ((-1 : ℤ) ^ (k : ℕ) •
      F.res (U.inter_face_subset j σ)
        (F.res (U.inter_face_subset k (FiniteCover.face j σ))
          (f (FiniteCover.face k (FiniteCover.face j σ))))) with hT
  -- The involution function
  let inv : Fin (q + 3) × Fin (q + 2) → Fin (q + 3) × Fin (q + 2) :=
    fun ⟨j, k⟩ =>
      if h : (k : ℕ) < (j : ℕ) then
        (⟨k.val, by have := k.isLt; omega⟩, ⟨j.val - 1, by have := j.isLt; omega⟩)
      else
        (⟨k.val + 1, by have := k.isLt; omega⟩, ⟨j.val, by have := k.isLt; omega⟩)
  -- Helper: sign cancellation
  have sign_cancel : ∀ (n m : ℕ) (x : F.obj (U.inter σ)),
      (-1 : ℤ) ^ n • ((-1 : ℤ) ^ m • x) +
      (-1 : ℤ) ^ (m + 1) • ((-1 : ℤ) ^ n • x) = 0 := by
    intro n m x
    rw [← mul_zsmul, ← mul_zsmul, ← add_smul]
    have : (-1 : ℤ) ^ (m + 1) = (-1 : ℤ) ^ m * (-1) := pow_succ _ _
    rw [this]; ring_nf; exact zero_smul _ _
  -- Now apply the involution manually via Finset.sum_eq_zero
  -- Actually, use sum_involution on T with inv
  change ∑ p ∈ Finset.univ ×ˢ Finset.univ, T p = 0
  apply Finset.sum_involution (fun p _ => inv p)
  -- (1) T(a) + T(inv(a)) = 0
  · rintro ⟨j, k⟩ _
    dsimp only [inv]
    split_ifs with h
    · -- k < j: inv = (⟨k,...⟩, ⟨j-1,...⟩)
      -- Need: T(j,k) + T(⟨k,...⟩, ⟨j-1,...⟩) = 0
      simp only [hT]
      -- The face compositions match by face_face_lt
      have hj_ne : j ≠ 0 := by intro hj0; simp [hj0] at h
      have hface := face_face_lt j k h σ hj_ne
      -- face (j.pred) (face k.castSucc σ) = face k (face j σ)
      have hj_eq : (⟨(k : ℕ), by have := k.isLt; omega⟩ : Fin (q + 3)) = k.castSucc :=
        Fin.ext (by simp)
      have hk_eq : (⟨(j : ℕ) - 1, by have := j.isLt; omega⟩ : Fin (q + 2)) = j.pred (by omega) :=
        Fin.ext (by simp [Fin.val_pred])
      have hface_eq : FiniteCover.face ⟨(j : ℕ) - 1, by have := j.isLt; omega⟩
        (FiniteCover.face ⟨(k : ℕ), by have := k.isLt; omega⟩ σ) =
        FiniteCover.face k (FiniteCover.face j σ) := by rw [hj_eq, hk_eq]; exact hface.symm
      rw [T_eq_of_face_eq j ⟨k.val, by have := k.isLt; omega⟩
        k ⟨(j : ℕ) - 1, by have := j.isLt; omega⟩ hface_eq]
      -- Now signs cancel
      rw [← mul_zsmul, ← mul_zsmul, ← add_smul]
      have : (-1 : ℤ) ^ (j : ℕ) = (-1 : ℤ) ^ ((j : ℕ) - 1) * (-1) := by
        conv_lhs => rw [show (j : ℕ) = (j : ℕ) - 1 + 1 from by omega]; rw [pow_succ]
      rw [this]; ring_nf; exact zero_smul _ _
    · -- k ≥ j: inv = (⟨k+1,...⟩, ⟨j,...⟩)
      push_neg at h
      simp only [hT]
      have hface := face_face_ge j k h σ (by have := k.isLt; omega)
      have hj_eq : (⟨(k : ℕ) + 1, by have := k.isLt; omega⟩ : Fin (q + 3)) = k.succ :=
        Fin.ext (by simp [Fin.val_succ])
      have hface_eq : FiniteCover.face ⟨(j : ℕ), by have := k.isLt; omega⟩
        (FiniteCover.face ⟨(k : ℕ) + 1, by have := k.isLt; omega⟩ σ) =
        FiniteCover.face k (FiniteCover.face j σ) := by rw [hj_eq]; exact hface.symm
      rw [T_eq_of_face_eq j ⟨(k : ℕ) + 1, by have := k.isLt; omega⟩
        k ⟨(j : ℕ), by have := k.isLt; omega⟩ hface_eq]
      exact sign_cancel (j : ℕ) (k : ℕ) _
  -- (2) T(a) ≠ 0 → inv(a) ≠ a
  · rintro ⟨j, k⟩ _ _
    dsimp only [inv]
    split_ifs with h
    · intro heq; have := congr_arg (fun p => (Prod.fst p).val) heq; simp at this; omega
    · intro heq
      have := congr_arg (fun p => (Prod.fst p).val) heq
      simp at this; omega
  -- (3) inv(a) ∈ s
  · rintro ⟨j, k⟩ _
    dsimp only [inv]
    split_ifs <;> exact Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩
  -- (4) inv(inv(a)) = a
  · rintro ⟨j, k⟩ _
    dsimp only [inv]
    by_cases h1 : (k : ℕ) < (j : ℕ)
    · -- k < j: inv(j,k) = (⟨k,...⟩, ⟨j-1,...⟩). Then j-1 ≥ k, so ¬(j-1 < k).
      simp only [h1, dif_pos, Fin.val_mk]
      have h2 : ¬ ((j : ℕ) - 1 < (k : ℕ)) := by omega
      rw [dif_neg h2]
      ext <;> simp; omega
    · -- k ≥ j: inv(j,k) = (⟨k+1,...⟩, ⟨j,...⟩). Then j < k+1.
      push_neg at h1
      have : ¬ (k : ℕ) < (j : ℕ) := by omega
      rw [dif_neg this, dif_pos (show (j : ℕ) < (k : ℕ) + 1 from by omega)]
      ext <;> simp

/-! ### Acyclicity -/

/-- The augmentation `ε` is injective (separation / uniqueness). -/
def IsSeparating (F : AbPresheaf X) (U : FiniteCover X ι) : Prop :=
  Function.Injective (cechAug F U)

/-- Compatible 0-cochains glue: `ker(d⁰) ⊆ im(ε)`. -/
def HasGluing (F : AbPresheaf X) (U : FiniteCover X ι) : Prop :=
  ∀ f : CechCochain F U 0, cechDiff F U 0 f = 0 → ∃ x, cechAug F U x = f

/-- The augmented Čech complex is exact at every degree.
`IsAcyclic F U` means: separation + gluing + higher vanishing. -/
def IsAcyclic (F : AbPresheaf X) (U : FiniteCover X ι) : Prop :=
  IsSeparating F U ∧ HasGluing F U ∧
  ∀ q : ℕ, ∀ f : CechCochain F U (q + 1), cechDiff F U (q + 1) f = 0 →
    ∃ g : CechCochain F U q, cechDiff F U q g = f

end CechComplex

/-! ### Cover refinement -/

section Refinement

variable {X : Type u} [TopologicalSpace X]
  {ι : Type v} [Fintype ι] {κ : Type v} [Fintype κ]

/-- A refinement from `V` (indexed by `κ`) to `U` (indexed by `ι`):
a map `τ : κ → ι` such that `V.sets j ⊆ U.sets (τ j)` for all `j`. -/
structure Refinement (V : FiniteCover X κ) (U : FiniteCover X ι) where
  /-- The index map. -/
  map : κ → ι
  /-- Each set of `V` is contained in the corresponding set of `U`. -/
  subset : ∀ j, V.sets j ⊆ U.sets (map j)

namespace Refinement

variable {V : FiniteCover X κ} {U : FiniteCover X ι} (r : Refinement V U)

/-- The multi-intersection of `V` at `r.map ∘ σ` refines that of `U`. -/
theorem inter_subset {q : ℕ} (σ : Fin (q + 1) → κ) :
    V.inter σ ⊆ U.inter (r.map ∘ σ) :=
  Set.iInter_mono fun k => r.subset (σ k)

/-- The induced cochain map `Č^q(U, F) → Č^q(V, F)`. -/
def cochainMap (F : AbPresheaf X) (q : ℕ) :
    CechCochain F U q → CechCochain F V q :=
  fun f σ => F.res (r.inter_subset σ) (f (r.map ∘ σ))

/-- The cochain map is an `AddMonoidHom`. -/
def cochainMapHom (F : AbPresheaf X) (q : ℕ) :
    CechCochain F U q →+ CechCochain F V q where
  toFun := r.cochainMap F q
  map_zero' := by ext σ; exact F.res_zero _
  map_add' f g := by ext σ; exact F.res_add _ _ _

/-- Face map commutes with composition by `r.map`. -/
private theorem face_comp_map {q : ℕ} (j : Fin (q + 2)) (σ : Fin (q + 2) → κ) :
    r.map ∘ FiniteCover.face j σ = FiniteCover.face j (r.map ∘ σ) := by
  ext k; simp [FiniteCover.face]

/-- The cochain map commutes with the Čech differential. -/
theorem cochainMap_comm_diff (F : AbPresheaf X) (q : ℕ) (f : CechCochain F U q) :
    r.cochainMap F (q + 1) (cechDiff F U q f) = cechDiff F V q (r.cochainMap F q f) := by
  ext σ
  simp only [cochainMap, cechDiff]
  rw [F.res_sum]
  congr 1; ext j
  rw [F.res_zsmul, F.res_comp]
  congr 1
  rw [F.res_comp]
  exact F.res_section_eq f _ _ (face_comp_map r j σ).symm

end Refinement

end Refinement

/-! ### Cover restriction and products -/

section CoverOps

variable {X : Type u} [TopologicalSpace X]

namespace FiniteCover

variable {ι : Type v} [Fintype ι]

/-- Restrict a cover to an open subset `W`.
The restricted cover has sets `U_i ∩ W` (viewed as subsets of `W`). -/
def restrict (U : FiniteCover X ι) (W : Set X) (_hW : IsOpen W)
    (hWcover : W ⊆ ⋃ i, U.sets i) : FiniteCover W ι where
  sets i := Subtype.val ⁻¹' (U.sets i)
  isOpen i := (U.isOpen i).preimage continuous_subtype_val
  isCover := by
    ext ⟨x, hx⟩
    simp only [Set.mem_iUnion, Set.mem_preimage, Set.mem_univ, iff_true]
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hWcover hx)
    exact ⟨i, hi⟩

/-- The product of two covers `U` (indexed by `ι`) and `V` (indexed by `κ`). -/
def prod {κ : Type v} [Fintype κ] (U : FiniteCover X ι) (V : FiniteCover X κ) :
    FiniteCover X (ι × κ) where
  sets p := U.sets p.1 ∩ V.sets p.2
  isOpen p := (U.isOpen p.1).inter (V.isOpen p.2)
  isCover := by
    ext x; simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_univ, iff_true]
    have hx1 := Set.mem_iUnion.mp (U.isCover ▸ Set.mem_univ x)
    have hx2 := Set.mem_iUnion.mp (V.isCover ▸ Set.mem_univ x)
    obtain ⟨i, hi⟩ := hx1
    obtain ⟨j, hj⟩ := hx2
    exact ⟨⟨i, j⟩, hi, hj⟩

/-- The product cover refines the first factor. -/
def prodRefineFst {κ : Type v} [Fintype κ] (U : FiniteCover X ι)
    (V : FiniteCover X κ) : Refinement (U.prod V) U where
  map p := p.1
  subset _ := Set.inter_subset_left

/-- The product cover refines the second factor. -/
def prodRefineSnd {κ : Type v} [Fintype κ] (U : FiniteCover X ι)
    (V : FiniteCover X κ) : Refinement (U.prod V) V where
  map p := p.2
  subset _ := Set.inter_subset_right

end FiniteCover

end CoverOps

/-! ### Acyclicity results -/

section AcyclicResults

variable {X : Type u} [TopologicalSpace X] {ι : Type v} [Fintype ι]

/-- `IsAcyclic` implies `IsSeparating`. -/
theorem IsAcyclic.separating {F : AbPresheaf X} {U : FiniteCover X ι}
    (h : IsAcyclic F U) : IsSeparating F U :=
  h.1

/-- `IsAcyclic` implies `HasGluing`. -/
theorem IsAcyclic.gluing {F : AbPresheaf X} {U : FiniteCover X ι}
    (h : IsAcyclic F U) : HasGluing F U :=
  h.2.1

/-- `IsAcyclic` implies higher vanishing. -/
theorem IsAcyclic.higher_vanishing {F : AbPresheaf X} {U : FiniteCover X ι}
    (h : IsAcyclic F U) (q : ℕ) (f : CechCochain F U (q + 1))
    (hf : cechDiff F U (q + 1) f = 0) :
    ∃ g : CechCochain F U q, cechDiff F U q g = f :=
  h.2.2 q f hf

/-- The augmentation is a group homomorphism. -/
def cechAugHom (F : AbPresheaf X) (U : FiniteCover X ι) :
    F.obj Set.univ →+ CechCochain F U 0 where
  toFun := cechAug F U
  map_zero' := by ext σ; exact F.res_zero _
  map_add' _ _ := by ext σ; exact F.res_add _ _ _

/-- The differential is a group homomorphism. -/
def cechDiffHom (F : AbPresheaf X) (U : FiniteCover X ι) (q : ℕ) :
    CechCochain F U q →+ CechCochain F U (q + 1) where
  toFun := cechDiff F U q
  map_zero' := by
    ext σ; simp only [cechDiff]
    convert Finset.sum_const_zero using 1
    apply Finset.sum_congr rfl; intro j _
    have h0 : (0 : CechCochain F U q) (FiniteCover.face j σ) =
        (0 : F.obj (U.inter (FiniteCover.face j σ))) := rfl
    rw [h0, show F.res (U.inter_face_subset j σ) (0 : F.obj _) = 0
      from F.res_zero _, smul_zero]
  map_add' f g := by
    ext σ; simp only [cechDiff]
    conv_rhs =>
      rw [show (cechDiff F U q f + cechDiff F U q g) σ =
        cechDiff F U q f σ + cechDiff F U q g σ from rfl]
      simp only [cechDiff]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro j _
    rw [show (f + g : CechCochain F U q) (FiniteCover.face j σ) =
        (F.instAddCommGroup _).toAdd.add (f _) (g _) from rfl,
      F.res_add]
    show _ • ((F.instAddCommGroup _).toAdd.add _ _) = _
    rw [show (F.instAddCommGroup _).toAdd.add
      (F.res _ (f (FiniteCover.face j σ))) (F.res _ (g (FiniteCover.face j σ))) =
      F.res _ (f (FiniteCover.face j σ)) + F.res _ (g (FiniteCover.face j σ)) from rfl,
      smul_add]

/-- The augmentation followed by `d⁰` is zero. -/
theorem cechDiff_comp_cechAug (F : AbPresheaf X) (U : FiniteCover X ι) (x : F.obj Set.univ) :
    cechDiff F U 0 (cechAug F U x) = 0 := by
  ext σ
  simp only [cechDiff, cechAug]
  rw [show (0 : CechCochain F U 1) σ = (0 : F.obj (U.inter σ)) from rfl]
  rw [Fin.sum_univ_two]
  simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_one, pow_one, neg_one_smul]
  rw [F.res_comp, F.res_comp]
  exact add_neg_cancel _

/-- Acyclicity from components: combining separation, gluing, and higher vanishing. -/
theorem isAcyclic_of_components {F : AbPresheaf X} {U : FiniteCover X ι}
    (hsep : IsSeparating F U) (hglue : HasGluing F U)
    (hvanish : ∀ q : ℕ, ∀ f : CechCochain F U (q + 1),
      cechDiff F U (q + 1) f = 0 → ∃ g : CechCochain F U q, cechDiff F U q g = f) :
    IsAcyclic F U :=
  ⟨hsep, hglue, hvanish⟩

end AcyclicResults

/-! ### Čech cohomology for single-set covers -/

section TrivialCover

variable {X : Type u} [TopologicalSpace X]

/-- A cover by a single open set (the whole space). -/
def FiniteCover.single (X : Type u) [TopologicalSpace X] : FiniteCover X Unit where
  sets _ := Set.univ
  isOpen _ := isOpen_univ
  isCover := Set.iUnion_const _

/-- Multi-intersection for the single cover is `Set.univ`. -/
theorem FiniteCover.single_inter {q : ℕ} (σ : Fin (q + 1) → Unit) :
    (FiniteCover.single X).inter σ = Set.univ :=
  Set.iInter_const (Set.univ : Set X)

private theorem unit_fun_eq {α : Type*} [Unique α] {n : ℕ} (σ : Fin n → α) :
    σ = fun _ => default :=
  funext fun _ => Subsingleton.elim _ _

omit [TopologicalSpace X] in
/-- Restriction by a subset proof from/to `Set.univ` is injective
when the source set equals `Set.univ`. -/
private theorem res_univ_injective (F : AbPresheaf X) {V : Set X}
    (hV : V = Set.univ) (h : V ⊆ Set.univ) :
    Function.Injective (F.res h) := by
  subst hV; exact fun _ _ heq => by rwa [F.res_id, F.res_id] at heq

omit [TopologicalSpace X] in
/-- Restriction by a subset proof where `V = U` is surjective. -/
private theorem res_eq_surjective (F : AbPresheaf X) {U V : Set X}
    (h : V ⊆ U) (hVU : V = U) :
    Function.Surjective (F.res h) := by
  subst hVU; exact fun y => ⟨y, F.res_id y⟩

/-- The single-set cover satisfies separation and gluing. -/
theorem single_isSeparating_and_hasGluing (F : AbPresheaf X) :
    IsSeparating F (FiniteCover.single X) ∧ HasGluing F (FiniteCover.single X) := by
  refine ⟨?_, ?_⟩
  · intro x y hxy
    have h := congr_fun hxy (fun _ => ())
    simp only [cechAug] at h
    exact res_univ_injective F (FiniteCover.single_inter _) _ h
  · intro f _
    obtain ⟨x, hx⟩ := res_eq_surjective F
      ((FiniteCover.single X).inter_subset_univ (fun _ => ()))
      (FiniteCover.single_inter _) (f (fun _ => ()))
    refine ⟨x, ?_⟩
    ext σ; simp only [cechAug]
    rw [unit_fun_eq σ]; exact hx

end TrivialCover

/-! ### Degree-zero acyclicity and the sheaf condition -/

section BasisSheaf

variable {X : Type u} [TopologicalSpace X]

/-- Degree-zero acyclicity: separation + gluing (the conditions that
correspond to the sheaf axiom for a cover). -/
def IsDegreeZeroAcyclic {ι : Type v} [Fintype ι] (F : AbPresheaf X)
    (U : FiniteCover X ι) : Prop :=
  IsSeparating F U ∧ HasGluing F U

/-- `IsAcyclic` implies degree-zero acyclicity. -/
theorem IsAcyclic.degreeZero {ι : Type v} [Fintype ι] {F : AbPresheaf X}
    {U : FiniteCover X ι} (h : IsAcyclic F U) : IsDegreeZeroAcyclic F U :=
  ⟨h.1, h.2.1⟩

/-- Degree-zero acyclicity from components. -/
theorem isDegreeZeroAcyclic_of_components {ι : Type v} [Fintype ι]
    {F : AbPresheaf X} {U : FiniteCover X ι}
    (hsep : IsSeparating F U) (hglue : HasGluing F U) :
    IsDegreeZeroAcyclic F U :=
  ⟨hsep, hglue⟩

/-- The single-set cover is degree-zero acyclic. -/
theorem isDegreeZeroAcyclic_single (F : AbPresheaf X) :
    IsDegreeZeroAcyclic F (FiniteCover.single X) :=
  single_isSeparating_and_hasGluing F

end BasisSheaf

/-! ### Product cover acyclicity (Proposition A.3(3) of Wedhorn) -/

section ProductAcyclicity

variable {X : Type u} [TopologicalSpace X]
  {ι : Type v} [Fintype ι] {κ : Type v} [Fintype κ]

/-- **Proposition A.3(3) prerequisite**: the restriction of a cover `V` to
a multi-intersection of `U` gives a cover of that intersection. -/
def FiniteCover.restrictToInter (U : FiniteCover X ι) (V : FiniteCover X κ)
    {q : ℕ} (σ : Fin (q + 1) → ι) :
    FiniteCover (U.inter σ) κ where
  sets j := Subtype.val ⁻¹' (V.sets j)
  isOpen j := (V.isOpen j).preimage continuous_subtype_val
  isCover := by
    ext ⟨x, _⟩
    simp only [Set.mem_iUnion, Set.mem_preimage, Set.mem_univ, iff_true]
    exact Set.mem_iUnion.mp (V.isCover ▸ Set.mem_univ x)

/-- Multi-intersection of `U.prod V` decomposes into an intersection of
`U`-multi-intersections and `V`-multi-intersections. -/
theorem FiniteCover.prod_inter_subset_inter {q : ℕ}
    (U : FiniteCover X ι) (V : FiniteCover X κ)
    (σ : Fin (q + 1) → ι × κ) :
    (U.prod V).inter σ ⊆ U.inter (Prod.fst ∘ σ) ∩ V.inter (Prod.snd ∘ σ) := by
  intro x hx
  exact ⟨Set.mem_iInter.mpr fun k => ((Set.mem_iInter.mp hx) k).1,
    Set.mem_iInter.mpr fun k => ((Set.mem_iInter.mp hx) k).2⟩

/-- Multi-intersection of `U.prod V` contains the intersection of the
`U`- and `V`-multi-intersections. -/
theorem FiniteCover.inter_inter_subset_prod_inter {q : ℕ}
    (U : FiniteCover X ι) (V : FiniteCover X κ)
    (σ : Fin (q + 1) → ι × κ) :
    U.inter (Prod.fst ∘ σ) ∩ V.inter (Prod.snd ∘ σ) ⊆ (U.prod V).inter σ := by
  intro x ⟨hU, hV⟩
  exact Set.mem_iInter.mpr fun k =>
    ⟨Set.mem_iInter.mp hU k, Set.mem_iInter.mp hV k⟩

/-- Multi-intersection of `U.prod V` equals the intersection. -/
theorem FiniteCover.prod_inter_eq {q : ℕ}
    (U : FiniteCover X ι) (V : FiniteCover X κ)
    (σ : Fin (q + 1) → ι × κ) :
    (U.prod V).inter σ = U.inter (Prod.fst ∘ σ) ∩ V.inter (Prod.snd ∘ σ) :=
  Set.Subset.antisymm (U.prod_inter_subset_inter V σ)
    (U.inter_inter_subset_prod_inter V σ)

end ProductAcyclicity
