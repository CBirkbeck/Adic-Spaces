/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Topology.Sets.Opens
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.GroupWithZero.Action
import Mathlib.Tactic.Ring

/-!
# Čech Cohomology for Finite Covers

We define the Čech complex for finite open covers and prove `d ∘ d = 0`.

## Main definitions

* `FiniteCover`: A finite open cover of a topological space.
* `FiniteCover.inter`: Multi-intersection `U_{σ(0)} ∩ ⋯ ∩ U_{σ(q)}`.
* `CechCochain`: The `q`-cochains `Č^q(U, F)`.
* `cechDiff`: The differential `d^q : Č^q → Č^{q+1}`.
* `cechAug`: The augmentation `ε : F(X) → Č^0(U, F)`.
* `IsAcyclic`: A cover is `F`-acyclic if the augmented complex is exact.

## Main results

* `cechDiff_comp_cechDiff`: `d^{q+1} ∘ d^q = 0`.

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

end CechComplex
