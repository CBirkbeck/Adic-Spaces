/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.Order.Group.Defs
import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Convex Subgroups of Linearly Ordered Commutative Groups

We define convex subgroups of linearly ordered commutative groups and prove
basic properties, following §7.1 of [Wedhorn, *Adic Spaces*].

## Main definitions

* `ConvexSubgroup Γ` : A subgroup of `Γ` that is order-convex.
* `ConvexSubgroup.quotientLinearOrder` : `LinearOrder` on `Γ ⧸ H.toSubgroup`.
* `ConvexSubgroup.quotientIsOrderedMonoid` : `IsOrderedMonoid` on `Γ ⧸ H.toSubgroup`.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn2019adic], §7.1
-/

variable (Γ : Type*) [CommGroup Γ] [LinearOrder Γ] [IsOrderedMonoid Γ]

/-- A **convex subgroup** of a linearly ordered commutative group `Γ` is a subgroup
that is order-convex: if `a ≤ x ≤ b` and `a, b ∈ H`, then `x ∈ H`. -/
structure ConvexSubgroup extends Subgroup Γ where
  convex' : ∀ {a b x : Γ}, a ∈ carrier → b ∈ carrier → a ≤ x → x ≤ b → x ∈ carrier

namespace ConvexSubgroup

variable {Γ}

instance : SetLike (ConvexSubgroup Γ) Γ where
  coe H := H.carrier
  coe_injective' := by
    intro ⟨H₁, _⟩ ⟨H₂, _⟩ h
    congr 1
    exact Subgroup.ext (Set.ext_iff.mp h)

instance : SubgroupClass (ConvexSubgroup Γ) Γ where
  mul_mem {H} := H.toSubgroup.mul_mem'
  one_mem {H} := H.toSubgroup.one_mem'
  inv_mem {H} := H.toSubgroup.inv_mem'

omit [IsOrderedMonoid Γ] in
@[ext]
theorem ext {H₁ H₂ : ConvexSubgroup Γ} (h : ∀ x, x ∈ H₁ ↔ x ∈ H₂) : H₁ = H₂ :=
  SetLike.ext h

omit [IsOrderedMonoid Γ] in
theorem convex (H : ConvexSubgroup Γ) {a b x : Γ} (ha : a ∈ H) (hb : b ∈ H)
    (h₁ : a ≤ x) (h₂ : x ≤ b) : x ∈ H :=
  H.convex' ha hb h₁ h₂

omit [IsOrderedMonoid Γ] in
/-- A convex subgroup contains every element between `1` and any of its members ≥ 1. -/
theorem mem_of_one_le_le {H : ConvexSubgroup Γ} {x h : Γ}
    (hh : h ∈ H) (h1 : 1 ≤ x) (hx : x ≤ h) : x ∈ H :=
  H.convex (one_mem H) hh h1 hx

omit [IsOrderedMonoid Γ] in
/-- A convex subgroup contains every element between any of its members ≤ 1 and `1`. -/
theorem mem_of_le_le_one {H : ConvexSubgroup Γ} {x h : Γ}
    (hh : h ∈ H) (hx : h ≤ x) (h1 : x ≤ 1) : x ∈ H :=
  H.convex hh (one_mem H) hx h1

/-- The trivial convex subgroup `{1}`. -/
instance : Bot (ConvexSubgroup Γ) where
  bot := {
    toSubgroup := ⊥
    convex' := by
      intro a b x ha hb h₁ h₂
      change x ∈ (⊥ : Subgroup Γ)
      rw [Subgroup.mem_bot]
      have ha' : a = 1 := Subgroup.mem_bot.mp ha
      have hb' : b = 1 := Subgroup.mem_bot.mp hb
      exact le_antisymm (h₂.trans hb'.le) (ha'.ge.trans h₁)
  }

/-- The full group as a convex subgroup. -/
instance : Top (ConvexSubgroup Γ) where
  top := {
    toSubgroup := ⊤
    convex' := fun _ _ _ _ => trivial
  }

omit [IsOrderedMonoid Γ] in
@[simp] theorem mem_bot {x : Γ} : x ∈ (⊥ : ConvexSubgroup Γ) ↔ x = 1 :=
  Subgroup.mem_bot

omit [IsOrderedMonoid Γ] in
@[simp] theorem mem_top {x : Γ} : x ∈ (⊤ : ConvexSubgroup Γ) :=
  trivial

/-- Convex subgroups are normal (automatic for commutative groups). -/
instance normal (H : ConvexSubgroup Γ) : H.toSubgroup.Normal :=
  Subgroup.normal_of_comm H.toSubgroup

omit [IsOrderedMonoid Γ] in
/-- An element `γ` with `1 ≤ γ` is in `H` iff `γ⁻¹` is. -/
theorem inv_mem_iff_mem {H : ConvexSubgroup Γ} {γ : Γ} :
    γ⁻¹ ∈ H ↔ γ ∈ H :=
  ⟨fun h => inv_inv γ ▸ inv_mem h, inv_mem⟩

/-- Partial order on convex subgroups by inclusion. -/
instance : PartialOrder (ConvexSubgroup Γ) :=
  { le := fun H₁ H₂ => ∀ x, x ∈ H₁ → x ∈ H₂
    le_refl := fun _ _ hx => hx
    le_trans := fun _ _ _ h₁₂ h₂₃ x hx => h₂₃ x (h₁₂ x hx)
    le_antisymm := fun _ _ h₁₂ h₂₁ => ext fun _ => ⟨h₁₂ _, h₂₁ _⟩ }

instance : OrderBot (ConvexSubgroup Γ) where
  bot_le := fun H _ hx => mem_bot.mp hx ▸ one_mem H

instance : OrderTop (ConvexSubgroup Γ) where
  le_top := fun _ _ _ => mem_top

/-! ### Elements outside a convex subgroup -/

omit [IsOrderedMonoid Γ] in
/-- If `γ ∉ H` and `γ < 1`, then `γ < h` for every `h ∈ H`.
Proof: if some `h ∈ H` satisfies `h ≤ γ`, then `h ≤ γ ≤ 1` with `h, 1 ∈ H` gives `γ ∈ H`
by convexity, contradicting `γ ∉ H`. -/
theorem lt_of_not_mem_of_lt_one (H : ConvexSubgroup Γ) {γ : Γ} (hγ : γ ∉ H) (hγ1 : γ < 1)
    {h : Γ} (hh : h ∈ H) : γ < h := by
  by_contra hle; push_neg at hle; exact hγ (H.convex' hh (one_mem H) hle hγ1.le)

omit [IsOrderedMonoid Γ] in
/-- If `γ ∉ H` and `1 < γ`, then `h < γ` for every `h ∈ H`.
Symmetric to `lt_of_not_mem_of_lt_one`. -/
theorem lt_of_not_mem_of_one_lt (H : ConvexSubgroup Γ) {γ : Γ} (hγ : γ ∉ H) (hγ1 : 1 < γ)
    {h : Γ} (hh : h ∈ H) : h < γ := by
  by_contra hle; push_neg at hle; exact hγ (H.convex' (one_mem H) hh hγ1.le hle)

/-! ### Quotient linear order on `Γ ⧸ H.toSubgroup`

Given a convex subgroup `H` of a linearly ordered commutative group `Γ`,
the quotient `Γ ⧸ H.toSubgroup` inherits a linear order defined by

  `[a] ≤ [b] ↔ b⁻¹ * a ≤ 1 ∨ b⁻¹ * a ∈ H`

and this order is compatible with the group structure, making the quotient
an ordered commutative group.
-/

/-- The predicate `c ≤ 1 ∨ c ∈ H` is invariant under right-multiplication by elements of `H`.
This is the key lemma for well-definedness of the quotient order. -/
private theorem quotientLE_aux (H : ConvexSubgroup Γ) (c k : Γ) (hk : k ∈ H.toSubgroup) :
    (c ≤ 1 ∨ c ∈ H.toSubgroup) ↔ (c * k ≤ 1 ∨ c * k ∈ H.toSubgroup) := by
  by_cases hc : (c : Γ) ∈ H
  · exact ⟨fun _ => .inr (H.toSubgroup.mul_mem hc hk), fun _ => .inr hc⟩
  · have hck : c * k ∉ H := by
      intro hmem; have := H.toSubgroup.mul_mem hmem (H.toSubgroup.inv_mem hk)
      simp only [mul_inv_cancel_right] at this; exact hc this
    simp only [show ¬(c ∈ H.toSubgroup) from hc, show ¬(c * k ∈ H.toSubgroup) from hck, or_false]
    exact ⟨fun h1 => le_of_lt (lt_inv_iff_mul_lt_one.mp (H.lt_of_not_mem_of_lt_one hc
        (lt_of_le_of_ne h1 (fun h => hc (h ▸ H.toSubgroup.one_mem))) (inv_mem hk))),
      fun h1 => by by_contra hc1; push_neg at hc1; exact absurd h1 (not_le.mpr
        (inv_lt_iff_one_lt_mul.mp (H.lt_of_not_mem_of_one_lt hc hc1 (inv_mem hk))))⟩

/-- The order relation on `Γ ⧸ H.toSubgroup`: `[a] ≤ [b]` iff `b⁻¹ * a ≤ 1` or
`b⁻¹ * a ∈ H`. Well-definedness uses `quotientLE_aux` and the fact that replacing `a, b` by
`a * h₁, b * h₂` with `h₁, h₂ ∈ H` changes `b⁻¹ * a` by an `H`-element. -/
instance quotientLE (H : ConvexSubgroup Γ) : LE (Γ ⧸ H.toSubgroup) where
  le x y := Quotient.liftOn₂' x y
    (fun a b => b⁻¹ * a ≤ 1 ∨ b⁻¹ * a ∈ H.toSubgroup)
    (fun a₁ b₁ a₂ b₂ ha hb => by
      rw [QuotientGroup.leftRel_apply] at ha hb
      change (b₁⁻¹ * a₁ ≤ 1 ∨ _) = (b₂⁻¹ * a₂ ≤ 1 ∨ _)
      have hk : (b₁⁻¹ * b₂)⁻¹ * (a₁⁻¹ * a₂) ∈ H.toSubgroup :=
        H.toSubgroup.mul_mem (H.toSubgroup.inv_mem hb) ha
      have : b₂⁻¹ * a₂ = (b₁⁻¹ * a₁) * ((b₁⁻¹ * b₂)⁻¹ * (a₁⁻¹ * a₂)) := by
        simp only [mul_inv_rev, inv_inv, ← mul_assoc]; simp [mul_comm, mul_left_comm, mul_assoc]
      rw [this]; exact propext (quotientLE_aux H _ _ hk))

theorem quotient_le_iff (H : ConvexSubgroup Γ) (a b : Γ) :
    ((a : Γ ⧸ H.toSubgroup) ≤ (b : Γ ⧸ H.toSubgroup)) ↔
    (b⁻¹ * a ≤ 1 ∨ b⁻¹ * a ∈ H.toSubgroup) :=
  Iff.rfl

private theorem quotient_le_total' (H : ConvexSubgroup Γ) (a b : Γ) :
    (a : Γ ⧸ H.toSubgroup) ≤ b ∨ (b : Γ ⧸ H.toSubgroup) ≤ a := by
  change (b⁻¹ * a ≤ 1 ∨ b⁻¹ * a ∈ H.toSubgroup) ∨
         (a⁻¹ * b ≤ 1 ∨ a⁻¹ * b ∈ H.toSubgroup)
  by_cases hm : b⁻¹ * a ∈ H.toSubgroup
  · exact .inl (.inr hm)
  · have hne : b⁻¹ * a ≠ 1 := fun h => hm (h ▸ H.toSubgroup.one_mem)
    rcases lt_or_gt_of_ne hne with h | h
    · exact .inl (.inl h.le)
    · exact .inr (.inl (le_of_lt (by
        rw [show a⁻¹ * b = (b⁻¹ * a)⁻¹ from by simp [mul_inv_rev, inv_inv]]
        exact inv_lt_one_of_one_lt h)))

/-- The quotient `Γ ⧸ H.toSubgroup` by a convex subgroup `H` carries a linear order:
`[a] ≤ [b]` iff `b⁻¹ * a ≤ 1` or `b⁻¹ * a ∈ H`. -/
noncomputable instance quotientLinearOrder (H : ConvexSubgroup Γ) :
    LinearOrder (Γ ⧸ H.toSubgroup) where
  le_refl x := by
    induction x using Quotient.inductionOn with
    | _ a => change a⁻¹ * a ≤ 1 ∨ _; left; simp
  le_trans x y z hxy hyz := by
    induction x using Quotient.inductionOn with | _ a =>
    induction y using Quotient.inductionOn with | _ b =>
    induction z using Quotient.inductionOn with | _ c =>
    change c⁻¹ * a ≤ 1 ∨ _; change b⁻¹ * a ≤ 1 ∨ _ at hxy; change c⁻¹ * b ≤ 1 ∨ _ at hyz
    have : c⁻¹ * a = (c⁻¹ * b) * (b⁻¹ * a) := by simp [mul_assoc, mul_inv_cancel_left]
    rw [this]
    rcases hxy with hxy | hxy <;> rcases hyz with hyz | hyz
    · left; exact mul_le_one' hyz hxy
    · rw [mul_comm]; exact (quotientLE_aux H _ _ hyz).mp (.inl hxy)
    · exact (quotientLE_aux H _ _ hxy).mp (.inl hyz)
    · right; exact H.toSubgroup.mul_mem hyz hxy
  le_antisymm x y hxy hyx := by
    induction x using Quotient.inductionOn with | _ a =>
    induction y using Quotient.inductionOn with | _ b =>
    change b⁻¹ * a ≤ 1 ∨ _ at hxy; change a⁻¹ * b ≤ 1 ∨ _ at hyx
    apply QuotientGroup.eq.mpr
    rcases hxy with hxy | hxy
    · rcases hyx with hyx | hyx
      · have h1 : 1 ≤ b⁻¹ * a := by
          rw [show b⁻¹ * a = (a⁻¹ * b)⁻¹ from by simp [mul_inv_rev, inv_inv]]
          exact one_le_inv_of_le_one hyx
        have : a⁻¹ * b = 1 := by
          rw [show a⁻¹ * b = (b⁻¹ * a)⁻¹ from by simp [mul_inv_rev, inv_inv]]
          exact inv_eq_one.mpr (le_antisymm hxy h1)
        rw [this]; exact H.toSubgroup.one_mem
      · exact hyx
    · rw [show a⁻¹ * b = (b⁻¹ * a)⁻¹ from by simp [mul_inv_rev, inv_inv]]
      exact H.toSubgroup.inv_mem hxy
  le_total x y := by
    induction x using Quotient.inductionOn with | _ a =>
    induction y using Quotient.inductionOn with | _ b =>
    exact quotient_le_total' H a b
  toDecidableLE := Classical.decRel _
  toDecidableEq := Classical.decEq _
  toDecidableLT := Classical.decRel _

/-- The quotient order on `Γ ⧸ H.toSubgroup` is compatible with the group operation,
i.e., `[a] ≤ [b] → [a * c] ≤ [b * c]`. In a commutative group this is immediate since
`(b * c)⁻¹ * (a * c) = b⁻¹ * a`. -/
instance quotientIsOrderedMonoid (H : ConvexSubgroup Γ) :
    IsOrderedMonoid (Γ ⧸ H.toSubgroup) where
  mul_le_mul_left a b hab c := by
    induction a using Quotient.inductionOn with | _ a =>
    induction b using Quotient.inductionOn with | _ b =>
    induction c using Quotient.inductionOn with | _ c =>
    change (b * c)⁻¹ * (a * c) ≤ 1 ∨ _
    change b⁻¹ * a ≤ 1 ∨ _ at hab
    have : (b * c)⁻¹ * (a * c) = b⁻¹ * a := by simp [mul_inv_rev, mul_comm, mul_assoc]
    rw [this]; exact hab

/-! ### Total ordering of convex subgroups -/

/-- Convex subgroups of a linearly ordered commutative group are totally ordered by inclusion.

*Proof.* Assume `H₁ ⊄ H₂`. Pick `a ∈ H₁ \ H₂` with `a ≠ 1` (since `1 ∈ H₂`).
If `1 < a`, then every `b ∈ H₂` satisfies `a⁻¹ < b < a` (by the "outside" lemmas),
so `b ∈ H₁` by convexity. The case `a < 1` is symmetric via `a⁻¹ > 1`. -/
theorem le_total_of_convex (H₁ H₂ : ConvexSubgroup Γ) : H₁ ≤ H₂ ∨ H₂ ≤ H₁ := by
  by_contra h
  push_neg at h
  obtain ⟨hne₁, hne₂⟩ := h
  -- a ∈ H₁ \ H₂
  obtain ⟨a, haH₁, haH₂⟩ := Set.not_subset.mp (show ¬(H₁ : Set Γ) ⊆ H₂ from hne₁)
  have ha1 : a ≠ 1 := fun h => haH₂ (h ▸ one_mem H₂)
  -- H₂ ≤ H₁: for all b ∈ H₂, b ∈ H₁
  have hle : ∀ b, b ∈ H₂ → b ∈ H₁ := by
    intro b hb
    rcases lt_or_gt_of_ne ha1 with ha_lt | ha_gt
    · -- a < 1: a < b (any b ∈ H₂) and b < a⁻¹
      have hab : a < b := H₂.lt_of_not_mem_of_lt_one haH₂ ha_lt hb
      have : a⁻¹ ∉ H₂ := inv_mem_iff_mem.not.mpr haH₂
      have hba : b < a⁻¹ :=
        H₂.lt_of_not_mem_of_one_lt this (one_lt_inv_of_inv ha_lt) hb
      exact H₁.convex haH₁ (inv_mem haH₁) hab.le hba.le
    · -- a > 1: a⁻¹ < b (any b ∈ H₂) and b < a
      have hba : b < a := H₂.lt_of_not_mem_of_one_lt haH₂ ha_gt hb
      have : a⁻¹ ∉ H₂ := inv_mem_iff_mem.not.mpr haH₂
      have hab : a⁻¹ < b :=
        H₂.lt_of_not_mem_of_lt_one this (inv_lt_one_of_one_lt ha_gt) hb
      exact H₁.convex (inv_mem haH₁) haH₁ hab.le hba.le
  exact hne₂ hle

noncomputable instance : LinearOrder (ConvexSubgroup Γ) :=
  { (inferInstance : PartialOrder (ConvexSubgroup Γ)) with
    le_total := le_total_of_convex
    toDecidableLE := Classical.decRel _
    toDecidableEq := Classical.decEq _
    toDecidableLT := Classical.decRel _ }

/-! ### Largest convex subgroup avoiding an element -/

/-- The largest convex subgroup of `Γ` that does not contain `γ`.
This is the union `⋃ { H : ConvexSubgroup Γ | γ ∉ H }`, which is well-defined because
convex subgroups are totally ordered and the union of a chain of subgroups avoiding `γ` still
avoids `γ`. Requires `γ ≠ 1` (since every subgroup contains `1`). -/
noncomputable def maxAvoid {γ : Γ} (hγ : γ ≠ 1) : ConvexSubgroup Γ where
  toSubgroup :=
    { carrier := { x | ∃ H : ConvexSubgroup Γ, γ ∉ H ∧ x ∈ H }
      mul_mem' := fun {a b} ⟨H₁, hγ₁, ha⟩ ⟨H₂, hγ₂, hb⟩ => by
        rcases le_total H₁ H₂ with h | h
        · exact ⟨H₂, hγ₂, H₂.toSubgroup.mul_mem' (h _ ha) hb⟩
        · exact ⟨H₁, hγ₁, H₁.toSubgroup.mul_mem' ha (h _ hb)⟩
      one_mem' := ⟨⊥, mem_bot.not.mpr hγ, one_mem ⊥⟩
      inv_mem' := fun {a} ⟨H, hγH, ha⟩ => ⟨H, hγH, H.toSubgroup.inv_mem' ha⟩ }
  convex' := by
    intro a b x ⟨H₁, hγ₁, ha⟩ ⟨H₂, hγ₂, hb⟩ h₁ h₂
    rcases le_total H₁ H₂ with h | h
    · exact ⟨H₂, hγ₂, H₂.convex (h _ ha) hb h₁ h₂⟩
    · exact ⟨H₁, hγ₁, H₁.convex ha (h _ hb) h₁ h₂⟩

theorem mem_maxAvoid_iff {γ : Γ} {hγ : γ ≠ 1} {x : Γ} :
    x ∈ maxAvoid hγ ↔ ∃ H : ConvexSubgroup Γ, γ ∉ H ∧ x ∈ H := Iff.rfl

/-- The element `γ` is not in `maxAvoid hγ`. -/
theorem not_mem_maxAvoid {γ : Γ} (hγ : γ ≠ 1) : γ ∉ maxAvoid hγ :=
  fun ⟨_, hγH, hγH'⟩ => hγH hγH'

/-- Any convex subgroup not containing `γ` is `≤ maxAvoid hγ`. -/
theorem le_maxAvoid_of_not_mem {γ : Γ} {hγ : γ ≠ 1} {H : ConvexSubgroup Γ} (h : γ ∉ H) :
    H ≤ maxAvoid hγ :=
  fun _ hx => ⟨H, h, hx⟩

/-! ### Properties of `maxAvoid`

The quotient `Γ ⧸ (maxAvoid hγ).toSubgroup` has the property that every nontrivial
convex subgroup contains `[γ]`. This is a key step toward the cofinal property
needed for valuation coarsening (§7.1 of Wedhorn). -/

/-- Every nontrivial convex subgroup of `Γ ⧸ (maxAvoid hγ)` contains `[γ]`.

*Proof.* Let `K` be nontrivial in `Γ/H` where `H = maxAvoid hγ`. Its preimage `π⁻¹(K)` is
a convex subgroup of `Γ` containing `H`. If `γ ∉ π⁻¹(K)`, then `π⁻¹(K) ≤ H`
by maximality, forcing `K = ⊥`. So `γ ∈ π⁻¹(K)`, i.e., `[γ] ∈ K`. -/
theorem maxAvoid_mem_of_nontrivial {γ : Γ} (hγ : γ ≠ 1)
    (K : ConvexSubgroup (Γ ⧸ (maxAvoid hγ).toSubgroup))
    (hK : K ≠ ⊥) :
    (QuotientGroup.mk' (maxAvoid hγ).toSubgroup γ : Γ ⧸ _) ∈ K := by
  by_contra hγK
  -- Build the preimage of K as a convex subgroup of Γ
  have hπ_mono : Monotone (QuotientGroup.mk' (maxAvoid hγ).toSubgroup) := by
    intro a b hab; left; rwa [inv_mul_le_iff_le_mul, mul_one]
  let C : ConvexSubgroup Γ :=
    { toSubgroup := K.toSubgroup.comap (QuotientGroup.mk' (maxAvoid hγ).toSubgroup)
      convex' := fun ha hb h₁ h₂ => K.convex ha hb (hπ_mono h₁) (hπ_mono h₂) }
  -- C contains maxAvoid hγ (elements map to 1 ∈ K)
  have hle : maxAvoid hγ ≤ C := fun x hx => by
    change (x : Γ ⧸ (maxAvoid hγ).toSubgroup) ∈ K
    rw [(QuotientGroup.eq_one_iff x).mpr hx]; exact one_mem K
  -- γ ∉ C (since [γ] ∉ K)
  have hγC : γ ∉ C := hγK
  -- So C ≤ maxAvoid hγ (by maximality)
  have hle' : C ≤ maxAvoid hγ := le_maxAvoid_of_not_mem hγC
  -- C = maxAvoid hγ, so K is trivial
  apply hK; ext ⟨x⟩; simp only [mem_bot]; constructor
  · exact fun hx => (QuotientGroup.eq_one_iff x).mpr (hle' _ hx)
  · intro hx; rw [hx]; exact one_mem K

end ConvexSubgroup
