# Tate Acyclicity — Parallelizable Tickets

**Master goal:** Prove Wedhorn Theorem 8.28(b): strongly noetherian Tate rings are sheafy.
**Reference:** Wedhorn, *Adic Spaces*, pp.80-85 + Appendix A (pp.104-106).
**Constraint:** No `sorry` or `axiom`.
**Full plan:** `docs/plans/2026-03-21-tate-acyclicity.md`

---

## Agent Coordination Protocol

**EVERY agent MUST follow these rules:**

1. **Before starting a ticket:** Update the tracker table below — set Status
   to `IN PROGRESS`, fill in your Agent ID and start date. **Commit this change**
   before writing any code. This prevents two agents from picking up the same ticket.

2. **Check for conflicts:** Before picking a ticket, read this file and check
   the tracker. If a ticket is `IN PROGRESS`, do NOT work on it. Pick a
   different ticket from the same wave, or wait.

3. **Check dependencies:** Only pick up tickets whose dependencies are `DONE`.
   See the dependency graph below.

4. **When finished:** Update the tracker — set Status to `DONE`, fill in the
   completion date and the commit hash. **Commit this change** immediately.

5. **If blocked:** Set Status to `BLOCKED`, add a note explaining why, and commit.

6. **Do not modify files owned by another in-progress ticket.** Each ticket
   lists its file(s). If another ticket is IN PROGRESS on that file, wait.

7. **Commit frequently** with messages referencing the ticket number
   (e.g., `TICKET-1A: define CechCochain and cechDiff`).

## Tracker

| Ticket | Status | Agent | Started | Completed | Commit | Notes |
|--------|--------|-------|---------|-----------|--------|-------|
| 0 | NOT STARTED | — | — | — | — | |
| 1A | NOT STARTED | — | — | — | — | |
| 1B | NOT STARTED | — | — | — | — | Depends: 1A |
| 2A | NOT STARTED | — | — | — | — | |
| 2B | NOT STARTED | — | — | — | — | Depends: 2A, 0 |
| 3 | NOT STARTED | — | — | — | — | Depends: 2B |
| 4 | NOT STARTED | — | — | — | — | Depends: 1A, 2B, 3, 6 |
| 5 | NOT STARTED | — | — | — | — | Depends: 1B, 4 |
| 6 | NOT STARTED | — | — | — | — | Depends: 0 |

## Dependency Graph

```
TICKET-0 ──────────────────────────────────────────────────────────
  (prereqs)
      │
      ├──→ TICKET-1A ──→ TICKET-1B ─────────────────────┐
      │    (Čech defs)   (Čech theorems)                 │
      │                                                  │
      ├──→ TICKET-2A ──→ TICKET-2B ──→ TICKET-3 ──→ TICKET-4
      │    (Tate defs)   (Tate flat)   (restriction)  (Laurent)
      │                                                  │
      └──→ TICKET-6 (open mapping / Artin-Rees)──────────┘
                                                         │
                                                    TICKET-5
                                                    (assembly)
```

**Can run in parallel:** {1A, 2A, 6} then {1B, 2B} then {3} then {4} then {5}

---

## TICKET-0: Prerequisite Mathlib Audit

**Status:** NOT STARTED
**Assignee:** (any agent)
**Estimated:** 1 hour
**Blocks:** All other tickets
**Output:** A markdown report in `docs/plans/mathlib-audit-tate.md`

### Task

Audit mathlib v4.29.0-rc3 for the following APIs. For each, report:
- Does it exist? (exact declaration name + file)
- If not, how hard to prove? (trivial / medium / hard)
- Alternative approaches if missing

### Checklist

- [ ] **Artin-Rees lemma**: `∃ c, I^n M ∩ N ⊆ I^{n-c} N` for f.g. submodules over noetherian rings. Search for `artinRees`, `artin_rees`, `Ideal.smul_inf_le`.
- [ ] **Open mapping for I-adic modules**: Surjective maps between f.g. modules over noetherian I-adic rings are open. Search for `IsOpenMap`, `Ideal.adic_module_isOpen`.
- [ ] **Completion preserves exact sequences**: For strict morphisms of topological abelian groups, completion preserves exactness. Search for `UniformSpace.Completion.map_exact`, `strictMorphism`.
- [ ] **5-lemma**: Search for `five_lemma`, `fiveLemma`, or snake lemma `snake_lemma`.
- [ ] **Faithful flatness API**: What lemmas does `RingHom.faithfullyFlat` provide? Can we deduce injectivity of `A → ∏ B_i` from faithful flatness of each `A → B_i`?
- [ ] **Tensor product over algebra**: `M ⊗[A] N` for modules, right exactness of tensor. Search for `TensorProduct.rightExact`.
- [ ] **Power series coefficients API**: `MvPowerSeries.coeff`, convergence, algebra structure. Check `RestrictedPowerSeries.lean` in the project.
- [ ] **IsNoetherianRing preservation**: Does mathlib prove `R noetherian → R⟦X⟧ noetherian` or `R noetherian → R[X] noetherian`? Search `Polynomial.isNoetherianRing`, `PowerSeries.isNoetherianRing`.

### Acceptance criteria

A markdown file listing each item with: exists/missing, exact name, file path, and if missing, a 1-paragraph proposal for how to prove it.

---

## TICKET-1A: Čech Complex — Definitions

**Status:** NOT STARTED
**Assignee:** (any agent)
**Estimated:** ~150 lines
**Blocks:** TICKET-1B
**Depends on:** TICKET-0
**File:** `Adic spaces/CechCohomology.lean`

### Context

Wedhorn Appendix A (pp.104-106). No Čech cohomology exists in mathlib or the project. We build it from scratch, working concretely with `Fin`-indexed finite covers.

### Task

Define the Čech complex for finite open covers of a topological space, with values in a presheaf of abelian groups (or rings).

### Definitions to create

```
-- A finite open cover indexed by Fin n
structure FinCover (X : Type*) [TopologicalSpace X] (n : ℕ) where
  sets : Fin n → Set X
  isOpen : ∀ i, IsOpen (sets i)
  isCover : ⋃ i, sets i = Set.univ

-- Multi-intersection U_{i₀} ∩ ... ∩ U_{i_q}
def FinCover.inter (U : FinCover X n) (σ : Fin (q+1) →o Fin n) : Set X

-- q-cochains: ∏_{σ : Fin(q+1) →o Fin n} F(U_σ)
def CechCochain (F : Set X → Type*) (U : FinCover X n) (q : ℕ) : Type*

-- Alternating q-cochains
def CechCochainAlt (F : Set X → Type*) (U : FinCover X n) (q : ℕ) : Type*

-- Differential d^q : Č^q → Č^{q+1}
def cechDiff (F : Set X → Type*) (res : ∀ {U V}, V ⊆ U → F U → F V)
    (U : FinCover X n) (q : ℕ) : CechCochain F U q → CechCochain F U (q+1)

-- Augmentation ε : F(X) → Č^0
def cechAugmentation (F : Set X → Type*) (res : ∀ {U V}, V ⊆ U → F U → F V)
    (U : FinCover X n) : F Set.univ → CechCochain F U 0

-- Augmented Čech complex
structure AugCechComplex (F : Set X → Type*) (U : FinCover X n) where
  ...

-- F-acyclicity: the augmented complex is exact
def IsAcyclic (F : Set X → Type*) (U : FinCover X n) : Prop
```

### Key properties to prove

- [ ] `cechDiff_comp_cechDiff : cechDiff q+1 ∘ cechDiff q = 0`
- [ ] `cechAugmentation_comp_cechDiff : cechDiff 0 ∘ cechAugmentation = 0`

### Acceptance criteria

- File compiles with `lake env lean "Adic spaces/CechCohomology.lean"`
- Zero warnings
- All definitions are well-typed and usable
- `d ∘ d = 0` proved
- At least 1 docstring per public definition

---

## TICKET-1B: Čech Complex — Refinement Theorems

**Status:** NOT STARTED
**Assignee:** (any agent)
**Estimated:** ~250 lines
**Blocks:** TICKET-5
**Depends on:** TICKET-1A
**File:** `Adic spaces/CechCohomology.lean` (append to file from 1A)

### Context

Wedhorn Appendix A, Propositions A.3 and A.4. These are the key structural
theorems that let us reduce sheafiness to acyclicity on a basis.

### Theorems to prove

**Prop A.3(2):** If `V` refines `U` (i.e., ∀ j, V_j ⊆ U_{τ(j)} for some τ),
then `U` is F-acyclic iff `V` is F-acyclic.

*Proof:* The refinement map τ induces a chain map `Č•(U,F) → Č•(V,F)` which
is a quasi-isomorphism (standard homotopy argument).

**Prop A.3(3):** The product cover `U × V := (U_i ∩ V_j)_{i,j}` is F-acyclic
iff `U` is F-acyclic.

*Proof:* `U × V` refines both `U` and `V`. Use (2).

**Prop A.4:** Let B be a basis of the topology stable under finite intersections.
If F is a presheaf on B, and every covering of U ∈ B by elements of B is
F-acyclic, then:
- F extends uniquely to a sheaf F' on X
- Ȟ^q(U, F) = H^q(U, F') = 0 for all U ∈ B and q ≥ 1

*Proof:* Exactness of `0 → F(U) → Č^0 → Č^1` shows F' is a sheaf on B.
The acyclicity of the augmented complex for all B-coverings of U ∈ B gives
Ȟ^q(U, F) = 0. By Cartan's theorem (Godement II.5.9.2), Ȟ^q = H^q for
all open U.

### Steps

- [ ] Define refinement map `τ : V refines U`
- [ ] Construct chain map induced by refinement
- [ ] Prove Prop A.3(2) (refinement preserves acyclicity)
- [ ] Prove Prop A.3(3) (product covers)
- [ ] State and prove Prop A.4 (sheaf on basis)
- [ ] Connect to existing `RationalCovering` from Presheaf.lean

### Acceptance criteria

- File compiles, zero warnings
- Prop A.3(2), A.3(3), A.4 all proved (no sorry)
- Connected to `RationalCovering` type

---

## TICKET-2A: Tate Algebra — Definitions and Basic Properties

**Status:** NOT STARTED
**Assignee:** (any agent)
**Estimated:** ~150 lines
**Blocks:** TICKET-2B
**Depends on:** TICKET-0
**File:** `Adic spaces/TateAlgebra.lean`

### Context

Wedhorn Remark 8.29 and §5.7. The Tate algebra `A⟨X⟩` is the ring of restricted
power series: `∑ aₙ Xⁿ` with `aₙ → 0`. For a f.g. A-module M, define `M⟨X⟩`
similarly. The project already has `RestrictedPowerSeries.lean` with
`MvPowerSeries.IsRestricted` and `restrictedMvPowerSeriesSubring`.

### Definitions to create

```
-- Tate algebra: A⟨X⟩ (univariate restricted power series)
-- Use existing restrictedMvPowerSeriesSubring with k=1, or define directly
def tateAlgebra (A : Type*) [CommRing A] [TopologicalSpace A] :
    Subring (PowerSeries A)

-- Module of restricted power series M⟨X⟩
def tateModule (M : Type*) [AddCommGroup M] [Module A M]
    [TopologicalSpace M] : Type*

-- Natural map μ_M : M ⊗_A A⟨X⟩ → M⟨X⟩
def tateModuleMap (M : Type*) ... : M ⊗[A] tateAlgebra A → tateModule M

-- Topology on A⟨X⟩ making it a Tate ring
instance : TopologicalSpace (tateAlgebra A)
instance : IsTopologicalRing (tateAlgebra A)
instance : IsTateRing (tateAlgebra A) -- X is a topologically nilpotent unit
```

### Key lemma

- [ ] `tateAlgebra_quotient_iso` : `A⟨X⟩ / (X) ≅ A` (the augmentation)

### Acceptance criteria

- File compiles, zero warnings
- `tateAlgebra`, `tateModule`, `tateModuleMap` all defined
- `IsTateRing` instance on `tateAlgebra A`
- Augmentation quotient isomorphism proved

---

## TICKET-2B: Tate Algebra — Flatness (Lemma 8.31)

**Status:** NOT STARTED
**Assignee:** (any agent)
**Estimated:** ~200 lines
**Blocks:** TICKET-3
**Depends on:** TICKET-2A, TICKET-0 (Artin-Rees audit)
**File:** `Adic spaces/TateAlgebra.lean` (append)

### Context

Wedhorn Lemma 8.31. This is the algebraic engine behind the sheafiness proof.

### Theorems to prove

**Remark 8.29:** `μ_M : M ⊗_A A⟨X⟩ → M⟨X⟩` is bijective when A is noetherian.
*Proof:* Clear for M = A^n (free). General: take presentation A^n → A^m → M → 0,
tensor with A⟨X⟩ (right exact), get A⟨X⟩^n → A⟨X⟩^m → M ⊗ A⟨X⟩ → 0.
Prop 6.18(2) shows u and p are continuous and open. By 5-lemma on the diagram
with M⟨X⟩, conclude μ_M is bijective.

**Lemma 8.31(1):** `A⟨X⟩` is faithfully flat over A.
*Proof:* Flat because μ_M bijective means `M ⊗ A⟨X⟩ ≅ M⟨X⟩`, and M⟨X⟩
contains M (constant power series), so `M → M ⊗ A⟨X⟩` is injective.
Faithful because `A⟨X⟩/(X) ≅ A`.

**Lemma 8.31(2):** `A⟨X⟩/(f-X)` and `A⟨X⟩/(1-fX)` are flat over A for any f ∈ A.
*Proof:* For any f.g. A-module M, need to show multiplication by `g = f - X`
(resp. `g = 1 - fX`) on `M⟨X⟩` is injective. If `gu = 0` where
`u = ∑ mₙXⁿ`, the relation `fm₀ = 0, fmₙ = mₙ₋₁` (for g = f-X) gives
`f^{l+1}m_l = 0`. Since M is noetherian, the submodule generated by
{m₀, m₁, ...} is finitely generated, say by m₀,...,m_l. Then
`m_{2l+1} = am_l` for some a, and `f^{l+1}m_{2l+1} = af^{l+1}m_l = 0`.
Thus the submodule M' = 0, so u = 0.

### Steps

- [ ] Prove `tateModuleMap_bijective` for free modules
- [ ] Prove `tateModuleMap_bijective` for f.g. modules (using presentation + 5-lemma)
- [ ] Prove `tateAlgebra_flat` (Lemma 8.31(1), flat part)
- [ ] Prove `tateAlgebra_faithfullyFlat` (Lemma 8.31(1), faithful part)
- [ ] Prove `multiplication_injective_fX` (Lemma 8.31(2), g = f-X case)
- [ ] Prove `multiplication_injective_1fX` (Lemma 8.31(2), g = 1-fX case)
- [ ] Prove `tateAlgebra_quotient_flat` (Lemma 8.31(2))

### Acceptance criteria

- Lemma 8.31(1) and 8.31(2) fully proved, no sorry
- File compiles, zero warnings

---

## TICKET-3: Flatness of Restriction Maps (Prop 8.30 + Cor 8.32)

**Status:** NOT STARTED
**Assignee:** (any agent)
**Estimated:** ~200 lines
**Blocks:** TICKET-4
**Depends on:** TICKET-2B
**File:** `Adic spaces/FlatnessResults.lean`

### Context

Wedhorn Prop 8.30 and Cor 8.32. Connects the abstract Tate algebra flatness
to the presheaf structure.

### Theorems to prove

**Prop 8.30:** For rational subsets U ⊆ V ⊆ Spa A (with A strongly noetherian
Tate), the restriction `O_X(V) → O_X(U)` is flat.
*Proof:* WLOG V = X, A complete. By Remark 7.55, U = R(f/1) or R(1/f).
Then O_X(U) = A⟨X⟩/(f-X) or A⟨X⟩/(1-fX), flat by Lemma 8.31(2).

**Cor 8.32:** The product `O_X(X) → ∏ O_X(U_i)` is faithfully flat (and injective).
*Proof:* Factors through A⟨X⟩ (faithfully flat by 8.31(1)).

### Interface with existing code

- Uses `presheafValue` from Presheaf.lean (= completion of Localization.Away s)
- Uses `restrictionMap` from Presheaf.lean
- Needs to connect `presheafValue D` with `tateAlgebra A / (f-X)` or similar
- This connection (Example 6.38 / equation 8.1.1) may be the hardest part

### Steps

- [ ] Establish `presheafValue ≅ A⟨X⟩/(f-X)` for rational subsets of the form R(f/1)
- [ ] Establish `presheafValue ≅ A⟨X⟩/(1-fX)` for R(1/f)
- [ ] Prove Prop 8.30 using Lemma 8.31(2)
- [ ] Prove Cor 8.32 using Lemma 8.31(1)

### Acceptance criteria

- Prop 8.30 and Cor 8.32 fully proved, no sorry
- Connected to existing `presheafValue` and `restrictionMap`

---

## TICKET-4: Laurent Cover Exactness — Completed vs Decompleted (Lemma 8.33)

**Status:** NOT STARTED
**Assignee:** (experienced agent — hardest ticket)
**Estimated:** ~400 lines
**Blocks:** TICKET-5
**Depends on:** TICKET-1A, TICKET-2B, TICKET-3, TICKET-6
**File:** `Adic spaces/LaurentCoverExact.lean`

### Context

Wedhorn Lemma 8.33, p.83. This is the **heart** of the entire proof — the
completed vs decompleted exactness argument.

### Setup

For `f ∈ A`, define the 2-element cover:
- `U₁ = R(f/1) = {x ∈ Spa A : x(f) ≤ 1}`
- `U₂ = R(1/f) = {x ∈ Spa A : x(f) ≥ 1}`

The augmented Čech complex is:
`0 → O_X(X) → O_X(U₁) × O_X(U₂) → O_X(U₁ ∩ U₂) → 0`

Using the identifications:
- `O_X(U₁) = A⟨ζ⟩/(f-ζ)`
- `O_X(U₂) = A⟨η⟩/(1-fη)`
- `O_X(U₁ ∩ U₂) = A⟨ζ, ζ⁻¹⟩/(f-ζ)`

### The 3×3 diagram

```
                    0                     0
                    ↓                     ↓
(f-ζ)A⟨ζ⟩ × (1-fη)A⟨η⟩  →λ'→  (f-ζ)A⟨ζ,ζ⁻¹⟩  → 0    [Row 1: kernels]
                    ↓                     ↓
0 → A  →ι→  A⟨ζ⟩ × A⟨η⟩      →λ→   A⟨ζ,ζ⁻¹⟩          [Row 2: Tate algebras]
                    ↓                     ↓
0 → A  →ε→  O_X(U₁) × O_X(U₂) →δ→  O_X(U₁∩U₂)  → 0  [Row 3: presheaf values]
                    ↓                     ↓
                    0                     0
```

### Proof steps

1. **Define Laurent algebra** `A⟨ζ, ζ⁻¹⟩` (power series in ζ and ζ⁻¹ with
   coefficients → 0 in both directions)

2. **Prove decomposition** `A⟨ζ, ζ⁻¹⟩ = A⟨ζ⟩ + ζ⁻¹·A⟨ζ⁻¹⟩` (direct sum of
   positive and negative parts)

3. **Construct λ** : `A⟨ζ⟩ × A⟨η⟩ → A⟨ζ, ζ⁻¹⟩` by
   `(g(ζ), h(η)) ↦ g(ζ) - h(ζ⁻¹)`

4. **Prove λ surjective** (from the decomposition in step 2)

5. **Prove ker(λ) = im(ι)**: If `g(ζ) = h(ζ⁻¹)`, comparing coefficients gives
   `aₖ = bₖ = 0` for k > 0 and `a₀ = b₀`. So `(g, h) = ι(a₀)`.

6. **Row 1 exact**: `λ'` surjective by similar coefficient argument applied to
   `(f-ζ)A⟨ζ,ζ⁻¹⟩ = (f-ζ)A⟨ζ⟩ + (1-fζ⁻¹)ζ⁻¹A⟨ζ⁻¹⟩`

7. **Columns exact**: by definition (quotient by the ideals (f-ζ), (1-fη))

8. **Diagram chase** (snake lemma or direct): rows 1+2 exact with exact columns
   ⟹ row 3 exact. This is the "decompleted" exactness.

9. **Open mapping** (Prop 6.18(2)): The maps ι, λ are continuous and open
   (surjective maps of f.g. modules over noetherian Tate rings are open
   by Artin-Rees). Therefore the quotient maps to row 3 preserve exactness.

10. **Completion**: Since all maps are strict (continuous + open on image),
    passing to the I-adic completion preserves the exact sequence.
    Row 3 = completion of the decompleted row ⟹ row 3 is exact.

### Steps

- [ ] Define `laurentAlgebra A` (A⟨ζ, ζ⁻¹⟩)
- [ ] Prove decomposition A⟨ζ, ζ⁻¹⟩ = A⟨ζ⟩ ⊕ ζ⁻¹·A⟨ζ⁻¹⟩₊
- [ ] Define and prove λ surjective
- [ ] Prove ker(λ) = im(ι)
- [ ] Prove row 1 exact
- [ ] Prove columns exact
- [ ] Diagram chase → row 3 exact (decompleted)
- [ ] Prove maps are open (using TICKET-6)
- [ ] Prove completion preserves exact sequence
- [ ] Package as `laurentCover_isAcyclic`

### Acceptance criteria

- Lemma 8.33 fully proved, no sorry
- The completed vs decompleted argument is explicit
- Connected to `IsAcyclic` from CechCohomology.lean

---

## TICKET-5: General Acyclicity + Assembly (Lemma 8.34, Thm 8.28(b))

**Status:** NOT STARTED
**Assignee:** (any agent)
**Estimated:** ~250 lines
**Blocks:** None (final ticket)
**Depends on:** TICKET-1B, TICKET-4
**Files:** `Adic spaces/TateAcyclicity.lean` (new),
  `Adic spaces/StructureSheaf.lean` (modify), `Adic spaces.lean` (modify)

### Context

Wedhorn Lemma 8.34 and Theorem 8.28(b). Induction on covers using
Laurent cover exactness + Čech refinement.

### Definition

```
-- Strongly noetherian Tate ring (Wedhorn Definition 8.28 condition (b))
class IsStronglyNoetherianTate (A : Type*) [CommRing A] [TopologicalSpace A]
    extends IsTateRing A where
  noetherian_ring_of_def : ∃ P : PairOfDefinition A, IsNoetherianRing P.A₀
  -- + stability under topologically finite type base change
```

### Theorems to prove

**Lemma 8.34:** Standard covers of a complete strongly noetherian Tate ring are
O_X-acyclic. Proof by induction:
- (i) 2-element Laurent covers are acyclic (Lemma 8.33 = TICKET-4)
- (ii) Laurent covers generated by units refine to acyclic covers
- (iii) Every rational cover has a Laurent cover refinement
- (iv) Combine with Prop A.3 (TICKET-1B)

**Theorem 8.28(b):** O_X is a sheaf. Proof:
- Rational subsets form a basis stable under intersections (existing in project)
- Standard covers are acyclic on this basis (Lemma 8.34)
- By Prop A.4 (TICKET-1B), O_X is a sheaf

### Steps

- [ ] Define `IsStronglyNoetherianTate`
- [ ] Prove rational localizations preserve strongly noetherian (Example 6.38)
- [ ] Define Laurent covers
- [ ] Prove 2-element Laurent covers acyclic (wrap TICKET-4)
- [ ] Prove Laurent cover refinement exists (Lemma 8.34(ii)-(iii))
- [ ] Prove Lemma 8.34 by induction
- [ ] Prove `IsStronglyNoetherianTate.isSheafyTopRing` (Theorem 8.28(b))
- [ ] Add `IsSheafy` instance to StructureSheaf.lean
- [ ] Update imports in `Adic spaces.lean`
- [ ] Full `lake build` verification

### Acceptance criteria

- Theorem 8.28(b) fully proved, no sorry
- `IsSheafy` instance registered
- Full project builds with zero errors

---

## TICKET-6: Open Mapping Theorem for I-adic Modules

**Status:** NOT STARTED
**Assignee:** (any agent)
**Estimated:** ~200 lines
**Blocks:** TICKET-4
**Depends on:** TICKET-0 (to know if Artin-Rees exists)
**File:** `Adic spaces/OpenMapping.lean`

### Context

Wedhorn Prop 6.18(2). This is a prerequisite for the completed vs decompleted
argument (TICKET-4). We need: surjective A-linear maps between f.g. modules
over a noetherian I-adic ring are open (with the I-adic topology).

### What to prove

**Artin-Rees Lemma** (if not in mathlib):
For a noetherian ring A, ideal I, f.g. A-module M, and submodule N ⊆ M:
`∃ c, ∀ n ≥ c, I^n M ∩ N = I^{n-c}(I^c M ∩ N)`

**Prop 6.18(1):** For a noetherian Tate ring A and a f.g. A-module M, the
I-adic topology on M (for any ideal of definition I) is the unique
topology making M a topological A-module with I^n M → 0.

**Prop 6.18(2):** Any surjective A-linear map u : M → N between f.g. modules
(with canonical topology) is continuous and open.
*Proof:* Continuous by definition (I-adic). Open: ker(u) ⊆ M is a submodule.
By Artin-Rees, `I^n M ∩ ker(u) ⊆ I^{n-c} ker(u)`. Since `u(I^n M) = I^n N`,
the map on quotients `M/I^n M → N/I^n N` has kernel
`(I^n M + ker u)/I^n M ≅ ker(u)/(I^n M ∩ ker u)`. By Artin-Rees, this is
surjected by `ker(u)/I^{n-c} ker(u)`, which is a finite module quotient.
This gives openness of u.

**Completion preserves exact sequences:**
If `0 → K → M → N → 0` is a short exact sequence of f.g. modules over a
noetherian I-adic ring, with all maps continuous and open, then the completed
sequence `0 → K̂ → M̂ → N̂ → 0` is exact.
*Proof:* K̂ = lim K/I^n K, M̂ = lim M/I^n M, N̂ = lim N/I^n N.
By Artin-Rees, `I^n M ∩ K` and `I^{n-c} K` are cofinal, so K̂ = lim K/(I^n M ∩ K).
The short exact sequence `0 → K/(I^n M ∩ K) → M/I^n M → N/I^n N → 0`
is exact for each n. Taking inverse limits (of surjective systems, hence exact)
gives the completed sequence.

### Steps

- [ ] Check if Artin-Rees is in mathlib (from TICKET-0). If not, prove it.
- [ ] Prove Prop 6.18(1) (canonical topology on f.g. modules)
- [ ] Prove Prop 6.18(2) (surjective ⟹ open)
- [ ] Prove completion preserves exact sequences for strict morphisms
- [ ] Package as API lemmas usable by TICKET-4

### Acceptance criteria

- All three results proved, no sorry
- Clean API for TICKET-4 to consume

---

## Summary Table

| Ticket | File | Lines | Depends on | Can parallel with | Difficulty |
|--------|------|-------|------------|-------------------|------------|
| **0** | (report) | N/A | — | — | Easy |
| **1A** | CechCohomology.lean | ~150 | 0 | 2A, 6 | Medium |
| **1B** | CechCohomology.lean | ~250 | 1A | 2B | Medium |
| **2A** | TateAlgebra.lean | ~150 | 0 | 1A, 6 | Medium |
| **2B** | TateAlgebra.lean | ~200 | 2A, 0 | 1B | Hard |
| **3** | FlatnessResults.lean | ~200 | 2B | — | Hard |
| **4** | LaurentCoverExact.lean | ~400 | 1A, 2B, 3, 6 | — | **Very Hard** |
| **5** | TateAcyclicity.lean | ~250 | 1B, 4 | — | Medium |
| **6** | OpenMapping.lean | ~200 | 0 | 1A, 2A | Hard |

**Parallel execution plan:**
- **Wave 1** (3 agents): TICKET-0, then {TICKET-1A, TICKET-2A, TICKET-6}
- **Wave 2** (2 agents): {TICKET-1B, TICKET-2B}
- **Wave 3** (1 agent): TICKET-3
- **Wave 4** (1 agent): TICKET-4
- **Wave 5** (1 agent): TICKET-5
