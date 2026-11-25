import OAI.Hierarchy.ABPFirstCutStep
import OAI.Hierarchy.ABPFirstCutAvoid

namespace OAI
/-! # Coefficients of prefixes up to the first cut

At each branching-program vertex, `pending` retains the coefficient contributions of
paths that have avoided every cut so far. At a cut, `hit` collects precisely the
contributions arriving from such prefixes.
-/

namespace Hierarchy.ABPFirstCut

open scoped BigOperators

noncomputable section

variable {V : Type} {τ : V → Type} {F : Type*} [Field F] [DecidableEq V]

/-- The coefficient accumulated before any cut in the family has been visited. -/
def pending (family : Finset (Finset V)) (a : ∀ i, τ i) :
    {n : ℕ} → Rows F (Σ i, τ i) n → Fin n → Finset V → F
  | _, .source => fun _ S => if S = ∅ then 1 else 0
  | _, .snoc prev edges => Fin.lastCases
      (fun S => if S ∈ family then 0 else step a edges (pending family a prev) S)
      (pending family a prev)

/-- The coefficient arriving at a vertex along prefixes that avoided all earlier cuts.
Evaluated at a member of `family`, it is the first-hit coefficient for that cut. -/
def hit (family : Finset (Finset V)) (a : ∀ i, τ i) :
    {n : ℕ} → Rows F (Σ i, τ i) n → Fin n → Finset V → F
  | _, .source => fun _ _ => 0
  | _, .snoc prev edges => Fin.lastCases
      (step a edges (pending family a prev)) (hit family a prev)

variable (family : Finset (Finset V)) (a : ∀ i, τ i) {n : ℕ}
    (prev : Rows F (Σ i, τ i) n) (edges : List (Fin n × Affine F (Σ i, τ i)))

@[simp] theorem pending_source (t : Fin 1) (S : Finset V) :
    pending (F := F) family a .source t S = (if S = ∅ then 1 else 0) := rfl

@[simp] theorem hit_source (t : Fin 1) (S : Finset V) :
    hit (F := F) family a .source t S = 0 := rfl

@[simp] theorem pending_castSucc (t : Fin n) (S : Finset V) :
    pending family a (.snoc prev edges) t.castSucc S = pending family a prev t S := by
  simp [pending]

@[simp] theorem pending_last (S : Finset V) :
    pending family a (.snoc prev edges) (Fin.last n) S =
      (if S ∈ family then 0 else step a edges (pending family a prev) S) := by
  simp [pending]

@[simp] theorem hit_castSucc (t : Fin n) (S : Finset V) :
    hit family a (.snoc prev edges) t.castSucc S = hit family a prev t S := by
  simp [hit]

@[simp] theorem hit_last (S : Finset V) :
    hit family a (.snoc prev edges) (Fin.last n) S =
      step a edges (pending family a prev) S := by
  simp [hit]

theorem pending_eq_zero_of_not_avoids (rows : Rows F (Σ i, τ i) n) (t : Fin n) (S : Finset V)
    (hEmpty : ∅ ∉ family) (hAvoid : ¬ Avoids family S) : pending family a rows t S = 0 := by
  induction rows generalizing S with
  | source =>
    have h : S ≠ ∅ := by
      rintro rfl
      exact hAvoid (avoids_empty hEmpty)
    simp [h]
  | snoc prev edges ih =>
    induction t using Fin.lastCases with
    | last =>
      rw [pending_last]
      split_ifs with hS
      · rfl
      · apply step_eq_zero_of_local
        · exact fun t => ih t S hAvoid
        · exact fun t i hi => ih t (S.erase i) (fun h => hAvoid (avoids_of_erase hi hS h))
    | cast t => simpa only [pending_castSucc] using ih t S hAvoid

variable {a} {b : ∀ i, τ i}

theorem pending_congr (rows : Rows F (Σ i, τ i) n) (t : Fin n) (S : Finset V)
    (h : ∀ i ∈ S, a i = b i) : pending family a rows t S = pending family b rows t S := by
  induction rows generalizing S with
  | source => rfl
  | snoc prev edges ih =>
    induction t using Fin.lastCases with
    | last =>
      simp only [pending_last]
      split_ifs
      · rfl
      · exact step_congr edges S h fun t T hT => ih t T (fun i hi => h i (hT hi))
    | cast t => simpa only [pending_castSucc] using ih t S h

theorem hit_congr (rows : Rows F (Σ i, τ i) n) (t : Fin n) (S : Finset V)
    (h : ∀ i ∈ S, a i = b i) : hit family a rows t S = hit family b rows t S := by
  induction rows with
  | source => rfl
  | snoc prev edges ih =>
    induction t using Fin.lastCases with
    | last =>
      simp only [hit_last]
      exact step_congr edges S h fun t T hT =>
        pending_congr family prev t T (fun i hi => h i (hT hi))
    | cast t => simpa only [hit_castSucc] using ih t

end

end Hierarchy.ABPFirstCut

end OAI
