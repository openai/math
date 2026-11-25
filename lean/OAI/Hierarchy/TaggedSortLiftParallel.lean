import OAI.Hierarchy.TaggedSortLiftStage
import Mathlib.Data.Fintype.BigOperators

namespace OAI
/-! # Inlining disjoint block-sort schedules in parallel

The columns of an outer pass can use different internal wire layouts. At each
clock the disjoint union of their local blocks is a single global layer.
-/

namespace Hierarchy.Tagged.SortLift

open scoped BigOperators Classical
noncomputable section

variable {n : ℕ} {α κ : Type*} [LinearOrder κ]

def indexedStage {B : Type} [Fintype B] (w : B → ℕ)
    (i o : (Σ b, Fin (w b)) ≃ Fin n) : Stage n where
  blocks := Fintype.card B
  length c := w ((Fintype.equivFin B).symm c)
  input := (Equiv.sigmaCongrLeft (β := fun b => Fin (w b)) (Fintype.equivFin B).symm).trans i
  output := (Equiv.sigmaCongrLeft (β := fun b => Fin (w b)) (Fintype.equivFin B).symm).trans o

theorem indexed_eval {B : Type} [Fintype B] (w : B → ℕ) (i o : (Σ b, Fin (w b)) ≃ Fin n)
    (b : B) (j : Fin (w b)) (key : α → κ) (x : Fin n → α) :
    (indexedStage w i o).eval key x (o ⟨b,j⟩) =
      x (i ⟨b,Tuple.sort (fun r => key (x (i ⟨b,r⟩))) j⟩) := by
  obtain ⟨c,rfl⟩ := (Fintype.equivFin B).symm.surjective b
  exact (indexedStage w i o).eval_output key x c j

def refineRows {B : Type} {w : B → ℕ} {k : B → ℕ} {v : ∀ b, Fin (k b) → ℕ}
    (child : ∀ b, (Σ c, Fin (v b c)) ≃ Fin (w b)) (outer : (Σ b, Fin (w b)) ≃ Fin n) :
    (Σ z : (Σ b, Fin (k b)), Fin (v z.1 z.2)) ≃ Fin n :=
  (Equiv.sigmaAssoc fun b c => Fin (v b c)).trans ((Equiv.sigmaCongrRight child).trans outer)

def refineStage (S : Stage n) (T : ∀ b, Stage (S.length b)) : Stage n :=
  indexedStage (fun z : (Σ b, Fin (T b).blocks) => (T z.1).length z.2)
    (refineRows (fun b => (T b).input) S.input) (refineRows (fun b => (T b).output) S.output)

theorem refine_eval (S : Stage n) (T : ∀ b, Stage (S.length b))
    (key : α → κ) (x : Fin n → α) (b : Fin S.blocks) (r : Fin (S.length b)) :
    (refineStage S T).eval key x (S.output ⟨b,r⟩) =
      (T b).eval key (fun i => x (S.input ⟨b,i⟩)) r := by
  obtain ⟨⟨c,j⟩,rfl⟩ := (T b).output.surjective r
  rw [(T b).eval_output]
  exact indexed_eval (fun z : (Σ b : Fin S.blocks, Fin (T b).blocks) => (T z.1).length z.2)
    (refineRows (fun b => (T b).input) S.input)
    (refineRows (fun b => (T b).output) S.output) ⟨b,c⟩ j key x

theorem refine_width (S : Stage n) (T : ∀ b, Stage (S.length b)) (P : ℕ → Prop)
    (ok : ∀ b c, P ((T b).length c)) :
    ∀ z, P ((refineStage S T).length z) := fun _z => ok _ _

def sameOutput (S : Stage n) : Stage n := { S with input := S.output }

/-- Place the child stages on the parent output layout after the first parallel pass. -/
def parallel (S : Stage n) : (d : ℕ) → (∀ b, Fin d → Stage (S.length b)) → List (Stage n)
  | 0, _ => []
  | d+1, T => refineStage S (fun b => T b 0) ::
      parallel (sameOutput S) d (fun b i => T b i.succ)

theorem parallel_length (S : Stage n) (d : ℕ) (T : ∀ b, Fin d → Stage (S.length b)) :
    (parallel S d T).length = d := by
  induction d generalizing S with
  | zero => rfl
  | succ d ih => exact congrArg Nat.succ (ih (sameOutput S) (fun b i => T b i.succ))

theorem parallel_width (S : Stage n) (d : ℕ) (T : ∀ b, Fin d → Stage (S.length b))
    (P : ℕ → Prop) (ok : ∀ b i c, P ((T b i).length c)) :
    ∀ U ∈ parallel S d T, ∀ z, P (U.length z) := by
  induction d generalizing S with
  | zero => simp [parallel]
  | succ d ih =>
    intro U hU
    rcases List.mem_cons.mp hU with rfl | later
    · exact refine_width S _ P (fun b => ok b 0)
    · exact ih (sameOutput S) (fun b i => T b i.succ) (fun b i => ok b i.succ) _ later

theorem parallel_eval (S : Stage n) (d : ℕ) (T : ∀ b, Fin d → Stage (S.length b))
    (key : α → κ) (x : Fin n → α) (start : d = 0 → S.input = S.output)
    (b : Fin S.blocks) (r : Fin (S.length b)) :
    run (parallel S d T) key x (S.output ⟨b,r⟩) =
      run (List.ofFn (T b)) key (fun i => x (S.input ⟨b,i⟩)) r := by
  induction d generalizing S x with
  | zero =>
    simpa [parallel,run] using congrArg (fun e : (Σ b, Fin (S.length b)) ≃ Fin n => x (e ⟨b,r⟩)) (start rfl).symm
  | succ d ih =>
    rw [List.ofFn_succ]
    let U := refineStage S (fun b => T b 0)
    have result := ih (sameOutput S) (fun b i => T b i.succ) (U.eval key x) (by intro; rfl) b r
    refine result.trans ?_
    have slice : (fun i : Fin (S.length b) => U.eval key x (S.output ⟨b,i⟩)) =
        (T b 0).eval key (fun i => x (S.input ⟨b,i⟩)) :=
      funext fun i => refine_eval S _ key x b i
    exact congrArg (fun y : Fin (S.length b) → α =>
      run (List.ofFn (fun i : Fin d => T b i.succ)) key y r) slice

end
end Hierarchy.Tagged.SortLift

end OAI
