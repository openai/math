import OAI.Computability.NearSquareRoot.SynchronizedScheduleProgram

/-! # Semantics of serialized synchronized stages

For local words of different lengths, a row records an idle exactly at the
coordinates where the corresponding abstract layer has no operation.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace SynchronizedLayers.ScheduleProgram

open IntegerMultiplication IntegerMultiplication.Code

variable {X : Type} {n : ℕ} (kind : X → Kind)

/-- The tag and optional operations, in physical block order. -/
def serialize (s : Layer (fun _ : Fin n => X) (fun _ => kind)) :=
  (kindCode s.slot, List.ofFn s.action)

private theorem row_eq_serialize (s : Kind) (w : Fin n → List X) (t : ℕ) :
    row kind s (List.ofFn w, tally t) =
      serialize kind (slotLayer (fun _ => kind) s (fun i => (w i).drop t)) := by
  change (kindCode s, (List.ofFn w).map (fun v => ((v.map (mask kind s)).drop (tally t).length).headD none)) =
    (kindCode s, List.ofFn _)
  simp only [tally_length, List.map_ofFn]
  congr 1
  apply congrArg List.ofFn
  funext i
  change ((List.map (mask kind s) (w i)).drop t).headD none = ((w i).drop t).head?.bind (mask kind s)
  rw [← List.map_drop]
  cases (w i).drop t <;> rfl

private theorem cycles_eq_schedule (w : Fin n → List X) (D start : ℕ) :
    (List.ofFn (fun j : Fin D => tally (start + j.val))).flatMap (fun t => cycle kind (List.ofFn w,t)) =
      (schedule (fun _ => kind) D (fun i => (w i).drop start)).map (serialize kind) := by
  induction D generalizing start with
  | zero => rfl
  | succ D ih =>
    rw [List.ofFn_succ]
    simp only [List.flatMap_cons, Fin.val_zero, Nat.add_zero, Fin.val_succ, cycle, schedule, List.map_cons,
      List.cons_append, List.nil_append, row_eq_serialize]
    congr 1
    congr 1
    congr 1
    simpa only [List.tail_drop, cycle, Nat.add_right_comm start, Nat.add_assoc] using ih (start+1)

/-- The generated rows spell every slot of the mathematical schedule in order. -/
theorem plan_eq_schedule (w : Fin n → List X) (D : ℕ) :
    plan kind (List.ofFn w,tally D) =
      (schedule (fun _ => kind) D w).map (serialize kind) := by
  change (Iter.lineup (tally D)).flatMap _ = _
  rw [Iter.lined]
  simpa using cycles_eq_schedule kind w D 0

/-- Read one optional block operation from an encoded layer. -/
def readBlock (r : (Bool × Bool) × List (Option X)) (i : ℕ) : Option X :=
  r.2[i]?.join

@[simp] theorem readBlock_serialize (s : Layer (fun _ : Fin n => X) (fun _ => kind))
    (i : Fin n) : readBlock (serialize kind s) i.val = s.action i := by
  simp [readBlock, serialize, i.isLt]

/-- Removing idle fields from the generated rows recovers each input word. -/
theorem plan_executes (w : Fin n → List X) {D : ℕ} (hd : ∀ i, (w i).length ≤ D) (i : Fin n) :
    (plan kind (List.ofFn w,tally D)).filterMap (fun r => readBlock r i.val) = w i := by
  rw [plan_eq_schedule, List.filterMap_map]
  simpa [Function.comp_def] using schedule_executes (fun _ => kind) w hd i

/-- Interpreting the serialized rows with the given local gates computes
the tensor product of the original local circuits. -/
theorem plan_tensor {A : Fin n → Type*} [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
    {R : Type*} [CommSemiring R] (eval : ∀ i, X → Matrix (A i) (A i) R)
    (w : Fin n → List X) {D : ℕ} (hd : ∀ i, (w i).length ≤ D) :
    ((plan kind (List.ofFn w,tally D)).map (fun r => SynchronizedPadding.tensorMatrix
      (fun i => ((readBlock r i.val).map (eval i)).getD 1))).prod =
        SynchronizedPadding.tensorMatrix (fun i => ((w i).map (eval i)).prod) := by
  rw [plan_eq_schedule, List.map_map]
  have h (s : Layer (fun _ : Fin n => X) (fun _ => kind)) :
      (fun i : Fin n => ((readBlock (serialize kind s) i.val).map (eval i)).getD 1) =
        applyLayer (fun _ => kind) eval s := by
    funext i
    rw [readBlock_serialize]
    rfl
  simp only [Function.comp_def, h]
  exact schedule_tensor (fun _ => kind) eval w hd

end SynchronizedLayers.ScheduleProgram

end NearSquareRoot
end Computability
end OAI
