import OAI.Computability.NearSquareRoot.BoundedIndexedSweep
import OAI.Computability.NearSquareRoot.FixedCandidateAdmissible
import OAI.Computability.NearSquareRoot.FixedCandidateInterface
import OAI.Computability.NearSquareRoot.FixedLayerTickets

/-! # Physical execution of the full chronological transform

The same finite layer command consumes each short ticket on the forest tape.
Only one record bank and the unprocessed part of the ticket list remain live.
The length ruler is present at every boundary.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace FixedLayer

open IntegerMultiplication Code Space FixedCandidate ProductRecovery DigitPacking
open FixedPoint FixedLayerTickets ShortFourier.BatchWord

private theorem forest_getD {D : Type} [Codec D] (z : D) (l : List D) :
    Task.forest (fun j => send (l.getD j z)) (List.range l.length) = send l := by
  rw [← Task.forest_map send (fun j => l.getD j z), Task.forest_send]
  congr 1
  apply List.ext_getElem (by simp)
  intro i ha hb
  simp [List.getD, hb]

/-- A single indexed sweep, starting from the actual prepared list of chronological tickets. -/
theorem sweep {I D : Type} [Codec D] (z : D) (rows : I → List D)
    (state : I → ℕ → Tree) (a V work : I → ℕ)
    (step : BoundedTask (fun e : (i : I) × Fin (rows i).length => a e.1) (fun e => work e.1)
      (fun e => .fork (send ((rows e.1)[e.2.val])) (state e.1 e.2.val))
      (fun e => state e.1 (e.2.val+1)))
    (hv : ∀ i, (send (rows i)).count ≤ V i)
    (hs : ∀ i j, j ≤ (rows i).length → (state i j).count ≤ V i) :
    BoundedTask (fun i => (rows i).length*a i+V i) (fun i => V i+work i)
      (fun i => .fork (send (rows i)) (state i 0)) (fun i => state i (rows i).length) := by
  have run := BoundedTask.indexedSweep (fun i => (rows i).length)
    (fun i j => send ((rows i).getD j z)) state a V work
    (step.conform (fun _ => rfl) (fun _ => rfl) (fun e => by simp [List.getD, e.2.isLt])
      (fun _ => rfl)) (fun i => by rw [forest_getD]; exact hv i) hs
  simpa only [forest_getD] using run

noncomputable section

variable {n : ℕ} (h : Directory n)

def steps (F : Program h) : ℕ :=
  letI := BoxFin.modulus_neZero h
  F.count

/-- The tape array after j completed rows, in the original packed address numbering. -/
def stateAfter (F : Program h) (v : Array n) (j : ℕ) : Array n :=
  letI := BoxFin.modulus_neZero h
  F.run (v ∘ index h) j ∘ (index h).symm

theorem prefix_zero (F : Program h) (v : Array n) : stateAfter h F v 0 = v := by
  funext i
  simp [stateAfter, Layers.run]

theorem prefix_comp_index (F : Program h) (v : Array n) (j : ℕ) :
    letI := BoxFin.modulus_neZero h
    stateAfter h F v j ∘ index h = F.run (v ∘ index h) j := by
  funext i
  simp [stateAfter]

/-- Action of one stage on an already packed array. -/
def nextArray (F : Program h) (j : ℕ) (v : Array n) : Array n :=
  letI := BoxFin.modulus_neZero h
  F.apply j (v ∘ index h) ∘ (index h).symm

theorem prefix_succ (F : Program h) (v : Array n) (j : ℕ) :
    nextArray h F j (stateAfter h F v j) = stateAfter h F v (j+1) := by
  let _ := BoxFin.modulus_neZero h
  rw [nextArray, prefix_comp_index]
  rfl

/-- Energy range for an individual physical layer. -/
def working (v : Array n) : Prop :=
  letI := BoxFin.modulus_neZero h
  ‖recordArray (v ∘ index h)‖ ≤ (2:ℝ)^(13*addressBits n)

theorem prefix_working (F : Program h) (hk : 1 ≤ addressBits n) (v : Array n)
    (hadm : Admissible h v)
    (correct : ForwardOK h F ∨ InverseOK h F) {j : ℕ} (hj : j ≤ steps h F) :
    working h (stateAfter h F v j) := by
  let _ := BoxFin.modulus_neZero h
  unfold working
  rw [prefix_comp_index]
  cases correct with
  | inl hF => exact prefix_workingRange F hF hk _ hadm hj
  | inr hF => exact prefix_workingRange F hF hk _ hadm hj

variable {I : Type} (n : I → ℕ) (hv : ∀ i, Directory (n i)) (dir : I → Bool)

/-- The direct-order position is used by all physical row subroutines, even
though the machine traverses the word in reverse. -/
def rowKey (i : I) : Key := (dir i,tally (addressBits (n i)))

structure RowInput where
  instanceIndex : I
  position : Fin (directedPlan (rowKey n dir instanceIndex)).length
  payload : Array (n instanceIndex)
  inRange : working (hv instanceIndex) payload

def RowInput.ticket (e : RowInput n hv dir) : Ticket :=
  header (rowKey n dir e.instanceIndex,tally e.position.val)

abbrev Admitted := {e : (i : I) × Array (n i) // Admissible (hv e.1) e.2}

private theorem sweep_time_bound (C b a : ℕ) : a + C*(b+1)+1 ≤ (C+2)*(a+b+1) := by
  have h := Nat.mul_le_mul_left C (show b+1 ≤ a+b+1 by omega)
  rw [Nat.add_mul]
  omega

private theorem sweep_space_bound (C b : ℕ) : C*(b+1)+b+1 ≤ (C+2)*(b+1) := by
  rw [Nat.add_mul]
  omega

/-- Compose actual stage executions at every working input into a physical
transform on every admitted input. The array and ticket table fit linearly in
the input width. A separate arena bounds the peak workspace of a row. -/
theorem runProgramAt (area : I → ℕ) (fit : ∀ i, n i ≤ area i) (hn : ∀ i, 2 ≤ n i) (hk : ∀ i, 1 ≤ addressBits (n i))
    (F : ∀ i, Program (hv i))
    (len : ∀ i, steps (hv i) (F i) = (directedPlan (rowKey n dir i)).length)
    (ok : ∀ i, ForwardOK (hv i) (F i) ∨ InverseOK (hv i) (F i))
    (out : (i : I) → Fin (directedPlan (rowKey n dir i)).length → Array (n i) → Array (n i))
    (agree : ∀ i (j : Fin (directedPlan (rowKey n dir i)).length) u,
      nextArray (hv i) (F i) j.val u =
        out i ⟨(directedPlan (rowKey n dir i)).length-1-j.val, by omega⟩ u)
    (clock : ℕ → ℕ)
    (localRun : BoundedTask (fun e : RowInput n hv dir => clock (n e.instanceIndex))
      (fun e => area e.instanceIndex) (fun e => .fork (send (e.ticket n hv dir)) (framed e.payload))
      (fun e => framed (out e.instanceIndex e.position e.payload)))
    (prepare : BoundedTask (fun e : Admitted n hv => n e.val.1) (fun e => n e.val.1)
      (fun e => framed e.val.2)
      (fun e => .fork (send (chronological (rowKey n dir e.val.1))) (framed e.val.2)))
    (K : ℕ) (vol : ∀ i, (send (chronological (rowKey n dir i))).count ≤ K*(n i+1)) :
    BoundedTask (fun e : Admitted n hv => 3*boxDepth (addressBits (n e.val.1))*clock (n e.val.1) + n e.val.1)
      (fun e => area e.val.1) (fun e => framed e.val.2) (fun e => framed (eval (hv e.val.1) (F e.val.1) e.val.2)) := by
  let rows (e : Admitted n hv) := chronological (rowKey n dir e.val.1)
  let st (e : Admitted n hv) (j : ℕ) := stateAfter (hv e.val.1) (F e.val.1) e.val.2 j
  have rl (e : Admitted n hv) : (rows e).length = steps (hv e.val.1) (F e.val.1) :=
    (chronological_length _).trans (len _).symm
  let typ := (e : Admitted n hv) × Fin (rows e).length
  have inside (s : typ) : s.2.val < (directedPlan (rowKey n dir s.1.val.1)).length :=
    Nat.lt_of_lt_of_eq s.2.isLt (chronological_length _)
  let input (s : typ) : RowInput n hv dir :=
    let q := s.1.val.1
    let aj : Fin (directedPlan (rowKey n dir q)).length := ⟨s.2.val, by
      exact inside s⟩
    ⟨q,⟨(directedPlan (rowKey n dir q)).length-1-aj.val, by omega⟩,st s.1 aj.val,
      prefix_working (hv q) (F q) (hk q) _ s.1.property (ok q) ((rl _).le.trans' s.2.isLt.le)⟩
  have stage := localRun.on input
  have step : BoundedTask (fun s : typ => clock (n s.1.val.1)) (fun s => area s.1.val.1)
      (fun s => .fork (send ((rows s.1)[s.2.val])) (framed (st s.1 s.2.val)))
      (fun s => framed (st s.1 (s.2.val+1))) := by
    apply stage.conform (fun _ => rfl) (fun _ => rfl)
    · intro s
      congr 2
      exact (chronological_at _ ⟨s.2.val, inside s⟩).symm
    · intro s
      apply congrArg framed
      exact (agree s.1.val.1 ⟨s.2.val,inside s⟩ _).symm.trans
        (prefix_succ _ _ _ _)
  let C := K+75000
  let V (e : Admitted n hv) := C*(n e.val.1+1)
  have H := sweep (default : Ticket) rows (fun e j => framed (st e j))
    (fun e => clock (n e.val.1)) V (fun e => area e.val.1) step
    (fun e => (vol e.val.1).trans (Nat.mul_le_mul_right _ (Nat.le_add_right ..)))
    (fun e j _ => (framed_size (hn _) _).trans (Nat.mul_le_mul_right _ (Nat.le_add_left ..)))
  let t (e : Admitted n hv) := 3*boxDepth (addressBits (n e.val.1))*clock (n e.val.1) + n e.val.1
  have rlen (e : Admitted n hv) : (rows e).length = 3*boxDepth (addressBits (n e.val.1)) :=
    (chronological_length _).trans (directedPlan_length _ _)
  have main := H.bound (time' := t) (space' := fun e => area e.val.1) (C+2) (C+2) (fun e => by
    rw [rlen]
    exact sweep_time_bound C _ _) (fun e => by
      apply le_trans _ (sweep_space_bound C (area e.val.1))
      exact Nat.add_le_add_right (Nat.add_le_add_right (Nat.mul_le_mul_left _ (Nat.succ_le_succ (fit e.val.1))) _) _)
  have boot := prepare.mono (time' := t) (fun e => Nat.le_add_left ..) (fun e => fit e.val.1)
  apply sequence boot
  apply main.conform (fun _ => rfl) (fun _ => rfl)
  · intro e
    simp [rows,st,prefix_zero]
  · intro e
    rw [rl]
    rfl

/-- The linear-space instance of the chronological sweep. -/
theorem runProgram (hn : ∀ i, 2 ≤ n i) (hk : ∀ i, 1 ≤ addressBits (n i))
    (F : ∀ i, Program (hv i))
    (len : ∀ i, steps (hv i) (F i) = (directedPlan (rowKey n dir i)).length)
    (ok : ∀ i, ForwardOK (hv i) (F i) ∨ InverseOK (hv i) (F i))
    (out : (i : I) → Fin (directedPlan (rowKey n dir i)).length → Array (n i) → Array (n i))
    (agree : ∀ i (j : Fin (directedPlan (rowKey n dir i)).length) u,
      nextArray (hv i) (F i) j.val u =
        out i ⟨(directedPlan (rowKey n dir i)).length-1-j.val, by omega⟩ u)
    (clock : ℕ → ℕ)
    (localRun : BoundedTask (fun e : RowInput n hv dir => clock (n e.instanceIndex))
      (fun e => n e.instanceIndex) (fun e => .fork (send (e.ticket n hv dir)) (framed e.payload))
      (fun e => framed (out e.instanceIndex e.position e.payload)))
    (prepare : BoundedTask (fun e : Admitted n hv => n e.val.1) (fun e => n e.val.1)
      (fun e => framed e.val.2)
      (fun e => .fork (send (chronological (rowKey n dir e.val.1))) (framed e.val.2)))
    (K : ℕ) (vol : ∀ i, (send (chronological (rowKey n dir i))).count ≤ K*(n i+1)) :
    AdmissiblePass n hv (fun u => 3*boxDepth (addressBits u)*clock u + u)
      (fun i => eval (hv i) (F i)) :=
  runProgramAt n hv dir n (fun _ => le_rfl) hn hk F len ok out agree clock localRun prepare K vol

end
end FixedLayer

end NearSquareRoot
end Computability
end OAI
