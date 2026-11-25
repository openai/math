import OAI.ThreeFlat.RAM.TickTerminalPinJobs
import OAI.ThreeFlat.RAM.TickTerminalRootRun

namespace OAI
/-! # Saving a selected terminal root's pin map in its own interval -/

namespace Hierarchy.TraceReceiverMapSave
open ThreeFlat RAM DescriptorExpr DescriptorScan
open Computability.VPVNP.BurstRAM PrivateRAM PhysicalProcedure
open RAM.TickTerminalRoot RAM.HistoryTerminalTape
open scoped Classical Fin.CommRing

variable {W p ports : ℕ}

/-- Native command preparation keeps each cached endpoint located below the
temporary terminal seed bank. All wire incidences depend only on the original
public half table and retain their numbering through the preparation. -/
theorem ready_incidences (A : Arena) (m : Memory W) (bounds : RootBounds A m)
    (π : Fin ports → Fin p)
    (inc : Incidences (terminal A (natMemory m)) (natMemory m) m π)
    (endpointBefore : let T:=terminal A (natMemory m); T.endpoints+T.ext ≤ A.seed) :
    Incidences (terminal A (natMemory m)) (natMemory m) (readyImage A m) π := by
  refine ⟨?_,inc.covered,inc.wire⟩
  intro k hk
  let T := terminal A (natMemory m)
  change k.val < T.ext at hk
  change T.endpoints+T.ext ≤ A.seed at endpointBefore
  have lo : T.endpoints+k.val < A.seed := by omega
  have first := bounds.first
  have apart := bounds.disjoint
  have belowCommands : T.endpoints+k.val < A.commands := by omega
  have belowArguments : T.endpoints+k.val < A.arguments := by omega
  have same : readyImage A m (T.endpoints+k.val)=m (T.endpoints+k.val) := by
    simp only [readyImage,commandImage,seedImage,fillSegment,not_le.mpr lo,
      not_le.mpr belowCommands,not_le.mpr belowArguments,false_and,ite_false]
  exact same.trans (inc.endpoint k hk)

/-- The final metadata job and the four-word control update preserve every
disjoint pin of the selected terminal's scratch map. -/
theorem pin_output (A : Arena) (m : Memory W) (π : Fin ports → Fin p)
    (k : Fin ports) (inc : Incidences (terminal A (natMemory m)) (natMemory m) (readyImage A m) π)
    (ctrl : A.map+k.val≠((A.seed+5 : ℕ):Word W).val)
    (metaFree : let T := terminal A (natMemory m)
      A.map+k.val < T.meta ∨ T.meta+4*T.rows ≤ A.map+k.val)
    (saveFree : A.map+k.val < A.control ∨ A.control+4 ≤ A.map+k.val) :
    output A m (A.map+k.val) = ((2+(π k).val : ℕ) : Word W) := by
  let T := terminal A (natMemory m)
  let raw := natMemory m
  let r := readyImage A m
  let cur : Word W := ((A.seed+5 : ℕ) : Word W)
  let mid := pinMemory T raw cur r
  change PhysicalInputCopy.copied _ _ _ _ _=_
  rw [PhysicalInputCopy.copied_outside _ _ _ _ _ saveFree]
  change HistoryReadyTape.after cur (TickTerminalPrimitive.jobs T raw cur r) r _=_
  unfold TickTerminalPrimitive.jobs
  rw [HistoryReadyTape.after_append]
  have afterLast : HistoryReadyTape.after cur [TickTerminalPrimitive.joinedJob T mid] mid (A.map+k.val)
      = mid (A.map+k.val) := by
    apply HistoryReadyTape.after_away _ _ _ _ ctrl
    intro job member
    obtain rfl := List.mem_singleton.mp member
    exact metaFree
  exact afterLast.trans (pin_after T raw cur r π inc k ctrl)

/-- The copy reads its destination from the same indirect header that drives
the native scan. Its source is the common scratch bank used by the root routine. -/
def expression (W src current : ℕ) : Term W 0 1 :=
  .load (.binary .add (.literal src) (.binary .sub (.result 0) (.load (.load (.literal current)))))

private theorem expression_eval (src current : ℕ) (mem : Memory W) (a : Word W) :
    (expression W src current).eval Fin.elim0 mem (fun _ => a) =
      mem ((src : Word W)+(a-mem (mem (current : Word W).val).val)).val := by
  simp only [expression,Term.eval_load,Term.eval_binary,Term.eval_literal]
  rfl

def procedure (W : ℕ) (A : Arena) (current : ℕ) : Procedure W :=
  HeaderScan.procedure (current : Word W) 0 1 (expression W A.map current)

def one (W : ℕ) (A : Arena) (current : ℕ) : Procedure W :=
  (TickTerminalRoot.one W A).seq (procedure W A current)

theorem copy (A : Arena) (current dst n : ℕ) (m : Memory W)
    (endFit : dst+n < 2^W) (srcFit : A.map+n ≤ 2^W)
    (lo : m (m (current : Word W).val).val=(dst : Word W))
    (len : m (m (current : Word W).val+1).val=(n : Word W))
    (ptrOff : (current : Word W).val < dst ∨ dst+n ≤ (current : Word W).val)
    (hdrOff : (m (current : Word W).val).val < dst ∨ dst+n ≤ (m (current : Word W).val).val)
    (apart : A.map+n ≤ dst ∨ dst+n ≤ A.map) :
    (procedure W A current).Spec (·=m)
      (fun _ out => out=fillSegment dst n (fun a=>m (A.map+(a-dst))) m) (13+22*n) := by
  intro _ _ _ machine
  have work : (expression W A.map current).binds ≤ 9 := by
    simp [expression,Term.binary,Term.load,Term.literal,Term.binds]
  have cost : 13+n*(2*(expression W A.map current).binds+4) ≤ 13+22*n := by
    have step := Nat.mul_le_mul_left n (show 2*(expression W A.map current).binds+4 ≤ 22 by omega)
    simpa only [Nat.mul_comm 22 n] using Nat.add_le_add_left step 13
  refine Procedure.Spec.atMemory (A:=procedure W A current)
    (HeaderScan.spec (current:Word W) 0 1 (expression W A.map current)
      (fun state => state=m) (fun _ => dst) (fun _ => n)
      (fun _ a => m (A.map+(a-dst))) _ (fun _ _ => ⟨endFit,cost⟩) ?_ ?_) m rfl machine
  · intro state eq
    subst state
    exact ⟨by simpa using lo,by simpa using len⟩
  · intro state eq a mem low high same
    subst state
    rw [expression_eval]
    rw [same _ ptrOff,same _ hdrOff,lo]
    have dstVal : (dst:Word W).val=dst := Fin.val_cast_of_lt (by omega)
    have ge : (dst:Word W) ≤ a := by change (dst:Word W).val ≤ a.val; rwa [dstVal]
    have delta : (a-(dst:Word W)).val=a.val-dst :=
      (Fin.sub_val_of_le ge).trans (by rw [dstVal])
    have address : ((A.map:Word W)+(a-(dst:Word W))).val=A.map+(a.val-dst) := by
      calc
        _ = ((A.map:Word W)+((a-(dst:Word W)).val:Word W)).val :=
          congrArg (fun t : Word W=>((A.map:Word W)+t).val) (Fin.cast_val_eq_self _).symm
        _ = _ := by rw [←Nat.cast_add,delta,Fin.val_cast_of_lt (by omega)]
    rw [address]
    exact same _ (by omega)

/-- Execute the scratch-root routine and immediately copy its pin map to the
persistent, task-specific base before another root reuses the scratch rows. -/
theorem run (A : Arena) (current dst n : ℕ) (m : Memory W) (bounds : RootBounds A m)
    (endFit : dst+n < 2^W) (srcFit : A.map+n ≤ 2^W)
    (lo : let out:=output A m; out (out (current : Word W).val).val=(dst : Word W))
    (len : let out:=output A m; out (out (current : Word W).val+1).val=(n : Word W))
    (ptrOff : (current : Word W).val < dst ∨ dst+n ≤ (current : Word W).val)
    (hdrOff : let h := (output A m (current : Word W).val).val; h < dst ∨ dst+n ≤ h)
    (apart : A.map+n ≤ dst ∨ dst+n ≤ A.map) :
    (one W A current).Spec (·=m)
      (fun _ out => out=fillSegment dst n (fun a=>output A m (A.map+(a-dst))) (output A m))
      (oneCost W A (terminal A (natMemory m)) (natMemory m)+(13+22*n)) := by
  intro _ _ _ machine
  exact Procedure.Spec.mono (A:=one W A current)
    (Procedure.Spec.seq (A:=TickTerminalRoot.one W A) (B:=procedure W A current) (one_spec A m bounds)
      (copy A current dst n (output A m) endFit srcFit lo len ptrOff hdrOff apart)
      (fun _ _ h=>h)) (fun _ h=>h) (fun _ _ h=>h.choose_spec.2) le_rfl machine

theorem saved_pin (A : Arena) (m : Memory W) (dst : ℕ) (π : Fin ports → Fin p)
    (k : Fin ports) (inc : Incidences (terminal A (natMemory m)) (natMemory m) (readyImage A m) π)
    (ctrl : A.map+k.val≠((A.seed+5 : ℕ):Word W).val)
    (metaFree : let T := terminal A (natMemory m)
      A.map+k.val < T.meta ∨ T.meta+4*T.rows ≤ A.map+k.val)
    (saveFree : A.map+k.val < A.control ∨ A.control+4 ≤ A.map+k.val) :
    fillSegment dst ports (fun a=>output A m (A.map+(a-dst))) (output A m) (dst+k.val)
      = ((2+(π k).val : ℕ) : Word W) := by
  have inside : dst ≤ dst+k.val ∧ dst+k.val < dst+ports := by have := k.isLt; omega
  simpa [fillSegment,inside] using pin_output A m π k inc ctrl metaFree saveFree

end Hierarchy.TraceReceiverMapSave

end OAI
