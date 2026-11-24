import OAI.Computability.VPVNP.RAMTapeRecordWord
import OAI.Computability.VPVNP.RAMSortBlockSlices

/-!
# Completing the serialized pre-sort block

Each unused record slot contributes five all-zero words. The remaining-slot
counter controls padding independently of the values in the accumulated
records. The last pass reverses the whole buffer once to expose records and
their word bits in the order consumed by the first sorting layer.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.RecordBuffer

open Routine

private def zeros : ℕ → FiniteRoutine Port
  | 0 => .ret
  | k+1 => (appendWord .zeros).followedBy (zeros k)

/-- Append one zero record for each unary mark left after probe emission. -/
def pad : FiniteRoutine Port := .ofRoutine
  (popLoop Port.remaining (fun _ => true) (halt false) (zeros 5).body)

/-- Pop the completed reverse buffer onto the output stack. -/
def reverse : FiniteRoutine Port := .ofRoutine
  (popLoop Port.reverseBuffer (fun _ => true) (push Port.output false) (push Port.output true))

/-- Pad every unused slot with a zero record, then reverse the buffer to obtain the sorting
input in record order. -/
def close : FiniteRoutine Port := pad.followedBy reverse

private def cells (s : Stacks Port) (remaining : ℕ) (buf out : List Bool) : Stacks Port
  | .remaining => List.replicate remaining true
  | .reverseBuffer => buf
  | .output => out
  | j => s j

private theorem set_remaining (s : Stacks Port) (k k' : ℕ) (buf out : List Bool) :
    Function.update (cells s k buf out) .remaining (List.replicate k' true) = cells s k' buf out := by
  funext i; cases i <;> simp [cells]

private theorem set_buffer (s : Stacks Port) (k : ℕ) (buf out b : List Bool) :
    Function.update (cells s k buf out) .reverseBuffer b = cells s k b out := by
  funext i; cases i <;> simp [cells]

private theorem set_output (s : Stacks Port) (k : ℕ) (buf out o : List Bool) :
    Function.update (cells s k buf out) .output o = cells s k buf o := by
  funext i; cases i <;> simp [cells]

private theorem zeros_run (s : Stacks Port) {w : ℕ} (ht : s .temp = []) (hz : s .zeros = List.replicate w false)
    (t k : ℕ) (buf out : List Bool) :
    (zeros t).Runs (t*(5*w+2)+1) (cells s k buf out)
      (cells s k (List.replicate (t*w) false ++ buf) out) := by
  induction t generalizing buf with
  | zero => simpa [zeros, FiniteRoutine.ret, FiniteRoutine.Runs, FiniteRoutine.ofRoutine] using runs_ret (cells s k buf out)
  | succ t ih =>
    have h := appendWord_run (src := .zeros) (by decide) (by decide) (cells s k buf out) ht
    change (appendWord .zeros).Runs (5*(s .zeros).length+2) _ (Function.update _ _ ((s .zeros).reverse ++ buf)) at h
    rw [hz, List.reverse_replicate, List.length_replicate, set_buffer] at h
    have H := h.followedBy (ih (List.replicate w false ++ buf))
    rw [show 5*w+2+(t*(5*w+2)+1) = (t+1)*(5*w+2)+1 by ring] at H
    simpa only [zeros, Nat.succ_mul, List.replicate_add, List.append_assoc] using H

private theorem pad_run (s : Stacks Port) {w : ℕ} (ht : s .temp = []) (hz : s .zeros = List.replicate w false)
    (k : ℕ) (buf out : List Bool) :
    pad.Runs (k*(25*w+12)+1) (cells s k buf out)
      (cells s 0 (List.replicate (k*(5*w)) false ++ buf) out) := by
  induction k generalizing buf with
  | zero =>
    simp only [Nat.zero_mul, Nat.zero_add, List.replicate_zero, List.nil_append]
    exact Runs.popLoop_empty Port.remaining (fun _ => true) (halt false) (zeros 5).body (s := cells s 0 buf out) rfl
  | succ k ih =>
    have head : cells s (k+1) buf out .remaining = true :: List.replicate k true := List.replicate_succ
    have hb := zeros_run s ht hz 5 k buf out
    have H := Runs.popLoop_true_continue Port.remaining (fun _ => true) (halt false) (zeros 5).body head rfl
      (by rw [set_remaining]; exact hb) (ih (List.replicate (5*w) false ++ buf))
    rw [show 1+(5*(5*w+2)+1)+(k*(25*w+12)+1) = (k+1)*(25*w+12)+1 by ring] at H
    simpa only [pad, FiniteRoutine.ofRoutine, Nat.succ_mul, List.replicate_add, List.append_assoc] using H

private theorem reverse_run (s : Stacks Port) (k : ℕ) (buf out : List Bool) :
    reverse.Runs (2*buf.length+1) (cells s k buf out) (cells s k [] (buf.reverse++out)) := by
  induction buf generalizing out with
  | nil => exact Runs.popLoop_empty Port.reverseBuffer (fun _ => true) (push Port.output false) (push Port.output true) (s := cells s k [] out) rfl
  | cons b xs ih =>
    have head : cells s k (b::xs) out .reverseBuffer = b::xs := rfl
    have hb := runs_push Port.output b (cells s k xs out)
    change (push Port.output b).Runs 1 _ (Function.update _ .output (b::out)) at hb
    rw [set_output] at hb
    have H := Runs.popLoop_continue Port.reverseBuffer (fun _ => true) (push Port.output false) (push Port.output true)
      head rfl (by rw [set_buffer]; cases b <;> exact hb) (ih (b::out))
    rw [show 1+1+(2*xs.length+1) = 2*(xs.length+1)+1 by omega] at H
    simpa only [reverse, FiniteRoutine.ofRoutine, FiniteRoutine.Runs, List.length_cons, List.reverse_cons,
      List.append_assoc, List.singleton_append] using H

/-- Closing adds the exact prescribed suffix of zero bits. It clears the
slot counter and reverse buffer, and preserves the five field registers,
the zero template, and the empty scratch stack. -/
theorem close_run (s : Stacks Port) (w k : ℕ) (buf : List Bool) (ht : s .temp = [])
    (hz : s .zeros = List.replicate w false) (hk : s .remaining = List.replicate k true)
    (hb : s .reverseBuffer = buf.reverse) (ho : s .output = []) :
    close.Runs (k*(25*w+12)+1 + (2*(buf.length+k*(5*w))+1)) s
      (Function.update (Function.update (Function.update s .remaining []) .reverseBuffer [])
        .output (buf ++ List.replicate (k*(5*w)) false)) := by
  have h₁ := pad_run s ht hz k buf.reverse []
  have h₂ := reverse_run s 0 (List.replicate (k*(5*w)) false ++ buf.reverse) []
  have h := h₁.followedBy h₂
  have hi : cells s k buf.reverse [] = s := by funext j; cases j <;> simp [cells, hk, hb, ho]
  have hout (x : List Bool) : cells s 0 [] x =
      Function.update (Function.update (Function.update s .remaining []) .reverseBuffer []) .output x := by
    funext j; cases j <;> simp [cells]
  rw [hi, hout] at h
  simpa only [close, List.length_append, List.length_replicate, List.length_reverse, List.reverse_append,
    List.reverse_replicate, List.reverse_reverse, List.append_nil, Nat.add_comm (k*(5*w))] using h


open RAMSerialization

/-- The same byte sequence emitted by consecutive `appendRecord` calls. -/
def serialized {w : ℕ} (hw : 2 ≤ w) (records : List (Option (WordRecord w))) : List Bool :=
  records.flatMap (fun r => List.ofFn ((recordFormat hw).encode r))

theorem block_serialized {w H : ℕ} (hw : 2 ≤ w) (block : Fin (4*H) → Option (WordRecord w)) :
    List.ofFn ((blockFormat H hw).encode block) = serialized hw (List.ofFn block) := by
  let bits := (blockFormat H hw).encode block
  have cast : 4*H*5*w = (4*H)*(5*w) := Nat.mul_assoc _ _ _
  rw [List.ofFn_congr cast ((blockFormat H hw).encode block), List.ofFn_mul]
  rw [serialized, List.flatMap_def, List.map_ofFn]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext i
  apply congrArg List.ofFn
  funext j
  have h := congrFun (blockEncode_slice H hw block i) j
  change bits ⟨i.val*(5*w)+j.val, _⟩ = _
  apply Eq.trans _ h
  apply congrArg bits
  apply Fin.ext
  change i.val*(5*w)+j.val = i.val*5*w+j.val
  ring

private theorem padding_serialized {w : ℕ} (hw : 2 ≤ w) (k : ℕ) :
    serialized hw (List.replicate k none) = List.replicate (k*(5*w)) false := by
  induction k with
  | zero => simp [serialized]
  | succ k ih =>
    rw [List.replicate_succ, serialized, List.flatMap_cons, recordFormat_empty, List.ofFn_const,
      ← serialized, ih, ← List.replicate_add]
    apply congrArg (fun a => List.replicate a false)
    ring

/-- When the existing records followed by the vacant slots describe a
complete block, the output is its canonical sorting-exchange encoding. -/
theorem close_block {w H : ℕ} (hw : 2 ≤ w) (k : ℕ) (s : Stacks Port)
    (records : List (Option (WordRecord w))) (block : Fin (4*H) → Option (WordRecord w))
    (hblock : List.ofFn block = records ++ List.replicate k none)
    (ht : s .temp = []) (hz : s .zeros = List.replicate w false) (hk : s .remaining = List.replicate k true)
    (hb : s .reverseBuffer = (serialized hw records).reverse) (ho : s .output = []) :
    close.Runs (k*(25*w+12)+1 + (2*(4*H*5*w)+1)) s
      (Function.update (Function.update (Function.update s .remaining []) .reverseBuffer [])
        .output (List.ofFn ((blockFormat H hw).encode block))) := by
  have he : List.ofFn ((blockFormat H hw).encode block) =
      serialized hw records ++ List.replicate (k*(5*w)) false := by
    rw [block_serialized, hblock, serialized, List.flatMap_append, ← serialized, ← serialized,
      padding_serialized]
  have hlen := congrArg List.length he
  simp only [List.length_ofFn, List.length_append, List.length_replicate] at hlen
  rw [he, hlen]
  exact close_run s w k (serialized hw records) ht hz hk hb ho

end RAMTape.RecordBuffer

end VPVNP
end Computability
end OAI
