import OAI.ThreeFlat.RAM.TickAuxRequestWord
import OAI.ThreeFlat.RAM.ExpressionScan
import OAI.ThreeFlat.RAM.TickBitAddress

namespace OAI
/-! # Streaming two four-word records per bit for native comparison -/

namespace ThreeFlat.RAM.TickRequestStream

open Computability.VPVNP.BurstRAM PrivateRAM DescriptorExpr Diagonal.TickAuxiliary TickBitRelation
open scoped Fin.CommRing

variable {w k : ℕ}

def program (start : ℕ) (rule : Term w k 1) : Term w k 1 :=
  let delta := Term.binary .sub (.result 0) (.literal (start : Word w))
  let idx := Term.binary .div delta (.literal 8)
  let col := Term.binary .mod delta (.literal 8)
  (TickAuxRequestWord.program w k).instantiate ![rule.instantiate (fun _ => idx),idx,col]

theorem program_binds (start : ℕ) (rule : Term w k 1) :
    (program start rule).binds ≤ rule.binds+220 := by
  have h := TickAuxRequestWord.program_binds w k
  simp [program, Term.binary, Term.literal, Term.binds, Fin.sum_univ_succ]
  omega

def dataWord (start : ℕ) (rule : ℕ → Rule) (address : ℕ) : Word w :=
  let i := (address-start)/8
  let d : Fin 8 := ⟨(address-start)%8,Nat.mod_lt _ (by decide)⟩
  TickAuxRequestWord.columns (paddedRequest (rule i) (TickAuxRequestWord.slot d) (i : Word w))
    (TickAuxRequestWord.index d)

theorem dataWord_at (start : ℕ) (rule : ℕ → Rule) (i : ℕ) (d : Fin 8) :
    dataWord (w:=w) start rule (start+8*i+d.val) =
      (paddedRequest (rule i) (TickAuxRequestWord.slot d) (i : Word w)).column
        (TickAuxRequestWord.index d) := by
  have hd := d.isLt
  have hi : (start+8*i+d.val-start)/8 = i := by omega
  have hc : (⟨(start+8*i+d.val-start)%8,Nat.mod_lt _ (by decide)⟩ : Fin 8) = d := by
    apply Fin.ext
    change (start+8*i+d.val-start)%8 = d.val
    omega
  simp only [dataWord,hi,hc]
  rfl

theorem filled_prepared {a : ℕ} (start : ℕ) (rule : ℕ → Rule) (m : Memory w)
    (fit : start+8*a ≤ 2^w) :
    ChunkRequests.preparedRows (fillSegment start (8*a) (dataWord start rule) m)
      (start : Word w) 4 (a*2) = rangeRows (fun j : Fin a => rule j.val) 0 := by
  apply preparedRangeRows_nat (fun j : Fin a => rule j.val) _ fit
  intro i d
  have hi := i.isLt
  have hd := d.isLt
  rw [fillSegment, ite_eq_left (show start ≤ start+8*i.val+d.val ∧ start+8*i.val+d.val < start+8*a by omega)]
  exact dataWord_at start rule i.val d

/-- The continuation may compute the rule by arbitrary native reads. The
address decomposition itself uses two native operations after subtraction. -/
theorem program_eval {a : ℕ} (start : ℕ) (rule : ℕ → Rule) (e : Term w k 1)
    (par : Fin k → Word w) (mem : Memory w) (addr : Word w) (lo : start ≤ addr.val)
    (hi : addr.val < start+8*a) (fit : 64 ≤ 2^w)
    (correct : ∀ i : Fin a, e.eval par mem (fun _ => (i.val : Word w)) = ((rule i.val).tag : Word w)) :
    (program start e).eval par mem (fun _ => addr) = dataWord start rule addr.val := by
  let i : Fin a := ⟨(addr.val-start)/8,by omega⟩
  let d : Fin 8 := ⟨(addr.val-start)%8,Nat.mod_lt _ (by decide)⟩
  let delta : Term w k 1 := Term.binary .sub (Term.result (0 : Fin 1)) (Term.literal (start : Word w))
  let idx := Term.binary .div delta (Term.literal 8)
  let col := Term.binary .mod delta (Term.literal 8)
  let v : Fin 1 → Word w := fun _ => addr
  have small := addr.isLt
  have sd : addr.val-start < 2^w := by omega
  have hdelta : delta.eval par mem v = ((addr.val-start : ℕ) : Word w) := by
    rw [Nat.cast_sub lo]
    change addr - (start : Word w) = (addr.val : Word w) - (start : Word w)
    have hcast : (addr.val : Word w) = addr := Fin.ext (Nat.mod_eq_of_lt addr.isLt)
    rw [hcast]
  have eight : (8 : Word w).val = 8 := Nat.mod_eq_of_lt (show (8 : ℕ) < 2^w by omega)
  have hidx : idx.eval par mem v = (i.val : Word w) := by
    simp only [idx, Term.eval_binary, Term.eval_literal, hdelta, BinaryOp.eval,
      Fin.val_cast_of_lt sd, eight]
    rfl
  have hcol : col.eval par mem v = (d.val : Word w) := by
    simp only [col, Term.eval_binary, Term.eval_literal, hdelta, BinaryOp.eval,
      Fin.val_cast_of_lt sd, eight]
    rfl
  let args := ![e.instantiate (fun _ => idx),idx,col]
  change ((TickAuxRequestWord.program w k).instantiate args).eval par mem v = _
  rw [Term.eval_instantiate]
  apply TickAuxRequestWord.program_eval fit (rule i.val) (i.val : Word w) d par mem
  · change (e.instantiate (fun _ => idx)).eval par mem v = _
    rw [Term.eval_instantiate]
    simpa only [hidx] using correct i
  · exact hidx
  · exact hcol

end ThreeFlat.RAM.TickRequestStream

end OAI
