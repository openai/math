import OAI.Computability.MultitapeWeakETH.WordExpression
import OAI.Computability.VPVNP.CompressorRefreshMapOperands

/-! # Reading native operand ranges from packed node arguments -/

namespace OAI.Computability.MultitapeWeakETH.OperandSpan

open IntegerMultiplication Code VPVNP BurstRAM Compression PairSimulation NodeArguments
open NativeGrid TerminalWords CompressorRecords
open private address address_poly address_eq from OAI.Computability.MultitapeWeakETH.TerminalColumns
open scoped Fin.CommRing
noncomputable section

/-- A node argument occupies its own bit tape, starting at offset zero. -/
def cell (q : Bits.Word × Bits.Word) : Bool :=
  Iter.pick false (q.1,capped (q.2,ruler q.1))

theorem cell_poly : Poly cell :=
  (Easy.fst.poly.pair ((Easy.snd.pair (Easy.ruler Easy.fst)).poly.compose capped_poly)).compose (Iter.facile false).poly

def memory (bs : Bits.Word) {w : ℕ} (addr : Word w) :=
  PrimedInputRAM.encodeBit w (cell (bs,wordBits addr))

/-- The private node-buffer convention of the refresh geometry holds on the actual
packed bits, even for independent incoming and outgoing assignments of a loop. -/
theorem node_fields {w a g : ℕ} (X : State a g) (v : X.network.Site) (h : X.network.Half v)
    (fit : (packed X v h).length ≤ 2^w) :
    RefreshMapOperands.NodeFields ⟨0,0⟩ 0 X v h (memory (w:=w) (packed X v h)) := by
  intro dir j i
  obtain ⟨pre,post,rows,location⟩ := packed_member X v h dir j
  have inside := i.isLt
  have len : (packed X v h).length = pre.length + X.halfWidth v dir j + post.length := by simp [rows,Nat.add_assoc]
  have small : pre.length+i.val < 2^w := by omega
  simp only [memory,Arena.fieldAddress,Arena.base,Nat.zero_mul,Nat.zero_add]
  apply congrArg (PrimedInputRAM.encodeBit w)
  rw [← location]
  have valid : pre.length+i.val < (packed X v h).length := by omega
  simp only [cell,capped,value_native,Fin.val_natCast,Nat.mod_eq_of_lt small,ruler_length,
    Nat.min_eq_left valid.le,Iter.search _ _ _ valid]
  simp only [rows,List.append_assoc,List.getElem_append_right (Nat.le_add_right ..),Nat.add_sub_cancel_left,
    List.getElem_append_left (by simp : i.val < (List.ofFn (fieldBits X v h dir j)).length),
    List.getElem_ofFn]


abbrev Input := (Bits.Word × Bits.Word) × Tally

/-- Read a run of bits at successive addresses from a single node tape. The
counter and addition use the native word width. -/
def span (q : Input) := (Iter.lineup q.2).map fun i => cell (q.1.1,address (q.1.2,i))

theorem span_poly : Poly span := by
  have base : Poly (fun q : (Bits.Word × Bits.Word) × Tally => q.1.2) := by fun_prop
  have one := ((Easy.fst.compose Easy.fst).poly.pair ((base.pair Easy.snd.poly).compose address_poly)).compose cell_poly
  exact (Easy.fst.poly.pair (Easy.snd.poly.compose Iter.poly_line)).compose (Poly.push ([],[]) [] one)

theorem span_eq {w l : ℕ} (wide : 0 < w) (bs : Bits.Word) (start : ℕ) (v : Fin l → Bool)
    (data : ∀ i : Fin l, memory bs ((start+i.val : ℕ) : Word w) = PrimedInputRAM.encodeBit w (v i)) :
    span ((bs,wordBits (start : Word w)),tally l) = List.ofFn v := by
  simp only [span,Iter.lined,List.map_ofFn,Function.comp_def,address_eq]
  apply congrArg List.ofFn
  funext i
  have h := data i
  simp only [memory,Nat.cast_add] at h
  have one : (1 : Word w) ≠ 0 := fun eq => by
    have clash := congrArg Fin.val eq
    simp at clash
    omega
  cases hv : cell (bs,wordBits ((start : Word w)+(i.val : Word w))) <;> cases hb : v i <;>
    simp_all [PrimedInputRAM.encodeBit]

end
end OAI.Computability.MultitapeWeakETH.OperandSpan
