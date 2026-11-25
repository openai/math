import OAI.Computability.MultitapeWeakETH.HiddenLookup
import OAI.Computability.MultitapeWeakETH.OperandSpan
import OAI.Computability.VPVNP.PairShrinkOldHalfAddresses

/-! # A bit-tape implementation of the private old-child packet memory -/

namespace OAI.Computability.MultitapeWeakETH.NamedPackets

open IntegerMultiplication Code VPVNP BurstRAM BurstRAM.PrivateRAM PairSimulation NodeArguments
open NativeGrid TerminalWords
open scoped Fin.CommRing
noncomputable section

abbrev Bank := List Bits.Word × List Bits.Word
abbrev Input := (Bank × Bits.Word) × Bits.Word

/-- Memory words are bit values. Child frames begin at the node ordinal times
a common positive stride; the frame contents are the supplied, variable-size packets. -/
theorem cell_program :
    ∃ read : Input → Bool, Poly read ∧ ∀ {w : ℕ} (bank : Bank) (stride node : ℕ) (bs : Bits.Word),
      let A : Arena := ⟨0,stride⟩
      let P : Packet := ⟨node,bs⟩
      let mem (addr : Word w) := PrivateFields.bitValue w (read ((bank,wordBits (stride : Word w)),wordBits addr))
      stride < 2^w → bs.length ≤ stride → node*stride + bs.length ≤ 2^w →
      ShrinkHidden.fetch (wordBits (node : Word w),bank) = bs →
      P.Fits A w 0 ∧ P.Stored A (DFS.scratch 0 mem) := by
  obtain ⟨div,dc,dv⟩ := WordExpression.binary_program .div
  obtain ⟨mod,mc,mv⟩ := WordExpression.binary_program .mod
  let args (q : Input) := (q.2,q.1.2)
  let read (q : Input) := OperandSpan.cell (ShrinkHidden.fetch (div (args q),q.1.1),mod (args q))
  have ap : Poly args := (Easy.snd.pair (Easy.fst.compose Easy.snd)).poly
  have cp : Poly read := ((((ap.compose dc).pair (Easy.fst.compose Easy.fst).poly).compose ShrinkHidden.fetch_poly).pair
    (ap.compose mc)).compose OperandSpan.cell_poly
  refine ⟨read,cp,?_⟩
  intro w bank stride node bs A P mem sf len space found
  have base : A.base node = node*stride := Nat.zero_add _
  refine ⟨⟨Nat.zero_le _,len,base.symm ▸ space⟩,?_⟩
  intro i
  have bi : i.val < bs.length := i.isLt
  have si : i.val < stride := bi.trans_le len
  have positive := Nat.zero_lt_of_lt si
  let addr : Word w := ((node*stride+i.val : ℕ) : Word w)
  have number : addr.val = node*stride+i.val := Fin.val_cast_of_lt ((Nat.add_lt_add_left bi _).trans_le space)
  have quo : BinaryOp.div.eval addr (stride : Word w) = (node : Word w) := by
    change Fin.ofNat _ (addr.val/(stride : Word w).val) = _
    rw [number,Fin.val_cast_of_lt sf,Nat.mul_comm node stride,Nat.mul_add_div positive,Nat.div_eq_of_lt si,Nat.add_zero]
    rfl
  have rem : BinaryOp.mod.eval addr (stride : Word w) = (i.val : Word w) := by
    change Fin.ofNat _ (addr.val%(stride : Word w).val) = _
    rw [number,Fin.val_cast_of_lt sf,Nat.mul_add_mod_self_right,Nat.mod_eq_of_lt si]
    rfl
  change rawScratch (DFS.scratch 0 mem) ((A.base node+i.val : ℕ) : Word w) = PrivateFields.bitValue w bs[i.val]
  rw [base]
  apply congrArg (PrivateFields.bitValue w)
  change OperandSpan.cell (ShrinkHidden.fetch (div (wordBits addr,wordBits (stride : Word w)),bank),
    mod (wordBits addr,wordBits (stride : Word w))) = _
  rw [dv,mv,quo,rem,found]
  simp only [OperandSpan.cell,capped,value_native,Fin.val_cast_of_lt (si.trans sf),ruler_length,
    Nat.min_eq_left bi.le,Iter.search _ _ _ bi]

end
end OAI.Computability.MultitapeWeakETH.NamedPackets
