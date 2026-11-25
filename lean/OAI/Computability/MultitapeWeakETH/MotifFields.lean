import OAI.Computability.MultitapeWeakETH.HistoryField
import OAI.Computability.VPVNP.MotifEntry

/-! # Polynomial bit-tape reads of the finite motif table coordinates -/

namespace OAI.Computability.MultitapeWeakETH.MotifFields

open IntegerMultiplication Code Carry Staff Strip VPVNP StackInterpreter
noncomputable section

abbrev Input := Bits.Word × Tally

private def digit (a : ℕ) (q : Bool × Label (Fin (2^a))) : Label (Fin (2^(a+1))) :=
  ⟨⟨q.1.toNat + 2*q.2.val.val,by
    have h := q.2.val.isLt
    have b := Bool.toNat_le q.1
    rw [pow_succ]; omega⟩⟩

/-- The offset is unary, the field width belongs to the fixed finite motif, and a missing
high bit contributes zero. The machine returns an index into the finite parameter table. -/
def read : (a : ℕ) → Input → Label (Fin (2^a))
  | 0,_ => ⟨0⟩
  | a+1,q => digit a (Iter.pick false q,read a (q.1,()::q.2))

theorem read_poly (a : ℕ) : Poly (read a) := by
  induction a with
  | zero => exact Code.Poly.const _
  | succ a ih =>
    have next : Poly (fun q : Input => (q.1,()::q.2)) := by fun_prop
    exact (((Iter.facile false).poly.pair (next.compose ih)).compose (Easy.finite (digit a)).poly)

private theorem probe {w : ℕ} (x : Fin w → Bool) (start : ℕ) :
    Iter.pick false (List.ofFn x,tally start) = MotifEntry.paddedBit x start := by
  by_cases h : start<w
  · simpa only [MotifEntry.paddedBit,dite_eq_left h] using Iter.entry x ⟨start,h⟩ false
  · simp [Iter.pick,MotifEntry.paddedBit,h,List.drop_eq_nil_of_le (show (List.ofFn x).length≤start by simpa using Nat.le_of_not_gt h)]

theorem read_eq {w : ℕ} (x : Fin w → Bool) (a start : ℕ) :
    (read a (List.ofFn x,tally start)).val = MotifEntry.fieldIndex x start a := by
  induction a generalizing start with
  | zero => rfl
  | succ a ih =>
    apply Fin.ext
    change (Iter.pick false (List.ofFn x,tally start)).toNat + 2*(read a (List.ofFn x,()::tally start)).val.val = _
    rw [probe,← tally_succ,ih]
    rfl

private abbrev reg : Regime ((Bits.Word × Tally) × Tally) := ⟨size,send,Dom.base _⟩

/-- Start of copy i in a run of fixed-width fields above a variable payload. -/
def copy (a : ℕ) (q : (Bits.Word × Tally) × Tally) :=
  read a (q.1.1,tally (q.1.2.length+a*q.2.length))

theorem copy_poly (a : ℕ) : Poly (copy a) := by
  have base : Realizes reg (fun q => q.1.2.length) := by
    change Poly (fun q : (Bits.Word × Tally) × Tally => tally q.1.2.length)
    simpa only [recover_tally] using (Easy.fst (Y:=Tally) |>.compose (Easy.snd (X:=Bits.Word) (Y:=Tally))).poly
  have num : Realizes reg (fun q => q.2.length) := by
    change Poly (fun q : (Bits.Word × Tally) × Tally => tally q.2.length)
    simpa only [recover_tally] using (Easy.snd (X:=Bits.Word × Tally) (Y:=Tally)).poly
  exact ((Easy.fst.compose Easy.fst).poly.pair (base.plus ((Realizes.fix a).times num))).compose (read_poly a)

theorem copy_tag {u a v : ℕ} (x : Fin (v+u*a) → Bool) (i : Fin u) :
    (copy a ((List.ofFn x,tally v),tally i.val)).val = MotifEntry.readTag x i := by
  simp only [copy,tally_length,read_eq,MotifEntry.readTag]

end
end OAI.Computability.MultitapeWeakETH.MotifFields
