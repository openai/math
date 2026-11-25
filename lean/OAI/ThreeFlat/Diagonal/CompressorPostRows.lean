import OAI.ThreeFlat.Diagonal.CompressorTemplateGraph
import OAI.ThreeFlat.Diagonal.CompressorSixColumns

namespace OAI
/-! # The row selected at an absolute successor graph address -/
namespace ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkStage.Template
open Computability.VPVNP.Compression Computability.VPVNP.BurstRAM Computability.VPVNP.BurstRAM.PrivateRAM RAM.PhysicalPinsExpr RAM.DescriptorExpr Placement
open scoped Fin.NatCast
variable {w : ℕ} (cell : Word w) (m : Memory w) (vs : Fin 1 → Word w)
local notation "V" => Formula.value (fun _=>cell) m vs

private theorem select_fin {a : ℕ} (q : F) (body : Fin a → F) (i : Fin a)
    (fit : a≤2^w) (value : V q=(i.val:Word w)) (xs : List (Fin a)) (h : i∈xs) :
    V (xs.foldr (fun j tail=>.select .eq q (.lit j.val) (body j) tail) (.lit 0))=V (body i) := by
  induction xs with
  | nil => simp at h
  | cons j xs ih =>
    have eq : ((i.val:Word w)=(j.val:Word w)) ↔ i=j := by
      constructor
      · intro e
        apply Fin.ext
        simpa only [Fin.val_cast_of_lt (i.isLt.trans_le fit),Fin.val_cast_of_lt (j.isLt.trans_le fit)]
          using congrArg Fin.val e
      · rintro rfl
        rfl
    by_cases yes : i=j
    · subst j
      simp [Formula.value,Comparison.test,Fin.ofNat_eq_cast,value]
    · change (if Comparison.eq.test (V q) (j.val:Word w) then _ else _)=_
      simp only [Comparison.test,value,beq_iff_eq,eq,ite_eq_right yes]
      exact ih ((List.mem_cons.mp h).resolve_left yes)

theorem column_read (S : Graph.Stage) (lay : Bool) (i : Fin 6)
    (lo len row : ℕ) (fit : 6≤2^w) (lenFits : len<2^w) (within : row<len)
    (top : lo+i.val*len+row<2^w) (start : V (f nextGraph)=(lo:Word w)) (length : V (f nextSlots)=(len:Word w))
    (here : vs 0=((lo+i.val*len+row:ℕ):Word w)) (selectedWord : V (f selected)=if lay then 1 else 0)
    (one : (1:Word w)≠0) :
    V (graph S false)=V (update S lay (decide (3≤ i.val))
      (![Graph.Field.neighbor,.matePort,.delta,.neighbor,.matePort,.delta] i)
      (column o (f nextGraph) (f nextSlots) i.val)) := by
  let q := Formula.op .div (.op .sub (.reg 0) (f nextGraph)) (f nextSlots)
  have hq : V q=(i.val:Word w) := by
    change BinaryOp.div.eval (vs 0-V (f nextGraph)) (V (f nextSlots))=_
    rw [here,start,length,Nat.cast_add,Nat.cast_add]
    have e (a b c : Word w) : a+b+c-a=b+c := by abel
    rw [e,←Nat.cast_add,op_cast .div (i.val*len+row) len ⟨by omega,lenFits⟩]
    simp [natOp,Nat.mul_comm i.val len,Nat.mul_add_div (Nat.zero_lt_of_lt within),Nat.div_eq_of_lt within]
  let entry (layout : Bool) (j : Fin 6) := update S layout (decide (3 ≤ j.val))
    (![Graph.Field.neighbor,.matePort,.delta,.neighbor,.matePort,.delta] j)
    (column o (f nextGraph) (f nextSlots) j.val)
  have dispatch (layout : Bool) := select_fin cell m vs q (entry layout) i fit hq _ (List.mem_finRange i)
  cases lay <;>
    simp only [graph,Formula.value,Comparison.test,selectedWord,Fin.ofNat_eq_cast,Nat.cast_one,
      beq_iff_eq,Ne.symm one,Bool.false_eq_true,ite_false,ite_true,eq_self]
  · exact dispatch false
  · exact dispatch true

theorem identifier_read (S : Graph.Stage) (lay : Bool)
    (selectedWord : V (f selected)=if lay then 1 else 0) (one : (1:Word w)≠0) :
    V (graph S true)=V (update S lay false .identifier (f keys)) := by
  cases lay <;> simp [graph,Formula.value,Comparison.test,selectedWord,Ne.symm one]


end ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkStage.Template

end OAI
