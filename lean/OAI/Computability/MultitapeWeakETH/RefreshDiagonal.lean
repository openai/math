import OAI.Computability.MultitapeWeakETH.RefreshEntry
import OAI.Computability.VPVNP.CompressorRefreshDiagonalFrame

/-! # The two bit-string comparisons in a refresh entry -/

namespace OAI.Computability.MultitapeWeakETH.RefreshOperands

open IntegerMultiplication Code VPVNP BurstRAM CompressorRecords PhaseRecipe Compression Compression.Refresh
open Compression.DegreeRefresh PortRefresh OperandInputs NewSlots StackInterpreter TerminalWords
open PairSimulation NodeArguments RefreshMapOperands NetworkKernel
open scoped Fin.CommRing
noncomputable section

variable {A : Type} [Codec A] (eval : Expr → Query A → Bits.Word) (ep : ∀ e, Poly (eval e))

/-- A length is the native word difference of the old endpoints. Read the same
number of bits from the old slot and the corresponding new external segment. -/
def compareSpan (start stop seg : Expr) (x : Query A) : Bool :=
  let len := capped (eval (stop.sub start) x,x.2.2)
  decide (OperandSpan.span ((x.2.1.1,eval start x),len) = OperandSpan.span ((x.2.1.2,eval seg x),len))

include ep in
theorem compareSpan_poly (start stop seg : Expr) : Poly (compareSpan eval start stop seg) := by
  have len := ((ep (stop.sub start)).pair (Easy.snd.compose Easy.snd).poly).compose capped_poly
  have left : Poly (fun x : Query A => x.2.1.1) := by fun_prop
  have right : Poly (fun x : Query A => x.2.1.2) := by fun_prop
  have r₁ := (((left.pair (ep start)).pair len).compose OperandSpan.span_poly)
  have r₂ := (((right.pair (ep seg)).pair len).compose OperandSpan.span_poly)
  exact (r₁.pair r₂).compose NearSquareRoot.Benes.easyWordEq.poly

omit [Codec A] in
theorem compareSpan_eq {w l : ℕ} (wide : 0<w) (x : Query A) (C : LevelRecipe.Context w)
    (run : ∀ e, eval e x = wordBits (C.eval e)) (start stop seg : Expr) (base other : ℕ)
    (pos : C.eval start = (base : BurstRAM.Word w)) (target : C.eval seg = (other : BurstRAM.Word w))
    (finish : C.eval stop = (base : BurstRAM.Word w) + (l : BurstRAM.Word w))
    (room : l < 2^w) (bound : l ≤ x.2.2.length) (u v : Fin l → Bool)
    (lhs : ∀ i : Fin l, OperandSpan.memory x.2.1.1 ((base+i.val : ℕ) : BurstRAM.Word w) = PrimedInputRAM.encodeBit w (u i))
    (rhs : ∀ i : Fin l, OperandSpan.memory x.2.1.2 ((other+i.val : ℕ) : BurstRAM.Word w) = PrimedInputRAM.encodeBit w (v i)) :
    compareSpan eval start stop seg x = decide (u=v) := by
  classical
  have len : C.eval (stop.sub start) = (l : BurstRAM.Word w) := by
    change C.eval stop - C.eval start = _
    rw [finish,pos,add_sub_cancel_left]
  have size : capped (eval (stop.sub start) x,x.2.2) = tally l := by
    rw [run,len]
    simp only [capped,NativeGrid.value_native,Fin.val_natCast,Nat.mod_eq_of_lt room,Nat.min_eq_left bound]
  unfold compareSpan
  rw [size,run,run,pos,target]
  dsimp only
  rw [OperandSpan.span_eq wide _ _ _ lhs,OperandSpan.span_eq wide _ _ _ rhs]
  simp [List.ofFn_injective.eq_iff]

variable {k : Type} [_root_.Field k] {S : BlockSchedule k} (B : S.Templates)

def diagonalExpr := DiagonalFrame.fields (2^S.portExponent) (refreshSlots S.degree_bounds.2 (Sum.inl 0))
  (input (RefreshBlockPlan.shape B))

def guard (x : Query A) :=
  compareSpan eval (diagonalExpr B 0) (diagonalExpr B 1) (diagonalExpr B 2) x &&
  compareSpan eval (diagonalExpr B 3) (diagonalExpr B 4) (diagonalExpr B 5) x

include ep in
theorem guard_poly : Poly (guard eval B) := by
  convert Poly.choose (compareSpan_poly eval ep (diagonalExpr B 0) (diagonalExpr B 1) (diagonalExpr B 2))
    (compareSpan_poly eval ep (diagonalExpr B 3) (diagonalExpr B 4) (diagonalExpr B 5)) (Code.Poly.const false) using 1
  funext x
  unfold guard
  cases compareSpan eval (diagonalExpr B 0) (diagonalExpr B 1) (diagonalExpr B 2) x <;> rfl

end
end OAI.Computability.MultitapeWeakETH.RefreshOperands
