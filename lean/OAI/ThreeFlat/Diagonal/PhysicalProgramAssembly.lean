import OAI.ThreeFlat.Diagonal.PhysicalShrinkAssembly
import OAI.ThreeFlat.Diagonal.PhysicalRefreshWords
import OAI.ThreeFlat.Diagonal.PhysicalStageProgram

namespace OAI
/-! # Concrete history forests along a sequence of physical binary passes -/

noncomputable section
namespace ThreeFlat.Diagonal.PhysicalStage
open HistoryContraction
open scoped Classical BigOperators

variable {F Pins : Type} [Field F]

/-- Apply the actual shrink and refresh assemblers to every chosen history.
The count, owner order and word-bit encoding are computed at each node from
its current state. -/
def Program.assembly {s : ℕ} (P : Program F s) (rem : ℕ) (A : State (2^s) (P.charge+rem)) :
    (P.run rem A).Assembler Pins := by
  induction P with
  | done s => exact ⟨PUnit.unit⟩
  | shrink s t T small tail ih =>
    let e := Nat.add_assoc (shrinkCharge s) tail.charge rem
    let B : State (2^s) (shrinkCharge s+(tail.charge+rem)) := e ▸ A
    let R := shrinkBinary T s (2^t) (tail.charge+rem) (Nat.two_pow_pos _) (by exact_mod_cast small) B
    let next := fun i => tail.run rem (R.next i)
    exact Run.inputAssembler e A (.step R next)
      (Run.assembleStep R next (shrinkBinary_assembler T s (2^t) _ _ _ B)
        (fun i => ih (R.next i)))
  | refresh s t h pad c γ C T hm hh sym rows zero conn degree tail ih =>
    let e := Nat.add_assoc s tail.charge rem
    let B : State (2^s) (s+(tail.charge+rem)) := e ▸ A
    let R := refreshBinary T B hm hh sym rows zero conn
    let M := recastMove degree R
    let next := fun i => tail.run rem (M.next i)
    exact Run.inputAssembler e A (.step M next)
      (Run.assembleStep M next
        (Move.outputAssembler degree R (refreshBinary_assembler T B hm hh sym rows zero conn))
        (fun i => ih (M.next i)))

def Program.onLanes {s lanes : ℕ} (P : Program F s) (rem : ℕ)
    (A : State (2^s) lanes) (e : lanes=P.charge+rem) : Run F A :=
  recast e A (P.run rem (e ▸ A))

def Program.assembleOnLanes {s lanes : ℕ} (P : Program F s) (rem : ℕ)
    (A : State (2^s) lanes) (e : lanes=P.charge+rem) :
    (P.onLanes rem A e).Assembler Pins :=
  Run.inputAssembler e A _ (P.assembly rem _)

end ThreeFlat.Diagonal.PhysicalStage

namespace ThreeFlat.Diagonal.PhysicalStage.Program
open HistoryContraction
open scoped Classical BigOperators
noncomputable section
variable {F Pins : Type} [Field F]

attribute [local irreducible] shrinkBinary shrinkBinary_assembler

set_option maxHeartbeats 600000 in
/-- The positive run and the retained journal instantiate the same head
assembler and the same branch-indexed tail, including the lane alignment. -/
theorem assembly_shrink_step (s t : ℕ) (T : ShrinkMotif.Table F)
    (small : ((2^(2*(2^s)+1)*(2^s)*(2^s):ℕ):ℝ)/2^t≤1/1024)
    (tail : Program F t) (rem : ℕ) (A : State (2^s) ((Program.shrink s t T small tail).charge+rem)) :
    let e:=Nat.add_assoc (shrinkCharge s) tail.charge rem
    let B : State (2^s) (shrinkCharge s+(tail.charge+rem)):=e ▸ A
    let size : ((2^(2*(2^s)+1)*(2^s)*(2^s):ℕ):ℝ)/(2^t:ℕ)≤1/1024 := by exact_mod_cast small
    let R:=shrinkBinary T s (2^t) (tail.charge+rem) (Nat.two_pow_pos _) size B
    let next:=fun i=>tail.run rem (R.next i)
    (Program.shrink s t T small tail).assembly (Pins := Pins) rem A =
      Run.inputAssembler (Pins := Pins) e A (.step R next)
      (Run.assembleStep (Pins := Pins) R next (shrinkBinary_assembler (Pins := Pins) T s (2^t) (tail.charge+rem) (Nat.two_pow_pos _) size B)
        (fun i=>(tail.assembly rem (R.next i) : (next i).Assembler Pins))) := rfl

theorem assembly_refresh_step (s t h pad : ℕ) (c : Fin (2^s)→Fin (2^s)→ℕ) (γ C : ℝ)
    (T : RefreshMotif.Table F c (1+h+pad) C) (hm : 2≤2^s) (hh : 0<h)
    (sym : ∀i j,c i j=c j i) (rows : ∀i,∑j,c i j=h) (zero : ∀i,c i i=0)
    (conn : Expander.Bound (Expander.transition c h) ℝ γ) (degree : 1+h+pad=2^t)
    (tail : Program F t) (rem : ℕ)
    (A : State (2^s) ((Program.refresh s t h pad c γ C T hm hh sym rows zero conn degree tail).charge+rem)) :
    let e:=Nat.add_assoc s tail.charge rem
    let B : State (2^s) (s+(tail.charge+rem)):=e ▸ A
    let R:=refreshBinary T B hm hh sym rows zero conn
    let M:=recastMove degree R
    let next:=fun i=>tail.run rem (M.next i)
    ((Program.refresh s t h pad c γ C T hm hh sym rows zero conn degree tail).assembly rem A : _)=
      Run.inputAssembler e A (.step M next) (Run.assembleStep M next
        (Move.outputAssembler degree R (refreshBinary_assembler T B hm hh sym rows zero conn))
        (fun i=>(tail.assembly rem (M.next i) : (next i).Assembler Pins))) := rfl

end

end ThreeFlat.Diagonal.PhysicalStage.Program

end
end OAI
