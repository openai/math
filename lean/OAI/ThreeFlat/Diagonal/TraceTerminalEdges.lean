import OAI.ThreeFlat.Diagonal.ProgramEdgeCount
import OAI.ThreeFlat.Diagonal.PhysicalRecordFamily
import OAI.ThreeFlat.Diagonal.PhysicalShrinkBase
import OAI.ThreeFlat.Diagonal.PhysicalCardinalTransport
import OAI.ThreeFlat.Diagonal.ProgramDirectory
import OAI.ThreeFlat.Diagonal.NavigationDirectory

namespace OAI
/-! # The publicly indexed edge and width spans of a retained terminal graph -/

namespace ThreeFlat.Diagonal.PhysicalStage.Program
open scoped Classical
noncomputable section
variable {F : Type} [Field F]

private theorem cast_edges {d l l' n : ℕ} (e : l=l') (A : State d l) (R : Run F (e ▸ A : State d l'))
    (fixed : ∀ h,(R.terminalLayer h).state.edgeCount=n) :
    ∀ h,((recast e A R).terminalLayer h).state.edgeCount=n := by cases e;exact fixed

private theorem next_card {d l D D' L n : ℕ} {A : State d l} (e : D=D') (R : Move F A D L)
    (all : ∀j,Fintype.card (R.next j).Base=n) : ∀j,Fintype.card ((recastMove e R).next j).Base=n := by
  cases e;exact all

private theorem step_edges {d l D L : ℕ} {A : State d l}
    (R : Move F A D L) (next : ∀ j, Run F (R.next j))
    (h : (Run.step R next).plan.History) :
    ((Run.step R next).terminalLayer h).state.edgeCount =
      ((next h.1).terminalLayer (Run.tailHistory R next h)).state.edgeCount := rfl

set_option maxHeartbeats 850000 in
theorem finalEdges_eq {s : ℕ} (P : Program F s) (rem : ℕ) (X : State (2^s) (P.charge+rem)) :
    ∀ h,((P.run rem X).terminalLayer h).state.edgeCount=P.finalEdges rem (Fintype.card X.Base) := by
  induction P with
  | done s =>
    intro h
    change (Fintype.card X.Base*2^s)*2^(0+rem)=_
    simp [finalEdges]
  | shrink s t G small tail ih =>
    let b:=tail.charge+rem
    let e:=Nat.add_assoc (shrinkCharge s) tail.charge rem
    let B : State (2^s) (shrinkCharge s+b):=e ▸ X
    let M:=shrinkBinary G s (2^t) b (Nat.two_pow_pos _) (by exact_mod_cast small) B
    let nxt:=fun j=>tail.run rem (M.next j)
    apply cast_edges e X (.step M nxt)
    intro h
    have size:=shrinkBinary_next_base G s (2^t) b (Nat.two_pow_pos _) (by exact_mod_cast small) B h.1
    refine (step_edges M nxt h).trans ?_
    calc _ = tail.finalEdges rem (Fintype.card (M.next h.1).Base) := ih (M.next h.1) (Run.tailHistory M nxt h)
         _ = _ := by rw [size,baseCast e X];rfl
  | refresh s t h pad c γ C G hm hh sym rows zero conn deg tail ih =>
    let b:=tail.charge+rem
    let e:=Nat.add_assoc s tail.charge rem
    let B : State (2^s) (s+b):=e ▸ X
    let R:=refreshBinary G B hm hh sym rows zero conn
    let M:=recastMove deg R
    let nxt:=fun j=>tail.run rem (M.next j)
    apply cast_edges e X (.step M nxt)
    intro hist
    have size:=next_card deg R (refreshBinary_next_base G B hm hh sym rows zero conn) hist.1
    refine (step_edges M nxt hist).trans ?_
    calc _ = tail.finalEdges rem (Fintype.card (M.next hist.1).Base) := ih (M.next hist.1) (Run.tailHistory M nxt hist)
         _ = _ := by rw [size,baseCast e X];rfl

end
end ThreeFlat.Diagonal.PhysicalStage.Program

namespace ThreeFlat.Diagonal.PhysicalStage
open scoped Classical
noncomputable section
variable {F : Type} [Field F]

def Program.terminalExponent : {s : ℕ} → Program F s → ℕ
  | s,.done _ => s
  | _,.shrink _ _ _ _ tail => tail.terminalExponent
  | _,.refresh _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ tail => tail.terminalExponent

theorem Program.finalEdges_le {s : ℕ} (P : Program F s) (r v : ℕ) :
    P.finalEdges r v≤2^P.terminalExponent*(v*2^(P.charge+r)) := by
  induction P generalizing v with
  | done s =>
    simp only [Program.finalEdges,Program.terminalExponent,Program.charge,Nat.zero_add]
    exact le_of_eq (by ring)
  | shrink s t G ok tail ih =>
    let tag:=CompressorPacking.tagBits (2^s)
    apply (ih (v*2^tag)).trans (Nat.mul_le_mul_left _ _)
    rw [Nat.mul_assoc,←pow_add]
    apply Nat.mul_le_mul_left
    apply Nat.pow_le_pow_right (by decide)
    change tag + (tail.charge + r) ≤ (shrinkCharge s + tail.charge) + r
    dsimp only [tag, shrinkCharge]
    omega
  | refresh s t h pad c γ C G hm hh sym rows zero conn degree tail ih =>
    apply (ih (v*2^s)).trans
    simp only [Program.charge,Program.terminalExponent,pow_add,Nat.mul_assoc,le_refl]

theorem Program.terminalExponent_cast {s t : ℕ} (e : s=t) (P : Program F s) :
    (e ▸ P : Program F t).terminalExponent=P.terminalExponent := by cases e;rfl

theorem Block.terminalExponent_shrinkPrefix (B : Block F) (n i : ℕ) (tail : Program F (B.exponent (i+n))) :
    (B.shrinkPrefix n i tail).terminalExponent=tail.terminalExponent := by
  induction n generalizing i with
  | zero => rfl
  | succ n ih => simp only [Block.shrinkPrefix,Program.terminalExponent,ih,Program.terminalExponent_cast]

theorem Block.terminalExponent_repeat (B : Block F) (n : ℕ) :
    (B.repeat n).terminalExponent=B.exponent 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simpa only [Block.repeat,Block.prefix,B.terminalExponent_shrinkPrefix,Program.terminalExponent_cast,
      Program.terminalExponent] using ih

end
end ThreeFlat.Diagonal.PhysicalStage

namespace ThreeFlat.Diagonal.NavigationPass
open NavigationDirectory

theorem width_before_heap (K : ℕ) (ss : List Stage) (c : Cursor) (hi : c.width≤c.heap) :
    (finish K ss c).width≤(finish K ss c).heap := by
  induction ss generalizing c with
  | nil => exact hi
  | cons s ss ih =>
    apply ih
    cases s <;> simp only [allocate,CompressorPacking.Native.ShrinkStage.extra_extent,RefreshStageLayout.extra_extent] <;> omega

end ThreeFlat.Diagonal.NavigationPass

end OAI
