import OAI.Hierarchy.ProtocolRAMCalendarStripPorts
import OAI.Hierarchy.ProtocolRAMBoughtCatalogue

namespace OAI
/-! # A repair occurrence may refer only to core edges or its own originating purchase -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.CatalogueRows
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage CoreBoard AdaptiveProbe BoughtSockets PurchaseFrozen
open ThreeFlat.RAM DescriptorExpr
open scoped Fin.CommRing Classical
variable {w : ℕ} {C H A B : Type*} {h d k : ℕ} {S : PurchaseSampler}

def Board.CoreOrPad (b : Board) (value : Word w) : Prop := value.val<b.coreRows ∨ value.val=b.rows

theorem Board.coreOnly_cases (b : Board) (u : Expr) (m : Memory w) (r : Word w) (room : b.rows<2^w) :
    b.CoreOrPad ((b.coreOnly u).eval m r) := by
  have core : b.coreRows<2^w:=by unfold rows at room;omega
  unfold CoreOrPad coreOnly
  simp only [Expr.eval,Comparison.test,decide_eq_true_eq,Fin.lt_def,Fin.val_cast_of_lt core]
  split
  · exact Or.inl (by assumption)
  · exact Or.inr (Fin.val_cast_of_lt room)

theorem StripPorts.primary_cases (p : StripPorts S h d k C H B) (b : Board)
    (e : ColumnWires.Role C H (A⊕B) k) (m : Memory w) (r : Word w) (room : b.rows<2^w) :
    b.CoreOrPad ((p.primary b e).eval m r) ∨
    ∃ origin : B,e=.extra (.inr origin) ∧ (p.primary b e).eval m r=(p.probe origin).eval m r := by
  cases e with
  | catalyst c j => exact .inl (b.coreOnly_cases _ m r room)
  | radius c j side => exact .inl (b.coreOnly_cases _ m r room)
  | cross c j s t => exact .inl (b.coreOnly_cases _ m r room)
  | horizontal i l => exact .inl (b.coreOnly_cases _ m r room)
  | extra t =>
    cases t with
    | inl => exact .inl (.inr (Fin.val_cast_of_lt room))
    | inr u => exact .inr ⟨u,rfl,rfl⟩

theorem physicalEdge_val (b : Board) (keep raw : Expr) (m : Memory w) (r : Word w) (room : b.rows<2^w) :
    ((StripChart.physicalEdge b keep raw).eval m r).val=
      if (raw.eval m r).val<b.coreRows then (raw.eval m r).val else if (raw.eval m r).val<b.rows then
        if keep.eval m r=0 then b.rows else (raw.eval m r).val else b.rows := by
  have core:b.coreRows<2^w:=by unfold Board.rows at room;omega
  simp only [StripChart.physicalEdge,Expr.eval,Comparison.test,decide_eq_true_eq,Fin.lt_def,beq_iff_eq,
    Nat.cast_zero,Fin.val_cast_of_lt core,Fin.val_cast_of_lt room]
  split_ifs <;> first | rfl | exact Fin.val_cast_of_lt room

/-- The raw ordinal may be evaluated in different state snapshots; core-edge and
padding comparisons use no mutable purchase flag. -/
theorem physicalEdge_core (b : Board) (keep raw other : Expr) (m out : Memory w) (r r' : Word w)
    (room : b.rows<2^w) (same : raw.eval m r=other.eval out r') (bounded : b.CoreOrPad (raw.eval m r)) :
    (StripChart.physicalEdge b keep raw).eval m r=(b.checkedEdge other).eval out r' := by
  apply Fin.ext
  rw [physicalEdge_val _ _ _ _ _ room,b.checkedEdge_val _ _ _ room,←same]
  rcases bounded with h|h
  · simp [h]
  · have lower : b.coreRows≤b.rows:=Nat.le_add_right _ _
    simp [h,Nat.not_lt_of_ge lower]

/-- The acquired case reads exactly the archived cell of its own known event
and original signed-DFS ordinal. Agreement on that one persistent cell suffices. -/
theorem physicalEdge_birth (b : Board) (keep raw other : Expr) (m out : Memory w) (r r' : Word w)
    (j : Fin b.boughtRows) (room : b.rows<2^w) (same : raw.eval m r=other.eval out r')
    (value : raw.eval m r=((b.coreRows+j.val:ℕ):Word w))
    (flag : keep.eval m r=b.bought.flag.eval out (j.val:Word w)) :
    (StripChart.physicalEdge b keep raw).eval m r=(b.checkedEdge other).eval out r' := by
  apply Fin.ext
  rw [physicalEdge_val _ _ _ _ _ room,b.checkedEdge_val _ _ _ room,←same,value,flag]
  have st : ((b.coreRows+j.val:ℕ):Word w)-(b.coreRows:Word w)=(j.val:Word w):=by rw [Nat.cast_add];abel
  rw [st]

end Hierarchy.ProtocolRAM.Calendar.CatalogueRows
end

end OAI
