import OAI.Hierarchy.DescentSparseBinLookup
import OAI.Hierarchy.DescentPackedPorts
import OAI.Hierarchy.DescentPackedFieldGather

namespace OAI
/-! # The return slot of each genuine preceding neighbor, shared across group lanes -/
namespace Hierarchy.DescentResetReciprocalPeer
open DescentSIMDLookup DescentPackedColony DescentPackedZip DescentPacking.SparseBinRAM
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure DescriptorExpr
open scoped Classical Fin.CommRing
open private DescentPacking.PackedMatch.Local.Gather.encode_zero from OAI.Hierarchy.DescentPackedFieldGather
noncomputable section
variable {H D G M b w : ℕ}
abbrev Adj (H D : ℕ) := Fin H→Fin D→Option (Fin H)
def reaches (adj : Adj H D) (v : Fin H) (i j : Fin D) := (adj v i).bind (fun u=>adj u j)=some v

def back (P : Ports D) (H : ℕ) (own live : Expr) (i j : Fin D) : Expr :=
  let away:=neighborID P i
  let returned : Expr:=.lookup P.roster (.op .add (scale D away) (.lit j.val))
  .branch .eq away (.lit H) (.lit 0) (.branch .eq returned own live (.lit 0))

theorem back_fits (P : Ports D) (prior : Bank) (out : ℕ) (access : Accessible P prior H G M w out)
    (own use : Expr) (o : own.Fits w out) (l : use.Fits w out) (i j : Fin D) : (back P H own use i j).Fits w out:=by
  have away : (neighborID P i).Fits w out:=⟨access.roster,access.ids i,trivial⟩
  exact ⟨away,trivial,trivial,⟨⟨access.roster,scale_fits D _ away,trivial⟩,o,l,trivial⟩⟩

theorem back_source (P : Ports D) (prior : Bank) (out : ℕ) (access : Accessible P prior H G M w out)
    (adj : Adj H D) (m : Memory w) (real : Mounted P adj m G M) (own use : Expr)
    (rowID : ∀p : Row H G M,own.eval m ((row H G M p).val:Word w)=(p.1.val:Word w))
    (v : Fin H→Fin G→Cell b) (source : Source use v M m) (i j : Fin D) :
    Source (back P H own use i j) (fun h g=>if reaches adj h i j then v h g else 0) M m:=by
  intro p
  have small (u : Fin H) (a : Fin D) : u.val*D+a.val<P.roster.size:=by
    apply lt_of_lt_of_le _ access.rosterRoom
    have t:=Nat.mul_le_mul_right D (Nat.succ_le_of_lt u.isLt)
    rw [Nat.succ_mul] at t
    have :=a.isLt
    omega
  have outside : H<2^w:=access.offRoom.trans_lt access.offsets.2.1
  have rx : (neighborID P i).eval m ((row H G M p).val:Word w)=(target (adj p.1 i):Word w):=by
    simp only [neighborID,Expr.eval,bank_read _ m ((row H G M p).isLt.trans_le (access.idsRoom i)) (access.ids i),
      real.ids,bank_read _ m (small p.1 i) access.roster,real.roster]
  have branch : (data (fun h g=>if reaches adj h i j then v h g else 0) p).val=
      if reaches adj p.1 i j then (data v p).val else 0:=by
    by_cases yes : reaches adj p.1 i j
    · simp [data,yes]
    · simp [data,yes,DescentPacking.PackedMatch.Local.Gather.encode_zero]
  rw [branch]
  unfold back
  simp only [Expr.eval,rx,Comparison.test]
  cases leg : adj p.1 i with
  | none=>simp [leg,reaches,target]
  | some u=>
    have notEnd : (u.val:Word w)≠(H:Word w):=by
      intro he
      have same:=congrArg Fin.val he
      rw [Fin.val_cast_of_lt (u.isLt.trans outside),Fin.val_cast_of_lt outside] at same
      exact u.isLt.ne same
    simp only [target,Option.elim_some,leg,reaches,Option.bind_some,rowID]
    have offset : (scale D (neighborID P i)).eval m ((row H G M p).val:Word w)=(u.val*D:ℕ):=by
      rw [scale_eval,rx,leg]
      simp [target,Nat.cast_mul,mul_comm]
    rw [offset]
    simp only [RowOp.opcode,BinaryOp.eval,←Nat.cast_add,bank_read _ m (small u j) access.roster,real.roster]
    have equal : (target (adj u j):Word w)=(p.1.val:Word w) ↔ adj u j=some p.1:=by
      cases bck : adj u j with
      | none=>simp [target,Fin.ext_iff,Fin.val_cast_of_lt outside,Fin.val_cast_of_lt (p.1.isLt.trans outside),ne_of_gt p.1.isLt]
      | some a=>simp [target,Fin.ext_iff,Fin.val_cast_of_lt (a.isLt.trans outside),Fin.val_cast_of_lt (p.1.isLt.trans outside)]
    by_cases yes : adj u j=some p.1
    · simp [notEnd,yes,target,source p]
    · have missed : (target (adj u j) : Word w) ≠ (p.1.val : Word w) := fun h => yes (equal.mp h)
      simp [notEnd,missed,yes]

end
end Hierarchy.DescentResetReciprocalPeer

end OAI
