import OAI.Hierarchy.ProbeFixedWideSpillOffsets
import OAI.Hierarchy.ProtocolRAMBoughtCatalogueCost

namespace OAI
/-! # Height-independent cost of the original spill-offset operand programs -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.DatedSpillOffsets
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage.CoreBoard.HistoryRoles

def offsetWork (D : ℕ) := 1+D*(200+80*D)

private theorem total_le (n bound : ℕ) (f : Fin n→Expr) (terms : ∀i,(f i).work≤bound) :
    (LocalPrefix.total n f).work≤1+n*(bound+1) := by
  induction n with
  | zero=>simp [LocalPrefix.total,Expr.work]
  | succ n ih=>
    have t:=terms 0
    have h:=ih (fun i=>f i.succ) (fun i=>terms i.succ)
    simp only [LocalPrefix.total,Expr.work,Nat.succ_mul]
    omega

theorem Side.fromSector_work {D : ℕ} (rows original sites full only bits : ℕ) (stride site role : Bank)
    (ordinal : Expr) (short : ordinal.work≤43) :
    (Side.fromSector (D:=D) rows original sites full only bits stride site role ordinal).prefix.work≤offsetWork D := by
  let here:=Expr.lookup site .row
  let index:=Expr.lookup role .row
  let col (start : ℕ) := SiteControls.columns (D:=D) original start sites bits stride here
  have reg (start : ℕ) (i : Fin D) : ((col start i).ordinal).work=19 ∧ ((col start i).opposite).work=19 ∧
      ((col start i).width).work=19 := by
    simp [col,SiteControls.columns,page_work,here,Expr.work]
  let peer:=chooseField (2*D) 0 (fun j=>(col full (untagRole j)).opposite) index
  have selector : peer.work≤1+(2*D)*28 :=
    (BoughtSockets.choose_work_bound (2*D) 0 19 _ index (fun j=>(reg full (untagRole j)).2.1.le)).trans_eq (by rfl)
  change (LocalPrefix.total D (fun i=>LocalPrefix.term (col only i) ⟨ordinal,peer,.lit 1⟩)).work≤offsetWork D
  have terms (i : Fin D) :
      (LocalPrefix.term (col only i) ⟨ordinal,peer,.lit 1⟩).work ≤ 199+80*D := by
    have ⟨ha,hb,hc⟩:=reg only i
    change (col only i).ordinal.work + ordinal.work +
      ((col only i).opposite.work + peer.work + (col only i).width.work + 1 + 1) + 1 + 1 ≤ _
    rw [ha,hb,hc]
    omega
  exact (total_le D (199+80*D) _ terms).trans_eq (by unfold offsetWork; ring)

end Hierarchy.ProtocolRAM.Calendar.DatedSpillOffsets
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open ProbeStage.CoreBoard.HistoryRoles
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)

theorem wide_spill_offset_work :
    ∃C : ℕ,∀h width bits datedROM terminalROM terminalWork oldStart newStart leftOnly rightOnly,
      let sides:=v.wideSpillOffsetSides h width bits datedROM terminalROM terminalWork oldStart newStart leftOnly rightOnly
      sides.1.prefix.work≤C ∧ sides.2.prefix.work≤C := by
  refine ⟨DatedSpillOffsets.offsetWork v.widePacketDegree,?_⟩
  intro h width bits datedROM terminalROM terminalWork oldStart newStart leftOnly rightOnly sides
  have small : (v.wideRoleID h width bits).work≤43 := by
    unfold wideRoleID
    rw [DatedRoleInput.id_work]
    change 2*7+3*7+8≤43
    decide
  exact ⟨DatedSpillOffsets.Side.fromSector_work _ _ _ _ _ _ _ _ _ _ small,
    DatedSpillOffsets.Side.fromSector_work _ _ _ _ _ _ _ _ _ Expr.row (by decide)⟩

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
