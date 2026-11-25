import OAI.Hierarchy.TaggedWideSiteFieldWork
import OAI.Hierarchy.TaggedWideDatedLedger
import OAI.Hierarchy.TaggedWideDatedRoleSheetCost

namespace OAI
/-! # Expression-size accounting on every physically generated dated sheet -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.WideCPU
open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM
open ProbeStage.CoreBoard.HistoryRoles RoleProgram NativeSiteWork

def Fields.Work {p : Shape} (x : Fields p) (B : ℕ) :=
  ∀i,(x.selected i).work≤B ∧ (x.site i).work≤B ∧ ∀j,(x.value i j).work≤B

def sheetExprBound (E B : ℕ) :=
  (chooseCost E (8*B)+chooseCost E (chooseCost E (8*B))+3)+(chooseCost E (8*B)+13)+5

private theorem choose_mono {n m B C : ℕ} (hn : n≤ m) (hb : B≤C) : chooseCost n B≤chooseCost m C := by
  unfold chooseCost
  gcongr

theorem Shape.sheet_work (p : Shape) (sites rom work B E : ℕ) (fields : Fields p)
    (parties : p.parties≤E) (columns : p.columns≤E) (cap : fields.Work B) :
    ((p.sheet sites rom work fields).address).work≤ sheetExprBound E B ∧
      ((p.sheet sites rom work fields).value).work≤ sheetExprBound E B := by
  let val:=SiteScatter.selectedValue (I:=p.candidates) rom fields.selected fields.value
  let table:=RoleROM.bank (rom+3*p.count) sites
  let index:=SiteScatter.fieldIndex (I:=p.candidates) (C:=p.columns) rom table fields.site
  have one:=choose_mono (B:=8*B) parties le_rfl
  have two:=choose_mono parties (choose_mono (B:=8*B) columns le_rfl)
  have v : val.work≤chooseCost E (8*B)+chooseCost E (chooseCost E (8*B))+3 :=
    (selectedValue rom p.candidates B _ _ (fun i=>(cap i).1) (fun i j=>(cap i).2.2 j)).trans
      (Nat.add_le_add_right (Nat.add_le_add one two) 3)
  have ix : index.work≤chooseCost E (8*B)+13 :=
    (fieldIndex rom p.candidates p.columns B table _ (fun i=>(cap i).2.1)).trans (Nat.add_le_add_right one _)
  change (RoleWidths.destination (work+1) work val index).work≤_ ∧ val.work≤_
  rw [role_destination]
  unfold sheetExprBound
  constructor <;> omega

variable {T : ℕ} (p : Dated T)

def Dated.exprBound (E B : ℕ) :=
  sheetExprBound E B+(4*B+14)+(2*B+3)+(1+p.lanes*(B+1))+40

theorem Dated.expression_bounds (rom work E B : ℕ)
    (roles : ∀j,DatedRoleSheets.InputWork p.physical p.chart p.sockets (p.amount j) p.ordinal B)
    (size : ∀j,(p.ballot j).parties≤E ∧ (p.ballot j).columns≤E ∧ (p.control j).parties≤E ∧
      (p.control j).columns≤E)
    (ballots : ∀j,(p.fields j (p.siteROM rom) (p.siteStride rom) (p.roleStart work j.castSucc)
      (p.roleStart work j.succ)).Work B)
    (ctrl : ∀j,(p.controls j (p.siteStride rom) (p.roleStart work j.castSucc) (p.roleStart work j.succ)
      (p.ballotStart work j+1)).Work B)
    (slots : ∀b,(p.orderedSlot b).work≤B) :
    ∀i,(p.sheets rom work i).address.work≤p.exprBound E B ∧
      (p.sheets rom work i).value.work≤p.exprBound E B := by
  have cap : sheetExprBound E B≤p.exprBound E B := by unfold Dated.exprBound;omega
  apply p.each_sheet rom work (fun page=>page.address.work≤p.exprBound E B ∧ page.value.work≤p.exprBound E B)
  · intro j f
    have a:=DatedRoleSheets.dest_work p.physical p.chart p.sockets (p.siteStride rom)
      (p.amount j) p.ordinal (roles j) (p.roleStart work j) p.roleWords f
    have v:=DatedRoleSheets.word_work p.physical p.chart p.sockets (p.amount j) p.ordinal (roles j) f
    exact ⟨a.trans (by unfold Dated.exprBound;omega),v.trans (by unfold Dated.exprBound;omega)⟩
  · intro j
    have s:=size j
    have b:=(p.ballot j).sheet_work p.sites (p.ballotROM rom j) (p.ballotStart work j) B E _ s.1 s.2.1 (ballots j)
    exact ⟨b.1.trans cap,b.2.trans cap⟩
  · intro j
    have s:=size j
    have b:=(p.control j).sheet_work p.sites (p.controlROM rom j) (p.controlBase work j) B E _ s.2.2.1 s.2.2.2 (ctrl j)
    exact ⟨b.1.trans cap,b.2.trans cap⟩
  · simp only [Dated.widthPage,triple,Expr.work,Dated.exprBound]
    constructor <;> omega
  · intro b
    have val:=Nat.mul_le_mul_left p.lanes (Nat.add_le_add_right (slots b) 1)
    simp only [Dated.slotPage,Expr.work,ProtocolRAM.scale_work,Dated.exprBound]
    constructor <;> omega

end Hierarchy.ProtocolRAM.Calendar.WideCPU

end
end OAI
