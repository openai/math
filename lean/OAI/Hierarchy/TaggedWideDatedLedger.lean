import OAI.Hierarchy.TaggedWideDatedLayout
import OAI.Hierarchy.TaggedWideScatterBill

namespace OAI
/-! # The full finite ledger of the dated native sheets -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.WideCPU
open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM
open ProbeStage Native
open scoped Classical BigOperators
variable {T : ℕ} (p : Dated T)

/-- Independent linear dimensions of every actual iteration. -/
structure Dated.Dimensions (U : ℕ) : Prop where
  one : 1≤U
  sites : p.sites≤U
  directory : p.siteDirectorySize≤U
  physical : p.physical≤U
  roles : p.roleWords≤U
  edges : p.rawEdges≤U
  ballot : ∀j,(p.ballot j).count≤U ∧ p.sites*(p.ballot j).columns≤U
  control : ∀j,(p.control j).count≤U ∧ p.sites*(p.control j).columns≤U

theorem end_bound {base U : ℕ} {s : Fin T→ℕ} (cap : ∀j,s j≤4*U) :
    endOf base s≤base+(4*T*T)*U := by
  have h : (∑j,s j)≤T*(4*U) := by simpa using Finset.sum_le_sum (s:=Finset.univ) (fun j _=>cap j)
  apply (Nat.add_le_add_left (Nat.mul_le_mul_left T h) base).trans_eq
  ring

theorem Dated.address_bounds {U : ℕ} (d : p.Dimensions U) (rom work : ℕ) :
    p.romEnd rom≤rom+(3+8*T*T)*U ∧ p.workEnd work≤work+((T+1)*18+8*T*T+14)*U := by
  have adv (shape : Shape) (count : shape.count≤U) : shape.advice p.sites≤4*U := by
    unfold Shape.advice
    linarith only [d.sites,count]
  have span (shape : Shape) (cost : shape.count≤U ∧ p.sites*shape.columns≤U) : shape.span p.sites≤4*U := by
    unfold Shape.span
    linarith only [d.one,cost.1,cost.2]
  have roles : p.roleSpan≤6*U := by
    unfold Dated.roleSpan ProbeStage.CoreBoard.HistoryRoles.DatedRoleSheets.span
    linarith only [d.one,d.roles,d.physical]
  have rolesEnd : p.rolesEnd work≤work+(T+1)*18*U := by
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left (T+1) (Nat.mul_le_mul_left 3 roles)) work).trans_eq
    ring
  have ra := end_bound (base:=p.firstROM rom) (fun j=>adv _ (d.ballot j).1)
  have rb := end_bound (base:=p.controlROMStart rom) (fun j=>adv _ (d.control j).1)
  have wa := end_bound (base:=p.rolesEnd work) (fun j=>span _ (d.ballot j))
  have wb := end_bound (base:=p.controlStart work) (fun j=>span _ (d.control j))
  change p.controlROMStart rom≤(rom+p.sites+p.siteDirectorySize)+(4*T*T)*U at ra
  change p.maskROM rom≤p.controlROMStart rom+(4*T*T)*U at rb
  change p.controlStart work≤p.rolesEnd work+(4*T*T)*U at wa
  change p.maskStart work≤p.controlStart work+(4*T*T)*U at wb
  constructor
  · unfold Dated.romEnd
    linarith only [ra,rb,d.sites,d.directory,d.edges]
  · unfold Dated.workEnd Dated.slotStart
    linarith only [rolesEnd,wa,wb,d.one,d.edges]

theorem fin_cases_all {m n : ℕ} {α : Type*} (P : α→Prop) (a : Fin m→α) (b : Fin n→α)
    (l : ∀i,P (a i)) (r : ∀i,P (b i)) : ∀i,P (Fin.addCases a b i) := by
  intro i
  induction i using Fin.addCases with
  | left i=> simpa using l i
  | right i=> simpa using r i

theorem Dated.each_sheet (rom work : ℕ) (P : Scatter→Prop)
    (roles : ∀j f,P (p.rolePage rom work j f))
    (ballots : ∀j,P (p.ballotPage rom work j)) (controls : ∀j,P (p.controlPage rom work j))
    (widths : P (p.widthPage rom work)) (slots : ∀b,P (p.slotPage work b)) :
    ∀i,P (p.sheets rom work i) := by
  unfold Dated.sheets
  apply fin_cases_all
  · apply fin_cases_all
    · apply fin_cases_all
      · exact fun i=>roles _ _
      · exact fin_cases_all P _ _ ballots controls
    · intro i
      induction i using Fin.cases with
      | zero=>exact widths
      | succ i=>exact slots false
  · exact fun _=>slots true

theorem Dated.sheet_rows {U : ℕ} (d : p.Dimensions U) (rom work : ℕ) :
    ∀i,(p.sheets rom work i).length≤3*U ∧ (p.sheets rom work i).rows≤3*U := by
  apply p.each_sheet rom work (fun page=>page.length≤3*U ∧ page.rows≤3*U)
  · intro j f
    change p.roleWords≤3*U ∧ p.physical+p.physical≤3*U
    constructor <;> linarith only [d.roles,d.physical]
  · intro j
    change p.sites*(p.ballot j).columns≤3*U ∧ (p.ballot j).count≤3*U
    have q:=d.ballot j; omega
  · intro j
    change p.sites*(p.control j).columns≤3*U ∧ (p.control j).count≤3*U
    have q:=d.control j; omega
  · change 3*p.rawEdges≤3*U ∧ p.rawEdges≤3*U
    have q:=d.edges;omega
  · intro b
    change p.rawEdges≤3*U ∧ p.rawEdges≤3*U
    have q:=d.edges;omega

theorem Dated.sheet_resources {h K B : ℕ} (d : p.Dimensions (K*2^h)) (rom work w : ℕ)
    (expressions : ∀i,(p.sheets rom work i).address.work≤B ∧ (p.sheets rom work i).value.work≤B) :
    (∑i,(p.sheets rom work i).ticks)≤((Dated.last T+1)*(15+(3*K)*(24+4*B)))*2^h ∧
    text (ProcedureBank.program (Dated.last T) (fun i=>(p.sheets rom work i).code w))≤
      (Dated.last T+1)*(57+8*B) ∧
    CheapCode (ProcedureBank.program (Dated.last T) (fun i=>(p.sheets rom work i).code w)) := by
  exact scatter_bank_resources (Dated.last T) w (p.sheets rom work)
    (fun i=>by simpa only [Nat.mul_assoc] using p.sheet_rows d rom work i) expressions

end Hierarchy.ProtocolRAM.Calendar.WideCPU

end
end OAI
