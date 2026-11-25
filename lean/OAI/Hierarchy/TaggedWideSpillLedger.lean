import OAI.Hierarchy.TaggedWideCompileFieldCost
import OAI.Hierarchy.TaggedWideDatedExpressions
import OAI.Hierarchy.TaggedWideDatedSocketWork

namespace OAI
/-! # All signed-to-clipped and spill-only date scans on the same original native bank -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.WideCPU
open Computability.VPVNP.BurstRAM PrivateRAM SiteControls
open ProbeStage.CoreBoard.HistoryRoles RoleProgram
open ThreeFlat.RAM
open scoped Classical BigOperators
variable {T : ℕ} (z : SpillDates T)
local notation "g" => z.original

theorem SpillDates.end_bound {U : ℕ} (d : (g).Dimensions U) (start : ℕ) :
    z.endAt start≤ start+((T+1)*54+12*T*T+14)*U := by
  have s : (g).roleSpan≤6*U := by
    unfold Dated.roleSpan DatedRoleSheets.span
    linarith only [d.one,d.roles,d.physical]
  have root : z.roleRoot start 2≤ start+((T+1)*36)*U := by
    change start+2*((T+1)*(3*(g).roleSpan))≤_
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left (T+1) (Nat.mul_le_mul_left 3 s))) start).trans_eq
    ring
  have bound:=((g).address_bounds d 0 (z.roleRoot start 2)).2
  have lower : (g).maskStart (z.roleRoot start 2)≤(g).workEnd (z.roleRoot start 2) := by
    unfold Dated.workEnd Dated.slotStart;omega
  have spans (j : Fin T) : ((g).control j).span (g).sites≤4*U := by
    unfold Shape.span
    linarith only [d.one,(d.control j).1,(d.control j).2]
  have final:=WideCPU.end_bound (base:=(g).maskStart (z.roleRoot start 2)) spans
  change z.endAt start≤(g).maskStart (z.roleRoot start 2)+(4*T*T)*U at final
  linarith only [root,bound,lower,final]

theorem SpillDates.each (rom oldWork start : ℕ) (count : ∀i,(g).controlColumns i=fieldCount (g).roleCount)
    (P : Scatter→Prop) (r : ∀i,P (z.roleSheet rom start i))
    (a : ∀i,P (z.ballot rom oldWork start i)) (b : ∀i,P (z.packetControl rom oldWork start i))
    (c : ∀i,P (z.spillControl rom oldWork start i count)) :
    ∀i,P (z.sheets rom oldWork start count i) := by
  intro i
  exact fin_cases_all P _ _ r (fin_cases_all P _ _ a (fin_cases_all P _ _ b c)) (Fin.cast _ i)

theorem SpillDates.sizes {U : ℕ} (d : (g).Dimensions U) (rom oldWork start : ℕ)
    (count : ∀i,(g).controlColumns i=fieldCount (g).roleCount) :
    ∀i,(z.sheets rom oldWork start count i).length≤2*U ∧ (z.sheets rom oldWork start count i).rows≤2*U := by
  apply z.each rom oldWork start count (fun page=>page.length≤2*U ∧ page.rows≤2*U)
  · intro i
    change (g).roleWords≤2*U ∧ (g).physical+(g).physical≤2*U
    have a:=d.roles;have b:=d.physical;omega
  · intro i
    change (g).sites*((g).ballot i).columns≤2*U ∧ ((g).ballot i).count≤2*U
    have a:=d.ballot i;omega
  · intro i
    change (g).sites*((g).control i).columns≤2*U ∧ ((g).control i).count≤2*U
    have a:=d.control i;omega
  · intro i
    change (g).sites*((g).control i).columns≤2*U ∧ ((g).control i).count≤2*U
    have a:=d.control i;omega

theorem SpillDates.expression_bounds (rom oldWork start E B : ℕ) (count : ∀i,(g).controlColumns i=fieldCount (g).roleCount)
    (role : ∀(f : Fin 3) j,DatedRoleSheets.InputWork (g).physical (g).chart (g).sockets ((z.roles f).amount j) (g).ordinal B)
    (size : ∀j,((g).ballot j).parties≤E ∧ ((g).ballot j).columns≤E ∧ ((g).control j).parties≤E ∧ ((g).control j).columns≤E)
    (ballot : ∀j,((g).fields j ((g).siteROM rom) ((g).siteStride rom) ((g).roleStart oldWork j.castSucc)
      (z.dateRole start j 0)).Work B)
    (control : ∀j,((g).controls j ((g).siteStride rom) ((g).roleStart oldWork j.castSucc) (z.dateRole start j 0)
      ((g).ballotStart (z.roleRoot start 2) j+1)).Work B)
    (cheapSpill : spillFieldCost (g).roleCount≤B) :
    let F:=sheetExprBound E B+(4*B+14)+(2*B+3)
    ∀i,(z.sheets rom oldWork start count i).address.work≤F ∧ (z.sheets rom oldWork start count i).value.work≤F := by
  intro F
  have fee : sheetExprBound E B≤F := by dsimp only [F];omega
  apply z.each rom oldWork start count (fun page=>page.address.work≤F ∧ page.value.work≤F)
  · intro x
    let stage : Fin 3×Fin ((T+1)*3):=finProdFinEquiv.symm x
    let date : Fin (T+1)×Fin 3:=finProdFinEquiv.symm stage.2
    let initial:=(g).roleStart (z.roleRoot start stage.1) date.1
    let current:=(z.roles stage.1).amount date.1
    have left:=DatedRoleSheets.dest_work (g).physical (g).chart (g).sockets ((g).siteStride rom)
      current (g).ordinal (role stage.1 date.1) initial (g).roleWords date.2
    have right:=DatedRoleSheets.word_work (g).physical (g).chart (g).sockets current (g).ordinal (role stage.1 date.1) date.2
    exact ⟨left.trans (by dsimp only [F];omega),right.trans (by dsimp only [F];omega)⟩
  · intro j
    have s:=size j
    have a:=((g).ballot j).sheet_work (g).sites ((g).ballotROM rom j) ((g).ballotStart (z.roleRoot start 2) j)
      B E _ s.1 s.2.1 (ballot j)
    exact ⟨a.1.trans fee,a.2.trans fee⟩
  · intro j
    have s:=size j
    have b:=((g).control j).sheet_work (g).sites ((g).controlROM rom j) ((g).controlBase (z.roleRoot start 2) j)
      B E _ s.2.2.1 s.2.2.2 (control j)
    exact ⟨b.1.trans fee,b.2.trans fee⟩
  · intro j
    let p:=(g).control j
    let site:=spillControls (g).sites (g).physical (g).roleCount z.cap ((g).siteStride rom)
      (z.preClip oldWork start j) ((g).roleStart oldWork j.succ) (z.dateRole start j 1) (z.dateRole start j 2)
    let fields : Fields p := ⟨site.selected,site.site,fun i f=>site.value i (f.cast (count j))⟩
    have rate:=spill_controls_work (g).sites (g).physical (g).roleCount z.cap ((g).siteStride rom)
      (z.preClip oldWork start j) ((g).roleStart oldWork j.succ) (z.dateRole start j 1) (z.dateRole start j 2)
    have paid : fields.Work B := fun i=>⟨(rate i).1.trans cheapSpill,(rate i).2.1.trans cheapSpill,
      fun f=>((rate i).2.2 (f.cast (count j))).trans cheapSpill⟩
    have s:=size j
    have c:=p.sheet_work (g).sites ((g).controlROM rom j) (z.spillStart start j) B E fields s.2.2.1 s.2.2.2 paid
    exact ⟨c.1.trans fee,c.2.trans fee⟩

end Hierarchy.ProtocolRAM.Calendar.WideCPU

end
end OAI
