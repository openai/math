import OAI.Hierarchy.TaggedWideDatedDimensions
import OAI.Hierarchy.TaggedWideDatedExpressions
import OAI.Hierarchy.ProbeFixedWidePacketCost
import OAI.Hierarchy.TaggedWideControlFieldCost

namespace OAI
/-! # One coefficient for the native dated program and both of its address regions -/
noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard HistoryRoles
open RoleProgram WideCPU Native ThreeFlat.RAM
open scoped Classical BigOperators

variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
local notation "T" => (events v.mesh).length
local notation "D" => v.widePacketDegree
local notation "E" => v.datedArity

theorem wide_dated_resources_of_roles (ell baseWork : ℕ)
    (readers : ∀h width unitCost,
      let g:=v.wideDated h width ell unitCost
      (∀j,DatedRoleSheets.InputWork g.physical g.chart g.sockets (g.amount j) g.ordinal baseWork) ∧
        (∀b,(g.orderedSlot b).work≤baseWork)) :
    ∃ K : ℕ,∀ h width unitCost rom work W,
      let g:=v.wideDated h width ell unitCost
      (∑i,(g.sheets rom work i).ticks)≤K*2^h ∧
        text (ProcedureBank.program (Dated.last T) (fun i=>(g.sheets rom work i).code W))≤K ∧
        CheapCode (ProcedureBank.program (Dated.last T) (fun i=>(g.sheets rom work i).code W)) ∧
        g.romEnd rom≤rom+K*2^h ∧ g.workEnd work≤work+K*2^h := by
  let B:=baseWork+v.packetValueRate+SiteControls.controlCost D E
  let Y:=sheetExprBound E B+(4*B+14)+(2*B+3)+(1+2^ell*(B+1))+40
  let J:=Dated.last T+1
  let C:=v.datedCapacity
  let tick:=J*(15+3*C*(24+4*Y))
  let bytes:=J*(57+8*Y)
  let romFee:=(3+8*T*T)*C
  let arena:=((T+1)*18+8*T*T+14)*C
  let K:=tick+bytes+romFee+arena
  refine ⟨K,?_⟩
  intro h width unitCost rom work W g
  have source:=readers h width unitCost
  have big : baseWork≤B := by dsimp only [B];omega
  have vfit : v.packetValueRate≤B := by dsimp only [B];omega
  have roles (j : Fin (T+1)) :
      DatedRoleSheets.InputWork g.physical g.chart g.sockets (g.amount j) g.ordinal B := by
    have r:=source.1 j
    exact ⟨r.size.trans big,r.id.trans big,r.atSite.trans big,r.code.trans big,r.otherSite.trans big⟩
  have dims:=v.wide_dated_arities h width ell unitCost
  have vals j : (g.fields j (g.siteROM rom) (g.siteStride rom) (g.roleStart work j.castSucc)
      (g.roleStart work j.succ)).Work B := by
    intro i
    let bits:=ProtocolRAMPurchaseSampler.bits (g.sites*D)
    let date:=(events v.mesh).get j
    exact ⟨(v.widePacket_selected_work h width bits (g.siteROM rom) (g.siteStride rom)
      (g.roleStart work j.castSucc) (g.roleStart work j.succ) date i).trans vfit,
      (v.widePacket_site_work h width bits (g.siteROM rom) (g.siteStride rom)
        (g.roleStart work j.castSucc) (g.roleStart work j.succ) date i).trans vfit,
      fun f=>(v.widePacket_value_work h width bits (g.siteROM rom) (g.siteStride rom)
        (g.roleStart work j.castSucc) (g.roleStart work j.succ) date i f).trans vfit⟩
  have controls j : (g.controls j (g.siteStride rom) (g.roleStart work j.castSucc) (g.roleStart work j.succ)
      (g.ballotStart work j+1)).Work B := by
    intro i
    have input:=SiteControls.fixed_work g.sites g.physical D (v.wideNeighborCap width unitCost)
      (g.siteStride rom) (g.roleStart work j.castSucc) (g.roleStart work j.succ)
      (g.ballotStart work j+1) (g.ballot j).columns (v.widePacketLowStart h width ((events v.mesh).get j)) i
    have cap : SiteControls.controlCost D (g.ballot j).columns≤B := by
      dsimp only [B,SiteControls.controlCost]
      have col : (g.ballot j).columns≤E := (dims j).2.1
      omega
    exact ⟨input.1.trans cap,input.2.1.trans cap,fun f=>(input.2.2 f).trans cap⟩
  have expr : ∀i,(g.sheets rom work i).address.work≤Y ∧ (g.sheets rom work i).value.work≤Y :=
    g.expression_bounds rom work E B roles dims vals controls (fun b=>(source.2 b).trans big)
  have dimensions:=v.wide_dated_dimensions h width ell unitCost
  obtain ⟨runtime,hardware,cheap⟩:=g.sheet_resources dimensions rom work W expr
  obtain ⟨readOnly,mutable⟩:=g.address_bounds dimensions rom work
  have time : tick≤K := by dsimp only [K];omega
  have textBill : bytes≤K := by dsimp only [K];omega
  have romBill : romFee≤K := by dsimp only [K];omega
  have workBill : arena≤K := by dsimp only [K];omega
  refine ⟨runtime.trans (Nat.mul_le_mul_right _ time),hardware.trans textBill,cheap,?_,?_⟩
  · apply readOnly.trans
    simpa only [romFee,Nat.mul_assoc] using Nat.add_le_add_left (Nat.mul_le_mul_right (2^h) romBill) rom
  · apply mutable.trans
    simpa only [arena,Nat.mul_assoc] using Nat.add_le_add_left (Nat.mul_le_mul_right (2^h) workBill) work

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat

end
end OAI
