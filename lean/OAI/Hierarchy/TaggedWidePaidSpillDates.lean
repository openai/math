import OAI.Hierarchy.TaggedWideSpillLedger
import OAI.Hierarchy.TaggedWidePaidDated
import OAI.Hierarchy.ProbeFixedWideSpillDates

namespace OAI
/-! # Concrete resources of every corrected chronological spill/control sheet -/
noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage Native CoreBoard HistoryRoles
open RoleProgram WideCPU ThreeFlat.RAM
open scoped Classical BigOperators
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
local notation "T" => (events v.mesh).length
local notation "E" => v.datedArity
local notation "D" => v.widePacketDegree

theorem wide_spill_date_resources (ell : ℕ) :
    ∃ K : ℕ,∀ h width unitCost bits rankFirst rom oldWork start W,
      let z:=v.wideSpillDates h width ell unitCost bits rankFirst
      let columns:=v.wide_spill_columns h width ell unitCost
      z.ticks rom oldWork start columns≤K*2^h ∧
        text (z.program W rom oldWork start columns)≤K ∧ CheapCode (z.program W rom oldWork start columns) ∧
        z.endAt start≤ start+K*2^h := by
  obtain ⟨I,original⟩:=v.wide_dated_role_inputs
  let A:=4*v.wideRoleWorkBound+58
  let B:=22*A+4+I+v.packetValueRate+SiteControls.controlCost D E+SiteControls.spillFieldCost D
  let Y:=sheetExprBound E B+(4*B+14)+(2*B+3)
  let C:=v.datedCapacity
  let J:=SpillDates.last T+1
  let ticks:=J*(15+2*C*(24+4*Y))
  let bytes:=J*(57+8*Y)
  let arena:=((T+1)*54+12*T*T+14)*C
  let K:=ticks+bytes+arena
  refine ⟨K,?_⟩
  intro h width unitCost bits rankFirst rom oldWork start W z columns
  let g:=v.wideDated h width ell unitCost
  have rate:=original h width ell unitCost
  have dims:=v.wide_dated_dimensions h width ell unitCost
  have arity:=v.wide_dated_arities h width ell unitCost
  have idFit : I≤B := by dsimp only [B];omega
  have valueFit : v.packetValueRate≤B := by dsimp only [B];omega
  have middle (j : Fin T) : (z.middle j).work≤A :=
    v.wide_spill_middle_work h width bits j.val (v.wideSpillPage h width bits rankFirst j.val)
  have only (b : Bool) (j : Fin T) : (z.only b j).work≤A := by
    have q : (z.only b j).work≤22 := by
      cases b <;> change 7+1+(7+5)+1+1≤22 <;> decide
    exact q.trans (by dsimp only [A];omega)
  have amounts (f : Fin 3) (j : Fin (T+1)) : ((z.roles f).amount j).work≤A := by
    induction j using Fin.cases with
    | zero=>change 1≤A;dsimp only [A];omega
    | succ j=>
      change (if f=0 then z.middle j else z.only (decide (f=2)) j).work≤A
      split <;> first | exact middle j | exact only _ j
  have roles (f : Fin 3) (j : Fin (T+1)) :
      DatedRoleSheets.InputWork g.physical g.chart g.sockets ((z.roles f).amount j) g.ordinal B := by
    have r:=rate.1 j
    have sw:=DatedRows.each_work g.physical _ _ (amounts f j) (amounts f j)
    exact ⟨sw.trans (by dsimp only [B];omega),r.id.trans idFit,r.atSite.trans idFit,r.code.trans idFit,r.otherSite.trans idFit⟩
  have ballots j : (g.fields j (g.siteROM rom) (g.siteStride rom) (g.roleStart oldWork j.castSucc)
      (z.dateRole start j 0)).Work B := by
    intro i
    let pb:=ProtocolRAMPurchaseSampler.bits (g.sites*D)
    let e:=(events v.mesh).get j
    exact ⟨(v.widePacket_selected_work h width pb (g.siteROM rom) (g.siteStride rom)
      (g.roleStart oldWork j.castSucc) (z.dateRole start j 0) e i).trans valueFit,
      (v.widePacket_site_work h width pb (g.siteROM rom) (g.siteStride rom)
        (g.roleStart oldWork j.castSucc) (z.dateRole start j 0) e i).trans valueFit,
      fun f=>(v.widePacket_value_work h width pb (g.siteROM rom) (g.siteStride rom)
        (g.roleStart oldWork j.castSucc) (z.dateRole start j 0) e i f).trans valueFit⟩
  have controls j : (g.controls j (g.siteStride rom) (g.roleStart oldWork j.castSucc) (z.dateRole start j 0)
      (g.ballotStart (z.roleRoot start 2) j+1)).Work B := by
    intro i
    have input:=SiteControls.fixed_work g.sites g.physical D (v.wideNeighborCap width unitCost) (g.siteStride rom)
      (g.roleStart oldWork j.castSucc) (z.dateRole start j 0) (g.ballotStart (z.roleRoot start 2) j+1)
      (g.ballot j).columns (v.widePacketLowStart h width ((events v.mesh).get j)) i
    have cap : SiteControls.controlCost D (g.ballot j).columns≤B := by
      have col : (g.ballot j).columns ≤ E := (arity j).2.1
      have byArity : SiteControls.controlCost D (g.ballot j).columns ≤ SiteControls.controlCost D E := by
        unfold SiteControls.controlCost
        omega
      exact byArity.trans (by dsimp only [B]; omega)
    exact ⟨input.1.trans cap,input.2.1.trans cap,fun f=>(input.2.2 f).trans cap⟩
  have expr:=z.expression_bounds rom oldWork start E B columns roles arity ballots controls
    (show SiteControls.spillFieldCost D≤B by dsimp only [B];omega)
  have sizes:=z.sizes dims rom oldWork start columns
  obtain ⟨runtime,program,cheap⟩:=scatter_bank_resources (K:=2*C) (B:=Y) (h:=h) (SpillDates.last T)
    W (z.sheets rom oldWork start columns) (fun i=>by simpa only [Nat.mul_assoc] using sizes i) expr
  have time : ticks≤K := by dsimp only [K];omega
  have textFee : bytes≤K := by dsimp only [K];omega
  have space : arena≤K := by dsimp only [K];omega
  refine ⟨runtime.trans (Nat.mul_le_mul_right _ time),program.trans textFee,cheap,(z.end_bound dims start).trans ?_⟩
  simpa only [arena,Nat.mul_assoc] using Nat.add_le_add_left (Nat.mul_le_mul_right (2^h) space) start

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat

end
end OAI
