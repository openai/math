import OAI.Hierarchy.ProtocolRAMCatalystArchiveGrowth
import OAI.Hierarchy.ProtocolRAMCatalystStripOwnerCost

namespace OAI
/-! # Explicit height-independent overhead of the actual terminal strip ledger -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.StripChart
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage AdaptiveProbe ColumnWires CoreBoard ReportSockets CatalystArchive
open CoreRoute CatalogueRows StripDirectory BoughtSockets PurchaseFrozen
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical

variable {z W k q dpth w goods edges : ℕ} {S : PurchaseSampler}
local notation "radixAt" => 2^W
local notation "nStages" => Stages z radixAt
local notation "rolesAt" => max (Fintype.card (PayloadRole nStages k)) (Fintype.card (PurchasedRole dpth k))
local notation "nSlots" => Fintype.card (Slots z radixAt k)
variable (s : Boards z (2^W) k q dpth) (c : Mesh) (b : CatalogueRows.Board)
    (G : PortBanks ((c.inject+c.cool)*c.outerFuel))
variable (F : Type*) [Field F] [SiteNaming (ColumnSite (PayloadStrip.Columns (Stages z (2^W))) k)]
    [SiteNaming (ColumnSite (ChainStrip.Columns dpth) k)]

def fixedOwnerRoles (d k depth : ℕ) :=
  max (Fintype.card (PayloadRole (18*(d-1)+1) k)) (Fintype.card (PurchasedRole depth k))

def terminalExtraText (c : Mesh) (d k depth : ℕ) :=
  let attempts:=(c.inject+c.cool)*c.outerFuel
  let u:=ownerWork (fixedOwnerRoles d k depth) k (ownerColumnCost d k attempts)
  15+fuel c*(11+4*u)+(65+4*operationBound (18*(d-1)+1) k attempts)

def terminalExtraClock (c : Mesh) (d k degree depth : ℕ) :=
  let attempts:=(c.inject+c.cool)*c.outerFuel
  let roleCount:=fixedOwnerRoles d k depth
  let cost:=ownerWork roleCount k (ownerColumnCost d k attempts)
  let rows:=ownerRowFactor d k degree depth roleCount
  16+fuel c*(4+rows*(2*cost+4))+2*slotFactor d k*(22+2*operationBound (18*(d-1)+1) k attempts)

set_option maxHeartbeats 1200000 in
/-- The owner term and both routed index passes are the actual compiled
procedures. Both extra coefficients are fixed before varying the height. -/
theorem terminal_growth (arena : Arena) (C : Chart w q goods) (mesh : C.mesh=c)
    (p : Recipes) (x : Source) (flag : ℕ) (sink : Sink nSlots edges) (src : ℕ)
    (ss : List PaidWidths.Slice) (a : ReserveUse.Archive) (count n reserve : ℕ) :
    let ledger:=ownerLedger s c b G F arena
    let attempts:=(c.inject+c.cool)*c.outerFuel
    let routes:=CoreRoute.stages sink.banks p x S z W k attempts
    Native.text (terminal C ledger routes flag sink src ss a count n reserve)≤
      Native.text (paidReporter C flag sink src ss a count n reserve)+terminalExtraText c radixAt k dpth ∧
    terminalTime C ledger routes sink ss a count n reserve≤
      paidReporterTime C sink ss a count n reserve+terminalExtraClock c radixAt k s.sampler.degree dpth*2^z := by
  intro ledger attempts routes
  have phase : nStages=18*(radixAt-1)+1:=CoreCatalogue.total_stages z radixAt
  have roles : rolesAt=fixedOwnerRoles radixAt k dpth:=by unfold fixedOwnerRoles; rw [phase]
  let rowFactor:=ownerRowFactor radixAt k s.sampler.degree dpth rolesAt
  let expression:=ownerWork rolesAt k (ownerColumnCost radixAt k attempts)
  have owner (e : Event) : ledger.rows e≤rowFactor*2^z ∧ (clamp count (ledger.term e)).work≤expression := by
    have rowsAt := ledger_owner_rows (z:=z) (W:=W) (k:=k) (q:=q) (depth:=dpth) s c b G F arena e
    have workAt := ledger_owner_work (z:=z) (W:=W) (k:=k) (q:=q) (depth:=dpth) s c b G F arena count e
    dsimp only [ledger,rowFactor,expression,attempts]
    exact ⟨rowsAt,workAt⟩
  constructor
  · have code:=terminal_text_bound (S:=S) (attempts:=attempts) C ledger p x flag sink src ss a count n reserve
    have header:=ledger.text_bound C.mesh count expression (fun e _=>(owner e).2)
    have length : (events C.mesh).length=fuel c := (event_count C.mesh).trans (congrArg fuel mesh)
    rw [length] at header
    have price : operationBound nStages k attempts = operationBound (18*(radixAt-1)+1) k attempts :=
      congrArg (fun n=>operationBound n k attempts) phase
    rw [price] at code
    have work : expression=ownerWork (fixedOwnerRoles radixAt k dpth) k (ownerColumnCost radixAt k attempts) :=
      congrArg (fun r=>ownerWork r k (ownerColumnCost radixAt k attempts)) roles
    rw [work] at header
    apply code.trans
    change _≤_+(15+fuel c*(11+4*(ownerWork (fixedOwnerRoles radixAt k dpth) k (ownerColumnCost radixAt k attempts)))+
      (65+4*operationBound (18*(radixAt-1)+1) k attempts))
    exact (Nat.add_le_add_right (Nat.add_le_add_left header _) _).trans_eq (Nat.add_assoc ..)
  · have price:=terminal_clock_growth (S:=S) (attempts:=attempts) C ledger p x sink ss a count n reserve
      rowFactor expression (fun e _=>owner e)
    have factor :
        16+fuel C.mesh*(4+rowFactor*(2*expression+4))+
          2*slotFactor radixAt k*(22+2*operationBound (18*(radixAt-1)+1) k attempts) =
        terminalExtraClock c radixAt k s.sampler.degree dpth := by
      dsimp only [rowFactor,expression,terminalExtraClock]
      rw [mesh,roles]
    exact price.trans_eq (congrArg (fun cost=>paidReporterTime C sink ss a count n reserve+cost*2^z) factor)

end Hierarchy.ProtocolRAM.Calendar.StripChart
end

end OAI
