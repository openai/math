import OAI.Computability.BorderVNP.RoutingISASparseReportSources

/-! # The signed input window at its actual native returns

The report emitter reads the ordered owned cells and the three argument writers
publish their compressed tasks in the private directory. Charging those two
visits together counts each scheduled delivery and original power slot in the
same cell order as the native writers.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator.ScheduleClock

open VPVNP.BurstRAM BorderVNP.Cube Cube.Physical Cube.TeamRowClock Cube.TeamRowSources
open Crossing Packing.CellAddresses Packing.Directory DiagonalTallyCellReports
open Diagonal.ExternalSew.Fragments CellPacket CellSparse CellSparse.Packet CellSparse.Packet.Source
open CellPacketGeometry BorderVNP.FiniteEvaluator.OpenSuffix

private theorem inputTicks_le {c o k r a probes fixed cables cableBound cube bundles bundleCells controlCells global
    bundleSetup controlSetup controlStep controlFinish taskSetup taskStep fr desc sparse reports cells : ℕ}
    (constant : c ≤ fixed)
    (control : o+k ≤ 82*cables+cube+(bundleSetup+16*bundleCells+30*bundles+1)+
      (controlSetup+controlCells*controlStep+1+controlFinish))
    (report : r ≤ reports) (args : a+probes ≤ fr+(taskSetup+controlCells*taskStep+2)+sparse)
    (fragment : fr ≤ 32*desc) (cell : sparse+reports ≤ cells)
    (cableFit : cables ≤ cableBound) (bundleFit : bundleCells ≤ global) (controlFit : controlCells=global) :
    c+(o+(k+(r+a)))+probes ≤ fixed+(bundleSetup+16*global+30*bundles+1+
      (controlSetup+global*controlStep+1+controlFinish+(taskSetup+global*taskStep+2)))+32*desc+
      (82*cableBound+cube)+cells := by
  subst global
  omega

section Inputs

variable {Site E I A P : Type} [Fintype A] [Fintype P] {w r X width p d R H B description : ℕ}
    {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8}
    {a : CubeArena.Layout} {orig assigned : ℕ → ℕ} {D : LengthDeclaration a.n a.header.d} {team : Fin (r+1)}
    {label : Fin a.cells → Label (a.n+1) a.header.d} {recv : A → Fin a.cells} {incoming : A → ℕ}

set_option quotPrecheck false

local notation "head" => (pub 0).val
local notation "weights" => LocalRow.weightLayout a head D.1.val
local notation "teams" => LocalRow.teamLayout a r
local notation "owner" => (fun z : Fin a.header.d => assigned (a.ownerBase+z.val))
local notation "owned" => TeamRows.ownedGroups a.n a.b a.h a.K a.s

/-- The five successive native returns following the completed routing passes. -/
abbrev InputVisits (id : TableEntry a.n a.b a.h a.K a.s → ℕ) (pub : Arg → Word w)
    (mac : TeamOpcode.Macros w 8) (s : Bank w) (m : Memory w) :=
  Σ c : Returns (CubeConstants.install id) pub mac s m,
  Σ o : Returns owned pub mac c.val.2.1 c.val.2.2,
  Σ d : Returns SignedPrep.controls pub mac o.val.2.1 o.val.2.2,
  Σ r : Returns prepareCellReports pub mac d.val.2.1 d.val.2.2,
    Returns SignedPrep.arguments pub mac r.val.2.1 r.val.2.2

/-- The physical data and charge at the named input cuts. Naming the family
allows transport from the inverse of the seven-stage execution to an explicit
visited tuple without reindexing individual memory-dependent arrays. -/
def InputVisitCost (id : TableEntry a.n a.b a.h a.K a.s → ℕ)
    (desc : LabelIndex.Layout) (before : ℕ → ℕ) (z axes : ℕ)
    {s m} (x : Returns (signedInputs id owned) pub mac s m)
    (v : InputVisits (a:=a) id pub mac s m) : Prop :=
    let constantsMem := v.1.val.2.2
    let ownedMem := v.2.1.val.2.2
    let reportMem := v.2.2.1.val.2.2
    let argumentMem := v.2.2.2.1.val.2.2
    let args := (argumentVisitsEquiv pub mac v.2.2.2.1.val.2.1 argumentMem).symm v.2.2.2.2
    let host := HostScatter.Layout.fromFrame head (readings ownedMem)
    let pad := Padding.Layout.fromFrame head (readings ownedMem)
    a.ScannerWords head team.val D.1.val owner (readings pub) (readings constantsMem) D.2 →
    LocalReceived a head team.val D owner constantsMem →
    ∀ used : ℕ → ℕ, Padding.TailHeader D.1 owner (Function.Embedding.refl ℕ) team.val pad (readings ownedMem) used
      a.header.blocks a.b a.h a.K a.s →
    host.team=team.val → host.ScheduledCables (readings ownedMem) (a.header.blocks*(a.h*a.b)) D.1 owner →
    host.count ≤ desc.cableCount →
    ∀ L : BorderVNP.FiniteEvaluator.OpenSuffix.Inputs, Ready L head (readings ownedMem) w → L.bundles.cells ≤ a.cells →
    ∀ fr : FragmentDirectoryInput pub argumentMem, fr.layout.host.count ≤ desc.cableCount →
    fr.layout.count ≤ desc.deliveryCount → fr.layout.cells ≤ desc.cells →
    L.control.toLayout.Fields (readings args.1.val.2.2) → L.control.toLayout.Room (readings args.1.val.2.2) w →
    ∀ (src : SparseCallInput pub args.2.1.val.2.2)
      (S : SparseReportSources Site E I P a D label recv incoming assigned team.val description p d R H B
        src fr.layout (readings argumentMem) L.control (readings args.1.val.2.2))
      (q : ReportCursor), PreparedReportInput pub reportMem S.reportRows q description →
      traceCost x.val.1+privateDirectoryTicks pub x.val.2.2 ≤
        (CubeConstants.install id).slots+argumentDirectory a.cells L.bundles.bundles+32*descriptorTicks desc before z axes weights teams+
        (82*desc.cableCount+cubeCoefficient a.n a.b a.h a.K a.s width*(a.alphabet^2+X+1))+cellWork w (2^p+2^d) (R*(H*B)) X

set_option maxHeartbeats 2000000 in
/-- Charge every returning signed input and all private argument probes in its
actual final directory. All layout and delivery conditions refer to the native
cut memories of this return. The next private call may still reject. -/
theorem signedInputs_source_charge (id : TableEntry a.n a.b a.h a.K a.s → ℕ)
    (copies : 1 ≤ a.K) (room : a.ReplayRoom w head)
    (schedule : GroupWeights.ScheduleResult weights teams orig assigned)
    (image : GroupWeights.PhysicalImage weights orig a.header.blocks a.b a.K a.h D label recv incoming)
    (positive : 0<a.h*a.b) (alphabet : 0<a.header.d)
    (pass : (TeamBudget.Layout.mk (r+1) X a.teamTotals).Passes assigned)
    (hw : 0<w) (descPositive : 1 ≤ description)
    (desc : LabelIndex.Layout) (before : ℕ → ℕ) (z axes : ℕ)
    {s m} (x : Returns (signedInputs id owned) pub mac s m) :
    InputVisitCost (Site:=Site) (E:=E) (I:=I) (A:=A) (P:=P) (team:=team) (X:=X) (width:=width)
      (p:=p) (d:=d) (R:=R) (H:=H) (B:=B) (description:=description) (label:=label) (recv:=recv)
      (incoming:=incoming) (assigned:=assigned) (D:=D) id desc before z axes x
      ((SignedPrep.inputVisitsEquiv id pub mac owned s m).symm x) := by
  let v := (SignedPrep.inputVisitsEquiv id pub mac owned s m).symm x
  unfold InputVisitCost
  intro constantsMem ownedMem reportMem argumentMem args host pad words views used tails teamID cables hostCount
    L ready bundleCount fr frCables frRows frCells builderFields builderRoom src S q seed
  have constant := constants_charge id v.1.property
  have control := (ownedControls_charge (width:=width) copies room words views schedule image positive alphabet pass used
    tails teamID cables L ready v.2.1.property v.2.2.1.property).1
  have report := report_return_original seed v.2.2.2.1
  have argCost := arguments_source_charge v.2.2.2.2 fr L.control.toLayout ready.controlBase.symm builderFields builderRoom src
  have fragment := fragmentDirectory_le fr.layout (readings argumentMem) desc before z axes weights teams frCables frRows frCells
  have cell := S.charge schedule image hw descPositive pass seed v.2.2.2.2.val.2.2
  have vals := SignedPrep.inputVisitsEquiv_val id pub mac owned v.1 v.2.1 v.2.2.1 v.2.2.2.1 v.2.2.2.2
  change (SignedPrep.inputVisitsEquiv id pub mac owned s m v).val=_ at vals
  rw [show SignedPrep.inputVisitsEquiv id pub mac owned s m v=x from Equiv.apply_symm_apply ..] at vals
  rw [vals]
  simp only [Transmission.cost_append]
  exact inputTicks_le constant control report argCost fragment cell hostCount bundleCount S.cellCount

end Inputs

end RoutingISA.Evaluator.ScheduleClock

end BorderVNP
end Computability
end OAI
