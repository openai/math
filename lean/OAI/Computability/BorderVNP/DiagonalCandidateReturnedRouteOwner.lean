import OAI.Computability.BorderVNP.DiagonalSignedCandidateCubeWords
import OAI.Computability.BorderVNP.DiagonalRoutedSourceReports
import OAI.Computability.BorderVNP.RoutingISASignedPrepOwned
import OAI.Computability.BorderVNP.DiagonalOneTeamOpenedReports
import OAI.Computability.BorderVNP.DiagonalFrozenPaddingControls

/-! # The native owner read by one returning candidate on its matching route -/

namespace OAI
namespace Computability
namespace BorderVNP

set_option quotPrecheck false
set_option maxHeartbeats 1600000
set_option maxRecDepth 6000

namespace RoutingISA.Evaluator.SignedPrep

open VPVNP.BurstRAM BorderVNP.Cube Physical Tally TeamContraction JointHeader
open PackedHistoryCircuit Packing Packing.Directory LocalRow Transmission Crossing Scatter.Assignment

variable {w R budget : ℕ} (task : SignedTaskArena.Layout) {D : Directory.Layout} {pp lp : ℕ → ℕ × ℕ}
    (raw : Broadcast task.cube.n task.cube.header.d task.cube.header.cap)
local notation3 (prettyPrint := false) "decl" => Prod.mk (Fin.ofNat (task.cube.n+1) (readCode (task.cube.n+1) raw.1))
  (fun (p : Sym2 (Fin task.cube.header.d)) (j : Fin (task.cube.n+1)) => readCode (task.cube.header.cap+1) (raw.2 p j))
variable {frame receiving : ℕ} {pins : Pins.Layout} {fields : Pins.ProcessorFields pins} {f : BroadcastFrame}
    {guess : ℕ → Bool} {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8} {reg : Bank w} {mem : Memory w}
    {I : Type*} [Fintype I] {host : I → Fin task.cube.cells} {key : I ↪ ℕ} {sizes : I → ℕ}
    {dim : ℕ} {P : Type*} {bits : P → ℕ} {N : Network dim P bits} {cell : N.Site → Fin task.cube.cells}
    {A : Type*} [Fintype A] (recv : A → Fin task.cube.cells) (amount : A → ℕ)
    (label : Fin task.cube.cells → Label (task.cube.n+1) task.cube.header.d)
local notation3 (prettyPrint := false) "group" => fun j : Fin task.cube.header.d =>
  TeamNative.owner R (declarationWeight task.cube.header.blocks task.cube.b task.cube.K task.cube.h decl label recv amount) j.val
local notation3 (prettyPrint := false) "representative" => fun c : ℕ =>
  if hc : c<task.cube.cells then group (label ⟨c,hc⟩ (decl).1) else 0
local notation3 (prettyPrint := false) "owners" =>
  greedyOwner (blocks:=task.cube.header.blocks) (K:=task.cube.K) (h:=task.cube.h) R task.cube.b task.cube.s label recv amount

local notation3 (prettyPrint := false) "siteType" => CandidateSite (R:=R) (X:=budget) task.cube D pp lp raw
  representative decl group frame receiving pins fields f guess pub mac reg mem host key sizes N cell recv amount
local notation3 (prettyPrint := false) "prior(" localSite ")" => readings (localSite).published.val.2.2
local notation3 (prettyPrint := false) "entry(" localSite ")" => readings (localSite).receipt.history.dataInput
local notation3 (prettyPrint := false) "input(" localSite ")" => powerHeaderImage task.cube f.dst (readings (localSite).receipt.labeling.val.2.2)

/-- The returned native schedule stores the receiver determined by the actual
advertised declaration. A matching route gives that same greedy receiver on
every original cell, including one with an empty local report bank. -/
theorem CandidateSite.returned_route_owners (site : siteType) (q : NativeAssignments.Routed (b:=task.cube.b) (s:=task.cube.s) owners)
    (matched : (Routed.encode owners q).declaration=decl) :
    ∀ c : Fin task.cube.cells, (task.cube.receivingOwner frame (decl).1 R input(site) c.val).val =
      routedOwnerWord task.cube owners label q c.val := by
  intro c
  have choice : Routed.trueDeclaration task.cube.b task.cube.s q.1=decl := matched
  have actual := congrArg Fin.val (site.receipt.owners c)
  change (task.cube.receivingOwner (pub 0).val (decl).1 R input(site) c.val).val =
    (if hc : c.val<task.cube.cells then group (label ⟨c.val,hc⟩ (decl).1) else 0).val at actual
  simp only [dite_eq_left c.isLt,Fin.eta] at actual
  have number := congrArg (fun d' : LengthDeclaration task.cube.n task.cube.header.d =>
    (TeamNative.owner R (declarationWeight task.cube.header.blocks task.cube.b task.cube.K task.cube.h
      d' label recv amount) (label c d'.1).val).val) choice
  change (owners q.1 (label c (chosen task.cube.b task.cube.s q.1))).val =
    (group (label c (decl).1)).val at number
  have atFrame := congrArg (fun j : ℕ => (task.cube.receivingOwner j (decl).1 R input(site) c.val).val) site.origin.symm
  exact atFrame.trans (actual.trans (number.symm.trans (routedOwnerWord_at task.cube owners label q c).symm))

/-- Both the chosen original-cell owners and the pre-writer geometry come
from the very same individual returned label run. Only the advertised
length declaration is compared with the recovered selector choices. -/
theorem CandidateSite.returned_route_entry (site : siteType) (q : NativeAssignments.Routed (b:=task.cube.b) (s:=task.cube.s) owners)
    (matched : (Routed.encode owners q).declaration=decl)
    (old : Fin 81 → Word w) (origin edges cells pinned subtotal : ℕ)
    (signed : site.old=routingExtension (task.extension pinned f.team subtotal old) D origin edges cells) :
    NativeEntry task.cube frame site.control (decl).1 R input(site) prior(site) entry(site) ∧
    ∀ c : Fin task.cube.cells, (task.cube.receivingOwner frame (decl).1 R input(site) c.val).val =
      routedOwnerWord task.cube owners label q c.val := by
  have boot := site.input
  rw [signed] at boot
  have native := site.receipt.native_entry task site.placement f old origin edges cells pinned subtotal site.fresh
    site.gates site.outputs site.width site.off site.ell site.control site.profile site.claims site.pad raw site.actual boot
  rw [site.origin] at native
  exact ⟨native,site.returned_route_owners task raw recv amount label q matched⟩

open FiniteEvaluator Packing.BottomReports Packing.RoutingOutputs DiagonalTallyCellReports

/-- Make the original team's single opened report on its own successful
owned return. Both publications and the chosen receiver refer to the
candidate obtained on this branch of the physical scheduler. -/
noncomputable def CandidateSite.openedReportOnRoute (site : siteType)
    (q : NativeAssignments.Routed (b:=task.cube.b) (s:=task.cube.s) owners)
    (matched : (Routed.encode owners q).declaration=decl)
    (old : Fin 81 → Word w) (origin ports pinned subtotal : ℕ)
    (signed : site.old=routingExtension (task.extension pinned f.team subtotal old) D origin task.cube.cables task.cube.cells)
    (u : Fin (R+1)) {J bitCount : ℕ} (home : Fin J → Fin task.cube.cells)
    (header : Fin J → BundleHeader) (body factors : Fin J → List CellSparse.Factor)
    (supply wire : ℕ → ℕ) (bank : Fin J → ℕ → Bool)
    (counts : ℕ → Fin task.p.report.gadgets → Fin task.p.report.countWidth → Bool)
    {regs : Bank w} {before : Memory w}
    (owned : Returns (TeamRows.ownedGroups task.cube.n task.cube.b task.cube.h task.cube.K task.cube.s) pub mac regs before) :
    let table := bases origin task.cube.cables task.cube.cells J
    let ctl := controlsBase origin task.cube.cables task.cube.cells J ports
    let openInputs := task.openInputs u.val frame table.ends ctl table.livePairs ports J bitCount home header
    site.control=ctl →
    FrozenControlEntry task openInputs frame (pub 0).val ctl table.ends w (fun c => supply c.val)
      entry(site) (readings owned.val.2.2) →
    task.OpenRoom frame table.ends ctl table.livePairs ports J (2^bitCount) w →
    (∀ c : Fin task.cube.cells,
      prior(site) (table.ends+2*task.cube.cables+c.val)=supply c.val ∧
        prior(site) (table.livePairs+2*ports+c.val)=wire c.val) →
    SignedTaskArena.SingleOpenedReport task u frame origin ports home header body factors
      (routedOwnerWord task.cube owners label q) supply wire w := by
  intro table ctl openInputs controlBase control room widths
  have recovered := site.returned_route_entry task raw recv amount label q matched old origin
    task.cube.cables task.cube.cells pinned subtotal signed
  have native : NativeEntry task.cube frame ctl (decl).1 R input(site) prior(site) entry(site) :=
    controlBase ▸ recovered.1
  exact ⟨bitCount,input(site),prior(site),entry(site),readings owned.val.2.2,(decl).1,bank,counts,native,
    ⟨control.retained.primary,fun i hi s₁ s₂ => (control.retained.lower i hi s₁ s₂).trans (native.low i hi),
      control.retained.tables⟩,control.placement,room,recovered.2,widths⟩

end RoutingISA.Evaluator.SignedPrep

namespace RoutingISA.SignedTaskArena

open Packing Packing.BottomReports DiagonalTallyCellReports

variable {t : Layout} {R J frame origin ports w : ℕ} {u : Fin (R+1)}
    {home : Fin J → Fin t.cube.cells} {header : Fin J → BundleHeader}
    {body factors : Fin J → List CellSparse.Factor} {who supply wire : ℕ → ℕ}

/-- The native report reads only original finite cell numbers. It can be
stated with the selected source's owner function whenever those words
agree on that finite interval. -/
def SingleOpenedReport.reowner
    (o : SingleOpenedReport t u frame origin ports home header body factors who supply wire w) (next : ℕ → ℕ)
    (agree : ∀ c : Fin t.cube.cells, who c.val=next c.val) :
    SingleOpenedReport t u frame origin ports home header body factors next supply wire w :=
  { o with selected := fun c => (o.selected c).trans (agree c) }

/-- Reindexing the source owner preserves the visited rows, including
the sampled header counts and each bundle's original physical slots. -/
theorem SingleOpenedReport.reowner_cells
    (o : SingleOpenedReport t u frame origin ports home header body factors who supply wire w) (next : ℕ → ℕ)
    (agree : ∀ c : Fin t.cube.cells, who c.val=next c.val) : (o.reowner next agree).cells=o.cells := rfl

end RoutingISA.SignedTaskArena

end BorderVNP
end Computability
end OAI
