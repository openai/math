import OAI.Computability.BorderVNP.DiagonalOwnedReportSourceWords
import OAI.Computability.BorderVNP.DiagonalExternalFragmentNativeWords
import OAI.Computability.BorderVNP.RoutingISASignedPrepOwned
import OAI.Computability.BorderVNP.DiagonalPrivatePathRead

/-! # The actual recovered routed assignment in all signed report memories -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal.ExternalSew.Fragments

open VPVNP BurstRAM Crossing TeamContraction RoutingISA RoutingISA.Transmission RoutingISA.Pins Routing
open Packing Packing.CellAddresses BorderVNP.Cube Cube.Physical Cube.Scatter Cube.NativeIntervals
open Cube.HostAddress Cube.HostScatter Cube.TeamRows Cube.Tally Scatter.Assignment
open Diagonal.Layout DiagonalTallyPacketEmit FiniteEvaluator RoutingISA.Evaluator CellMacro.Generator
open DiagonalTallyCellReports DiagonalTallyAllocation NativeAssignments
open scoped Classical
set_option maxHeartbeats 1800000
set_option maxRecDepth 5000

/-- The public owned-group processor on one simultaneous tuple of native
prefix returns, before invoking a single private checker. -/
abbrev visitedOwnedScans {ar : CubeArena.Layout} {id : TableEntry ar.n ar.b ar.h ar.K ar.s → ℕ} {R w : ℕ}
    {pub : Fin (R+1) → Arg → Word w} {mac : Fin (R+1) → TeamOpcode.Macros w 8}
    {s : Fin (R+1) → Bank w} {m : Fin (R+1) → Memory w}
    (v : ∀ u, SignedPrep.Visits id (pub u) (mac u) (s u) (m u)) :=
  SignedPrep.ownedHistory ar pub mac (fun u => (v u).constants.val.2.1) (fun u => (v u).constants.val.2.2)
    (fun u => (v u).owned)

variable {R r t pins link inner n W V g entries desc D C m nP M : ℕ}
    {Edge : Type} {G : Wiring R r t pins link inner n Edge}
    {inputPin : Fin pins → Bool} {ext : Exterior R r link → Bool} {wire : WireLayout (R+1) r link}
    {pp lp : ℕ → ℕ × ℕ} {owner : ℕ → Fin (R+1)} {origin stride : ℕ}
    {H : Fin (R+1) → TeamHistory W} {ib hb sb : Fin (R+1) → ℕ}
    {layout : SharedRows.Layout} {src : Fin (R+1) → ℕ → ℕ} {anchor : Fin (R+1)}
    {ar : CubeArena.Layout} {decl : LengthDeclaration ar.n ar.header.d}
    {group : Fin ar.header.d → Fin (R+1)}
    {owners : (Packet ar.n ar.header.d ar.header.blocks → Selector ar.n ar.K ar.h) → Fin ar.header.d → Fin (R+1)}
    {template : Frame} {id : TableEntry ar.n ar.b ar.h ar.K ar.s → ℕ} {count : ℕ}

variable {teamPub : Fin (R+1) → Arg → Word W} {teamMac : Fin (R+1) → TeamOpcode.Macros W 8}
    {teamReg : Fin (R+1) → Bank W} {teamMem : Fin (R+1) → Memory W}
    (visits : ∀ u, SignedPrep.Visits id (teamPub u) (teamMac u) (teamReg u) (teamMem u))
local notation3 (prettyPrint := false) "owned" => visitedOwnedScans (ar:=ar) visits

local notation "PL" => fun u => G.pinLayout u (ib u) (hb u) (sb u)
local notation "dir" => freeDirectory R r (G.program.length+t) link V g entries desc

variable {f : ReturnedDelivery G inputPin ext wire
    (freeDirectory R r (G.program.length+t) link V g entries desc) pp lp owner origin stride H
    (fun u => G.pinLayout u (ib u) (hb u) (sb u))}
    (writer : SharedWriters f layout src) (symbols : SymbolFrame layout (src anchor) ar.header.blocks ar.K ar.h decl group)
    (handoff : OwnedHandoff f layout src ar decl group template id count (visitedOwnedScans (ar:=ar) visits))
    {q : NativeAssignments.Routed (b := ar.b) (s := ar.s) owners}
    (receipt : ObservedOwned ar decl group (visitedOwnedScans (ar:=ar) visits) owners (f.receivedRows layout group) q)
    (N : Network D (FreeBlock R V) (fun _ => g)) (cell : N.Site → Fin C)
    (edgeID : N.Edge ↪ Fin m) (portID : FreeBlock R V ↪ Fin nP)
    {il : NativeIntervals.Layout} (ord : N.CrossingEdge cell ≃ Fin M) {row : Fin M ↪o Fin il.count}
    (label : Fin C → Label (ar.n+1) ar.header.d)
    {before scan : Fin (R+1) → ℕ → ℕ} {hz : ar.header.d^(ar.n+1) = il.alphabet}

set_option quotPrecheck false in
local notation "axis" => chosen ar.b ar.s q.1
local notation3 (prettyPrint := false) "host" => hostLayout (visitedOwnedScans (ar:=ar) visits).pub (visitedOwnedScans (ar:=ar) visits).output

variable (tab : HostTables (blocks := ar.header.blocks) (b := ar.b) (h := ar.h) (K := ar.K) (s := ar.s)
    N cell edgeID portID il ord row label (chosen ar.b ar.s q.1) group Fin.valEmbedding (visitedOwnedScans (ar:=ar) visits).pub (visitedOwnedScans (ar:=ar) visits).output origin stride before scan hz)
    (cap : ∀ u, load (cablePair ord (crossSrc N cell) (crossDst N cell) label)
      (crossWidth N cell ∘ ord.symm) u ≤ ar.header.blocks*(ar.h*ar.b))

variable {reports : Fin (R+1) → ReportLayout} (roster : ReceivedRows reports C)
    (sections : Fin (R+1) → OpenSuffix.Inputs)
    {post : Fin (R+1) → AfterTasks} {beforeTasks : Fin (R+1) → BeforeTasks}
    {banks : Fin (R+1) → CellBanks.Layout} {cursor : Fin (R+1) → ReportCursor} {description : Fin (R+1) → ℕ}
local notation3 (prettyPrint := false) "slot" => packedSlotEmbedding N cell ord label ar.header.blocks (ar.h*ar.b) cap
local notation3 (prettyPrint := false) "whereTeam" c => (roster.order.symm c).1

include writer symbols handoff receipt tab in
/-- The receiving teams read exactly the recovered physical routed bits and
substituted raw inputs, after their actual arbitrarily guessed reports have
already been stored. This applies also to rejected cell data. -/
theorem visited_report_words_at_inputs (hg : 0<g) (room : r*(2*(G.program.length+t)+R*link)≤V*g)
    (place : LivePlacement N cell edgeID portID lp) (input : Fin pins → Bool)
    (subst : ∀ u, SubstitutionAt (PL u) (extendGuess input) (H u).initial)
    (assigned : ∀ z : FreePort R r (G.program.length+t),
      let c := cell (N.attach (freeLane hg room z).1)
      owner c.val=group (label c axis))
    (pointers : ∀ u, (host u).packets=ar.header.packetBase ∧ (host u).singles=ar.singleBank)
    (baseAddr : origin=ar.cellBank) (strideAddr : stride=ar.cellStride) (cells : C≤ar.cells)
    (belongs : ∀ u (i : Fin (roster.cells u).length),group (label (roster.order ⟨u,i⟩) axis)=u)
    (ready : ∀ u, OpenSuffix.Ready (sections u) (teamPub u 0).val (readings (visits u).owned.val.2.2) W)
    (placed : ∀ u, OpenSuffix.Placement (sections u) ar (beforeTasks u) (teamPub u 0).val
      (readings (visits u).owned.val.2.2))
    (alloc : ∀ u, ReportAllocation (beforeTasks u) (post u) (banks u) (reports u) (roster.cells u) (cursor u))
    (seed : ∀ u, PreparedReportInput (teamPub u) (visits u).controls.val.2.2 (roster.cells u) (cursor u) (description u))
    (origins : ∀ u, (banks u).bankStart=origin) (strides : ∀ u, (banks u).stride=stride)
    (widths : ∀ u (i : Fin (roster.cells u).length), ((roster.cells u).get i).supplied=suppliedSize N cell (roster.order ⟨u,i⟩)) :
    SourceWords N cell edgeID portID hg room lp origin stride (freeBits G input)
      (routedEnds N cell owners slot q) (fun c => readings (visits (whereTeam c)).reports.val.2.2) := by
  have original := native_source_words_at_inputs writer symbols handoff receipt N cell edgeID portID ord label tab cap hg
    room place input subst assigned pointers baseAddr strideAddr cells
  have eqn : hostWords label axis group (owned).pub (owned).output =
      (fun c => OpenSuffix.hostImage (teamPub (whereTeam c) 0).val (readings (visits (whereTeam c)).owned.val.2.2)) := by
    funext c
    obtain ⟨⟨u,i⟩,rfl⟩ := roster.order.surjective c
    let c := roster.order ⟨u,i⟩
    have who : (roster.order.symm c).1=u := congrArg Sigma.fst (roster.order.symm_apply_apply ⟨u,i⟩)
    have receiver : group (label c axis)=u := belongs u i
    change OpenSuffix.hostImage ((owned).pub (group (label c axis)) 0).val (readings ((owned).output (group (label c axis)))) =
      OpenSuffix.hostImage (teamPub (roster.order.symm c).1 0).val (readings (visits (roster.order.symm c).1).owned.val.2.2)
    rw [who,receiver]
    rfl
  rw [eqn] at original
  exact roster.sourceWords_after_reports N cell edgeID portID hg room lp origin stride (freeBits G input)
    (routedEnds N cell owners slot q) (a := ar) (H := sections) (visits := fun u => visits u)
    place ready placed alloc seed origins strides widths original

include writer symbols handoff receipt tab in
/-- The global receiving schedule specializes the two independent facts about
the sender's actual input lanes and the receiver's own compact cell enumeration. -/
theorem visited_report_source_words (hg : 0<g) (room : r*(2*(G.program.length+t)+R*link)≤V*g)
    (place : LivePlacement N cell edgeID portID lp) (input : Fin pins → Bool)
    (subst : ∀ u, SubstitutionAt (PL u) (extendGuess input) (H u).initial)
    (assigned : ∀ c : Fin C, owner c.val=group (label c axis))
    (pointers : ∀ u, (host u).packets=ar.header.packetBase ∧ (host u).singles=ar.singleBank)
    (baseAddr : origin=ar.cellBank) (strideAddr : stride=ar.cellStride) (cells : C≤ar.cells)
    (belongs : ∀ u (i : Fin (roster.cells u).length), owner (roster.order ⟨u,i⟩).val=u)
    (ready : ∀ u, OpenSuffix.Ready (sections u) (teamPub u 0).val (readings (visits u).owned.val.2.2) W)
    (placed : ∀ u, OpenSuffix.Placement (sections u) ar (beforeTasks u) (teamPub u 0).val
      (readings (visits u).owned.val.2.2))
    (alloc : ∀ u, ReportAllocation (beforeTasks u) (post u) (banks u) (reports u) (roster.cells u) (cursor u))
    (seed : ∀ u, PreparedReportInput (teamPub u) (visits u).controls.val.2.2 (roster.cells u) (cursor u) (description u))
    (origins : ∀ u, (banks u).bankStart=origin) (strides : ∀ u, (banks u).stride=stride)
    (widths : ∀ u (i : Fin (roster.cells u).length), ((roster.cells u).get i).supplied=suppliedSize N cell (roster.order ⟨u,i⟩)) :
    SourceWords N cell edgeID portID hg room lp origin stride (freeBits G input)
      (routedEnds N cell owners slot q) (fun c => readings (visits (whereTeam c)).reports.val.2.2) := by
  exact visited_report_words_at_inputs visits writer symbols handoff receipt N cell edgeID portID ord label tab cap
    roster sections hg room place input subst (fun z => assigned (cell (N.attach (freeLane hg room z).1))) pointers
    baseAddr strideAddr cells (fun u i => (assigned (roster.order ⟨u,i⟩)).symm.trans (belongs u i)) ready placed alloc seed
    origins strides widths

end Diagonal.ExternalSew.Fragments

end BorderVNP
end Computability
end OAI
