import OAI.Computability.BorderVNP.DiagonalOwnedCheckedMinimum

/-! # The actual owned traversal on the already checked least coordinate -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction

open VPVNP BurstRAM Diagonal.Layout RoutingISA RoutingISA.Transmission RoutingISA.Evaluator SignedPrep
open BorderVNP.Cube Physical Physical.NativeAssignments Scatter Scatter.Assignment
open DiagonalTallyPacketEmit
open scoped BigOperators
open private declaredTeam_eq from OAI.Computability.BorderVNP.CubeScatterReturnedOwnedFamily

variable {R r t d link inner n w : ℕ} {Edge : Type} {G : Wiring R r t d link inner n Edge}
    {pin : Fin d → Bool} {ext : Exterior R r link → Bool} {L : Routing.WireLayout (R+1) r link}
    {D : Packing.Directory.Layout} {pp lp : ℕ → ℕ × ℕ} {owner : ℕ → Fin (R+1)} {origin stride : ℕ}
    {H : Fin (R+1) → TeamHistory w} {pins : Fin (R+1) → Pins.Layout}
    {f : ReturnedDelivery G pin ext L D pp lp owner origin stride H pins} {g : SharedRows.Layout}
    {src : Fin (R+1) → ℕ → ℕ} {anchor : Fin (R+1)}

variable (ar : CubeArena.Layout) (decl : LengthDeclaration ar.n ar.header.d)
    {Cell Data : Type*} [Fintype Data]
    (label : Cell → Label (ar.n+1) ar.header.d) (recv : Data → Cell) (dataWidth : Data → ℕ)
    (group : Fin ar.header.d → Fin (R+1)) (template : Frame)
    (id : TableEntry ar.n ar.b ar.h ar.K ar.s → ℕ) (count : ℕ)

local notation "owners" => greedyOwner R ar.b ar.s label recv dataWidth
set_option quotPrecheck false in
local notation "pub" => fun u : Fin (R+1) => (H u).pub
set_option quotPrecheck false in
local notation "mac" => fun u : Fin (R+1) => (H u).macros
local notation "pack" => CubeConstants.inArena template ar.stop ar.n ar.b ar.h ar.K ar.s
local notation "idBase" => CubeConstants.idBase ar.stop ar.n ar.b ar.h ar.K ar.s

/-- These premises consist of the true routed buffers, the installed constant operands,
and the decoded declaration and least-coordinate checks. The input declaration has passed the native minimum test. The program constructs
every assignment's native history and recovers the original assignment on every return. -/
noncomputable def SharedWriters.minimumOwnedEquiv (writer : SharedWriters f g src)
    (scheduled : group = declaredTeam ar decl label recv dataWidth R)
    (symbols : SymbolFrame g (src anchor) ar.header.blocks ar.K ar.h decl group)
    (banks : g.banks=ar.pairBase) (spacing : g.stride=ar.pairStride)
    (room : ∀ u, ar.ReplayRoom w (readings (H u).pub 0)) (table : ∀ u, f.table=ar.table (readings (H u).pub 0) count)
    (fp : ∀ u, g.frame=readings (H u).pub 0)
    (source : ∀ u, ar.ScannerWords (readings (H u).pub 0) u.val decl.1.val (fun x => (group x).val)
      (readings (H u).pub) (src u) decl.2)
    (fit : ∀ u, CubeConstants.Fits pack w (readings (H u).pub 0) idBase id)
    (fields : ∀ u, CubeConstants.Fields pack (readings (H u).pub 0) idBase (readings (H u).history.val.2.2))
    (installed : ∀ u, Evaluator.Returns (CubeConstants.install id) (H u).pub (H u).macros
      (H u).history.val.2.1 (H u).history.val.2.2)
    (copies : 1 ≤ ar.K) (labels : ar.header.d^(ar.n+1) ≤ 2^w)
    (packets : Physical.Owned.packetTrials ar.n ar.header.d ar.header.blocks*(ar.h*ar.s) < 2^w)
    (least : decl.1=firstMinimum (fun j => ∑ pair,decl.2 pair j)) :
    OwnedRuns ar pub mac (fun u => (installed u).val.2.1) (fun u => (installed u).val.2.2) ≃
      Matching ar owners decl (f.receivedRows g group) := by
  let regs u := (installed u).val.2.1
  let mem u := (installed u).val.2.2
  apply ownedEquiv ar owners decl (f.receivedRows g group) pub mac regs mem
  · intro z
    let F := ownedHistory ar pub mac regs mem z
    have handoff : OwnedHandoff f g src ar decl group template id count F :=
      ⟨fun _ => rfl,fun _ => rfl,banks,spacing,room,table,fp,source,fit,fields,
        fun u => ⟨_,(installed u).property⟩⟩
    obtain ⟨q,obs,_⟩ := writer.recover_owned_minimum ar decl label recv dataWidth group id F
      scheduled symbols handoff copies labels packets least
    exact ⟨q,obs.allocation.symm ▸ obs⟩
  · intro q u
    have shape : Routed.trueDeclaration ar.b ar.s q.val.1=decl := q.property.1
    have equal := declaredTeam_eq (R := R) ar (Routed.trueDeclaration ar.b ar.s q.val.1) label recv dataWidth
      (Routed.physicalShared owners q.val)
    have assigned : group=owners q.val.1 := scheduled.trans
      ((congrArg (fun x => declaredTeam ar x label recv dataWidth R) shape).symm.trans equal)
    have emits := (Routed.encode_shared owners q.val).symm.trans q.property.2
    obtain ⟨words,views⟩ := writer.replayInputs_after_install ar decl group symbols u template id count
      banks spacing (room u) (table u) (fp u) (source u) (fit u) (fields u) (installed u).property
    exact ar.replaySetup owners Fin.valEmbedding q.val u (H u).pub (mem u) decl (f.receivedRows g group)
      shape emits (room u) (by simpa only [assigned,Function.comp_def,Fin.valEmbedding,Function.Embedding.coeFn_mk] using words)
      (by simpa only [assigned,Function.comp_def,Fin.valEmbedding,Function.Embedding.coeFn_mk] using views)

/-- Read the actual endpoint banks and all selector and tape digits of the
chosen assignment after the minimum check. -/
theorem SharedWriters.minimumOwnedReceipt (writer : SharedWriters f g src)
    (scheduled : group = declaredTeam ar decl label recv dataWidth R)
    (symbols : SymbolFrame g (src anchor) ar.header.blocks ar.K ar.h decl group)
    (banks : g.banks=ar.pairBase) (spacing : g.stride=ar.pairStride)
    (room : ∀ u, ar.ReplayRoom w (readings (H u).pub 0)) (table : ∀ u, f.table=ar.table (readings (H u).pub 0) count)
    (fp : ∀ u, g.frame=readings (H u).pub 0)
    (source : ∀ u, ar.ScannerWords (readings (H u).pub 0) u.val decl.1.val (fun x => (group x).val)
      (readings (H u).pub) (src u) decl.2)
    (fit : ∀ u, CubeConstants.Fits pack w (readings (H u).pub 0) idBase id)
    (fields : ∀ u, CubeConstants.Fields pack (readings (H u).pub 0) idBase (readings (H u).history.val.2.2))
    (installed : ∀ u, Evaluator.Returns (CubeConstants.install id) (H u).pub (H u).macros
      (H u).history.val.2.1 (H u).history.val.2.2)
    (copies : 1 ≤ ar.K) (labels : ar.header.d^(ar.n+1) ≤ 2^w)
    (packets : Physical.Owned.packetTrials ar.n ar.header.d ar.header.blocks*(ar.h*ar.s) < 2^w)
    (least : decl.1=firstMinimum (fun j => ∑ pair,decl.2 pair j))
    (z : OwnedRuns ar pub mac (fun u => (installed u).val.2.1) (fun u => (installed u).val.2.2)) :
    let E := writer.minimumOwnedEquiv ar decl label recv dataWidth group template id count scheduled symbols
      banks spacing room table fp source fit fields installed copies labels packets least
    let F := ownedHistory ar pub mac (fun u => (installed u).val.2.1) (fun u => (installed u).val.2.2) z
    ObservedOwned ar decl group F owners (f.receivedRows g group) (E z).val := by
  intro E F
  let q := E z
  have known : ObservedOwned ar decl (owners q.val.1) F owners (f.receivedRows g group) q.val := by
    dsimp only [q,E,F]
    unfold SharedWriters.minimumOwnedEquiv
    apply ownedEquiv_receipt
  have shape : Routed.trueDeclaration ar.b ar.s q.val.1=decl := q.property.1
  have same := declaredTeam_eq (R:=R) ar (Routed.trueDeclaration ar.b ar.s q.val.1) label recv dataWidth
    (Routed.physicalShared owners q.val)
  have assigned : group=owners q.val.1 := scheduled.trans
    ((congrArg (fun x => declaredTeam ar x label recv dataWidth R) shape).symm.trans same)
  exact Eq.mp (congrArg (fun h => ObservedOwned ar decl h F owners (f.receivedRows g group) q.val) assigned.symm) known

end TeamContraction

end BorderVNP
end Computability
end OAI
