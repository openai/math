import OAI.Computability.BorderVNP.CubeScatterPhysicalDeclaration
import OAI.Computability.BorderVNP.CubeScatterReturnedOwnedViews
import OAI.Computability.BorderVNP.CubeTeamOwnedReturnedAssignment

/-! # Recovering the routed assignment from the returning native machines

The public minimum and all actual owned scans decode the raw shared rows.
The declaration now fixes the greedy schedule for the decoded selectors.
Replay then uses exactly the original owned entry memories, register banks,
and event lists. Its one recovered assignment accounts for the private tapes
and the final endpoint and vertex banks of those same runs.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction

open VPVNP BurstRAM Diagonal.Layout RoutingISA RoutingISA.Transmission Routing
open BorderVNP.Cube BorderVNP.Cube.Physical BorderVNP.Cube.Scatter
open TeamRows Scatter.Assignment DiagonalTallyPacketEmit

variable {R r t d link inner n w : ℕ} {Edge : Type} {G : Wiring R r t d link inner n Edge}
variable {pin : Fin d → Bool} {ext : Exterior R r link → Bool} {L : WireLayout (R+1) r link}
variable {D : Packing.Directory.Layout} {pp lp : ℕ → ℕ × ℕ} {owner : ℕ → Fin (R+1)} {origin stride : ℕ}
variable {H : Fin (R+1) → TeamHistory w} {pins : Fin (R+1) → Pins.Layout}
variable {f : ReturnedDelivery G pin ext L D pp lp owner origin stride H pins} {g : SharedRows.Layout}
variable {src : Fin (R+1) → ℕ → ℕ} {anchor : Fin (R+1)}

/-- The fitted physical inputs and consecutive returns from transmission, installation,
and the owned traversal. The last installer registers and memory are the actual
entry state of the runs recorded in `F`. -/
structure OwnedHandoff (f : ReturnedDelivery G pin ext L D pp lp owner origin stride H pins)
    (g : SharedRows.Layout) (src : Fin (R+1) → ℕ → ℕ) (ar : CubeArena.Layout)
    (decl : LengthDeclaration ar.n ar.header.d) (group : Fin ar.header.d → Fin (R+1))
    (template : Frame) (id : TableEntry ar.n ar.b ar.h ar.K ar.s → ℕ) (count : ℕ)
    (F : TeamRows.Returns (Fin (R+1)) ar w) : Prop where
  /-- The public argument bank is the one used by the completed transmission. -/
  pub : ∀ u, F.pub u = (H u).pub
  /-- The macro bank stays fixed between the two native stages. -/
  macros : ∀ u, F.macros u = (H u).macros
  /-- The row-view bank base and spacing agree with the scanner's allocation. -/
  banks : g.banks = ar.pairBase
  /-- The physical stride at every directed view. -/
  spacing : g.stride = ar.pairStride
  /-- Fitted arithmetic and scratch allocation of each team. -/
  room : ∀ u, ar.ReplayRoom w (readings (H u).pub 0)
  /-- The table checked by the actual returned delivery is the scanner's table. -/
  table : ∀ u, f.table = ar.table (readings (H u).pub 0) count
  /-- The returned primary frame is the physical shared writer's primary frame. -/
  frame : ∀ u, g.frame = readings (H u).pub 0
  /-- The shared writer's source contains the advertised declaration and owner words. -/
  source : ∀ u, ar.ScannerWords (readings (H u).pub 0) u.val decl.1.val (fun x => (group x).val)
    (readings (H u).pub) (src u) decl.2
  /-- Constant table entries and their physical placement fit the word width. -/
  fits : ∀ u, CubeConstants.Fits (CubeConstants.inArena template ar.stop ar.n ar.b ar.h ar.K ar.s)
    w (readings (H u).pub 0) (CubeConstants.idBase ar.stop ar.n ar.b ar.h ar.K ar.s) id
  /-- Actual received memory contains the constant installer fields. -/
  fields : ∀ u, CubeConstants.Fields (CubeConstants.inArena template ar.stop ar.n ar.b ar.h ar.K ar.s)
    (readings (H u).pub 0) (CubeConstants.idBase ar.stop ar.n ar.b ar.h ar.K ar.s)
    (readings (H u).history.val.2.2)
  /-- The actual installer path starts at the route's returned registers and RAM,
  and ends at the owned scanner's input registers and RAM. -/
  install : ∀ u, ∃ es, Runs (H u).pub (H u).macros (CubeConstants.install id)
    (H u).history.val.2.1 (H u).history.val.2.2 es (F.initialRegs u) (F.input u)

open private loads_congr from OAI.Computability.BorderVNP.CubePhysicalGreedyTally

/-- The native schedule's stored owner words agree with the least-load rule
on the advertised declaration itself, before any selector tuple is decoded. -/
theorem declared_owner_of_native_schedule {l : GroupWeights.Layout} {teams : TeamNative.Layout}
    {before after : ℕ → ℕ} (result : GroupWeights.ScheduleResult l teams before after)
    {a blocks b K h : ℕ} (advertised : LengthDeclaration a l.groups) {Data : Type*} [Fintype Data]
    (label : Fin l.cells → Label (a+1) l.groups) (recv : Data → Fin l.cells) (dataWidth : Data → ℕ)
    (image : GroupWeights.PhysicalImage l before blocks b K h advertised label recv dataWidth)
    (group : Fin l.groups → Fin (teams.r+1)) (stored : ∀ x, after (teams.owners+x.val) = (group x).val) :
    group = fun x => TeamNative.owner teams.r
      (declarationWeight blocks b K h advertised label recv dataWidth) x.val := by
  funext x
  apply Fin.ext
  rw [←stored x,result.owners x.val x.isLt]
  apply congrArg Fin.val
  apply congrArg firstMinimum
  apply loads_congr
  intro j hj
  have hk := hj.trans x.isLt
  exact (image.weight_eq ⟨j,hk⟩).trans (by simp [declarationWeight,hk])

variable (ar : CubeArena.Layout) (decl : LengthDeclaration ar.n ar.header.d)
variable {Cell Data : Type*} [Fintype Data]
variable (label : Cell → Label (ar.n+1) ar.header.d) (recv : Data → Cell) (dataWidth : Data → ℕ)

/-- Team ownership computed directly from the advertised row and incoming volumes. -/
def declaredTeam (R : ℕ) (x : Fin ar.header.d) : Fin (R+1) :=
  TeamNative.owner R (declarationWeight ar.header.blocks ar.b ar.K ar.h decl label recv dataWidth) x.val

private theorem declaredTeam_eq (shared : DeclaredShared ar.header.blocks ar.b ar.h ar.K ar.s decl) :
    declaredTeam ar decl label recv dataWidth R = greedyOwner R ar.b ar.s label recv dataWidth shared.1.val := by
  have actual := (passesLengths_iff ar.b ar.s shared.1.val decl).mp shared.1.property
  funext x
  simp only [declaredTeam,greedyOwner,actual]

variable (group : Fin ar.header.d → Fin (R+1))
variable (F : TeamRows.Returns (Fin (R+1)) ar w)
variable (owners : (Packet ar.n ar.header.d ar.header.blocks → Selector ar.n ar.K ar.h) → Fin ar.header.d → Fin (R+1))

/-- A single assignment spells all original shared and private observations,
has their actual owner allocation and tape lengths, and satisfies the physical
trace, cost and endpoint conclusions for the original returning states. -/
structure ObservedOwned (raw : Symbols ar.header.d → List Bool)
    (q : NativeAssignments.Routed (b := ar.b) (s := ar.s) owners) : Prop where
  /-- The recovered selectors use the scheduler's original owner function. -/
  allocation : owners q.1 = group
  /-- Exact lengths of the original private tapes. -/
  lengths : ∀ u, (F.tape ar u).length = (teamPrivateKeys ar.b ar.s q.1 decl.1 group u).length
  /-- Exact raw common rows and chronological native choices. -/
  observed : Routed.Realizes owners Fin.valEmbedding (F.layout ar Fin.valEmbedding decl)
    (fun _ => ar.header.packetBase) (fun _ => ar.singleBank) q (F.observed ar decl raw)
  /-- The original returns provide the decoded endpoint banks and full traversal conclusions. -/
  recovered : TeamRows.Recovered ar owners Fin.valEmbedding F decl q

variable {template : Frame} {id : TableEntry ar.n ar.b ar.h ar.K ar.s → ℕ} {count : ℕ}

private theorem recover_decoded (writer : SharedWriters f g src)
    (symbols : SymbolFrame g (src anchor) ar.header.blocks ar.K ar.h decl group)
    (handoff : OwnedHandoff f g src ar decl group template id count F)
    (shared : DeclaredShared ar.header.blocks ar.b ar.h ar.K ar.s decl)
    (emits : sharedWords decl shared = f.receivedRows g group)
    (scheduled : group = owners shared.1.val) :
    ∃! q, ObservedOwned ar decl group F owners (f.receivedRows g group) q := by
  choose _ install using handoff.install
  have inputs u := writer.replayInputs_after_install ar decl group symbols u template id count
      handoff.banks handoff.spacing (handoff.room u) (handoff.table u) (handoff.frame u) (handoff.source u)
      (handoff.fits u) (handoff.fields u) (install u)
  have room u : ar.ReplayRoom w (readings (F.pub u) 0) := handoff.pub u ▸ handoff.room u
  have words u := (inputs u).1
  have views u := (inputs u).2
  obtain ⟨sizes, q, ⟨hs,real,rec⟩, _⟩ :=
    F.recover ar owners Fin.valEmbedding decl (f.receivedRows g group) shared emits room f.word
      (fun u => by simpa only [handoff.pub, ←scheduled, Function.comp_def, Fin.valEmbedding, Function.Embedding.coeFn_mk] using words u)
      (fun u => by simpa only [handoff.pub, ←scheduled, Function.comp_def, Fin.valEmbedding, Function.Embedding.coeFn_mk] using views u)
  let z := F.observed ar decl (f.receivedRows g group)
  have accepts := Routed.accepts_of_decoded owners z shared emits sizes
  have unique := (Routed.accepts_iff_unique_dispatch owners Fin.valEmbedding (F.layout ar Fin.valEmbedding decl)
    (fun _ => ar.header.packetBase) (fun _ => ar.singleBank) (fun _ => rfl) (fun _ => rfl) z).mp accepts
  refine ⟨q,⟨hs ▸ scheduled.symm, ?_,real,rec⟩, fun q' h => unique.unique h.observed real⟩
  intro u
  rw [hs,scheduled]
  exact sizes u

/-- Decode the shared rows from the actual native header/minimum and team
returns, then reconstruct the unique greedy-owned private assignment on the
very same team histories. The scalar header hypotheses specify the locations
and word bounds of the actual instructions' operands. -/
theorem SharedWriters.recover_owned_family (writer : SharedWriters f g src)
    (scheduled : group = declaredTeam ar decl label recv dataWidth R)
    (symbols : SymbolFrame g (src anchor) ar.header.blocks ar.K ar.h decl group)
    (handoff : OwnedHandoff f g src ar decl group template id count F) (copies : 1 ≤ ar.K)
    (labels : ar.header.d^(ar.n+1) ≤ 2^w)
    (packets : Physical.Owned.packetTrials ar.n ar.header.d ar.header.blocks*(ar.h*ar.s) < 2^w)
    (dyn : HeaderDecode.Layout) {p : Arg → Word w} {mc : TeamOpcode.Macros w 8}
    {reg : Bank w} {m : Memory w} {es u mu fs out final}
    (decode : Runs p mc HeaderDecode.program reg m es u mu)
    (minimum : Runs p mc CubeLengths.minimum u mu fs out final)
    (fits : HeaderDecode.Fits dyn w) (atFrame : HeaderDecode.AtFrame dyn (readings p) (readings m))
    (primary : readings p 0+63 < 2^w) (header : dyn.header+12 < 2^w) (totalsRoom : dyn.totals+dyn.a ≤ 2^w)
    (separate : dyn.dense+dyn.entries ≤ dyn.totals ∨ dyn.totals+dyn.a ≤ dyn.dense)
    (sumRoom : dyn.d*dyn.d*dyn.cap < 2^w) (radix : dyn.d = ar.header.d) (axes : dyn.a = ar.n+1) :
    let l := CubeLengths.layout (readings p) (readings mu)
    CubeLengths.Fits w (readings p) (readings mu) → l.claimed = dyn.dense → l.totals = dyn.totals →
      l.coordinates = dyn.a → l.chosen = decl.1.val → CubeLengths.StoredRows (readings mu) l.claimed decl.2 →
      (∃! q, ObservedOwned ar decl group F (greedyOwner R ar.b ar.s label recv dataWidth) (f.receivedRows g group) q) ∧
        ∀ j : Fin (ar.n+1), readings mu (l.totals+j.val) = ∑ row, decl.2 row j := by
  intro l bounds claimed totals coords chosen stored
  obtain ⟨scans⟩ := writer.physical_scans ar decl group symbols template id count handoff.banks handoff.spacing
    copies handoff.room handoff.table handoff.frame handoff.source handoff.fits handoff.fields (fun u => by
      obtain ⟨events,install⟩ := handoff.install u
      exact ⟨events,F.initialRegs u,F.input u,F.events u,F.finalRegs u,F.output u,install,
        by simpa only [handoff.pub,handoff.macros] using F.path u⟩)
  obtain ⟨⟨shared,emits,_⟩,sums⟩ := writer.decode_raw_scheduled symbols scans labels packets (handoff.room anchor).capFit
    dyn decode minimum fits atFrame primary header totalsRoom separate sumRoom radix axes bounds claimed totals coords chosen stored
  exact ⟨recover_decoded ar decl group F _ writer symbols handoff shared emits
    (scheduled.trans (declaredTeam_eq ar decl label recv dataWidth shared)),sums⟩

end TeamContraction

end BorderVNP
end Computability
end OAI
