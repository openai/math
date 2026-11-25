import OAI.Computability.BorderVNP.DiagonalTrackedPowerRead
import OAI.Computability.BorderVNP.DiagonalOuterPowerHosts
import OAI.Computability.BorderVNP.DiagonalExternalSewEnrichedSum
import OAI.Computability.BorderVNP.DiagonalExternalFreeCanonical
import OAI.Computability.BorderVNP.CubePhysicalRoutedTallies

/-! # Reading the original terminal power word from its actual sewn cube path

A routed cable may expose different bits to its two endpoint sites. The pullback
therefore extends the words at the chosen host only. It reassembles the exterior
cables and the delivered grouped free fields before zero-padding unused lanes.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal.ExternalSew

open Crossing CellEntries BorderVNP.Cube BorderVNP.Cube.Physical
open private extendWires from OAI.Computability.BorderVNP.PackedInheritedRoundValue
open scoped Classical
set_option maxHeartbeats 1800000

section Sewing

variable {D n d blocks b h K s exp : ℕ} {A Fine Free Cable Group Cell Team Param Gadget : Type}
    [Fintype Cable] [DecidableEq Cell] [Fintype Team] [Fintype Param]
    {bits : A → ℕ} {cwidth : Cable → ℕ} (N : Network D A bits) (fine : Fine ↪ Σ a, Fin (bits a))
    (B : Bundle (FineView.layout N fine) Free Cable cwidth) (width : Group → ℕ)
    (lane : Free ↪ Σ g, Fin (width g)) (owner : Group → N.Site)
    (aligned : ∀ f, owner (lane f).1 = B.layout.attach f)
    (t : Tracked Team Param Gadget exp N) {cell : N.Site → Cell}

variable (slot : LiveBit (B.layout.packExternal width owner) cell ↪ Slot n d blocks (h*b)) (a : Physical.Path (B.layout.packExternal width owner) cell n d blocks b h K s)
    (bank : Ports width)

/-- The original incident cables and free words obtained from one actual sewn
host, including the chosen path's own half of every externally sewn cable. -/
noncomputable def sewnPathPowerInput (v : N.Site) : PowerInput N :=
  let z := extendWires (B.layout.packExternal width owner) v (pathEdges slot a v)
  let external := Network.readExternal width lane bank
  ⟨fun e => z (.inl e),FineView.extend fine (B.joined external (fun e => z (.inr e)))⟩

/-- Free grouping, exterior sewing and fine-slot extraction preserve the selected
unary bit on the specified path, even when the opposite endpoint has a different
value. Both readings take place at the tracked slot's own host. -/
theorem sewn_localUse (w : PowerSlot Team Param exp) :
    ((B.tracked (FineView.tracked N fine t)).packExternal width lane owner aligned).words.localUse (pathEdges slot a) (fun _ f => bank f.val) w.1 w.2.1 w.2.2 =
      t.powerRead w (sewnPathPowerInput N fine B width lane owner slot a bank (t.words.site w)) := by
  let v := t.words.site w
  let z := extendWires (B.layout.packExternal width owner) v (pathEdges slot a v)
  let free := Network.readExternal width lane bank
  have hz : (fun e : Packing.Inherited.Incident (B.layout.packExternal width owner) v => z e.val) = pathEdges slot a v := by
    funext e j
    simp only [z,extendWires,dite_eq_left e.property]
  have hl := congrArg (fun edges => ((B.tracked (FineView.tracked N fine t)).packExternal width lane owner aligned).words.selected v edges (fun f => bank f.val) w) hz
  exact hl.symm.trans (congrFun (B.read (FineView.tables N fine t.words.selected) z free v) w)

/-- Changing unused delivered words keeps the complete reconstructed terminal
input at each chosen host, with every asymmetric path endpoint held fixed. -/
theorem sewnPathPowerInput_congr (other : Ports width) (v : N.Site)
    (agree : ∀ f, bank (lane f).1 (lane f).2 = other (lane f).1 (lane f).2) :
    sewnPathPowerInput N fine B width lane owner slot a bank v =
      sewnPathPowerInput N fine B width lane owner slot a other v := by
  have same : Network.readExternal width lane bank = Network.readExternal width lane other := by
    funext f _
    exact agree f
  unfold sewnPathPowerInput
  rw [same]

end Sewing


section Enriched
open Crossing Shortening Cover Adaptive Packing Packing.DeckGrid
open PackedHistoryCircuit PackedHistoryCircuit.Normalized PackedHistoryCircuit.Normalized.EnrichedOuter
open PublicCapacity CellEntries TeamContraction ParseBatch
open scoped BigOperators Classical BorderVNP.Epoch.Cube

universe u

variable {D m start T : ℕ} [NeZero D] {K E : Type} [Field K] [Field E] {e : PaidIdentity K D m}
    {S : Normalized.SiteSchedule e} {shape : ℕ → Shape} {W : ℕ → Type} [∀ t, Fintype (W t)]
    {V : ℕ → ℕ → Type} [∀ t j, Fintype (V t j)] {w : ℕ → ℕ → ℕ}
    {R r t pins link inner n copies : ℕ} {Edge : Type} (G : Wiring R r t pins link inner n Edge)
    (axes gridDepth : ℕ) (order : Fin (GridHosts.tileCount axes gridDepth) ≃ (Fin axes → Deck (gridDepth+2)))
    (position : (Fin axes → Deck (gridDepth+2)) → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1})
    {deep : S.floor+1+S.drop*T ≤ start} (count : (fan S)^T*copies = R+1)
    {good : ∀ j, EnrichedOuter.State S start (Fin (GridHosts.tileCount axes gridDepth))
      (fun _ => copies*GridHosts.inputBlockWidth r n axes gridDepth) shape W j → Prop}
    (M : EnrichedOuter.Machine.{0,u} deep good V w) (bottom : Admissible good 0)
    (installed : bottom.val.pack.layout = (wiredGrid G axes gridDepth order position).groupedRepeat
      (fun _ : Fin (GridHosts.tileCount axes gridDepth) => GridHosts.inputBlockWidth r n axes gridDepth)
      order copies)
    {Team Param Gadget Hidden : Type} [Fintype Team] [Fintype Param] {exp : ℕ}
    (y : e.Entry → E)
    (hy : ∀ f : MvPolynomial e.Entry ℤ, MvPolynomial.eval₂Hom (Int.castRingHom K) e.entry f = 0 →
      MvPolynomial.eval₂Hom (Int.castRingHom E) y f = 0)
    (pos : e.Entry → Gadget) (base : Hidden → Tracked Team Param Gadget exp bottom.val.pack.layout)

/-- Enumerate the nested original team owners of the tagged terminal. -/
noncomputable local instance sewnPowerTeam {j : ℕ} : Fintype (Port (fan S) Team j) := Replay.batchFinite (fan S) Team j


set_option synthInstance.maxSize 4000
set_option maxRecDepth 6000

variable (hg : 0 < GridHosts.inputBlockWidth r n axes gridDepth) (q : (packHistory bottom M.epoch T).Index)
    (z : Fin ((fan S)^T) → Hidden) {cn cd blocks cb ch ck cs : ℕ} {Cell : Type} [DecidableEq Cell]
    {cell : (enrichedSewnLayout G axes gridDepth order position count M bottom installed q).Site → Cell}
    (slot : LiveBit (enrichedSewnLayout G axes gridDepth order position count M bottom installed q) cell ↪ Slot cn cd blocks (ch*cb))
    (a : Physical.Path (enrichedSewnLayout G axes gridDepth order position count M bottom installed q) cell cn cd blocks cb ch ck cs)
    (bank : Ports (fun _ : FreeBlock R (GridHosts.tileCount axes gridDepth) => GridHosts.inputBlockWidth r n axes gridDepth))

/-- The local terminal cable and port assignments for one actually attained sewn
cube host. Its original nested external words use the inverse copy flattening. -/
noncomputable def enrichedPathPowerInput (v : ((packHistory bottom M.epoch T).term q).val.pack.layout.Site) :
    PowerInput ((packHistory bottom M.epoch T).term q).val.pack.layout :=
  let L := (flattenPack T ((packHistory bottom M.epoch T).term q).val.pack).layout
  let h := enrichedBlockHosts G axes gridDepth order position count M bottom installed q
  let fine := GridHosts.groupedLane G (GridHosts.tileCount axes gridDepth) Fintype.card_pos ((fan S)^T) copies count
  let room := GridHosts.gridRoom G (show 0 < GridHosts.tileCount axes gridDepth from Fintype.card_pos)
  let old := sewnPathPowerInput L fine h.bundle (fun _ : FreeBlock R (GridHosts.tileCount axes gridDepth) =>
    GridHosts.inputBlockWidth r n axes gridDepth) (freeLane hg room) h.groupOwner slot a bank v
  ⟨old.edges,nestedPorts _ (fan S) T old.ports⟩

/-- The selected bit of the genuine enriched exterior path reads the pre-sewing
terminal's unary slot on this same path's old cables and supplied free fields. -/
theorem enrichedSewn_localUse (w0 : PowerSlot (Port (fan S) Team T) Param exp) :
    let t0 := EnrichedOuterReplay.terminal M y hy pos bottom base q z
    (enrichedSewnTerm G axes gridDepth order position count M bottom installed y hy pos base hg q z).words.localUse
      (pathEdges slot a) (fun _ f => bank f.val) w0.1 w0.2.1 w0.2.2 =
      t0.powerRead w0 (enrichedPathPowerInput G axes gridDepth order position count M bottom installed hg q slot a bank
        (t0.words.site w0)) := by
  let L := (flattenPack T ((packHistory bottom M.epoch T).term q).val.pack).layout
  let h := enrichedBlockHosts G axes gridDepth order position count M bottom installed q
  let fine := GridHosts.groupedLane G (GridHosts.tileCount axes gridDepth) Fintype.card_pos ((fan S)^T) copies count
  let room := GridHosts.gridRoom G (show 0 < GridHosts.tileCount axes gridDepth from Fintype.card_pos)
  let tag := EnrichedOuterReplay.terminal M y hy pos bottom base q z
  exact sewn_localUse L fine h.bundle (fun _ : FreeBlock R (GridHosts.tileCount axes gridDepth) =>
    GridHosts.inputBlockWidth r n axes gridDepth) (freeLane hg room) h.groupOwner (h.groupAligned hg room)
    tag.flat slot a bank w0

omit [DecidableEq Cell] in
/-- The processor team reading the sewn unary bit is the selected owner of its
actual retained original host cell on this very cube path. -/
theorem enrichedSewn_power_owner {Owner : Type} (label : Cell → Label (cn+1) cd) (team : Fin cd → Owner)
    (w0 : PowerSlot (Port (fan S) Team T) Param exp) :
    let old := portEquiv (fan S) Team T w0.1
    pathOwner label team a (.inl ((enrichedSewnTerm G axes gridDepth order position count M bottom installed
      y hy pos base hg q z).words.site w0)) =
      team (label (cell ((enrichedOuterHosts M bottom q).site ⟨old.1,(base (z old.1)).words.site (old.2,w0.2)⟩))
        (chosen cb cs a.2.2.2.1)) := by
  exact congrArg (fun v => team (label (cell v) (chosen cb cs a.2.2.2.1)))
    (EnrichedOuterReplay.terminal_power_site y hy pos M bottom base q z w0)

/-- The actual path reconstructs the same old terminal wires and grouped words
when two supplied free buffers agree on every emitted literal and pin lane. -/
theorem enrichedPathPowerInput_congr
    (other : Ports (fun _ : FreeBlock R (GridHosts.tileCount axes gridDepth) => GridHosts.inputBlockWidth r n axes gridDepth))
    (agree : ∀ f, let field := freeLane hg (GridHosts.gridRoom G Fintype.card_pos) f
      bank field.1 field.2 = other field.1 field.2)
    (v : ((packHistory bottom M.epoch T).term q).val.pack.layout.Site) :
    enrichedPathPowerInput G axes gridDepth order position count M bottom installed hg q slot a bank v =
      enrichedPathPowerInput G axes gridDepth order position count M bottom installed hg q slot a other v := by
  let L := (flattenPack T ((packHistory bottom M.epoch T).term q).val.pack).layout
  let h := enrichedBlockHosts G axes gridDepth order position count M bottom installed q
  let fine := GridHosts.groupedLane G (GridHosts.tileCount axes gridDepth) Fintype.card_pos ((fan S)^T) copies count
  let room := GridHosts.gridRoom G (show 0 < GridHosts.tileCount axes gridDepth from Fintype.card_pos)
  have he := sewnPathPowerInput_congr L fine h.bundle (fun _ : FreeBlock R (GridHosts.tileCount axes gridDepth) =>
    GridHosts.inputBlockWidth r n axes gridDepth) (freeLane hg room) h.groupOwner slot a bank other v agree
  exact congrArg (fun inp : PowerInput L =>
    (⟨inp.edges,nestedPorts _ (fan S) T inp.ports⟩ : PowerInput ((packHistory bottom M.epoch T).term q).val.pack.layout)) he

open RoutingISA RoutingISA.Transmission RoutingISA.Pins VPVNP.BurstRAM
variable {word entries desc origin stride : ℕ} {inputPin : Fin pins → Bool} {ext : Exterior R r link → Bool}
    {wire : Routing.WireLayout (R+1) r link} {pp lp : ℕ → ℕ × ℕ} {own : ℕ → Fin (R+1)}
    {H : Fin (R+1) → TeamHistory word} {ib hb sb : Fin (R+1) → ℕ}
    (delivery : ReturnedDelivery G inputPin ext wire
      (freeDirectory R r (G.program.length+t) link (GridHosts.tileCount axes gridDepth)
        (GridHosts.inputBlockWidth r n axes gridDepth) entries desc)
      pp lp own origin stride H (fun u => G.pinLayout u (ib u) (hb u) (sb u)))
    (pin : Fin pins → Bool)
    (subst : ∀ u, SubstitutionAt (G.pinLayout u (ib u) (hb u) (sb u)) (extendGuess pin) (H u).initial)

include delivery subst in
/-- The bit observed at this sewn path's host on the returning machine memories
is the pre-sewing terminal bit with the canonical substituted pin and literal
lanes. No equality of two distinct cable endpoint reads is required. -/
theorem enrichedSewn_received_localUse (w0 : PowerSlot (Port (fan S) Team T) Param exp) :
    let t0 := EnrichedOuterReplay.terminal M y hy pos bottom base q z
    let received := receivedBank (V := GridHosts.tileCount axes gridDepth) (g := GridHosts.inputBlockWidth r n axes gridDepth)
      lp own origin stride H
    let fixedBank := canonicalBank (G := G) hg (GridHosts.gridRoom G Fintype.card_pos) pin
    (enrichedSewnTerm G axes gridDepth order position count M bottom installed y hy pos base hg q z).words.localUse
      (pathEdges slot a) (fun _ f => received f.val) w0.1 w0.2.1 w0.2.2 =
      t0.powerRead w0 (enrichedPathPowerInput G axes gridDepth order position count M bottom installed hg q slot a fixedBank
        (t0.words.site w0)) := by
  intro t0 received fixedBank
  have read := enrichedSewn_localUse G axes gridDepth order position count M bottom installed y hy pos base hg q z slot a received w0
  have same := enrichedPathPowerInput_congr G axes gridDepth order position count M bottom installed hg q slot a received fixedBank
    (received_used hg (GridHosts.gridRoom G Fintype.card_pos) delivery pin subst) (t0.words.site w0)
  exact read.trans (congrArg (t0.powerRead w0) same)

end Enriched

end Diagonal.ExternalSew

end BorderVNP
end Computability
end OAI
