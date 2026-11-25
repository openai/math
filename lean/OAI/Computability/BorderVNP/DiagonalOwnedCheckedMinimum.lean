import OAI.Computability.BorderVNP.RoutingISASignedPrepOwnedPhysical
import OAI.Computability.BorderVNP.RoutingISASignedPrepBroadcast

/-! # Recovering the physical owned assignment after the native minimum test -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator.SignedPrep

open BorderVNP.Cube Physical
open scoped BigOperators

/-- The native range test and minimum test read the actual coordinate of
the same decoded binary declaration, including all its dense totals. -/
theorem decoded_firstMinimum (ar : CubeArena.Layout) (c : CheckedBroadcast ar)
    (checked : LocalRow.declaredMinimum c.val) :
    (decodedBroadcast ar c.val).1=firstMinimum (fun j => ∑ pair,(decodedBroadcast ar c.val).2 pair j) := by
  apply Fin.ext
  simpa only [decodedBroadcast,Fin.ofNat,Fin.val_mk,Nat.mod_eq_of_lt c.property.1,LocalRow.declaredMinimum] using checked

end RoutingISA.Evaluator.SignedPrep

namespace TeamContraction

open VPVNP BurstRAM Diagonal.Layout RoutingISA RoutingISA.Transmission RoutingISA.Evaluator SignedPrep
open BorderVNP.Cube Physical Physical.NativeAssignments Scatter Scatter.Assignment
open DiagonalTallyPacketEmit
open private recover_decoded declaredTeam_eq from OAI.Computability.BorderVNP.CubeScatterReturnedOwnedFamily

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

variable (F : TeamRows.Returns (Fin (R+1)) ar w) {constTemplate : Frame} {fixedCount : ℕ}

open scoped BigOperators

/-- Once the physical prefix has proved its least declaration coordinate,
all the actual owned lower-triangle scans and routed common words determine
their unique distributed assignment, including empty intervals. -/
theorem SharedWriters.recover_owned_minimum (writer : SharedWriters f g src)
    (scheduled : group = declaredTeam ar decl label recv dataWidth R)
    (symbols : SymbolFrame g (src anchor) ar.header.blocks ar.K ar.h decl group)
    (handoff : OwnedHandoff f g src ar decl group constTemplate id fixedCount F) (copies : 1 ≤ ar.K)
    (labels : ar.header.d^(ar.n+1) ≤ 2^w)
    (packets : Physical.Owned.packetTrials ar.n ar.header.d ar.header.blocks*(ar.h*ar.s) < 2^w)
    (least : decl.1 = firstMinimum (fun j => ∑ pair, decl.2 pair j)) :
    ∃! q : NativeAssignments.Routed (b:=ar.b) (s:=ar.s) owners,
      ObservedOwned ar decl group F owners (f.receivedRows g group) q := by
  obtain ⟨scans⟩ := writer.physical_scans ar decl group symbols constTemplate id fixedCount handoff.banks handoff.spacing
    copies handoff.room handoff.table handoff.frame handoff.source handoff.fits handoff.fields (fun u => by
      obtain ⟨events,install⟩ := handoff.install u
      exact ⟨events,F.initialRegs u,F.input u,F.events u,F.finalRegs u,F.output u,install,
        by simpa only [handoff.pub,handoff.macros] using F.path u⟩)
  obtain ⟨select,⟨word,⟨checked⟩⟩,_⟩ := scans.recover
  have passing := (TeamRows.rows_and_minimum_iff group ar.b ar.s select decl).mp
    ⟨fun _ _ _ => checked.row_counts labels packets (handoff.room anchor).capFit _,least⟩
  have valid : ∀ sym : Symbols ar.header.d,
      (decodeSelectors ar.n ar.K ar.h (packetVisits ar.header.blocks decl.1 sym).length
        ((f.receivedRows g group sym).take
          (rowSelectorBits ar.n ar.header.d ar.header.blocks ar.K ar.h decl.1 (Sym2.mk sym.val.1 sym.val.2)))).isSome := by
    intro sym
    rw [word,commonSelectors_decode]
    rfl
  obtain ⟨shared,emits,_⟩ := writer.decode_received symbols valid (fun other prefixes =>
    (commonSelectors_injective decl.1 (fun sym => (prefixes sym).symm.trans (word sym))) ▸ passing)
  exact recover_decoded ar decl group F _ writer symbols handoff shared emits
    (scheduled.trans (declaredTeam_eq ar decl label recv dataWidth shared))

end TeamContraction

end BorderVNP
end Computability
end OAI
