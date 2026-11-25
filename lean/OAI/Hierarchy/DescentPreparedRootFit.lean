import OAI.Hierarchy.DescentPreparedRootInputs
import OAI.Hierarchy.DescentFallbackRecordFit

namespace OAI
/-! # Static address certificates for the complete compiled root catalog -/
namespace Hierarchy.DescentFallbackPeriod.Projected.Receiver
open DescentSIMDLookup DescentPacking.PackedMatch.Local.Gather DescentSixParty.Chronology
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {D cap N n r c H G K R M h l t field Ht w : ℕ}
    (a : Receiver D cap N n r c H G K R M h l t field Ht w) (b : RootBook n r D (2^r) cap field)
local notation "groups" => 2^c
local notation "A" => RootTemplates.arena (a.headerEnd b) H groups M r n D
local notation "Page" => RootPage r (2^n)
local notation "index" p => (rootIndex r (2^n) p).val

/-- All remaining checks on a physical root date are static: the already-paid prefix,
the final address, the two incoming host banks, each expression's literal banks, and
the packed field widths. No inequalities about any branch's *data* are required. -/
theorem prepared_fit (pre : a.PrefixFits) (last : a.preparedEnd b<2^w)
    (neighbor : b.previousNeighbors.Fits w (a.headerEnd b)) (hub : b.previousHubs.Fits w (a.headerEnd b))
    (incoming : ∀p : Page,∀ j,(((b.table p).2.reads j).Fits w ((A).middle (index p))))
    (lanes : ∀p : Page,M*max ((b.table p).2.field*(b.table p).1) (b.table p).2.outputBits≤ w/2) :
    a.PreparedFits b := by
  have low:a.headerEnd b≤ a.preparedEnd b:=Nat.le_add_right ..
  have limits:=b.limits a.projectionEnd H groups M
  have hook:=DescentSharedBookScan.Public.record_fits b.previousNeighbors b.previousHubs Ht
    (limits.2.1.trans limits.2.2) (low.trans_lt last) neighbor hub
  refine ⟨pre,low.trans_lt last,?_⟩
  intro p
  let i:=index p
  let t:=(b.table p).2
  let base:=b.atPage a.projectionEnd H groups M p
  let src:=b.target a.projectionEnd H groups M p
  let menu:=t.terms base H groups M src
  have horizon:(A).first (i+1)≤ a.preparedEnd b:=Nat.add_le_add_left
    (Nat.mul_le_mul_left _ (rootIndex r (2^n) p).isLt) _
  have out:(A).output i+(A).rows<2^w:=by
    have bound:=Nat.add_le_add_left (RootArena.le_span (A).rows) ((A).output i)
    rw [RootArena.end_row] at bound
    exact (bound.trans horizon).trans_lt last
  have monotone:a.headerEnd b≤(A).first i:=Nat.le_add_right ..
  have name:=(rootIndex r (2^n) p).isLt
  have seen:=b.bounds a.projectionEnd H groups M w p
  have printed:t.stop base H groups M≤ a.headerEnd b :=
    seen.2.trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ name) _)
  have before:=printed.trans (monotone.trans (show (A).first i≤(A).middle i from Nat.le_add_right ..))
  obtain ⟨bounds,fit,_,_⟩:=t.geometry_at base ((A).middle i) ((A).output i) src rfl rfl before
    (incoming p) le_rfl out (lanes p)
  have reads:(assembly menu.tables menu.reads).Fits w ((A).middle i):=
    DescentPacking.PackedMatch.Local.Gather.fits menu.tables menu.reads _ bounds (List.finRange _)
  have lookupFit:(DescentSIMDLookup.lookup menu.menu).Fits w ((A).output i) :=
    ⟨⟨fit.dictionary,fit.source,trivial⟩,fit.mask,trivial⟩
  have first:(DescentSharedBookScan.record (b.common a.projectionEnd H) H D (2^Ht) (Ht+2)).Fits w ((A).first i) :=
    ProtocolRAMGeneratedWrite.fits_mono _ monotone hook
  rcases p with ⟨s,(⟨root,j⟩|root)⟩
  · exact ⟨⟨reads,lookupFit⟩,out⟩
  · exact ⟨⟨first,reads,lookupFit⟩,out⟩

end
end Hierarchy.DescentFallbackPeriod.Projected.Receiver

end OAI
