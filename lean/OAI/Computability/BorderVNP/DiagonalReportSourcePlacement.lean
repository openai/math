import OAI.Computability.BorderVNP.DiagonalOneReportSourceWords
import OAI.Computability.BorderVNP.DiagonalPinnedPlacementKeys
import OAI.Computability.BorderVNP.FiniteEvaluatorFragmentReportWords
import OAI.Computability.BorderVNP.PackedRoutingTeamAgreement

/-! # Reading the same source and report from equal occupied placement rows -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal.ExternalSew.Fragments

open Crossing Packing Packing.CellAddresses BorderVNP.Cube Cube.Physical
open scoped Classical

variable {D R r w link V g C m n entries desc : ℕ}
    {N : Network D (FreeBlock R V) (fun _ => g)} {cell : N.Site → Fin C}
    {edgeID : N.Edge ↪ Fin m} {portID : FreeBlock R V ↪ Fin n} {hg : 0<g}
    {room : r*(2*w+R*link)≤V*g} {origin stride : ℕ} {input : FreePort R r w → Bool}
    {ends : Bool → LiveBit N cell → Bool} {mem : Fin C → ℕ → ℕ}
    {pp lp pp' lp' : ℕ → ℕ × ℕ}
local notation3 (prettyPrint := false) "D₀" => freeDirectory R r w link V g entries desc

/-- Each actual literal uses one finite live destination. Agreement at the
directory's occupied keys therefore transports the entire physical source. -/
theorem SourceWords.withKeyPlacements
    (words : SourceWords N cell edgeID portID hg room lp origin stride input ends mem)
    (keys : ∀ k,(D₀).keyPlacement pp lp k=(D₀).keyPlacement pp' lp' k) :
    SourceWords N cell edgeID portID hg room lp' origin stride input ends mem := by
  refine ⟨words.crossing,?_⟩
  intro z a c
  have key : lp (a.1.1.val*V+a.1.2.val)=lp' (a.1.1.val*V+a.1.2.val) :=
    keys (.inr a.1)
  have address : laneAddress lp' a=laneAddress lp a := by
    unfold laneAddress
    rw [key]
  rw [address]
  exact words.free z

/-- Read on the same native owner even when one index was reconstructed by
inverting the compact roster and the other by the original public selector. -/
theorem SourceWords.reindexOwners {T : Type*} (read : T → ℕ → ℕ) {left right : Fin C → T}
    (words : SourceWords N cell edgeID portID hg room lp origin stride input ends (fun c => read (left c)))
    (same : ∀ c,left c=right c) :
    SourceWords N cell edgeID portID hg room lp origin stride input ends (fun c => read (right c)) := by
  rw [←funext same]
  exact words

end Diagonal.ExternalSew.Fragments

namespace RoutingISA.SignedTaskArena

open Packing VPVNP.BurstRAM

/-- Equality on the native directory's finite keys suffices to keep the
publication and every downstream retained report word at the same memory. -/
theorem ReportWords.withKeyPlacements {w head base : ℕ} {a : Layout} {D : Directory.Layout}
    {m : Memory w} {pp lp pp' lp' : ℕ → ℕ × ℕ} {written result : ℕ → ℕ} {signed : Bool}
    (ret : ReportWords a head (readings (Directory.ISA.publish m head base (D.directory pp lp))) written result signed)
    (bounds : D.DestinationBounds) (keys : ∀ k,D.keyPlacement pp lp k=D.keyPlacement pp' lp' k) :
    ReportWords a head (readings (Directory.ISA.publish m head base (D.directory pp' lp'))) written result signed := by
  rwa [←D.directory_congr_keys pp lp pp' lp' bounds keys]

end RoutingISA.SignedTaskArena

end BorderVNP
end Computability
end OAI
