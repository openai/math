import OAI.Hierarchy.DescentResetSignedTokenInputs
import OAI.Hierarchy.DescentDatedStageVenue

namespace OAI
/-! # Physical signed reset intake at a reached date -/
namespace Hierarchy.DescentResetSignedTokens
open DescentSixParty DescentCompiler DescentPackedColony DescentSIMDLookup ProtocolRAM
open DescentColonies DescentPacking.PackedMatch.Local.Stage
open Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F] {u : ℕ} {bs : P→ℕ} {W : MarkedWorld F u P bs}
  {G : PoweredGadget F} {price ε : ℝ} {S : AtomSchedule} {k age z D wire hist H w : ℕ}
  (r : Reached W G price ε S k age z D wire hist) (wide : Fintype.card r.V≤H)

def venueNames : r.V≃Fin (Fintype.card r.V) :=
  Equiv.ofBijective r.vertex ((Fintype.bijective_iff_injective_and_card _).mpr ⟨r.vertex.injective,by simp⟩)

variable (input : Dated.Operands) (sourceLanes targetLanes short : ℕ)
local notation "gr" => S.groupCount age
local notation "layout" => datedLayout r.placement H gr sourceLanes targetLanes short
local notation "order_" => r.order.trans Fin.valEmbedding
local notation "pages" => (fun t : Fin (2^k) × Fin (2*r.placement.cap) => input.wire t.1.val t.2.val)
local notation "pin" => Prepare.signed r.placement order_ S r.valid (Function.Embedding.refl _) (r.vertex.trans (Fin.castLEEmb wide))

/-- The signed-word premise is provided by the actual preceding stageVenue.
The host equivalence is exactly the dense site name in numberedHeader. -/
theorem stage_issued (base countBits floor : ℕ) (rs : Fin H→Fin D→Option (Fin H)) (m : Memory w)
    (recorded : stageVenue r wide input sourceLanes countBits floor rs m)
    (before : ∀(x : Fin (2^k)) (j : Fin (2*r.placement.cap)),(input.wire x.val j.val).Fits w base)
    (extent : ∀(x : Fin (2^k)) (j : Fin (2*r.placement.cap)),H*chunks gr sourceLanes≤(input.wire x.val j.val).size)
    (live : 0<sourceLanes) (cap : (layout).endAddress base<2^w) :
    ((layout).phase base w pages).Runs m ∧ ∀t,
      Reads ((layout).raw base t) (fun h g=>DescentSignedCableCodec.encode (pin t.1 t.2 h g)) targetLanes
        (((layout).phase base w pages).image m) ∧
      Reads (H := H) ((layout).bank base t)
        (fun h g=>PackedFlow.Padded.tokens r.placement order_ S r.valid (Equiv.refl _) (venueNames r) short h g t)
        targetLanes (((layout).phase base w pages).image m) := by
  exact venue_issued r.placement order_ S r.valid (Equiv.refl _) (venueNames r) wide sourceLanes targetLanes
    short base pages m (fun t=>before t.1 t.2) (fun t=>extent t.1 t.2)
    (fun t=>recorded.2.2.2.1 t.1 t.2) live cap

end
end Hierarchy.DescentResetSignedTokens

end OAI
