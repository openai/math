import OAI.Computability.BorderVNP.CubeScatterReturnedOwnedDeck
import OAI.Computability.BorderVNP.FiniteEvaluatorSignedCubeAllocation
import OAI.Computability.BorderVNP.FiniteEvaluatorCubeBanksNative
import OAI.Computability.BorderVNP.DiagonalTallyCallReadback

/-! # Raw gadget position lookup from the signed evaluator's owned cube receipts -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.SignedTaskArena

open BorderVNP.Cube BorderVNP.Cube.Tally BorderVNP.Cube.Padding.Banks DiagonalTallyPacketEmit
open VPVNP.BurstRAM FiniteEvaluator

variable {w : ℕ} (a : Layout) (pub : Arg → Word w) (owner : Fin a.cube.header.d → ℕ) (team demand : ℕ)
variable (A : Data a.cube.n a.cube.header.d a.cube.header.blocks a.cube.b a.cube.h a.cube.K a.cube.s)

local notation "cnt" => List.length (CubeVisits.teamList A.axis a.cube.header.blocks owner team)
local notation "scan" => a.cube.scanner (Fin.val (pub 0)) team A.axis.val a.cube.rowSelectorBits
local notation "fr" => a.lookupFrame cnt
local notation "actual" => CubeTriple.visits (l:=scan) A owner
local notation "ptr" => CubeConstants.idBase a.cube.stop a.cube.n a.cube.b a.cube.h a.cube.K a.cube.s

/-- The natural-word input stores each gadget's actual position ID and the three words
for each visited corner in the team's native order. -/
noncomputable def gadgetLookup : CubePacket.Inputs a.cube.n a.cube.b a.cube.h a.cube.K a.cube.s ℕ :=
  CubeDeck.inputs a.id fr a.cube.stop actual a.after.ids demand

/-- Read the true finite recipe and arbitrary gadget ID words installed by the native
constant program. Every owned-vertex argument is provided by the same physical
return, in the exact order in which its triples were written. -/
theorem wordPrepared_after_owned (original out : Memory w)
    (receipt : CubeTriple.Readback (l:=scan) A owner a.cube.powerBase a.cube.vertexBase a.cube.publicBase original out)
    (installed : CubeDeck.WordsAt fr a.cube.stop a.id (readings original))
    (initial : DiagonalTallyPacketEmit.Frame.resident {fr with count:=readings original ((pub 0).val+46)}
      (readings pub) (readings original))
    (tablePtr : (original ((pub 0).val+47)).val=ptr) (idPtr : (original ((pub 0).val+71)).val=a.after.ids)
    (packet : A.packetBase=a.cube.header.packetBase) (capacity : cnt ≤ a.cube.vertexCap)
    (reserved : cnt ≤ a.p.report.vertices)
    (digits : argumentWidth a.cube.n a.cube.b a.cube.h a.cube.K a.cube.s ≤ a.p.report.cubeWidth)
    (primary : (pub 0).val+112 ≤ a.cube.header.header) (word : a.after.packed ≤ 2^w) :
    CubePacket.WordPrepared (gadgetLookup a pub owner team demand A) a.id pub out := by
  have place : a.cube.publicBase ≤ a.cube.stop := by
    have parts := a.cube.separated
    have pairs : a.cube.pairBase ≤ a.cube.cellBank := Nat.le_add_right ..
    exact parts.2.2.2.1.trans (pairs.trans parts.2.2.2.2.2)
  have deck := CubeDeck.WordsAt.preserve fr a.cube.stop a.id installed fr
    (fun k lo _ => congrArg Fin.val (receipt.above k (place.trans lo)))
  have resident := receipt.resident fr (pub:=pub) rfl rfl initial
  obtain ⟨frameRoom,tableRoom,tripleRoom,bankRoom,outputRoom,separate,idRoom⟩ :=
    a.lookup_rooms A packet capacity reserved digits primary word
  apply CubeDeck.wordPrepared a.id fr a.cube.stop a.id actual a.after.ids demand pub out deck resident
    receipt.triples receipt.banks ((receipt.field 47 (by decide) (by decide)).trans tablePtr)
    ((receipt.field 71 (by decide) (by decide)).trans idPtr) frameRoom tableRoom tripleRoom _ outputRoom separate idRoom
  intro i
  exact bankRoom ((CubeVisits.teamList A.axis a.cube.header.blocks owner team).get i).1

/-- Both the task and private-call stages transport the actual raw gadget deck via the
address footprint. Private signs and choice bits have no shared-memory effects. -/
theorem wordPrepared_after_calls {P : CubePacket.Inputs a.cube.n a.cube.b a.cube.h a.cube.K a.cube.s ℕ}
    {initial before : Memory w} (prepared : CubePacket.WordPrepared P a.id pub initial)
    (preparation : ∀ k,CubePacket.ReadAt P pub k → before k=initial k)
    {mac : TeamOpcode.Macros w 8} {s es t mt} (run : Runs pub mac callOwnedCells s before es t mt) :
    CubePacket.WordPrepared P a.id pub mt := by
  rw [CellDispatch.memory_after_owned_calls run]
  exact CubePacket.WordPrepared.transfer P prepared preparation

end RoutingISA.SignedTaskArena

end BorderVNP
end Computability
end OAI
