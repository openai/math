import OAI.Computability.BorderVNP.DiagonalSignedDictionaryRoom
import OAI.Computability.BorderVNP.DiagonalRoutedConstantInstall
import OAI.Computability.BorderVNP.FiniteEvaluatorSharedCubeSource

/-! # The actual signed cube operand table at the end of a scheduled delivery -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction

open VPVNP BurstRAM Diagonal.Layout RoutingISA RoutingISA.Transmission RoutingISA.Evaluator Routing
open BorderVNP.Cube Physical DiagonalTallyPacketEmit

variable {R r t d link inner n w : ℕ} {Edge : Type} {G : Wiring R r t d link inner n Edge}
    {pin : Fin d → Bool} {ext : Exterior R r link → Bool} {L : WireLayout (R+1) r link}
    {D : Packing.Directory.Layout} {pp lp : ℕ → ℕ × ℕ} {owner : ℕ → Fin (R+1)} {origin stride : ℕ}
    {H : Fin (R+1) → TeamHistory w} {pins : Fin (R+1) → Pins.Layout}
    {f : ReturnedDelivery G pin ext L D pp lp owner origin stride H pins}
    (tape : SignedTaskArena.Layout) (decl : LengthDeclaration tape.cube.n tape.cube.header.d)
    (group : Fin tape.cube.header.d → Fin (R+1)) (template : Frame) (frame dataCount : ℕ)
    {src : Fin (R+1) → ℕ → ℕ}
    (writer : SharedWriters f (tape.cube.sharedRows frame decl.1.val dataCount) src)

local notation "pack" => CubeConstants.inArena template tape.cube.stop tape.cube.n tape.cube.b tape.cube.h tape.cube.K tape.cube.s
local notation "ids" => CubeConstants.idBase tape.cube.stop tape.cube.n tape.cube.b tape.cube.h tape.cube.K tape.cube.s

include writer in
/-- The physical writer's actual scanner and source-frame readback supplies
the signed numeric dictionary on every replayed team. Both register files
and RAM used for the next owned traversal are the installer outputs. -/
theorem SharedWriters.signedInstallFromWriterWords
    (common : ∀ u, readings (H u).pub 0=frame) (tab : f.table=tape.cube.table frame (dataCount+tape.cube.header.d.choose 2))
    (space : tape.after.packed ≤ 2^w) (values : CubeConstants.valueBound tape.id < 2^w)
    (room : ∀ u, tape.cube.ReplayRoom w (readings (H u).pub 0))
    (words : ∀ u, SharedCubeWords tape decl group u.val (readings (H u).pub) (src u) dataCount) :
    ∃ installed : (u : Fin (R+1)) → Returns (CubeConstants.install tape.id) (H u).pub (H u).macros
      (H u).history.val.2.1 (H u).history.val.2.2,
      ∀ u, CubeConstants.Fits pack w (readings (H u).pub 0) ids tape.id ∧
        CubeConstants.Fields pack (readings (H u).pub 0) ids (readings (H u).history.val.2.2) ∧
        traceCost (installed u).val.1 ≤ (CubeConstants.install tape.id).slots ∧
        readings (installed u).val.2.2=CubeConstants.image pack ids tape.id (readings (H u).history.val.2.2) := by
  have bounds u := tape.signed_dictionary_addresses (room u).primary space
  have ownTable u : f.table=tape.cube.table (readings (H u).pub 0) (dataCount+tape.cube.header.d.choose 2) :=
    (common u).symm ▸ tab
  have data := writer.signedInstallOnRoute tape.cube template tape.id (dataCount+tape.cube.header.d.choose 2)
    ownTable (fun u => (words u).fields template) (fun u => (room u).primary) (fun u => (bounds u).1)
    (fun u => (common u).symm) (bounds 0).2 values
  let z u := (data u).2.2.choose
  exact ⟨z,fun u => ⟨(data u).1,(data u).2.1,(data u).2.2.choose_spec.1⟩⟩

end TeamContraction

end BorderVNP
end Computability
end OAI
