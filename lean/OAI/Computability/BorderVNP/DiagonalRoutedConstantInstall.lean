import OAI.Computability.BorderVNP.FiniteEvaluatorSignedLookupWriter
import OAI.Computability.BorderVNP.RoutingISACubeConstantRun
import OAI.Computability.BorderVNP.RoutingISASignedPrepBuilder

/-! # Installing the signed cube dictionary on the actual returned shared routes -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction

open VPVNP BurstRAM Diagonal.Layout RoutingISA RoutingISA.Transmission RoutingISA.Evaluator Routing
open BorderVNP.Cube Physical DiagonalTallyPacketEmit
open private detOfUnsigned from OAI.Computability.BorderVNP.CubeISALocalRowFrame

variable {R r t d link inner n w : ℕ} {Edge : Type} {G : Wiring R r t d link inner n Edge}
    {pin : Fin d → Bool} {ext : Exterior R r link → Bool} {L : WireLayout (R+1) r link}
    {D : Packing.Directory.Layout} {pp lp : ℕ → ℕ × ℕ} {owner : ℕ → Fin (R+1)} {origin stride : ℕ}
    {H : Fin (R+1) → TeamHistory w} {pins : Fin (R+1) → Pins.Layout}
    {f : ReturnedDelivery G pin ext L D pp lp owner origin stride H pins} {g : SharedRows.Layout}
    {src : Fin (R+1) → ℕ → ℕ} (writer : SharedWriters f g src)
    (ar : CubeArena.Layout) (template : Frame) (id : TableEntry ar.n ar.b ar.h ar.K ar.s → ℕ) (count : ℕ)

local notation "pack" => CubeConstants.inArena template ar.stop ar.n ar.b ar.h ar.K ar.s
local notation "ids" => CubeConstants.idBase ar.stop ar.n ar.b ar.h ar.K ar.s

include writer in
/-- The physical route copies all constant pointers through to the real
installer. Each actual installation is unique and preserves the published
four-array image with its own clock charge. The decoded values may be zero. -/
theorem SharedWriters.signedInstallOnRoute
    (physical : ∀ u, f.table=ar.table (readings (H u).pub 0) count)
    (initial : ∀ u, CubeConstants.Fields pack (readings (H u).pub 0) ids (src u))
    (low : ∀ u, readings (H u).pub 0+112 ≤ ar.header.header)
    (privateRegion : ∀ u, readings (H u).pub 0+112 ≤ ar.stop)
    (frame : ∀ u, g.frame=readings (H u).pub 0)
    (total : CubeConstants.arenaEnd ar.stop id < 2^w) (values : CubeConstants.valueBound id < 2^w) :
    ∀ u, let base := readings (H u).pub 0
      let before := (H u).history.val.2.2
      CubeConstants.Fits pack w base ids id ∧ CubeConstants.Fields pack base ids (readings before) ∧
      ∃! z : Returns (CubeConstants.install id) (H u).pub (H u).macros (H u).history.val.2.1 before,
        traceCost z.val.1 ≤ (CubeConstants.install id).slots ∧
          readings z.val.2.2 = CubeConstants.image pack ids id (readings before) := by
  intro u base before
  have fit := CubeConstants.inArena_fits template ar.stop base id (privateRegion u) total values
  have fields := writer.returned_constant_fields ar base count (physical u) (low u) (frame u) pack ids u (initial u)
  obtain ⟨es,s,m,h,cost,image⟩ := CubeConstants.install_run (H u).pub (H u).macros
    (H u).history.val.2.1 before pack ids id fit fields
  refine ⟨fit,fields,⟨(es,s,m),h⟩,⟨cost,image⟩,?_⟩
  intro z _
  obtain ⟨trace,reg,ram⟩ := z.property.unique_of_deterministic
    (detOfUnsigned _ (CubeConstants.install_unsigned id).1) h
  exact Subtype.ext (Prod.ext trace (Prod.ext reg ram))

end TeamContraction

end BorderVNP
end Computability
end OAI
