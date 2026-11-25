import OAI.Computability.BorderVNP.DiagonalTallySignedHeaderRoute
import OAI.Computability.BorderVNP.CubeRouteCompleteSchedule

/-! # The original signed header on the shared writer’s physical input -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.SignedTaskArena

open VPVNP.BurstRAM Packing TeamContraction TeamContraction.JointHeader TeamContraction.ProcessorSlots
open BorderVNP.Cube BorderVNP.Cube.Physical RoutingISA.Evaluator RoutingISA.Transmission

variable {w reserve axes groups cap width : ℕ} (l : Layout) (A : StartupArena)
variable (p : PositiveFields reserve axes groups cap l.cube.teams l.dim width)
variable {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8} (team : ℕ) (frame : (pub 0).val=A.frame)
variable (size : A.header=PositiveFields.width reserve axes groups cap l.cube.teams l.dim width)
local notation "raw" => rawAddress A reserve axes groups cap
local notation "seed" => HeaderSeed l p pub raw team

include frame size in
/-- Reconstruction, private slot placement, and the actual demand-directory
publication preserve the previously copied claim in the post-pin image. -/
theorem HeaderSeed.afterEpochs {o : ℕ} {s t : Bank w} {pinMem : Memory w} {fresh dest clock : ℕ}
    {out : Fin o → ℕ} {es geom slotted}
    (input : seed pinMem)
    (geometry : PackedHistoryCircuit.GeometryReturn pub mac s pinMem fresh dest clock out es t geom)
    (placement : PrivatePlacement.Layout) (image : placement.Image (readings geom) placement.entries (readings slotted))
    (base : ℕ) (rows : List Packing.Directory.Row)
    (low : A.next ≤ fresh ∧ A.next ≤ placement.raw ∧ A.next ≤ placement.scratch ∧ A.next ≤ base) :
    seed (Packing.Directory.ISA.publish slotted (pub 0).val base rows) := by
  apply input.transfer
  intro x hx
  rw [frame] at hx
  obtain ⟨lower,_,next⟩ := rawAddress_room l A size
  exact ReaderKept.afterEpochs_word geometry placement image base rows A.next x low
    ((seedRead_before_pins l A size hx).trans_le next) (frame ▸ headerSeedRead_other hx lower (j:=9) (by decide) (by decide))

include frame size in
/-- From the actual public schedule return, the genuine shared-row writer’s input
contains the same parsed fields and reference operands as the original geometry. -/
theorem HeaderSeed.sharedInput {R : ℕ} {D : Packing.Directory.Layout} {pp lp : ℕ → ℕ × ℕ} {owner : ℕ → Fin (R+1)}
    {decl : LengthDeclaration l.cube.n l.cube.header.d} {group : Fin l.cube.header.d → Fin (R+1)} {pins : Pins.Layout}
    {s t : Bank w} {mem mt : Memory w} {es}
    (H : WriterHistory l.cube.n (Tally.selectorWidth l.cube.n l.cube.K l.cube.h) pub mac s mem es t mt)
    (cert : ReturnedWriters l.cube D pp lp owner decl group pins H) (input : seed mem)
    (placed : A.next ≤ l.cube.header.header) : seed H.sharedInput := by
  apply input.transfer
  intro x hx
  rw [frame] at hx
  obtain ⟨lower,_,next⟩ := rawAddress_room l A size
  have primary := (seedRead_before_pins l A size hx).trans_le (next.trans placed)
  have ne : x≠(pub 0).val+13 := frame ▸ headerSeedRead_other hx lower (j:=13) (by decide) (by decide)
  have data : x<(DataWriter.layout (readings pub) (readings H.dataInput)).output :=
    cert.emission.demand.records ▸ primary.trans_le (secondary_le_records l.cube)
  rw [H.dataImage cert.emission.demand.ready,DataWriter.publish,Function.update_of_ne ne,
    Directory.ISA.putWords_outside _ _ _ _ (.inl data)]
  exact cert.low x primary

end RoutingISA.SignedTaskArena

end BorderVNP
end Computability
end OAI
