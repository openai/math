import OAI.Hierarchy.DescentNamedSeedPosition
import OAI.Hierarchy.DescentSeedLoaderHeld
import OAI.Hierarchy.DescentNamedSeedHeldGeometry
import OAI.Hierarchy.DescentSeedNativeStartup

namespace OAI
/-! # Reached initial registers on the actual counted ballot and the full seed output -/
namespace Hierarchy.DescentDatedSeedStartup.SeedHeader.Input
open DescentCompiler DescentInitialHost DescentSeedRoot DescentWideSeedFlags DescentPackedEpochShelves
open DescentPackedProfileInstall DescentSixParty DescentSixParty.SeedNamed DescentPackedSeed
open DescentColonies Catalyst Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
set_option quotPrecheck false
variable {F : Type} [Field F] (G : PoweredGadget F) (op : RotorSpec) (t f g drift h : ℕ)
    (v : SeedHeader.Input F) (radix : v.schedule.radix=2^v.k) (count : Fintype.card (Vertex v.circuit)≤v.hosts)
local notation "digits" => v.schedule.initialDigits radix
local notation "g₀" => v.schedule.groupCount 0
local notation "l" => v.layout G t f g drift h
local notation "s" => v.width G
local notation "Z" => v.schedule.grainAt G.b v.p 0
local notation "lanes" => DescentDatedSeedStartup.Primitive.paletteLanes G op s Z h v.k
local notation "header" => v.base G h-1
local notation "pos" => v.position G op t f g drift h
local notation "image" => DescentDatedSeedStartup.Input.completeImage G op v.circuit digits count l header h Z
variable {q ε : ℝ} {wire z₀ w : ℕ} {c : (initialGroup v.circuit v.schedule.copies (v.width G)).Choice}
    (o : Origin v.circuit (G:=G) (S:=v.schedule) (q:=q) (fee:=ε) (z:=z₀) (wire:=wire) c (v.schedule.initialDigits radix))

theorem initial_held (m : Memory w) (wide : 16*digitsNeeded s≤h)
    (live : 0<lanes) (machine : h≤w)
    (signed : DescentSignedCableCodec.width 3 256*(l).packedLanes≤w)
    (fields : (l).operandBits*(l).operandLanes≤w)
    (space : v.floor G op t f g drift h<2^w) :
    (pos).ports.held o.source (pos).floor ((image) m) :=by
  obtain ⟨early,source⟩:=initial_held_geometry G t f g drift h v wide
  exact DescentDatedSeedStartup.Input.initial_held_of_public G op v.circuit digits count l header h Z o m
    signed fields early source live machine space

end
end Hierarchy.DescentDatedSeedStartup.SeedHeader.Input

end OAI
