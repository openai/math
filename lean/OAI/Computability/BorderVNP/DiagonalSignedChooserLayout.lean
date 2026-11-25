import OAI.Computability.BorderVNP.DiagonalSignedPublishedMeanRows
import OAI.Computability.BorderVNP.RoutingISASignedPrepRange
import OAI.Computability.BorderVNP.CubeRouteExteriorOwners

/-! # A common physical interval layout on all native returns of the signed history -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator.SignedPrep

open Crossing BorderVNP.Cube Cube.Physical Cube.NativeIntervals LocalRow CubeArena CubeHeaderInstall
open TeamContraction.JointHeader VPVNP.BurstRAM

/-- The single absolute interval directory for the selected sparse cable slots. -/
def signedChooserLayout (a : CubeArena.Layout) (frame origin : ℕ) : Cube.NativeIntervals.Layout :=
  ⟨frame,origin,a.cables,a.publicBase,a.alphabet,a.widthBase,a.ordinalBase⟩

variable {w R X : ℕ} {a : CubeArena.Layout} {D : Packing.Directory.Layout} {pp lp : ℕ → ℕ × ℕ}
    {slotted : Memory w} {base : ℕ} {pub : Arg → Word w} {f : BroadcastFrame} {old : Fin 81 → Word w}
    {fresh gates outputs width off ell controls : ℕ} {G : List Bool} {claims : List (List Bool)}
    {pad : ℕ} {raw : Broadcast a.n a.header.d a.header.cap}
    (room : PinnedRawInput (ar := a) (D := D) (pp := pp) (lp := lp) (pub := pub) (slotted := slotted) (base := base)
      f old fresh gates outputs width off ell controls G claims pad raw R X)
include room

local notation3 (prettyPrint := false) "head" => (pub 0).val
local notation3 (prettyPrint := false) "image" => readings (Packing.Directory.ISA.publish slotted head base (D.directory pp lp))
local notation3 (prettyPrint := false) "t" => LabelIndex.layout head image

/-- Control words 48, 56, 57 and 58, together with the two occupied cable
fields published by the signed directory writer, give exactly the same
interval layout at every calling team. -/
theorem PinnedRawInput.signed_chooser_layout (origin : ℕ) (start : (t).cables=origin) (count : (t).cableCount=a.cables) :
    NativeIntervals.chooserLayout t head (image (head+48)) (image (head+57)) (image (head+58)) =
      signedChooserLayout a head origin := by
  have bound := room.arena
  have pos : 0<a.header.d := (Nat.succ_pos 1).trans_le room.alphabet
  have square : a.alphabet ≤ a.alphabet^2 := by
    rw [pow_two]
    exact Nat.le_mul_of_pos_right _ (pow_pos pos _)
  obtain ⟨_,_,_,_,_,_,_,_⟩ := a.writer_order
  obtain ⟨_,_,_,_,_⟩ := arena_label_arrays a
  have growth : a.powerBase+a.n+1=a.groupWeights := by simp only [Layout.groupWeights,Nat.add_assoc]
  have prior : a.ordinalBase≤a.powerBase := by
    dsimp only [Layout.powerBase]
    omega
  have f48 := room.boot.arenaOperand a old fresh G.length gates outputs width off ell
    (k := 48) (value := a.publicBase) rfl (by omega)
  have f56 := room.boot.arenaOperand a old fresh G.length gates outputs width off ell
    (k := 56) (value := a.alphabet) rfl (by omega)
  have f57 := room.boot.arenaOperand a old fresh G.length gates outputs width off ell
    (k := 57) (value := a.widthBase) rfl (by omega)
  have f58 := room.boot.arenaOperand a old fresh G.length gates outputs width off ell
    (k := 58) (value := a.ordinalBase) rfl (by omega)
  change image (head+48)=a.publicBase at f48
  change (t).labels=a.alphabet at f56
  change image (head+57)=a.widthBase at f57
  change image (head+58)=a.ordinalBase at f58
  unfold NativeIntervals.chooserLayout signedChooserLayout
  rw [start,count,f48,f56,f57,f58]

/-- The genuine joint header also contains the pair directory and the two
static row widths read by the cable-host writer. -/
theorem PinnedRawInput.signed_host_operands :
    image (head+91)=a.pairDirectory ∧ image (head+93)=Tally.bankWidth a.n a.b a.h a.K a.s ∧
      image (head+94)=Tally.selectorWidth a.n a.K a.h := by
  have fit := room.arena
  have symbols := room.alphabet
  have base : 0<a.header.d*a.header.d := Nat.mul_pos (by omega) (by omega)
  have times : 0<(a.header.d*a.header.d)^(a.n+1)*2*a.header.blocks := by
    have positive := room.blocks
    positivity
  have words := Nat.le_mul_of_pos_left (Tally.bankWidth a.n a.b a.h a.K a.s) times
  have high : a.header.packetBase+(a.header.d*a.header.d)^(a.n+1)*2*a.header.blocks*Tally.bankWidth a.n a.b a.h a.K a.s ≤ a.publicBase := by
    dsimp only [Layout.publicBase,Layout.vertexBase,Layout.singleBank,Layout.packetEnd,bankStop]
    omega
  obtain ⟨_,_,_,_,_,_,_,_⟩ := a.writer_order
  have select := selector_room a.n a.b a.h a.K a.s
  exact ⟨room.boot.arenaOperand a old fresh G.length gates outputs width off ell
      (k := 91) (value := a.pairDirectory) rfl (by omega),
    room.boot.arenaOperand a old fresh G.length gates outputs width off ell
      (k := 93) (value := Tally.bankWidth a.n a.b a.h a.K a.s) rfl (by omega),
    room.boot.arenaOperand a old fresh G.length gates outputs width off ell
      (k := 94) (value := Tally.selectorWidth a.n a.K a.h) rfl (by omega)⟩

/-- The published geometry begins at the real allocation destination.
Every initial triple fitting the emitted word count precedes the next cube header. -/
theorem PinnedRawInput.signed_cable_extent (occupied : 3*a.cables≤outputs) :
    GeometryAdvice.Allocation.dest fresh G.length gates outputs width+3*a.cables≤a.header.header := by
  have header := congrArg CubeHeaderInstall.Inputs.header room.geometry
  change a.header.header=GeometryAdvice.Allocation.stop fresh G.length gates outputs width w at header
  rw [header]
  change _≤GeometryAdvice.Allocation.dest fresh G.length gates outputs width+outputs+_+_
  omega

end RoutingISA.Evaluator.SignedPrep

end BorderVNP
end Computability
end OAI
