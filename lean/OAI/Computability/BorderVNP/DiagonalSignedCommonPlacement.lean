import OAI.Computability.BorderVNP.RoutingISASignedPrepRange
import OAI.Computability.BorderVNP.CubeRouteCanonicalWriters

/-! # A common signed source directory on physically different pinned memories -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator

open Packing Packing.Directory TeamContraction VPVNP.BurstRAM
open _root_.OAI.Computability.BorderVNP.Cube Cube.Physical Tally LocalRow JointHeader

variable {w : ℕ} {ar : CubeArena.Layout} {D : Layout} {pp lp pp' lp' : ℕ → ℕ × ℕ}
    {pins : Pins.Layout} {pub : Arg → Word w} {slotted : Memory w} {base : ℕ}
    {I : Type*} [Fintype I] {cell : I → Fin ar.cells} {id : I ↪ ℕ} {width : I → ℕ}

/-- The native input on this particular pinned memory can use the common
representative's placement table. Equality of the actual destination keys
suffices even if unused physical cells of the two tables differ. -/
noncomputable def SlottedWriter.commonPlacement (writer : SlottedWriter ar D pp lp pins pub slotted base cell id width)
    (ref : BankPlacement D pp' lp' I cell id width) (same : ∀ k,writer.placement.key k=ref.key k) :
    SlottedWriter ar D pp' lp' pins pub slotted base cell id width where
  pinFrame := writer.pinFrame
  pointers := writer.pointers
  rawStart := writer.rawStart
  rawEnd := by
    rw [←writer.placement.directory_eq ref same writer.destinations]
    exact writer.rawEnd
  teams := writer.teams
  fields := writer.fields
  tailRoom := writer.tailRoom
  active := writer.active
  processors := writer.processors
  literal := writer.literal
  tapeRoom := writer.tapeRoom
  substituteRoom := writer.substituteRoom
  placement := ref
  destinations := writer.destinations
  slabs := writer.slabs

variable {f : BroadcastFrame} {old : Fin 81 → Word w} {fresh gates outputs widthBits off ell controls : ℕ}
    {G : List Bool} {claims : List (List Bool)} {pad : ℕ} {word : Broadcast ar.n ar.header.d ar.header.cap}
    {R X : ℕ}

/-- The raw scheduler guard reads the identical seven-word demand list after
renumbering unused placement addresses. Its reached memory is unchanged. -/
theorem SignedPrep.PinnedRawInput.commonPlacement
    (cert : SignedPrep.PinnedRawInput (ar:=ar) (D:=D) (pp:=pp) (lp:=lp) (pub:=pub) (slotted:=slotted) (base:=base)
      f old fresh gates outputs widthBits off ell controls G claims pad word R X)
    (same : D.directory pp lp=D.directory pp' lp') :
    SignedPrep.PinnedRawInput (ar:=ar) (D:=D) (pp:=pp') (lp:=lp') (pub:=pub) (slotted:=slotted) (base:=base)
      f old fresh gates outputs widthBits off ell controls G claims pad word R X := by
  obtain ⟨boot,geometry,frame,copied,alphabet,blocks,bank,arena,labels,cells,teams,count,budget,
    million,scaled,low,pointers,processors,payload,fields,space,records⟩ := cert
  rw [same] at boot labels cells pointers records
  exact ⟨boot,geometry,frame,copied,alphabet,blocks,bank,arena,labels,cells,teams,count,budget,
    million,scaled,low,pointers,processors,payload,fields,space,records⟩

end RoutingISA.Evaluator

end BorderVNP
end Computability
end OAI
