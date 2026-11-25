import OAI.Computability.BorderVNP.DiagonalAdmittedFrameOwnedState
import OAI.Computability.BorderVNP.DiagonalFrameSourceOwnedAt

/-! # Ownership and the retained site evidence at a single admitted route -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction

open VPVNP.BurstRAM Diagonal.Layout RoutingISA RoutingISA.Evaluator SignedPrep Routing ProcessorSlots JointHeader
open CellMacro.Generator BorderVNP.Cube Physical Physical.NativeAssignments Scatter Tally DiagonalTallyCellReports
open SignedTaskArena

variable {R r t d link inner n w reserve dim tally : ℕ} {Edge : Type}
    (G : Wiring R r t d link inner n Edge) (args : Fin (R+1) → UnitAddresses)
    (live : Fin d → Bool) (L : WireLayout (R+1) r link) (fixed : Block (R+1))
    (hw : 0<w) (size : ∀ u, (args u).header=L.header) (base : Fin (R+1) → ℕ)
    (fit : ∀ u, (G.transferFrame u (args u).header (args u).dst).Fits w (base u))
    (sa : SignedTaskArena.Layout)
variable (width : L.header=PositiveFields.width reserve sa.cube.n sa.cube.header.d
      (declarationCap sa.cube.n sa.cube.header.d sa.cube.header.blocks sa.cube.b sa.cube.h sa.cube.s) (R+1) dim tally)
    {gen : Fragment IO}
    (U : {ext : Exterior R r link → Bool // PositiveExterior G args live w ext} → Fin (R+1) → PinStart gen n w)
    (ib hb sb : Fin (R+1) → ℕ)
    (pinWidth : ∀ x u, (U x u).guessWidth=(G.pinLayout u (ib u) (hb u) (sb u)).guessWidth)
    (owners : (Packet sa.cube.n sa.cube.header.d sa.cube.header.blocks → Selector sa.cube.n sa.cube.K sa.cube.h) → Fin sa.cube.header.d → Fin (R+1))
    (S : SourceReports sa.cube owners) (rawPin : Fin d → Bool)
    (profile : Fin reserve → Bool) (claim : Fin ((R+1)*dim*tally) → Bool)

variable (allowed : RawBroadcast sa.cube → Prop) (template : DiagonalTallyPacketEmit.Frame) (entries : ℕ)
    (F : AdmittedPinnedFrames G args live L fixed hw size base fit sa.cube width U ib hb sb pinWidth sa.id
      owners S rawPin profile claim allowed template entries)

set_option maxHeartbeats 700000
set_option maxRecDepth 9000

/-- The admitted source is the source of its chosen frame, with the same
builder and report assignment. This identifies the source state used by
a selected site's native prefix issuer. -/
theorem AdmittedPinnedFrames.sourceOwnedState_at
    (honest : ∀ q : Routed (b:=sa.cube.b) (s:=sa.cube.s) owners, allowed (routeBroadcast sa.cube owners q).val)
    (q : {v : Routed (b:=sa.cube.b) (s:=sa.cube.s) owners // S.pins v}) (reports : S.actual q.val) (u : Fin (R+1)) :
    let c := routeBroadcast sa.cube owners q.val
    let lifted : {v : Declared sa.cube owners (decodedBroadcast sa.cube c.val) // S.pins v.val} :=
      ⟨⟨q.val,(decoded_routeBroadcast sa.cube owners q.val).symm⟩,q.property⟩
    F.sourceOwnedState G args live L fixed hw size base fit sa width U ib hb sb pinWidth owners S rawPin profile claim
        allowed template entries honest q reports u =
      (F.frame c (honest q.val)).sourceOwnedAt fixed S (F.builder c (honest q.val)) (F.source c (honest q.val))
        lifted reports u := by
  dsimp only [AdmittedPinnedFrames.sourceOwnedState,PreparationFrame.sourceOwnedAt]

local notation3 (prettyPrint := false) "PF(" c "," l "," e ")" =>
  pinnedBroadcastFrame G args live L fixed hw size base fit sa.cube width U ib hb sb pinWidth rawPin profile claim c l e

/-- The lookup sites and replay evidence retained when the admitted frames
were selected belong to the exact frame whose ownership return the decoder
recovers. Both may be eliminated together at the canonical broadcast. -/
theorem AdmittedPinnedFrames.selectOwnedSource
    (K : ∀ (c : CheckedBroadcast sa.cube) (_ : allowed c.val) (l : WireLayout (R+1) r link)
      (e : l.header=L.header) (frame : PF(c.val,l,e)), frame.Builders fixed sa.id owners → Prop)
    (held : ∀ c a, K c a (F.wire c.val) (F.extent c.val) (F.frame c a) (F.builder c a))
    (honest : ∀ q : Routed (b:=sa.cube.b) (s:=sa.cube.s) owners, allowed (routeBroadcast sa.cube owners q).val)
    (q : {v : Routed (b:=sa.cube.b) (s:=sa.cube.s) owners // S.pins v}) (reports : S.actual q.val) (u : Fin (R+1)) :
    let c := routeBroadcast sa.cube owners q.val
    let a := honest q.val
    let lifted : {v : Declared sa.cube owners (decodedBroadcast sa.cube c.val) // S.pins v.val} :=
      ⟨⟨q.val,(decoded_routeBroadcast sa.cube owners q.val).symm⟩,q.property⟩
    K c a (F.wire c.val) (F.extent c.val) (F.frame c a) (F.builder c a) ∧
      F.sourceOwnedState G args live L fixed hw size base fit sa width U ib hb sb pinWidth owners S rawPin profile claim
        allowed template entries honest q reports u =
      (F.frame c a).sourceOwnedAt fixed S (F.builder c a) (F.source c a) lifted reports u := by
  exact ⟨held _ _,F.sourceOwnedState_at G args live L fixed hw size base fit sa width U ib hb sb pinWidth owners S
    rawPin profile claim allowed template entries honest q reports u⟩

variable {G args live L fixed hw size base fit width U ib hb sb pinWidth owners S rawPin profile claim allowed template entries}

/-- Project the physical source directly from a concrete admitted frame
family. The task layout fixes its ID table while the selected family supplies
the pin dictionary, site layout, source reports, and actual builder. -/
theorem AdmittedPinnedFrames.sourceOwnerView
    (honest : ∀ q : Routed (b:=sa.cube.b) (s:=sa.cube.s) owners, allowed (routeBroadcast sa.cube owners q).val)
    (q : {v : Routed (b:=sa.cube.b) (s:=sa.cube.s) owners // S.pins v}) (reports : S.actual q.val) (u : Fin (R+1)) :
    let c := routeBroadcast sa.cube owners q.val
    let lifted : {v : Declared sa.cube owners (decodedBroadcast sa.cube c.val) // S.pins v.val} :=
      ⟨⟨q.val,(decoded_routeBroadcast sa.cube owners q.val).symm⟩,q.property⟩
    F.sourceOwnedState G args live L fixed hw size base fit sa width U ib hb sb pinWidth owners S rawPin profile claim
        allowed template entries honest q reports u =
      (F.frame c (honest q.val)).sourceOwnedAt fixed S (F.builder c (honest q.val)) (F.source c (honest q.val))
        lifted reports u :=
  F.sourceOwnedState_at G args live L fixed hw size base fit sa width U ib hb sb pinWidth
    owners S rawPin profile claim allowed template entries honest q reports u

end TeamContraction

end BorderVNP
end Computability
end OAI
