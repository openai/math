import OAI.Computability.BorderVNP.DiagonalAdmittedSourceIssuance
import OAI.Computability.BorderVNP.DiagonalUniformSourceOwnedAt

/-! # The registered native ownership return on a uniform source family -/

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
    {Shape : Type} (sources : Shape → SourceReports sa.cube owners) {physical uniform : Shape} (rawPin : Fin d → Bool)
    (profile : Fin reserve → Bool) (claim : Fin ((R+1)*dim*tally) → Bool)

variable (allowed : RawBroadcast sa.cube → Prop) (template : DiagonalTallyPacketEmit.Frame) (entries : ℕ)
    (F : AdmittedPinnedFrames G args live L fixed hw size base fit sa.cube width U ib hb sb pinWidth sa.id
      owners (sources physical) rawPin profile claim allowed template entries)

variable {G args live L fixed hw size base fit width U ib hb sb pinWidth owners rawPin profile claim allowed template entries}

/-- Equality of the two ownership observations on the same proposed
report tape, spelling the second one on the installed common frame. -/
def AdmittedPinnedFrames.OwnedStateOnUniform (alignment : physical=uniform)
    (honest : ∀ q : Routed (b:=sa.cube.b) (s:=sa.cube.s) owners, allowed (routeBroadcast sa.cube owners q).val)
    (q : {v : Routed (b:=sa.cube.b) (s:=sa.cube.s) owners // (sources physical).pins v})
    (reports : (sources physical).actual q.val) (u : Fin (R+1)) : Prop :=
    let c := routeBroadcast sa.cube owners q.val
    let ok := honest q.val
    let issued := F.frame c ok
    let b := F.builder c ok
    let agreement := (congrArg (fun f => issued.SourceAgreement fixed (sources f) b) alignment).mp (F.source c ok)
    let lifted : {v : Declared sa.cube owners (decodedBroadcast sa.cube c.val) // (sources uniform).pins v.val} :=
      ⟨⟨q.val,(decoded_routeBroadcast sa.cube owners q.val).symm⟩,
        (congrArg (fun f => (sources f).pins q.val) alignment).mp q.property⟩
    let tape := cast (congrArg (fun f => (sources f).actual q.val) alignment) reports
    F.sourceOwnedState G args live L fixed hw size base fit sa width U ib hb sb pinWidth owners (sources physical)
        rawPin profile claim allowed template entries honest q reports u =
      issued.sourceOwnedAt fixed (sources uniform) b agreement lifted tape u

set_option maxHeartbeats 1000000 in
/-- The checked builder and the common report directory recover the original
owned event list, public arguments, final registers and memory. -/
theorem AdmittedPinnedFrames.uniformSourceOwnerView (alignment : physical=uniform)
    (honest : ∀ q : Routed (b:=sa.cube.b) (s:=sa.cube.s) owners, allowed (routeBroadcast sa.cube owners q).val)
    (q : {v : Routed (b:=sa.cube.b) (s:=sa.cube.s) owners // (sources physical).pins v})
    (reports : (sources physical).actual q.val) (u : Fin (R+1)) : F.OwnedStateOnUniform sa sources alignment honest q reports u := by
  cases alignment
  exact F.sourceOwnerView sa honest q reports u

/-- The native ownership observations of one issued report tuple. -/
structure UniformOwnedReadback (w : ℕ) where
  /-- Original processor's public arguments, event trace, registers and RAM. -/
  original : (Arg → Word w) × List (TeamRAM.Event w) × Bank w × Memory w
  /-- The same observation supplied by the checked common-frame builder. -/
  source : (Arg → Word w) × List (TeamRAM.Event w) × Bank w × Memory w
  /-- Restoring the issued tuple preserves all four components. -/
  restored : original=source

/-- Return the two named physical observations and their checked agreement
without exposing the type parameters of the entire calendar in the result type. -/
noncomputable def AdmittedPinnedFrames.uniformOwnedReadback (alignment : physical=uniform)
    (honest : ∀ q : Routed (b:=sa.cube.b) (s:=sa.cube.s) owners, allowed (routeBroadcast sa.cube owners q).val)
    (q : {v : Routed (b:=sa.cube.b) (s:=sa.cube.s) owners // (sources physical).pins v})
    (reports : (sources physical).actual q.val) (u : Fin (R+1)) : UniformOwnedReadback w :=
    let c := routeBroadcast sa.cube owners q.val
    let ok := honest q.val
    let issued := F.frame c ok
    let b := F.builder c ok
    let agreement := (congrArg (fun f => issued.SourceAgreement fixed (sources f) b) alignment).mp (F.source c ok)
    let lifted : {v : Declared sa.cube owners (decodedBroadcast sa.cube c.val) // (sources uniform).pins v.val} :=
      ⟨⟨q.val,(decoded_routeBroadcast sa.cube owners q.val).symm⟩,
        (congrArg (fun f => (sources f).pins q.val) alignment).mp q.property⟩
    let tape := cast (congrArg (fun f => (sources f).actual q.val) alignment) reports
    ⟨F.sourceOwnedState G args live L fixed hw size base fit sa width U ib hb sb pinWidth owners (sources physical)
        rawPin profile claim allowed template entries honest q reports u,
      issued.sourceOwnedAt fixed (sources uniform) b agreement lifted tape u,
      F.uniformSourceOwnerView sa sources alignment honest q reports u⟩

end TeamContraction

end BorderVNP
end Computability
end OAI
