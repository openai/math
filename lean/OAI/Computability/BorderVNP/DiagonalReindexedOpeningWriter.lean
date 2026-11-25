import OAI.Computability.BorderVNP.DiagonalOpeningNativePlacement
import OAI.Computability.BorderVNP.PackedNativeDemandCableCast

/-! # The original slotted writer at the physical cable width -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator

open VPVNP.BurstRAM Packing RoutingOutputs NativeDemands Crossing
open Lean Meta Elab Term

/-- The private and live addresses of a canonical writer are preserved when the
embedding of its network cables is transported along an equality of widths. -/
def SlottedWriter.reindexCanonicalCables {w D ne np : ℕ} {P : Type} {I : Type*} [Fintype P] [Fintype I]
    {nb : P → ℕ} {N : Network D P nb} {ar : CubeArena.Layout} {dir : Directory.Layout}
    {cell : N.Site → Fin ar.cells} {edge : N.Edge ↪ Fin ne} {port : P ↪ Fin np}
    {old : Fin dir.entries ↪ N.Site} {live : (Fin dir.teams × Fin dir.sites) ↪ P} {gap : ℕ}
    {pins : Pins.Layout} {pub : Arg → Word w} {after : Memory w} {base : ℕ}
    {resides : I → Fin ar.cells} {key : I ↪ ℕ} {size : I → ℕ}
    (writer : SlottedWriter ar dir (privatePair N cell edge port dir old live gap)
      (livePair N cell edge port dir old live gap) pins pub after base resides key size)
    (he : ne = ar.cables) :
    SlottedWriter ar dir (privatePair N cell (edge.trans (finCongr he).toEmbedding) port dir old live gap)
      (livePair N cell (edge.trans (finCongr he).toEmbedding) port dir old live gap)
      pins pub after base resides key size := by
  simpa only [privatePair_cast_cables, livePair_cast_cables] using writer

private def nativeSlotParameters (args : Array Expr) (actual : Array Expr) : Array (FVarId × Expr) :=
  (args.zip actual).filterMap fun (arg,val) => if arg.isFVar then some (arg.fvarId!,val) else none

/-- Recover the exact network and address parameters of the issued writer and apply
the cable reindexing theorem to them. -/
elab (name := writerAcrossCables) "writerAcrossCables% " previous:ident cableEq:ident : term => do
  let writer ← getFVarFromUserName previous.getId
  let equality ← getFVarFromUserName cableEq.getId
  addTermInfo' previous writer
  addTermInfo' cableEq equality
  let some source ← whnfUntil (← inferType writer) ``SlottedWriter | throwError "missing the issued slotted writer"
  let rule ← mkConstWithFreshMVarLevels ``SlottedWriter.reindexCanonicalCables
  forallTelescope (← inferType rule) fun args _ => do
    let names ← args.mapM (fun a => a.fvarId!.getUserName)
    let some i := names.idxOf? `writer | throwError "missing input writer in cable reindexing rule"
    let some formal ← whnfUntil (← inferType args[i]!) ``SlottedWriter | throwError "unexpected original writer"
    unless ← isDefEq formal.getAppFn source.getAppFn do throwError "different writer universe"
    let mut inputs := nativeSlotParameters formal.getAppArgs source.getAppArgs
    for template in formal.getAppArgs, value in source.getAppArgs do
      if template.getAppFn.isConstOf ``privatePair then
        let some concrete ← whnfUntil value ``privatePair | throwError "issued private slots do not come from the original demand rows"
        inputs := inputs ++ nativeSlotParameters template.getAppArgs concrete.getAppArgs
    let result ← args.mapM fun field => do
      let n ← field.fvarId!.getUserName
      if n == `writer then return writer
      if n == `he then return equality
      let some (_,result) := inputs.find? (·.1 == field.fvarId!) | throwError "writer and original demand do not supply {n}"
      return result
    return mkAppN rule result

/-- Restore the original frame address of the private placement written on the middle memory. -/
theorem actualPrivateImageOnFrame {old head origin cables cells entries desc gap slots : ℕ}
    {before after : ℕ → ℕ} (agree : old = head)
    (observed : (privateLayout old origin cables cells entries desc gap).Image before slots after) :
    (privateLayout head origin cables cells entries desc gap).Image before slots after := by
  subst head
  exact observed

/-- The actual table-fit proof is retained on replacing its frame by an equal original address. -/
theorem actualPrivateFitOnFrame {old head origin cables cells entries desc gap w : ℕ}
    {before : ℕ → ℕ} (agree : old = head)
    (observed : (privateLayout old origin cables cells entries desc gap).Fits w before) :
    (privateLayout head origin cables cells entries desc gap).Fits w before := by
  subst head
  exact observed

end RoutingISA.Evaluator

end BorderVNP
end Computability
end OAI
