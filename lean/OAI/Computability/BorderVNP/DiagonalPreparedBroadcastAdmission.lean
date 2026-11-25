import OAI.Computability.BorderVNP.DiagonalPinnedDeclarationImage
import OAI.Computability.BorderVNP.DiagonalPreparedBroadcastGuards

/-! # Exact checked input to the global pinned routing equivalence -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator.SignedPrep

open VPVNP.BurstRAM BorderVNP.Cube Physical Tally LocalRow CubeArena CubeHeaderInstall
open TeamContraction TeamContraction.JointHeader TeamContraction.ProcessorSlots Transmission DiagonalResidueRAM
open CellMacro.Generator PackedHistoryCircuit Crossing _root_.OAI.Computability.BorderVNP.Cube.GroupWeights Cube.MeanChoice Cube.LabelIndex

variable {w n k : ℕ} {pub : Arg → Word w} {baseMac : TeamOpcode.Macros w 8} {gen : Fragment IO}
    {s : Bank w} {initial : Memory w} {trace out saved} (f : BroadcastFrame)
variable (boot : Runs pub (CompactMachine.install gen n baseMac) bootHeader s initial trace out saved) (stable : f.Stable (readings out))
    (positive : (saved f.dst).val ≠ 0)
    (pinRun : (Fin k → Bool) ≃ Pins.Return pub (CompactMachine.install gen n baseMac) (Function.update out 10 (saved f.dst)) saved)
    (pinChoices : ∀ v, (pinRun v).val.1.flatMap TeamRAM.Event.choices = List.ofFn v)
    (profile : (Fin k → Bool) ≃ Returns (withStartup pinGeometry) pub (CompactMachine.install gen n baseMac) s initial)
    (readChoices : ∀ v, (profile v).val.1.flatMap TeamRAM.Event.choices=List.ofFn v)
variable {ar : CubeArena.Layout} {D : Packing.Directory.Layout} {pp lp : ℕ → ℕ × ℕ}
    {pins : Pins.Layout} {slotted : Memory w} {base : ℕ}
    {I : Type*} [Fintype I] {cell : I → Fin ar.cells} {id : I ↪ ℕ} {widths : I → ℕ}
    (P : SlottedWriter ar D pp lp pins pub slotted base cell id widths)
    (old : Fin 81 → Word w) (fresh gates outputs width off ell controls : ℕ)
    (G : List Bool) (claims : List (List Bool)) (pad : ℕ) (rawDecl : Broadcast ar.n ar.header.d ar.header.cap)
    (R X : ℕ)
    (room : PinnedRawInput (ar := ar) (D := D) (pp := pp) (lp := lp) (pub := pub) (slotted := slotted) (base := base)
      f old fresh gates outputs width off ell controls G claims pad rawDecl R X)
local notation3 (prettyPrint := false) "published" => Packing.Directory.ISA.publish slotted (pub 0).val base (D.directory pp lp)
local notation3 (prettyPrint := false) "mac" => CompactMachine.install gen n baseMac

local notation3 (prettyPrint := false) "layout₀" => LabelIndex.layout (pub 0).val (readings published)

include P room boot stable positive pinChoices readChoices in
/-- Every simultaneous candidate preparation in particular reaches the complete
lead-team prefix. On its genuine directory that prefix forces both the raw range
and the eligible common declaration, even when its scalar weight later vanishes. -/
theorem prepared_allowed (table : TableEntry ar.n ar.b ar.h ar.K ar.s → ℕ) (v : Fin k → Bool)
    (prep : SignedPreps table pub baseMac gen n _ saved pinRun v) {events : List (TeamRAM.Event w)} {reg : Bank w}
    (directory : Runs pub mac (.seq PrivatePlacement.program Packing.Directory.ISA.program)
      (profile v).val.2.1 (profile v).val.2.2 events reg published)
    {d : ℕ} {Names A : Type*} [Fintype A] {bits : Names → ℕ} (N : Network d Names bits)
    (tile : N.Site → Fin ar.cells) (recv : A → Fin ar.cells) (amount : A → ℕ)
    {edgeOrd : N.CrossingEdge tile ↪ Fin (layout₀).cableCount} {dataOrd : A ↪ Fin (layout₀).deliveryCount}
    (placed : RowPlacement (networkRows N tile recv amount) (fromTables layout₀ (readings published) room.labels.endpoints)
      (finCongr room.cells.symm) (edgeOrd.sumMap dataOrd)) (hd : 0<ar.header.d) :
    declarationInRange rawDecl ∧ broadcastAllowed R X ar.header.blocks ar.b ar.K ar.h
      (meanPackedLabel N tile recv amount (List.finRange ar.cells) ar.n ar.header.d hd) recv amount rawDecl := by
  obtain ⟨range,least,tr,t,m,run,_,cap⟩ := prepared_raw_guards f boot stable positive pinRun pinChoices profile readChoices
    P old fresh gates outputs width off ell controls G claims pad rawDecl R X room table v prep directory
  have transfer := pinned_allowed_iff ar f old fresh gates outputs width off ell controls G claims pad rawDecl R X
    room N tile recv amount hd placed range reg ⟨(tr,t,m),run⟩
  exact ⟨range,transfer.mpr ⟨least,cap⟩⟩

end RoutingISA.Evaluator.SignedPrep

end BorderVNP
end Computability
end OAI
