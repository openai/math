import OAI.Computability.BorderVNP.DiagonalPinnedPublicationReturn
import OAI.Computability.BorderVNP.DiagonalSignedSlottedNetwork

/-! # Raw declaration checks on a signed pre-call path at its published directory -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator.SignedPrep

open VPVNP.BurstRAM BorderVNP.Cube Physical Tally LocalRow CubeArena CubeHeaderInstall
open TeamContraction TeamContraction.JointHeader TeamContraction.ProcessorSlots Transmission DiagonalResidueRAM
open CellMacro.Generator PackedHistoryCircuit

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

include P room boot stable positive pinChoices readChoices in
/-- A complete pinned native preparation on an arbitrary raw cube broadcast
passes the physical range, minimum and load checks at its actual published
slotted writer, even if the remaining private tests fail. -/
theorem prepared_raw_guards (table : TableEntry ar.n ar.b ar.h ar.K ar.s → ℕ) (v : Fin k → Bool)
    (prep : SignedPreps table pub baseMac gen n _ saved pinRun v)
    {events : List (TeamRAM.Event w)} {reg : Bank w}
    (directory : Runs pub mac (.seq PrivatePlacement.program Packing.Directory.ISA.program)
      (profile v).val.2.1 (profile v).val.2.2 events reg published) :
    declarationInRange rawDecl ∧ declaredMinimum rawDecl ∧ ∃ tr mid selected,
      Runs pub mac (.seq LabelIndex.directoryProgram NativeIntervals.prepare) reg published tr mid selected ∧
      (∀ j < ar.publicBase, readings selected j=readings published j) ∧
      capacities (weightLayout ar (pub 0).val (readCode (ar.n+1) rawDecl.1)) (teamLayout ar R) X
        (powerHeaderImage ar f.dst (readings selected)) := by
  let stages := (visitsEquiv table pub mac (pinRun v).val.2.1 (pinRun v).val.2.2).symm prep
  obtain ⟨_,run,silent⟩ := pinnedPublicationRun f boot stable positive pinRun pinChoices profile readChoices v
    stages.profile directory
  exact raw_guards P f old fresh gates outputs width off ell controls G claims pad rawDecl R X room run silent stages.profile

end RoutingISA.Evaluator.SignedPrep

end BorderVNP
end Computability
end OAI
