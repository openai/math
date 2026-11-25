import OAI.Computability.BorderVNP.FiniteEvaluatorOwnedContinuation
import OAI.Computability.BorderVNP.FiniteEvaluatorCubeOpenReadback

/-! # The local evaluation of a genuinely returned owned-group assignment

At a passing physical padding assignment, the four public opening stages
have one exact RAM endpoint. The remaining native paths are indexed by the
field-label reports of its owned cells. At that endpoint the source cube
entries are those of the original assignment.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FiniteEvaluator.OwnedContinuation

open VPVNP.BurstRAM RoutingISA BorderVNP.Cube CellPacket.Supplement
open scoped BigOperators Classical

variable {F : Type*} [Field F] [Fintype F] {w n b h K s : ℕ}
variable (pub : Arg → Word w) (N : ℕ) (bank : Bank w) (mem : Memory w)
variable (H : OpenSuffix.Inputs) (ready : OpenSuffix.Ready H (pub 0).val (readings mem) w)
variable (a : CubeArena.Layout) (reserved : DiagonalTallyAllocation.BeforeTasks) (deckEnd : ℕ)
variable (Y : CubePacket.Inputs n b h K s F) (original : CubePacket.Prepared Y pub mem)
variable (report : Reports.Layout) (rows : List Reports.Row) (tasks : TypedTaskBuilder.Layout)
variable (supp : ℕ → Batch.Cell) (count controls : ℕ)
variable (openPlace : OpenSuffix.Placement H a reserved (pub 0).val (readings mem))
variable (writePlace : TaskReadback.Placement pub Y report rows tasks supp count a.header.packetBase a.cellBank a.stop deckEnd)
variable (gap : deckEnd ≤ reserved.start)
variable (source : ∀ out : Memory w, readings out=H.image (pub 0).val (readings mem) →
  TaskReadback.Setup pub out report rows tasks supp count controls)
variable (fieldCount : report.scalars=Fintype.card F)

section
variable (codec : Cells.Codec)
local notation "lib" => Cells.library F codec
local notation "ret" => Cells.terminals F codec
local notation "fuel" => CompactMachine.nativeClock N
local notation "mac" => TeamSiteEvents.macros (w:=w) lib fuel
local notation "Values" => TaskReadback.Matrices F (Reports.Layout.digits report) rows

include ready original openPlace writePlace gap source fieldCount in
/-- Full finite-field multiplier after the owned row program, on its real
passing memory, with the two true charges subtracted from the overall clock. -/
theorem passing_factors_for (ticks burst clock : ℕ)
    (padding : (Padding.Layout.fromFrame (pub 0).val (readings mem)).Valid (readings mem))
    (time : H.cost (pub 0).val (readings mem) ≤ ticks)
    (wide : 2*Fintype.card F<w) (privateRoom : 2*Fintype.card F<fuel)
    (oneWord : 1 ≤ TeamScales.width N (1/2)) (wordCap : TeamScales.width N (1/2) ≤ burst)
    (choiceCap : N^25 ≤ clock) :
    ∃ z : Evaluator.Returns OpenSuffix.code pub mac bank mem,
      ∃ E : Values ≃ Evaluator.Returns prepareTasks pub mac z.val.2.1 z.val.2.2,
      readings z.val.2.2=H.image (pub 0).val (readings mem) ∧
      (∀ c : Values, ∀ i : Fin rows.length,
        ((Reports.rebit rows ((E c).val.1.flatMap TeamRAM.Event.choices))[i.val]'(by simp)).bits=
          FiniteScalarRounds.stream F (c i)) ∧
      ∀ X : Values → Cells.Inputs F, (∀ c : Values, let out := E c
        Cells.Prepared (X c) pub out.val.2.2 N codec ∧ CubePacket.Sources Y (X c).layout ∧
        traceCost z.val.1+traceCost out.val.1+(X c).validatorCost pub out.val.2.2+(X c).scalarCost+Y.cost ≤ ticks) →
      boundedWeight pub lib ret fuel code bank mem ticks burst clock =
        (∑ c : Values, (X c).hostFactor pub (E c).val.2.2) * ∏ i, Y.scalar i := by
  obtain ⟨z,image,_,suffix⟩ := passing_for (F:=F) pub N bank mem codec H ready ticks burst clock padding time
  have held := original.transfer Y (OpenSuffix.placed_words H a reserved deckEnd Y ready openPlace z.property
    writePlace.ordered.1 writePlace.ordered.2.2.2 gap writePlace.operands)
  obtain ⟨E,bits,factors⟩ := TaskReadback.report_factors_for pub z.val.2.1 z.val.2.2 N Y report rows tasks supp count controls
    (source _ image) writePlace held fieldCount codec (ticks-traceCost z.val.1) burst clock wide privateRoom oneWord wordCap choiceCap
  refine ⟨z,E,image,bits,fun X checked => suffix.trans (factors X ?_)⟩
  intro c
  obtain ⟨cell,locations,clockRoom⟩ := checked c
  exact ⟨cell,locations,by omega⟩

end

local notation "lib" => Cells.library F
local notation "ret" => Cells.terminals F
local notation "fuel" => CompactMachine.nativeClock N
local notation "mac" => TeamSiteEvents.macros (w:=w) lib fuel
local notation "Values" => TaskReadback.Matrices F (Reports.Layout.digits report) rows

include ready original openPlace writePlace gap source fieldCount in
/-- Full finite-field multiplier after the owned row program, on its real
passing memory, with the two true charges subtracted from the overall clock. -/
theorem passing_factors (ticks burst clock : ℕ)
    (padding : (Padding.Layout.fromFrame (pub 0).val (readings mem)).Valid (readings mem))
    (time : H.cost (pub 0).val (readings mem) ≤ ticks)
    (wide : 2*Fintype.card F<w) (privateRoom : 2*Fintype.card F<fuel)
    (oneWord : 1 ≤ TeamScales.width N (1/2)) (wordCap : TeamScales.width N (1/2) ≤ burst)
    (choiceCap : N^25 ≤ clock) :
    ∃ z : Evaluator.Returns OpenSuffix.code pub mac bank mem,
      ∃ E : Values ≃ Evaluator.Returns prepareTasks pub mac z.val.2.1 z.val.2.2,
      readings z.val.2.2=H.image (pub 0).val (readings mem) ∧
      (∀ c : Values, ∀ i : Fin rows.length,
        ((Reports.rebit rows ((E c).val.1.flatMap TeamRAM.Event.choices))[i.val]'(by simp)).bits=
          FiniteScalarRounds.stream F (c i)) ∧
      ∀ X : Values → Cells.Inputs F, (∀ c : Values, let out := E c
        Cells.Prepared (X c) pub out.val.2.2 N ∧ CubePacket.Sources Y (X c).layout ∧
        traceCost z.val.1+traceCost out.val.1+(X c).validatorCost pub out.val.2.2+(X c).scalarCost+Y.cost ≤ ticks) →
      boundedWeight pub lib ret fuel code bank mem ticks burst clock =
        (∑ c : Values, (X c).hostFactor pub (E c).val.2.2) * ∏ i, Y.scalar i :=
  passing_factors_for pub N bank mem H ready a reserved deckEnd Y original report rows tasks supp count controls
    openPlace writePlace gap source fieldCount .dense ticks burst clock padding time wide privateRoom oneWord wordCap choiceCap

end FiniteEvaluator.OwnedContinuation

end BorderVNP
end Computability
end OAI
