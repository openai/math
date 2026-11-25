import OAI.Computability.BorderVNP.FiniteEvaluatorTaskMatrices
import OAI.Computability.BorderVNP.FiniteEvaluatorPreparationWeight

/-! # Numerical value of the actual finite field report continuations

The full native task history is indexed by the matrices guessed at its owned
cells. After each such history the signed compact validators and scalar readers
act on the resulting RAM. The owned cube data survive these histories, so all
of them use the same numerical product of addressed cube entries.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FiniteEvaluator

open VPVNP.BurstRAM RoutingISA TeamContraction
open scoped Classical BigOperators

variable {F : Type*} [Field F] [Fintype F] {w n b h K s : ℕ}

/-- The signed checks on the compact cell inputs, cast to the field and multiplied
by the actual scalar-report readback from the same owned rows. -/
noncomputable def Cells.Inputs.hostFactor (X : Cells.Inputs F) (pub : Arg → Word w) (mem : Memory w) : F :=
  let f := CellDispatch.Frame.ofMemory pub mem
  ((((f.ownedRows mem 0 f.count).map (fun i => (X.cells i).weight)).prod : ℤ) : F) * X.outputs.prod

namespace TaskReadback

open CellPacket.Supplement

variable (pub : Arg → Word w) (bank : Bank w) (mem : Memory w) (N : ℕ)
variable (Y : CubePacket.Inputs n b h K s F) (reports : Reports.Layout) (rows : List Reports.Row)
variable (tasks : TypedTaskBuilder.Layout) (supp : ℕ → Batch.Cell) (count controls : ℕ)
variable (start : Setup pub mem reports rows tasks supp count controls)
variable {packet cell deck stop : ℕ} (placed : Placement pub Y reports rows tasks supp count packet cell deck stop)
variable (original : CubePacket.Prepared Y pub mem) (fields : reports.scalars=Fintype.card F)

section
variable (codec : Cells.Codec)
local notation "lib" => Cells.library F codec
local notation "ret" => Cells.terminals F codec
local notation "fuel" => CompactMachine.nativeClock N
local notation "mac" => TeamSiteEvents.macros (w:=w) lib fuel
local notation "Hist" => Evaluator.Returns prepareTasks pub mac bank mem
local notation "Values" => Matrices F reports.digits rows

include start placed original fields in
/-- Exact field sum of the two final pieces of the assembled positive branch,
beginning immediately before the real report choices. -/
theorem report_factors_for (ticks burst clock : ℕ) (wide : 2*Fintype.card F<w) (privateRoom : 2*Fintype.card F<fuel)
    (oneWord : 1 ≤ TeamScales.width N (1/2)) (wordCap : TeamScales.width N (1/2) ≤ burst)
    (choiceCap : N^25 ≤ clock) :
    ∃ E : Values ≃ Hist, (∀ c : Values, ∀ i : Fin rows.length,
      ((Reports.rebit rows ((E c).val.1.flatMap TeamRAM.Event.choices))[i.val]'(by simp)).bits=
        FiniteScalarRounds.stream F (c i)) ∧
      ∀ X : Values → Cells.Inputs F, (∀ c : Values, let out := E c
        Cells.Prepared (X c) pub out.val.2.2 N codec ∧ CubePacket.Sources Y (X c).layout ∧
        traceCost out.val.1+(X c).validatorCost pub out.val.2.2+(X c).scalarCost+Y.cost ≤ ticks) →
      boundedWeight pub lib ret fuel (.seq prepareTasks privateReturns) bank mem ticks burst clock =
        (∑ c : Values, (X c).hostFactor pub (E c).val.2.2) * ∏ i, Y.scalar i := by
  obtain ⟨decode,physical⟩ := return_equiv pub mac Y reports rows tasks supp count controls bank mem start placed original
  have sized (i : Fin rows.length) : rows[i].bits.length=reports.digits*Fintype.card F := by
    obtain ⟨_,_,_,_,dim⟩ := start.rooms i
    simpa only [fields,Nat.mul_comm] using dim
  let E := (matrixEquiv F reports.digits rows sized).trans decode.symm
  have bits (c : Values) : (matrixEquiv F reports.digits rows sized c).val=(E c).val.1.flatMap TeamRAM.Event.choices := by
    simpa only [E,Equiv.trans_apply,Equiv.apply_symm_apply] using (physical (E c)).1
  refine ⟨E,fun c i => ?_,?_⟩
  · rw [← bits c]
    exact matrixEquiv_read F reports.digits rows sized c i
  · intro X done
    have choices : 1 ≤ clock := by
      have pos : N≠0 := by rintro rfl; norm_num [TeamScales.width,Real.zero_rpow] at oneWord
      exact (Nat.one_le_pow _ _ (Nat.pos_of_ne_zero pos)).trans choiceCap
    let Bnd := Evaluator.BoundedReturns prepareTasks pub mac bank mem ticks burst clock
    let := Fintype.ofFinite Bnd
    have within (c : Values) : Within ticks burst clock (E c).val.1 :=
      ((E c).property.nativeOnly_limits (by decide)).mono (by have := (done c).2.2; omega) (Nat.zero_le _) choices
    let real : Values ≃ Bnd := E.trans ⟨fun x => ⟨x,by simpa only [Equiv.apply_symm_apply] using within (E.symm x)⟩,
      Subtype.val,fun _ => rfl,fun _ => rfl⟩
    rw [boundedWeight_seq,← real.sum_comp,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro c _
    obtain ⟨cells,src,time⟩ := done c
    have observed := (physical (E c)).2.1
    have after := CubePacket.Prepared.post (X c) cells Y observed src
    change weight pub lib ret fuel prepareTasks bank (E c).val.1 *
        boundedWeight pub lib ret fuel privateReturns (E c).val.2.1 (E c).val.2.2 (ticks-traceCost (E c).val.1) burst clock =
      (X c).hostFactor pub (E c).val.2.2 * ∏ i, Y.scalar i
    rw [weight_native pub lib ret fuel (E c).property (by decide),one_mul]
    exact CellsCube.bounded_prepared_for (X c) Y pub codec (E c).val.2.1 (E c).val.2.2 N _ _ _ cells after wide privateRoom oneWord
      (by omega) wordCap choiceCap

end

local notation "lib" => Cells.library F
local notation "ret" => Cells.terminals F
local notation "fuel" => CompactMachine.nativeClock N
local notation "mac" => TeamSiteEvents.macros (w:=w) lib fuel
local notation "Hist" => Evaluator.Returns prepareTasks pub mac bank mem
local notation "Values" => Matrices F reports.digits rows

include start placed original fields in
/-- Exact field sum of the two final pieces of the assembled positive branch,
beginning immediately before the real report choices. -/
theorem report_factors (ticks burst clock : ℕ) (wide : 2*Fintype.card F<w) (privateRoom : 2*Fintype.card F<fuel)
    (oneWord : 1 ≤ TeamScales.width N (1/2)) (wordCap : TeamScales.width N (1/2) ≤ burst)
    (choiceCap : N^25 ≤ clock) :
    ∃ E : Values ≃ Hist, (∀ c : Values, ∀ i : Fin rows.length,
      ((Reports.rebit rows ((E c).val.1.flatMap TeamRAM.Event.choices))[i.val]'(by simp)).bits=
        FiniteScalarRounds.stream F (c i)) ∧
      ∀ X : Values → Cells.Inputs F, (∀ c : Values, let out := E c
        Cells.Prepared (X c) pub out.val.2.2 N ∧ CubePacket.Sources Y (X c).layout ∧
        traceCost out.val.1+(X c).validatorCost pub out.val.2.2+(X c).scalarCost+Y.cost ≤ ticks) →
      boundedWeight pub lib ret fuel (.seq prepareTasks privateReturns) bank mem ticks burst clock =
        (∑ c : Values, (X c).hostFactor pub (E c).val.2.2) * ∏ i, Y.scalar i :=
  report_factors_for pub bank mem N Y reports rows tasks supp count controls start placed original fields .dense
    ticks burst clock wide privateRoom oneWord wordCap choiceCap

end TaskReadback
end FiniteEvaluator

end BorderVNP
end Computability
end OAI
