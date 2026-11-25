import OAI.Computability.BorderVNP.FiniteEvaluatorProgram
import OAI.Computability.BorderVNP.FiniteEvaluatorBoundedReassociation
import OAI.Computability.BorderVNP.FiniteEvaluatorCellsCubeNative
import OAI.Computability.BorderVNP.FiniteEvaluatorCubePost

/-! # Bounded native paths of the closed positive field evaluator

The preparatory paths run the actual pin, profile, layout, transmission, host
and report code. After each of those paths, the signed validator, scalar
readback and cube calls use the resulting shared memory and remaining clock.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FiniteEvaluator

open VPVNP.BurstRAM RoutingISA RoutingISA.Pins TeamContraction FiniteDiagonal
open BorderVNP.Cube BorderVNP.Cube.Tally
open scoped BigOperators Classical

variable {dim b h K d w : ℕ} {F : Type*} [Field F] [Fintype F]
variable (table : TableEntry dim b h K d → F)

/-- Source stages before the final typed task builder in the actual positive table. -/
noncomputable def preparationStages : List Code :=
  [preparePins, Evaluator.epochPlacement,
    .block [Packing.Directory.ISA.program,Evaluator.scheduleGroups dim (selectorWidth dim K h),Evaluator.route], openCells table]

/-- The exact preparatory source instructions up to the first cell call. -/
noncomputable def preparation : Code := (preparationStages table).foldr Code.seq prepareTasks

variable (pub : Arg → Word w) {L : Pins.Layout} (fields : ProcessorFields L) (f : BroadcastFrame)
variable (N : ℕ) (bank : Bank w) {pre hs : List (TeamRAM.Event w)} {post loaded : Bank w} {after mb : Memory w}
local notation "cfuel" => CompactMachine.nativeClock N
local notation "clib" => Cells.library F
local notation "cret" => Cells.terminals F
local notation "mac" => TeamSiteEvents.macros (w := w) clib cfuel

variable (startup : Runs pub (TeamSiteEvents.macros (Cells.library F) (CompactMachine.nativeClock N)) wideStartup bank (Evaluator.processorMemory fields w) pre post after)
variable (header : Runs pub (TeamSiteEvents.macros (Cells.library F) (CompactMachine.nativeClock N)) readBroadcast post after hs loaded mb)
variable (stable : f.Stable (readings loaded)) (high : (mb f.dst).val ≠ 0)
variable (ticks burst clock : ℕ) (fit : pre.length+hs.length+2 ≤ ticks)
local notation "startBank" => Function.update loaded 10 (mb f.dst)
local notation "remaining" => ticks-(pre.length+hs.length+2)
local notation "M" => Evaluator.processorMachine (program table) pub mac bank fields
local notation "Prefix" => Evaluator.BoundedReturns (preparation table) pub mac startBank mb remaining burst clock

include startup header stable high fit

/-- Each genuine bounded path of the closed positive-tag program corresponds to
one original preparation path and one original return of its field routines.
The emitted path retains the exact chronological tape and the product of the
two real field weights, including signed and field zero. -/
theorem program_positiveEquiv :
    ∃ E : (Σ x : Prefix, Evaluator.BoundedReturns privateReturns pub mac x.val.val.2.1 x.val.val.2.2
        (remaining-traceCost x.val.val.1) burst clock) ≃ NativePath M ticks burst clock, ∀ p,
      (E p).val = Evaluator.dispatchPrefix f mb pre hs ++ (p.1.val.val.1++p.2.val.val.1) ∧
      weight pub clib cret cfuel (program table) bank (E p).val =
        weight pub clib cret cfuel (preparation table) startBank p.1.val.val.1 *
          weight pub clib cret cfuel privateReturns p.1.val.val.2.1 p.2.val.val.1 := by
  obtain ⟨whole,hw⟩ := positive_weightedBodyEquiv pub clib cret cfuel (positive table) fields f bank
    startup header stable high (positive_returns table) ticks burst clock fit
  let join := chargedSeqEquiv pub (preparation table) privateReturns startBank mb remaining burst clock mac
  let bracket := reassociateEquiv pub mac (preparationStages table) prepareTasks privateReturns startBank mb remaining burst clock
  let internal := join.trans bracket.symm
  refine ⟨internal.trans whole,?_⟩
  rintro ⟨x,y⟩
  let path := internal ⟨x,y⟩
  have both := hw path
  refine ⟨both.1,both.2.trans ?_⟩
  exact (reassociate_weight pub clib cret cfuel (preparationStages table) prepareTasks privateReturns path.val.property).trans
    (weight_seq pub clib cret cfuel x.val.property y.val.property)

/-- The actual closed program on its positive physical tag. For every original
preparation path the cube operands reside in protected ranges at its exit,
and the evaluator preserves them across the sparse validator and report calls.
The final factor uses the very same cube table embedded in the code. -/
theorem program_positive_prepared (wide : 2*Fintype.card F<w) (privateFit : 2*Fintype.card F<cfuel)
    (oneWord : 1≤TeamScales.width N (1/2)) (words : TeamScales.width N (1/2) ≤ burst) (choices : N^25 ≤ clock) :
    letI := Fintype.ofFinite Prefix
    letI := Fintype.ofFinite (NativePath M ticks burst clock)
    ∀ (X : Prefix → Cells.Inputs F) (Y : Prefix → CubePacket.Inputs dim b h K d F),
      (∀ x : Prefix, let mem := x.val.val.2.2
        Cells.Prepared (X x) pub mem N ∧ CubePacket.Prepared (Y x) pub mem ∧
          CubePacket.Sources (Y x) (X x).layout ∧ (Y x).entry = table ∧
          (X x).validatorCost pub mem+(X x).scalarCost+(Y x).cost ≤ remaining-traceCost x.val.val.1) →
      (∑ p : NativePath M ticks burst clock, weight pub clib cret cfuel (program table) bank p.val) =
        ∑ x : Prefix, let mem := x.val.val.2.2
          let localFrame := CellDispatch.Frame.ofMemory pub mem
          weight pub clib cret cfuel (preparation table) startBank x.val.val.1 *
            (((((localFrame.ownedRows mem 0 localFrame.count).map (fun i => ((X x).cells i).weight)).prod : ℤ) : F) *
              (X x).outputs.prod * ∏ i, table (((Y x).visits i).entry (Y x).demand)) := by
  intro X Y prepared
  apply (positive_native_sum pub clib cret cfuel (positive table) fields f bank startup header stable high
    (positive_returns table) ticks burst clock fit).trans
  apply (reassociate_boundedWeight pub clib cret cfuel (preparationStages table) prepareTasks privateReturns startBank mb remaining burst clock).trans
  apply (boundedWeight_seq pub clib (preparation table) privateReturns startBank mb remaining burst clock cret cfuel).trans
  apply Finset.sum_congr rfl
  intro x _
  obtain ⟨cells,cube,ranges,deck,time⟩ := prepared x
  have afterCalls := CubePacket.Prepared.post (X x) cells (Y x) cube ranges
  have suffix := CellsCube.bounded_prepared (X x) (Y x) pub x.val.val.2.1 x.val.val.2.2 N _ _ _ cells afterCalls
    wide privateFit oneWord time words choices
  apply congrArg (weight pub clib cret cfuel (preparation table) startBank x.val.val.1 * ·)
  simpa only [privateReturns,CellsCube.code,CubePacket.Inputs.scalar,deck] using suffix

end FiniteEvaluator

end BorderVNP
end Computability
end OAI
