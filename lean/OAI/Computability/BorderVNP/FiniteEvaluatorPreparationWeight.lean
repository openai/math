import OAI.Computability.BorderVNP.FiniteEvaluatorProgramNative
import OAI.Computability.BorderVNP.DiagonalNativeSignedTags
import OAI.Computability.BorderVNP.DiagonalNativePhaseLimits

/-! # Field weights of the real preparation paths

Each accepted sequence of public reads, routing choices, packet scatters and
report guesses contributes a unit before the private calls. The proof follows
the actual instruction counter and registers, including every binary choice.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FiniteEvaluator

open VPVNP.BurstRAM RoutingISA TeamRAM FieldProcessor BorderVNP.Cube BorderVNP.Cube.Tally
open private groups_native owned_native from OAI.Computability.BorderVNP.DiagonalNativeSignedTags

variable {F : Type*} {dim b h K d w p r m g a k : ℕ} {Q Γ : Type}

private theorem native_sign (action : CallAction w (PrivateRAM.LogConfig w p r))
    {bits old t sg} (step : (TeamOpcode.nativeAction action).advance bits old = some (t,sg)) :
    sg=.plus := by
  cases action with
  | finish v => cases v <;> contradiction
  | reject => contradiction
  | _ =>
    cases bits with
    | nil => cases old with
      | nil => simp_all [TeamOpcode.nativeAction,Instr.advance]
      | cons x xs => cases xs <;> simp_all [TeamOpcode.nativeAction,Instr.advance]
    | cons bit bs => cases bs <;> cases old <;> simp_all [TeamOpcode.nativeAction,Instr.advance]

private theorem path_native [Field F] (P : TeamOpcode.Program p r k a) (pub : Fin k → Word w)
    (lib : Fin a → TeamSite.Macro Q Γ m g) (ret : Returns Q Γ F m a) (fuel : ℕ)
    (tags : ∀ pc, P.tag pc=.native) (s : TeamOpcode.State w p r) (es : List (TeamRAM.Event w))
    (valid : Local (P.fetch pub (TeamSiteEvents.macros lib fuel)) s es) :
    pathProduct P pub lib ret fuel s es = 1 := by
  induction es generalizing s with
  | nil => rfl
  | cons e es ih =>
    obtain ⟨_,next,advance,rest⟩ := valid
    have hp : e.sign=.plus := by
      have step := advance
      simp only [TeamOpcode.Program.fetch,tags] at step
      split at step
      · exact native_sign _ step
      · cases step
    have factor : eventWeight lib ret fuel (TeamOpcode.prepare P pub s).1 e=1 := by
      simp only [TeamOpcode.prepare,tags]
      split <;> simp [eventWeight,hp,Sign.value]
    simpa only [pathProduct,foldEvents,advance,factor,one_mul] using ih next rest

/-- All physical paths in a program compiled entirely to ordinary native tags
have field weight one, with the complete original choice and probe chronology. -/
theorem weight_native [Field F] (pub : Arg → Word w) (lib : Fin 8 → TeamSite.Macro Q Γ m g)
    (ret : Returns Q Γ F m 8) (fuel : ℕ) {c s mem es t mt}
    (run : Runs pub (TeamSiteEvents.macros lib fuel) c s mem es t mt) (native : c.nativeOnly=true) :
    weight pub lib ret fuel c s es=1 :=
  path_native _ _ _ _ _ (c.program_tag_native native) _ _ (execute_spec run.execute).1

/-- Every instruction in the assembled field evaluator preceding its validators
and field-return calls has an ordinary native opcode. -/
theorem preparation_nativeOnly [Fintype F] (table : TableEntry dim b h K d → F) :
    (preparation table).nativeOnly=true := by
  have constants := (CubeConstants.install (fun e => CubeWord.encode (table e))).nativeOnly_of_unsigned
    (CubeConstants.install_unsigned _).1
  simp only [preparation,preparationStages,List.foldr,openCells,Code.block,Code.nativeOnly,constants,groups_native,owned_native,
    show preparePins.nativeOnly=true by decide,show Evaluator.epochPlacement.nativeOnly=true by decide,
    show Packing.Directory.ISA.program.nativeOnly=true by decide,show Evaluator.route.nativeOnly=true by decide,
    show Padding.verify.nativeOnly=true by decide,show HostScatter.program.nativeOnly=true by decide,
    show Packing.BundleDirectory.program.nativeOnly=true by decide,show CellControlRows.program.nativeOnly=true by decide,
    show prepareTasks.nativeOnly=true by decide,Bool.and_self]

/-- The authentic positive-branch prefix contributes one and each of its events
costs at most one binary choice and zero extra word probes. -/
theorem preparation_weight [Field F] [Fintype F] (table : TableEntry dim b h K d → F)
    (pub : Arg → Word w) (lib : Fin 8 → TeamSite.Macro Q Γ m g) (ret : Returns Q Γ F m 8) (fuel : ℕ)
    {s mem es t mt} (run : Runs pub (TeamSiteEvents.macros lib fuel) (preparation table) s mem es t mt) :
    weight pub lib ret fuel (preparation table) s es=1 ∧ TeamContraction.Within (traceCost es) 0 1 es :=
  ⟨weight_native pub lib ret fuel run (preparation_nativeOnly table),run.nativeOnly_limits (preparation_nativeOnly table)⟩

open RoutingISA.Pins TeamContraction FiniteDiagonal
open scoped BigOperators Classical

variable [Field F] [Fintype F] (table : TableEntry dim b h K d → F)
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

/-- Every true bounded preparation history contributes the field values of its
owned validators, its scalar count readback, and the table entries selected by
its actual cube visits. -/
theorem program_positive_factors (wide : 2*Fintype.card F<w) (privateFit : 2*Fintype.card F<cfuel)
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
          ((((localFrame.ownedRows mem 0 localFrame.count).map (fun i => ((X x).cells i).weight)).prod : ℤ) : F) *
              (X x).outputs.prod * ∏ i, table (((Y x).visits i).entry (Y x).demand) := by
  intro X Y prepared
  apply (program_positive_prepared table pub fields f N bank startup header stable high ticks burst clock fit
    wide privateFit oneWord words choices X Y prepared).trans
  apply Finset.sum_congr rfl
  intro x _
  rw [(preparation_weight table pub clib cret cfuel x.val.property).1,one_mul]

end FiniteEvaluator

end BorderVNP
end Computability
end OAI
