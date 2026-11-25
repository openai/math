import OAI.Computability.BorderVNP.FiniteEvaluatorReportFactors
import OAI.Computability.BorderVNP.FiniteEvaluatorCubeOpenSuffix

/-! # The true padding branch of the finite-field continuation

After the owned groups have returned, the four physical tests and writers
continue to the report choices and private calls exactly when the padded
ends have their required values. A failed test contributes the empty sum.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FiniteEvaluator.OwnedContinuation

open VPVNP.BurstRAM RoutingISA TeamContraction BorderVNP.Cube
open scoped BigOperators Classical

variable {F : Type*} [Field F] [Fintype F] {w dim b h K s : ℕ}
variable (pub : Arg → Word w) (N : ℕ) (bank : Bank w) (mem : Memory w)

/-- The actual instructions following the cube's owned-group table in the assembled branch. -/
def codeFor (tasks : Code) : Code := .seq OpenSuffix.code (.seq tasks privateReturns)

section
variable (codec : Cells.Codec) (tasks : Code)
local notation "clib" => Cells.library F codec
local notation "cret" => Cells.terminals F codec
local notation "fuel" => CompactMachine.nativeClock N
local notation "mac" => TeamSiteEvents.macros (w:=w) clib fuel

/-- Reassociate the actual assembled code at its two native boundaries,
preserving the charged physical histories and all fetched scalar factors. -/
theorem at_owned_stage (table : TableEntry dim b h K s → F) (ticks burst clock : ℕ) :
    boundedWeight pub clib cret fuel (.seq (openCells table) (.seq tasks privateReturns)) bank mem ticks burst clock =
    boundedWeight pub clib cret fuel (.seq (CubeDeck.install table) (.seq (TeamRows.ownedGroups dim b h K s) (codeFor tasks))) bank mem ticks burst clock :=
  (reassociate_boundedWeight pub clib cret fuel [CubeDeck.install table,TeamRows.ownedGroups dim b h K s]
    OpenSuffix.code (.seq tasks privateReturns) bank mem ticks burst clock).symm

variable (H : OpenSuffix.Inputs) (ready : OpenSuffix.Ready H (pub 0).val (readings mem) w)
variable (ticks burst clock : ℕ)
local notation "valid" => Padding.Layout.Valid (Padding.Layout.fromFrame (Fin.val (pub 0)) (readings mem)) (readings mem)
local notation "testCost" => OpenSuffix.Inputs.cost H (Fin.val (pub 0)) (readings mem)
local notation "Prefix" => Evaluator.BoundedReturns OpenSuffix.code pub mac bank mem ticks burst clock

include ready in
/-- A rejected padding assignment has exactly zero field contribution at every
native resource allowance. -/
theorem rejected_stage (fail : ¬valid) :
    boundedWeight pub clib cret fuel (codeFor tasks) bank mem ticks burst clock=0 := by
  have no (x : Prefix) : False := fail (((OpenSuffix.run H ready).sound x.val.property).1)
  exact (boundedWeight_seq pub clib OpenSuffix.code (.seq tasks privateReturns) bank mem ticks burst clock cret fuel).trans
    (Finset.sum_eq_zero fun x _ => (no x).elim)

include ready in
/-- On valid padded ends the native public suffix has exactly one returning
history, and the report program starts from its true bank and final RAM with
the exact residual clock. -/
theorem passing_stage (pass : valid) (fits : testCost ≤ ticks) :
    ∃ z : Evaluator.Returns OpenSuffix.code pub mac bank mem,
      readings z.val.2.2=H.image (pub 0).val (readings mem) ∧ traceCost z.val.1 ≤ testCost ∧
      boundedWeight pub clib cret fuel (codeFor tasks) bank mem ticks burst clock =
        boundedWeight pub clib cret fuel (.seq tasks privateReturns) z.val.2.1 z.val.2.2
          (ticks-traceCost z.val.1) burst clock := by
  have test : TestRun pub mac OpenSuffix.code bank mem testCost valid (fun z => z.mem=H.image (pub 0).val (readings mem)) := OpenSuffix.run H ready
  obtain ⟨es,t,mt,run,cost,result⟩ := test.complete pass
  let z : Evaluator.Returns OpenSuffix.code pub mac bank mem := ⟨⟨es,t,mt⟩,run⟩
  have unsigned : OpenSuffix.code.unsigned=true := by decide
  have det : OpenSuffix.code.deterministic=true := by decide
  have cap : Within ticks burst clock es := ⟨cost.trans fits,fun e he => (run.deterministic_extra det e he).le.trans (Nat.zero_le _),
    fun e he => by rw [(run.unsigned_events unsigned e he).1]; exact Nat.zero_le _⟩
  let p : Prefix := ⟨z,cap⟩
  have only (x : Prefix) : x=p := by
    obtain ⟨as,regs,ram⟩ := x.val.property.unique_of_deterministic det run
    exact Subtype.ext (Subtype.ext (Prod.ext as (Prod.ext regs ram)))
  refine ⟨z,result,cost,?_⟩
  let := Fintype.ofFinite Prefix
  rw [codeFor,boundedWeight_seq,Finset.sum_eq_single p]
  · change weight pub clib cret fuel OpenSuffix.code bank es * _ = _
    rw [weight_native pub clib cret fuel run (OpenSuffix.code.nativeOnly_of_unsigned unsigned),one_mul]
  · intro x _ ne
    exact (ne (only x)).elim
  · intro out; exact (out (Finset.mem_univ _)).elim

end

/-- The actual instructions following the cube's owned-group table in the assembled branch. -/
def code : Code := .seq OpenSuffix.code (.seq prepareTasks privateReturns)

section
variable (codec : Cells.Codec)
local notation "clib" => Cells.library F codec
local notation "cret" => Cells.terminals F codec
local notation "fuel" => CompactMachine.nativeClock N
local notation "mac" => TeamSiteEvents.macros (w:=w) clib fuel

/-- Reassociate the actual assembled code at its two native boundaries,
preserving the charged physical histories and all fetched scalar factors. -/
theorem at_owned_for (table : TableEntry dim b h K s → F) (ticks burst clock : ℕ) :
    boundedWeight pub clib cret fuel (.seq (openCells table) (.seq prepareTasks privateReturns)) bank mem ticks burst clock =
    boundedWeight pub clib cret fuel (.seq (CubeDeck.install table) (.seq (TeamRows.ownedGroups dim b h K s) code)) bank mem ticks burst clock :=
  at_owned_stage pub N bank mem codec prepareTasks table ticks burst clock

variable (H : OpenSuffix.Inputs) (ready : OpenSuffix.Ready H (pub 0).val (readings mem) w)
variable (ticks burst clock : ℕ)
local notation "valid" => Padding.Layout.Valid (Padding.Layout.fromFrame (Fin.val (pub 0)) (readings mem)) (readings mem)
local notation "testCost" => OpenSuffix.Inputs.cost H (Fin.val (pub 0)) (readings mem)
local notation "Prefix" => Evaluator.BoundedReturns OpenSuffix.code pub mac bank mem ticks burst clock

include ready in
/-- A rejected padding assignment has exactly zero field contribution at every
native resource allowance. -/
theorem rejected_for (fail : ¬valid) :
    boundedWeight pub clib cret fuel code bank mem ticks burst clock=0 :=
  rejected_stage (F:=F) pub N bank mem codec prepareTasks H ready ticks burst clock fail

include ready in
/-- On valid padded ends the native public suffix has exactly one returning
history, and the report program starts from its true bank and final RAM with
the exact residual clock. -/
theorem passing_for (pass : valid) (fits : testCost ≤ ticks) :
    ∃ z : Evaluator.Returns OpenSuffix.code pub mac bank mem,
      readings z.val.2.2=H.image (pub 0).val (readings mem) ∧ traceCost z.val.1 ≤ testCost ∧
      boundedWeight pub clib cret fuel code bank mem ticks burst clock =
        boundedWeight pub clib cret fuel (.seq prepareTasks privateReturns) z.val.2.1 z.val.2.2
          (ticks-traceCost z.val.1) burst clock :=
  passing_stage (F:=F) pub N bank mem codec prepareTasks H ready ticks burst clock pass fits
end

local notation "clib" => Cells.library F
local notation "cret" => Cells.terminals F
local notation "fuel" => CompactMachine.nativeClock N
local notation "mac" => TeamSiteEvents.macros (w:=w) clib fuel

/-- Reassociate the actual assembled code at its two native boundaries,
preserving the charged physical histories and all fetched scalar factors. -/
theorem at_owned (table : TableEntry dim b h K s → F) (ticks burst clock : ℕ) :
    boundedWeight pub clib cret fuel (.seq (openCells table) (.seq prepareTasks privateReturns)) bank mem ticks burst clock =
    boundedWeight pub clib cret fuel (.seq (CubeDeck.install table) (.seq (TeamRows.ownedGroups dim b h K s) code)) bank mem ticks burst clock :=
  at_owned_for pub N bank mem .dense table ticks burst clock

variable (H : OpenSuffix.Inputs) (ready : OpenSuffix.Ready H (pub 0).val (readings mem) w)
variable (ticks burst clock : ℕ)
local notation "valid" => Padding.Layout.Valid (Padding.Layout.fromFrame (Fin.val (pub 0)) (readings mem)) (readings mem)
local notation "testCost" => OpenSuffix.Inputs.cost H (Fin.val (pub 0)) (readings mem)
local notation "Prefix" => Evaluator.BoundedReturns OpenSuffix.code pub mac bank mem ticks burst clock

include ready in
/-- A rejected padding assignment has exactly zero field contribution at every
native resource allowance. -/
theorem rejected (fail : ¬valid) :
    boundedWeight pub clib cret fuel code bank mem ticks burst clock=0 :=
  rejected_for (F:=F) pub N bank mem .dense H ready ticks burst clock fail

include ready in
/-- On valid padded ends the native public suffix has exactly one returning
history, and the report program starts from its true bank and final RAM with
the exact residual clock. -/
theorem passing (pass : valid) (fits : testCost ≤ ticks) :
    ∃ z : Evaluator.Returns OpenSuffix.code pub mac bank mem,
      readings z.val.2.2=H.image (pub 0).val (readings mem) ∧ traceCost z.val.1 ≤ testCost ∧
      boundedWeight pub clib cret fuel code bank mem ticks burst clock =
        boundedWeight pub clib cret fuel (.seq prepareTasks privateReturns) z.val.2.1 z.val.2.2
          (ticks-traceCost z.val.1) burst clock :=
  passing_for (F:=F) pub N bank mem .dense H ready ticks burst clock pass fits

end FiniteEvaluator.OwnedContinuation

end BorderVNP
end Computability
end OAI
