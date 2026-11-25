import OAI.Computability.BorderVNP.RoutingISAScheduleClockPhases
import OAI.Computability.BorderVNP.CellTeamPreparedPaths
import OAI.Computability.BorderVNP.DiagonalNativePhaseLimits

/-! # Finite argument and probe charges at every actual preparing return -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator.ScheduleClock

open VPVNP.BurstRAM BorderVNP.Cube BorderVNP.Cube.Tally

private theorem constantField_slots (f : Word 8) (xs : List ℕ) : (Constants.atField f xs).unitCostPath=true := by
  have literal (bs : List Bool) : (Constants.literal bs).unitCostPath=true := by
    induction bs with
    | nil => rfl
    | cons b bs ih => cases b <;> simp [Constants.literal,Code.unitCostPath,ih]
  have words : (Constants.emitWords xs).unitCostPath=true := by
    induction xs with
    | nil => rfl
    | cons a xs ih => simp only [Constants.emitWords,Constants.emitWord,Code.unitCostPath,literal,ih,Bool.and_self]
  change (true && (true && (Constants.emitWords xs).unitCostPath))=true
  rw [words]; rfl

/-- Installing the fixed cube lookup table uses its static number of
instructions, even before making any assertion about the data words. -/
theorem constants_charge {w n b h K s : ℕ} (id : TableEntry n b h K s → ℕ)
    {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8} {r m es t mt}
    (run : Runs pub mac (CubeConstants.install id) r m es t mt) :
    traceCost es ≤ (CubeConstants.install id).slots :=
  run.cost_le_slots (by simp only [CubeConstants.install,Code.block,Code.unitCostPath,constantField_slots,Bool.and_self])

open CellPacket.Supplement.Batch CellDispatch CompactMachine CellSparse

/-- The probes budgeted for the *next* private call directory is already
controlled by the physical argument lengths in this return, even when
a later private call rejects. This is the bound required before the
private histories are enumerated. -/
theorem preparedDirectory_charge {w count table controls n : ℕ} {Site : Type}
    (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8) (s : Bank w) (m : Memory w)
    (owned : ℕ → Owned Site) (cells : ℕ → CellInput) (frame : (pub 0).val+92 < 2^w)
    (pointer : readings m ((pub 0).val+92)+11 < 2^w)
    (width : readings m ((pub 0).val+30)=w) (len : readings m ((pub 0).val+90)=count)
    (base : readings m ((pub 0).val+89)=table) (ctrl : readings m (readings m ((pub 0).val+92)+11)=controls)
    (taskFit : table+7*count ≤ 2^w) (controlFit : controls+4*count ≤ 2^w)
    (init : ∀ i < count, Initial (owned i) table controls i m)
    (alloc : Allocation (pub 0).val table controls count w owned) :
    let rows := fun i => (owned i).typed
    let patched := written m (fun i => (owned i).cell) count
    let f := Frame.ofMemory pub patched
    TypedBatch.PlacedRows pub patched rows count n cells → TypedBatch.ControlLayout pub patched rows count →
    ∀ {es t mt}, Runs pub mac prepareArguments s m es t mt →
      traceCost es+privateDirectoryTicks pub mt ≤ nativeCharge owned f mt count := by
  intro rows patched f placed control es t mt run
  obtain ⟨fs,u,first,cost,_,_⟩ := prepareArguments_run (pub:=pub) (mac:=mac) s m owned frame pointer width len base ctrl
    taskFit controlFit init alloc
  obtain ⟨events,_,image⟩ := run.unique_of_deterministic (by decide) first
  subst mt
  rw [events]
  have burst := placed.total_burst_le alloc.typed (fun i hi => (init i hi).typedRoom.2) control
  have survives := control.survives.1
  unfold privateDirectoryTicks
  change traceCost fs + (17+7*(Frame.ofMemory pub (TypedBatch.written patched rows count)).count+
    4*((Frame.ofMemory pub (TypedBatch.written patched rows count)).ownedRows _ 0
      (Frame.ofMemory pub (TypedBatch.written patched rows count)).count).length+
    (_ : List ℕ).sum) ≤ _
  rw [survives]
  exact Nat.add_le_add cost (Nat.add_le_add_left burst _)

/-- The preparing windows contain all public bundle and task directory
instructions, local cube work, reports and subsequent private probes. -/
theorem argument_window {w p d X R params expWidth global localCount units prep reports
    fixed owned pad host bundle controls taskDir bundles cables F U : ℕ}
    (cube : owned+pad+host ≤ 82*cables+F*U)
    (bundleCap : bundle ≤ Packing.BundleDirectory.setup.slots+16*global+30*bundles+1)
    (controlsCap : controls ≤ CellControlRows.setup.slots+global*(CellControlRows.body.slots+1)+1+CellControlRows.finish.slots)
    (tasksCap : taskDir ≤ TypedTaskBuilder.setup.slots+global*(TypedTaskBuilder.body.slots+1)+2)
    (globalFit : global ≤ 2^p) (localFit : localCount ≤ global)
    (unitFit : units ≤ 2*(w+1)*(2^p+2^d)+18*(w+1)*X+3*X+2*(1000000*X/256)+R*(params*expWidth))
    (preparing : prep ≤ 64+11*global+100*localCount+308*units)
    (report : reports ≤ 54+79*localCount+105*2^p+516*X+131*(R*(params*expWidth))) :
    fixed+owned+pad+host+bundle+controls+reports+taskDir+prep ≤
      fixed+argumentDirectory global bundles+(82*cables+F*U)+cellWork w (2^p+2^d) (R*(params*expWidth)) X := by
  have cell := signed_cell_charge globalFit localFit unitFit preparing report
  unfold argumentDirectory cellWork
  omega

end RoutingISA.Evaluator.ScheduleClock

end BorderVNP
end Computability
end OAI
