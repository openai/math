import OAI.Computability.VPVNP.PairSimulationResidentMapLoopExact
import OAI.Computability.VPVNP.PairSimulationShrinkGatherSource

/-!
# Exact items in a finite resident map row

The native map loop advances one word after each occurrence. The actions
at the finite row ordinals therefore form an exact list starting at the
published row base, including the empty row.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.ResidentMapLoop.Exact

open BurstRAM BurstRAM.PrivateRAM

variable {w endAddr p r k n src : ℕ} {P : Program p r} {M : Machine w p r k}
variable {m : Memory w} {dfs : Fin 9 ↪ Fin r} {inv : Word w → Config w p r → Prop}

/-- Consecutive source words turn the indexed occurrence proofs into the exact loop list. -/
theorem Items.ofFn {f : Fin n → Action w endAddr}
    (each : ∀ i, Item P M m dfs inv (src + i.val) (f i)) :
    Items P M m dfs inv src (List.ofFn f) := by
  induction n generalizing src with
  | zero => simp [Items]
  | succ n ih =>
    rw [List.ofFn_succ]
    constructor
    · simpa only [Fin.val_zero, Nat.add_zero] using each 0
    · apply ih
      intro i
      simpa only [Fin.val_succ, Nat.add_assoc, Nat.add_comm i.val 1] using each i.succ

end PairSimulation.ResidentMapLoop.Exact

namespace PairSimulation.ShrinkMapImage.Registers

open BurstRAM CompressorRecords Compression Compression.ShrinkMotif MotifGrid MotifBlocks
open MotifConversion MapResidentRows

variable {K : Type} [Field K] {factor : ℝ}
variable {B : FixedBlock K demandSource demandTarget supply
  (realWidths demandMass) (realWidths supplyMass) (31 / 16) factor}
variable {w a g : ℕ} {X : State a (packingLaneBits a g)} {selection : X.ShrinkSelection B}
variable {side : Bool} {m : Memory w} {level term : Word w}

/-- Address of the first resident-map slot of a site, including sites with no entries. -/
noncomputable def MapRowSource.rowStart (R : MapRowSource X selection side m level term)
    (site : Site X) : ℕ :=
  ((ShrinkResidentLayout.layout X R.first).params a true w 5).val +
    (siteIndex X site).val * capacity a

theorem MapRowSource.rowCursor_eq (R : MapRowSource X selection side m level term)
    (site : Site X) (i : Fin (order X side site).length) :
    rowCursor X selection side site m level term R i = R.rowStart site + i.val := rfl

end PairSimulation.ShrinkMapImage.Registers

end VPVNP
end Computability
end OAI
