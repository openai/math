import OAI.Computability.VPVNP.PairShrinkPartyABReads
import OAI.Computability.VPVNP.PairShrinkPhysicalSourceBounds

/-! # Public AB read areas of a physical shrinking party

The old incidence columns use the actual number of outgoing arcs. The
classification and AB intersection tables fit their successive allocations
before the next level header.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.ShrinkResidentSources

open BurstRAM Compression Compression.ShrinkMotif CompressorRecords
open CompressorRecords.DescriptorSpace CompressorRecords.ShrinkBlockInputs
open scoped Fin.CommRing

variable {k : Type*} [_root_.Field k] {S : BlockSchedule k} {B : S.Templates} {i : Fin S.steps}
variable {w g : ℕ} {δ : ℝ} {X : State (a i) (packingLaneBits (a i) g)}
variable {ready : Ready (2 ^ a i) (Shrink.colors (a i)) (2 ^ b i) δ}
variable {sel : SelectedScore.Selection B X} {m : X.packingData.Motif} {party : Fin 6}
variable {base : Word w} {positions blocks cur H : ℕ}

local notation "lay" => BlockProgram.layout B base.val positions blocks
local notation "cut" => tableBase lay cur (0 : Fin 6)
local notation "first" => tableBase lay cur (1 : Fin 6)
local notation "source" => packedIncidence lay w cur (DemandRAM.oldCount X)

/-- The live shrinking level supplies all external bounds required by a
genuine AB job, including the last indexed three-word frame. -/
theorem Bounds.party_abAreas (bounds : Bounds B i X base positions blocks cur)
    (J : ShrinkPartyNative.Job X B.shrink ready sel m party w)
    (firstEq : J.first = first) (nextLe : levelStart lay (cur + 1) ≤ H) :
    J.ABAreas (levelStart lay cur : Word w) source cut H := by
  have tab (j : Fin 6) : tableBase lay cur j ≤ H :=
    (Nat.le_add_right _ _).trans ((tableEnd_le_nextLevel lay cur j).trans nextLe)
  have cutEq : cut = incidenceStart lay cur + 6 * slotCapacity lay := by
    simp only [tableBase, arrayBase, Fin.val_zero, Nat.zero_mul, Nat.add_zero]
  have column (j : Fin 6) : ((source).column j).val + DemandRAM.oldCount X ≤ H := by
    rw [packed_column]
    have within := Nat.mul_le_mul_right (DemandRAM.oldCount X) j.isLt
    rw [Nat.succ_mul] at within
    have cap := Nat.mul_le_mul_left 6 bounds.oldCapacity
    change 6 * DemandRAM.oldCount X ≤ 6 * slotCapacity lay at cap
    change (incidenceStart lay cur + j.val * DemandRAM.oldCount X) % 2^w + _ ≤ _
    exact (Nat.add_le_add_right (Nat.mod_le ..) _).trans
      (by have h := tab 0; rw [cutEq] at h; omega)
  have head : levelStart lay cur + 66 = incidenceStart lay cur := rfl
  have classEnd : (ShrinkInput.plan X cut).stop ≤ ShrinkInput.stop X cut :=
    (ShrinkInput.range_bounds X cut).2.2.2
  refine ⟨?_, classEnd.trans (bounds.fresh.trans (tab 1)), column 3, column 4, column 5, ?_⟩
  · have before := tab 0
    rw [cutEq, ← head] at before
    exact (Nat.add_le_add_right (Nat.mod_le ..) _).trans (by omega)
  · rw [firstEq]
    exact bounds.widthAfter.trans (tab 2)

end PairSimulation.ShrinkResidentSources

end VPVNP
end Computability
end OAI
