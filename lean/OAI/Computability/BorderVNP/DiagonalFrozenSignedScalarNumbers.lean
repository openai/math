import OAI.Computability.BorderVNP.DiagonalFrozenSignedTask

/-! # Exact scalar numbers in the selected signed task's physical report bank -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Branch Crossing Cover Packing ExternalSew PackedHistoryCircuit.Normalized PackedHistoryCircuit.Normalized.SelectedSchedule TeamScales
open TeamContraction TeamContraction.ProcessorSlots
open RoutingISA RoutingISA.SignedTaskArena _root_.OAI.Computability.BorderVNP.Cube
open scoped Classical BorderVNP.Epoch.Cube

variable {F K : Type} [Field F] [Field K] {D m : ℕ} (G : PaidIdentity F D m)
    (cube : FixedCube K)
local notation "entries" => TableEntry cube.pred cube.b cube.h cube.copies cube.width
local notation "gadgets" => Fintype.card (G.Entry ⊕ entries)

/-- Even when the paid-entry dictionary is empty, the chosen cube has a real
selector and a zero wire label in each basis, hence a real scalar coordinate. -/
theorem FixedCube.scalarDictionary_positive : 0 < gadgets := by
  let selector : Selector cube.pred cube.copies cube.h := (⟨0,cube.copies_pos⟩,fun _ => default)
  let vertex : Vertex (cube.pred+1) := default
  let scalar : entries := ⟨selector,vertex,⟨fun _ _ => 0,fun _ _ => 0⟩,⟨fun _ _ => 0,fun _ _ => 0⟩⟩
  exact Fintype.card_pos_iff.mpr ⟨Sum.inr scalar⟩

/-- The two injections into this shared paid/cube scalar directory use the
same numbering as the emitted task, including its highest legal coordinate. -/
theorem FixedCube.scalarNumber_le_last (z : G.Entry ⊕ entries) : cube.scalarNumber G z ≤ gadgets-1 :=
  Nat.le_pred_of_lt ((Fintype.equivFin _ z).isLt)

variable [NeZero D] {S : SiteSchedule G} {extra E dlog Q A B j : ℕ} {s : EpochScales S (cube.pred+1) extra}

/-- The actual frozen task, for every candidate and all packet allocations, has
a fixed positive report-gadget arity. Its largest legal identifier has constant
bit width on the joint schedule (polynomial logarithmic exponent zero). -/
theorem JointSchedule.frozenSignedTask_scalarNumbers (b : JointSchedule.{0} s (E+1) dlog Q A B j)
    (n l size headerFactor : ℕ) (initial : StartupArena) (dir : Directory.Layout)
    (profile ceiling outputs field : ℕ) (dirs : GeometryDirectories) :
    let task := b.frozenSignedTask cube n l size headerFactor initial dir profile ceiling outputs field dirs
    let breadth := (gadgets-1).size+1
    task.p.report.gadgets=gadgets ∧ 0 < task.p.report.gadgets ∧
      (∀ z : G.Entry, cube.scalarNumber G (.inl z) ≤ task.p.report.gadgets-1) ∧
      (∀ i : entries, cube.cubeID G i ≤ task.p.report.gadgets-1) ∧
      (task.p.report.gadgets-1).size+1 ≤ breadth*(logWidth (stretch b.ρ n) n+1)^0 := by
  exact ⟨rfl,cube.scalarDictionary_positive G,fun z => cube.scalarNumber_le_last G (.inl z),
    fun i => cube.scalarNumber_le_last G (.inr i),by simp only [pow_zero,Nat.mul_one]; rfl⟩

end Diagonal

end BorderVNP
end Computability
end OAI
