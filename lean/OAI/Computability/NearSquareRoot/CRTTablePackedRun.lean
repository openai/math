import OAI.Computability.NearSquareRoot.CRTTablePackedLayer
import OAI.Computability.NearSquareRoot.CRTTableBenesCertificate

/-! # The compiled Beneš switches execute a packed CRT shear row -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace CRTTable

variable {d : ℕ} (a w : Fin d → ℕ) [∀ j, NeZero (a j)] (hwidth : ∀ j, a j ≤ 2^w j)

/-- Actual raw bit tables for one external setting of one depth. The program
receives the selected external bits in the same order as the packed header. -/
noncomputable def packedTables (n : ℕ) (inv : Bool)
    (e : ExternalValues a w n) (b : TargetIndex d n) : Benes.RawTable :=
  let y := representative a w hwidth n e
  targetWordRows (tagAt a w n b.1.val b.2.val inv,
    packedControl n (List.finRange d) (addressField a w (fun _ => id) y))

theorem packedTables_represents (hdense : ∀ j, 2^w j ≤ 2*a j)
    (hcop : Pairwise (fun i j => (a i).Coprime (a j)))
    (n : ℕ) (hn : n < Nat.clog 2 d) (inv : Bool) (e : ExternalValues a w n)
    (b : TargetIndex d n) :
    Benes.RawRepresents (blockPerm a w hwidth n hn inv e b)
      (packedTables a w hwidth n inv e b) := by
  exact targetWordRows_represents a w (fun _ => id) hwidth hdense hcop n hn b.1
    (representative a w hwidth n e) inv b.2

/-- The complete sequence of switch layers computed from the generated tables
acts as the whole CRT shear row on the original padded address. -/
theorem packedStages_apply_row (hdense : ∀ j, 2^w j ≤ 2*a j)
    (hcop : Pairwise (fun i j => (a i).Coprime (a j)))
    (n : ℕ) (hn : n < Nat.clog 2 d) (inv : Bool) (D : ℕ) (width_le : ∀ g, w g ≤ D)
    (y : (g : Fin d) → AxisValue a w g) :
    let row := Stage.layerPerm a (fun g => Fin (2^w g-a g)) (Stage.atDepth d n hn)
    (Benes.executionOrder D).foldl
      (fun z t => Benes.packedStage (fun b => w (targetAxis d n b)) (packedTables a w hwidth n inv) t z)
      (packAddress a w hwidth n y) =
      packAddress a w hwidth n ((bif inv then row.symm else row) y) := by
  rw [Benes.packedStages_run _ _ _ (packedTables_represents a w hwidth hdense hcop n hn inv) D
    (fun b => width_le (targetAxis d n b))]
  exact (packedLayer_apply a w hwidth hdense hcop n hn inv y).symm

end CRTTable

end NearSquareRoot
end Computability
end OAI
