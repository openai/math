import OAI.Computability.BorderVNP.FiniteDiagonalCubePlan
import OAI.Computability.BorderVNP.CubeMeanPacked
import OAI.Computability.BorderVNP.CubeCommonVolume

/-! # The finite-field packet plan produced by the actual native mean-label scan -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FiniteDiagonal.FieldPacketPlan

open Crossing Cube Cube.Physical Diagonal
open scoped Classical

variable {D m d : ℕ} {P : Type*} {bits : P → ℕ} {F : Type*} [Field F]
  {Cell A : Type} [Fintype Cell] [DecidableEq Cell] [Fintype A]
  (N : Network D P bits) (cell : N.Site → Cell)
  (recv : A → Cell) (dataWidth : A → ℕ) (ord : N.CrossingEdge cell ≃ Fin m)
  (cs : List Cell) (distinct : cs.Nodup) (cover : cs.toFinset = Finset.univ)
  (cube : FixedCube F) (hd : 0 < d) {W : ℝ} {M : ℕ}
  (budget : PackedLabelBudget N cell recv dataWidth W M (d^(cube.pred+1)))

/-- Every padded slot, including those on entirely vacant pairs, belongs to
this physical field plan. The assignment sum uses one fixed table for each
packet selected by the native conditional-mean placement. -/
noncomputable def meanPlan : FieldPacketPlan N F where
  Cell := Cell
  finiteCell := inferInstance
  decEqCell := inferInstance
  cell := cell
  dimension := cube.pred
  alphabet := d
  blocks := blocksFor W (cube.h*cube.b) (d^(cube.pred+1))
  bitWidth := cube.b
  copies := cube.h
  alternatives := cube.copies
  supply := cube.width
  count := m
  order := ord
  label := meanPackedLabel N cell recv dataWidth cs cube.pred d hd
  capacity := load_le_blocks ord (crossSrc N cell) (crossDst N cell) (crossWidth N cell) _
    (fun e => e.property) ((Nat.cast_nonneg _).trans budget.dataVolume) cube.block_pos
    (pow_pos hd _) (meanPackedLoads N cell recv dataWidth cs distinct cover cube.pred d hd budget).1
  table := fun _ => cube.table
  valid := fun _ => cube.valid

/-- The native scatter and the finite-field expansion use the same slot
embedding of the original live crossing bits. -/
theorem meanPlan_slot :
    (meanPlan N cell recv dataWidth ord cs distinct cover cube hd budget).slot =
      meanPackedEmbedding N cell recv dataWidth ord cs distinct cover cube.pred d hd cube.block_pos budget := rfl

/-- Including a vacant padded packet opens its true scalar identity, with all
selector words retained in the physical field contraction. -/
theorem meanPlan_table (p : Packet cube.pred d (blocksFor W (cube.h*cube.b) (d^(cube.pred+1)))) :
    (meanPlan N cell recv dataWidth ord cs distinct cover cube hd budget).table p = cube.table := rfl

end FiniteDiagonal.FieldPacketPlan

end BorderVNP
end Computability
end OAI
