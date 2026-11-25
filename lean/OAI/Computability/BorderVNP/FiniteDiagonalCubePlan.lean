import OAI.Computability.BorderVNP.FiniteDiagonalCubeHostWeight
import OAI.Computability.BorderVNP.DiagonalFixedCube

/-! # The fixed field cube and the deterministically balanced host labels -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FiniteDiagonal.FieldPacketPlan

open Crossing Cube Cube.Physical Diagonal
open scoped Classical

variable {D m d : ℕ} {P : Type*} {bits : P → ℕ} {F : Type*} [Field F]
  {Cell A : Type} [Fintype Cell] [DecidableEq Cell] [Fintype A]
  (N : Network D P bits) [DecidableEq N.Edge] (cell : N.Site → Cell)
  (recv : A → Cell) (dataWidth : A → ℕ)
  (ord : N.CrossingEdge cell ≃ Fin m)
  (cs : List Cell) (hcs : cs.toFinset = Finset.univ)
  (cube : FixedCube F) (hd : 0 < d) {W : ℝ} {M : ℕ}
  (budget : PackedLabelBudget N cell recv dataWidth W M (d^(cube.pred+1)))

/-- Build the actual plan from the finite-field cube, incoming operand loads
and the public search for balanced product labels. -/
noncomputable def publicPlan : FieldPacketPlan N F where
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
  label := publicPackedLabel N cell recv dataWidth cs cube.pred d hd
  capacity := load_le_blocks ord (crossSrc N cell) (crossDst N cell) (crossWidth N cell) _
    (fun e => e.property) ((Nat.cast_nonneg _).trans budget.dataVolume) cube.block_pos
    (pow_pos hd _) (publicPackedLoads N cell recv dataWidth cs hcs cube.pred d hd budget).1
  table := fun _ => cube.table
  valid := fun _ => cube.valid

/-- Each bit is read at the same deterministic address as the real public
slot embedding in the packet geometry. -/
theorem publicPlan_slot :
    (publicPlan N cell recv dataWidth ord cs hcs cube hd budget).slot =
      publicPackedEmbedding N cell recv dataWidth ord cs hcs cube.pred d hd cube.block_pos budget := rfl

end FiniteDiagonal.FieldPacketPlan

end BorderVNP
end Computability
end OAI
