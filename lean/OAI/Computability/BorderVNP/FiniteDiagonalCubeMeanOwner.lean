import OAI.Computability.BorderVNP.FiniteDiagonalCubeMeanPlan
import OAI.Computability.BorderVNP.FiniteDiagonalCubeRawGrid
import OAI.Computability.BorderVNP.DiagonalPhysicalMeanOwner

/-! # Ownership of the finite-field terms on the true public mean-label placement -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FiniteDiagonal.FieldPacketPlan

open Crossing _root_.OAI.Computability.BorderVNP.Cube _root_.OAI.Computability.BorderVNP.Cube.Physical Diagonal
open scoped Classical

variable {D m d sites : ℕ} {P : Type} [Fintype P] {bits : P → ℕ} {F : Type*} [Field F]
  {Cell A : Type} [Fintype Cell] [DecidableEq Cell] [Fintype A]
  (N : Network D P bits) (cell : N.Site → Cell)
  (recv : A → Cell) (width : A → ℕ) (ord : N.CrossingEdge cell ≃ Fin m)
  (cs : List Cell) (distinct : cs.Nodup) (cover : cs.toFinset = Finset.univ)
  (cube : FixedCube F) (hd : 0 < d) {W : ℝ} {M : ℕ}
  (budget : PackedLabelBudget N cell recv width W M (d^(cube.pred+1)))
  {T : N.Tables F} (directory : FieldSiteDirectory N T) (siteID : N.Site ↪ Fin sites)

local notation "blocks" => blocksFor W (cube.h*cube.b) (d^(cube.pred+1))
local notation "label" => meanPackedLabel N cell recv width cs cube.pred d hd
local notation "plan" => meanPlan N cell recv width ord cs distinct cover cube hd budget

/-- The site's real tape enumeration and the native incoming data rows form
the public field frame of the very same mean-labelled cube placement. -/
noncomputable def meanFrame : FieldRawLayout plan directory where
  sites := sites
  siteID := siteID
  Operand := A
  finiteOperand := inferInstance
  recv := recv
  dataWidth := width

/-- The actual selected cube's owner in a field term equals the deterministic
group allocator computed from the selector and its own compact data rows. -/
theorem meanFrame_owners (R : ℕ) (select : Packet cube.pred d blocks → Selector cube.pred cube.copies cube.h) :
    (meanFrame N cell recv width ord cs distinct cover cube hd budget directory siteID).owners R select =
      greedyOwner R cube.b cube.width label recv width select := rfl

/-- The words in the native owner bank name the teams used by the public
finite-field path sum, even when the physical cell numbers are permuted. -/
theorem meanFrame_owner_stored {l : GroupWeights.Layout} {teams : TeamNative.Layout} {orig mem : ℕ → ℕ}
    (cells : Cell ≃ Fin l.cells) (hg : 0 < l.groups)
    (initial : PackedLabelBudget N cell recv width W M (l.groups^(cube.pred+1)))
    (schedule : GroupWeights.ScheduleResult l teams orig mem)
    (select : Packet cube.pred l.groups (blocksFor W (cube.h*cube.b) (l.groups^(cube.pred+1))) →
      Selector cube.pred cube.copies cube.h)
    {decl : LengthDeclaration cube.pred l.groups} (pass : passesLengths cube.b cube.width select decl)
    (physical : GroupWeights.PhysicalImage l orig (blocksFor W (cube.h*cube.b) (l.groups^(cube.pred+1)))
      cube.b cube.copies cube.h decl (meanPackedLabel N cell recv width cs cube.pred l.groups hg ∘ cells.symm)
      (cells ∘ recv) width) (g : Fin l.groups) :
    mem (teams.owners+g.val) = ((meanFrame N cell recv width ord cs distinct cover cube hg initial directory siteID).owners teams.r select g).val := by
  have stored := greedyOwner_stored schedule select pass _ _ _ physical g
  rwa [CellEntries.PacketPlacement.greedyOwner_reindex cells] at stored

end FiniteDiagonal.FieldPacketPlan

end BorderVNP
end Computability
end OAI
