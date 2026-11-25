import OAI.Hierarchy.DescentDatedOrdinaryOperands

namespace OAI
/-! # The attained ordinary branch, through seven fields of its next argument tableau -/
namespace Hierarchy
open DescentDatedAddressBook DescentPacking.PackedMatch.Local DescentOperandVectorArena ProtocolRAM
noncomputable section
namespace DescentPacking.PackedMatch.Local.Stage.Dated.Ordinary
def ordinaryWords (a : Ordinary) (old : Bank) (v : Layout) :=
  a.rotationEnd old 0+a.donorWords+v.endAddress 0

theorem ordinary_words_rate {ι : ℕ→Type*} (a : ∀h,ι h→Ordinary) (old : ∀h,ι h→Bank)
    (v : ∀h,ι h→Layout) (b : ScalarRoom a) (pack : ∀h i,SixBirths.unit (a h i).shapeAt≤(a h i).unit)
    (vector : Layout.ScalarRoom v) : DescentDatedAddressBook.Bounded (fun h i=>(a h i).ordinaryWords (old h i) (v h i)) :=
  (((rotation_rate a old b pack).add (donor_width_rate a b)).add (Layout.extent_rate v vector))
end DescentPacking.PackedMatch.Local.Stage.Dated.Ordinary
namespace DescentSixParty.Chronology.OrdinaryLink
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {G : PoweredGadget F}
variable {S : DescentCompiler.AtomSchedule} {q u ε : ℝ} {k i z D wire hist : ℕ} {W : MarkedWorld F d P bits}
variable {prior : Reached W G q ε S k i z D wire hist} {he : 0≤ε} {T : StageInput W G u ε}
variable {c : (T.result he).Choice} {n : Normalize ((T.result he).state c)} {z' D' : ℕ}
variable {target : Reached n.result G q ε S k (i+1) z' D' wire hist} (ticket : OrdinaryLink prior he T c n target)

def outputEnd (old : Bank) (v : Layout) (floor ℓ b short payload unit profile seats : ℕ) :=
  v.endAddress (ticket.endAddress old floor ℓ b short payload unit profile seats)

theorem output_coordinates (old : Bank) (v : Layout) (floor ℓ b short payload unit profile seats : ℕ) :
    let a:=ticket.ordinaryArea ℓ b payload unit profile seats
    floor≤ticket.outputEnd old v floor ℓ b short payload unit profile seats ∧
      ticket.outputEnd old v floor ℓ b short payload unit profile seats≤floor+a.ordinaryWords old v ∧
      ticket.outputEnd old v floor ℓ b short payload unit profile seats=
        floor+ticket.outputEnd old v 0 ℓ b short payload unit profile seats := by
  intro a
  have real:=ticket.concrete_extent old floor ℓ b short payload unit profile seats
  have above:=ticket.floor_le_end old floor ℓ b short payload unit profile seats
  have shift:=ticket.end_relocate old floor ℓ b short payload unit profile seats
  unfold outputEnd
  rw [DescentOperandVectorArena.affine v (ticket.endAddress old floor ..),
    DescentOperandVectorArena.affine v (ticket.endAddress old 0 ..)]
  change _ ∧ _≤floor+(a.rotationEnd old 0+a.donorWords+v.endAddress 0) ∧ _
  dsimp only [a]
  omega

end DescentSixParty.Chronology.OrdinaryLink
end
end Hierarchy

end OAI
