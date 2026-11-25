import OAI.Hierarchy.DescentReservationHeader
import OAI.Hierarchy.DescentDatedImage

namespace OAI
/-! # A single fixed installation of the attained-depth ceiling table -/
namespace Hierarchy.DescentReservationHeader
open DescentPlainTerminal.Suffix.Cutoff DescentPackedColony.Phase ProtocolRAM
open ThreeFlat.RAM PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
variable {w : ℕ}

def literal (base levels total K scale Y : ℕ) : Arena.Image w :=
  ⟨base,finish base levels total,DescentReservationHeader.header base levels total K scale Y (fun _=>0)⟩

theorem installed (base levels total K scale Y : ℕ) (mem : Memory w)
    (legal : finish base levels total<2^w) :
    let I:=literal (w:=w) base levels total K scale Y
    let dst:=header base levels total K scale Y mem
    let rows:=2^levels+2^(levels+total)
    I.program.Exec mem dst (4+10*rows) ∧ Resident base levels total K scale Y dst ∧
      (∀a,a<base ∨ finish base levels total≤a→dst a=mem a) ∧ CheapCode I.program ∧
      DescentStaticWordColumn.names I.program=15*(rows+1) := by
  let I:=literal (w:=w) base levels total K scale Y
  have length : I.length=2^levels+2^(levels+total):=by
    change (base+2^levels+2^(levels+total))-base=_
    rw [Nat.add_assoc,Nat.add_sub_cancel_left]
  have space : I.low+I.length<2^w:=by
    rw [length]
    simpa [I,literal,finish,Nat.add_assoc] using legal
  obtain ⟨execute,table,saved⟩:=I.issue mem space
  have eqn:I.output mem=header base levels total K scale Y mem:=by
    funext a
    by_cases lo:a<base
    · exact (saved a (.inl lo)).trans (frame _ _ _ _ _ _ _ _ (.inl lo)).symm
    by_cases hi:a<finish base levels total
    · rw [table a (Nat.le_of_not_gt lo) hi]
      by_cases which:a-base<2^levels
      · simp only [I,literal,DescentReservationHeader.header,ite_eq_right lo,ite_eq_left which]
      · have startLe : base+2^levels ≤ a := calc
          base+2^levels ≤ base+(a-base) := Nat.add_le_add_left (Nat.le_of_not_gt which) _
          _ = a := Nat.add_sub_of_le (Nat.le_of_not_gt lo)
        have inside : a-(base+2^levels)<2^(levels+total) := Nat.sub_lt_left_of_lt_add startLe hi
        simp only [I,literal,DescentReservationHeader.header,ite_eq_right lo,ite_eq_right which,ite_eq_left inside]
    · exact (saved a (.inr (Nat.le_of_not_gt hi))).trans
        (frame _ _ _ _ _ _ _ _ (.inr (Nat.le_of_not_gt hi))).symm
  rw [eqn,length] at execute
  have price:=I.hardware
  rw [length] at price
  exact ⟨execute,mounted ..,frame _ _ _ _ _ _ mem,price⟩

end
end Hierarchy.DescentReservationHeader

end OAI
