import OAI.Hierarchy.DescentSIMDLookup

namespace OAI
/-! # Rounded row volume for an arbitrary occupied group pitch -/
namespace Hierarchy.DescentDatedSeedStartup
open DescentSIMDLookup

/-- The width of an executed word can exceed the lookup-table payload.
The first incomplete chunk pays one machine word per genuine old host. -/
theorem chunk_work (H G M word short : ℕ) (fill : word≤M*short) :
    (H*chunks G M)*word ≤ H*word+H*G*short := by
  have bound:=Nat.div_mul_le_self (G+M-1) M
  change chunks G M*M≤G+M-1 at bound
  cases eqn:chunks G M with
  | zero=>simp
  | succ j=>
    have real : j*M≤G := by rw [eqn,Nat.succ_mul] at bound;omega
    have paid : j*word≤G*short := calc
      j*word≤j*(M*short) := Nat.mul_le_mul_left _ fill
      _=(j*M)*short := (Nat.mul_assoc ..).symm
      _≤G*short := Nat.mul_le_mul_right _ real
    have all:=Nat.mul_le_mul_left H paid
    simpa only [Nat.mul_succ,Nat.add_mul,Nat.mul_assoc,Nat.add_comm] using
      Nat.add_le_add_left all (H*word)


end Hierarchy.DescentDatedSeedStartup

end OAI
