import OAI.Hierarchy.DescentSignedReturnPopulation

namespace OAI
/-! # Charging the shared physical input lookup pages to the original hosts -/
namespace Hierarchy.DescentDatedAddressBook.MaterialProgram

private theorem square_linear_exp (m : ℕ) : (m+1)^2≤4*2^m := by
  induction m with
  | zero=>decide
  | succ m ih=>
    by_cases small : m<2
    · interval_cases m <;> decide
    · have large : 2≤ m := by omega
      have square:=Nat.mul_le_mul large large
      calc (m+1+1)^2≤2*((m+1)^2) := by nlinarith
           _ ≤ 4*2^(m+1) := by rw [pow_succ 2 m];nlinarith only [ih]

theorem halfPages_hosts (h M H : ℕ) (stock : 2^h≤2*M) (hosts : M≤H) : halfPages h≤64*(H*h) := by
  let m:=h/2
  have height : h+1≤2*(m+1) := by dsimp [m];omega
  have small:=Nat.pow_le_pow_left height 2
  have quad : (h+1)^2 ≤ 16*2^m := by nlinarith only [small,square_linear_exp m]
  have bins : 2^m*2^m≤2^h := by rw [←pow_add];exact Nat.pow_le_pow_right (by decide) (by dsimp [m];omega)
  calc halfPages h=2*(h+1)^2*2^m*h := rfl
       _ ≤ 2*(16*2^m)*2^m*h := by gcongr
       _ = 32*(2^m*2^m)*h := by ring
       _ ≤ 32*(2*H)*h := Nat.mul_le_mul_right h (Nat.mul_le_mul_left 32 (bins.trans (stock.trans (Nat.mul_le_mul_left 2 hosts))))
       _ = 64*(H*h) := by ring

theorem input_purchased_price (h M H N K A : ℕ) (stock : 2^h≤2*M) (hosts : M≤H) (blocks : 0<K) :
    A*purchased H N h ≤ H*h*(65*A)+H*(N*K)*(65*A) := by
  have pages:=halfPages_hosts h M H stock hosts
  have row : N≤N*K:=Nat.le_mul_of_pos_right N blocks
  have bill : purchased H N h ≤ 65*(H*h+H*(N*K)) := by
    unfold purchased
    have slots:=Nat.mul_le_mul_left H row
    omega
  exact (Nat.mul_le_mul_left A bill).trans_eq (by ring)

end Hierarchy.DescentDatedAddressBook.MaterialProgram

end OAI
