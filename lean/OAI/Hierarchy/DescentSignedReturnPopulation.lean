import OAI.Hierarchy.DescentMaterialPopulation

namespace OAI
/-! # One public count of old host rows, their group slots, and the shared literal pages -/
namespace Hierarchy.DescentDatedAddressBook.MaterialProgram
open DescentOrdinaryMarkProject

def halfPages (h : ℕ) := (2*(h+1)^2*2^(h/2))*h
def purchased (H G h : ℕ) := H*h+H*G+halfPages h

theorem shared_paid (H G h : ℕ) : Shape.shared h*h≤2*purchased H G h := by
  have side : h+2 ≤ 2*(h+1) := by omega
  have a : (h+2)^2 ≤ 2*(2*(h+1)^2) := calc
    (h+2)^2 ≤ (2*(h+1))^2 := Nat.pow_le_pow_left side 2
    _ = 2*(2*(h+1)^2) := by ring
  have page:=Nat.mul_le_mul_right h (Nat.mul_le_mul_right (2^(h/2)) a)
  have cap:halfPages h≤purchased H G h:=Nat.le_add_left ..
  exact page.trans (by simpa only [Shape.shared,halfPages,Nat.mul_assoc] using Nat.mul_le_mul_left 2 cap)

def returnFactor (growth a b : ℕ) := 2+2*(2+growth)+4*(2+growth)*2*(a+b)

theorem population_paid {A G H K G' growth h a b : ℕ}
    (positive : 0<A) (old : H≤2*A) (next : K≤A*growth) (groups : G'≤G) :
    population H K G G' h a b≤returnFactor growth a b*purchased A G h := by
  let R:=purchased A G h
  have host : H+K≤(2+growth)*A :=(Nat.add_le_add old next).trans_eq (by ring)
  have g : G+G'≤2*G:=by omega
  have row:A*h≤R:=(Nat.le_add_right (A*h) (A*G)).trans (Nat.le_add_right ..)
  have slot:A*G≤R:=(Nat.le_add_left (A*G) (A*h)).trans (Nat.le_add_right ..)
  have page:halfPages h≤R:=Nat.le_add_left ..
  have h₁ : h≤R:=(Nat.le_mul_of_pos_left _ positive).trans row
  have h₂ : 2^(h/2)*h≤R:=(Nat.mul_le_mul_right h (Nat.le_mul_of_pos_left (2^(h/2))
    (by positivity : 0<2*(h+1)^2))).trans page
  have rent : (H+K)*h≤(2+growth)*R:=(Nat.mul_le_mul_right h host).trans
    (by simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left (2+growth) row)
  have block : 4*(H+K)*(G+G')*(a+b)≤(4*(2+growth)*2*(a+b))*R:=calc
    _≤4*((2+growth)*A)*(2*G)*(a+b):=Nat.mul_le_mul_right _ (Nat.mul_le_mul (Nat.mul_le_mul_left 4 host) g)
    _=(4*(2+growth)*2*(a+b))*(A*G):=by ring
    _≤_:=Nat.mul_le_mul_left _ slot
  unfold population returnFactor
  calc
    _ = h+2^(h/2)*h+2*((H+K)*h)+4*(H+K)*(G+G')*(a+b):=by ring
    _ ≤ R+R+2*((2+growth)*R)+(4*(2+growth)*2*(a+b))*R :=
      Nat.add_le_add (Nat.add_le_add (Nat.add_le_add h₁ h₂) (Nat.mul_le_mul_left 2 rent)) block
    _ = _ :=by dsimp only [R];ring


end Hierarchy.DescentDatedAddressBook.MaterialProgram

end OAI
