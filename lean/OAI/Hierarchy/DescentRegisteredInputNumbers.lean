import OAI.Hierarchy.DescentSignedReturnPopulation

namespace OAI
/-! # Physical cost of the old operand/role repack and the host extension -/
namespace Hierarchy.DescentDatedAddressBook.MaterialProgram

def retileCharge (ratio rows oldH newH G h U : ℕ) :=
  4096*ratio*(rows+1)*(h+3*oldH*h+oldH*G*(2*U+U))+
  4096*ratio*halfPages h+512*ratio*(rows+1)*(h+newH*h+newH*G*U)

def retileFactor (rows U : ℕ) :=4096*(rows+1)*(7+6*U)+4096+512*(rows+1)*(3+2*U)

theorem retile_charge {A oldH newH h G u rows ratio : ℕ} (live : 0<A)
    (old : oldH≤2*A) (next : newH≤2*A) :
    retileCharge ratio rows oldH newH G h u≤ratio*retileFactor rows u*purchased A G h :=by
  let R:=purchased A G h
  have shop : A*h≤R:=(Nat.le_add_right (A*h) (A*G)).trans (Nat.le_add_right ..)
  have grains : A*G≤R:=(Nat.le_add_left (A*G) (A*h)).trans (Nat.le_add_right ..)
  have t : h≤R:=(Nat.le_mul_of_pos_left h live).trans shop
  have ticks {z : ℕ} (paid : z≤2*A) (x : ℕ) (room : A*x≤R) : z*x≤2*R:=
    (Nat.mul_le_mul_right x paid).trans ((Nat.mul_assoc 2 A x).le.trans (Nat.mul_le_mul_left 2 room))
  have a : h+3*oldH*h+oldH*G*(2*u+u)≤(7+6*u)*R:=by
    calc
      _ = h+3*(oldH*h)+(oldH*G)*(2*u+u):=by ring
      _ ≤ R+3*(2*R)+(2*R)*(2*u+u) :=
        Nat.add_le_add (Nat.add_le_add t (Nat.mul_le_mul_left 3 (ticks old h shop)))
          (Nat.mul_le_mul_right (2*u+u) (ticks old G grains))
      _ = _:=by ring
  have b : h+newH*h+newH*G*u≤(3+2*u)*R:=by
    calc
      _ ≤ R+2*R+(2*R)*u :=
        Nat.add_le_add (Nat.add_le_add t (ticks next h shop))
          (Nat.mul_le_mul_right u (ticks next G grains))
      _ = _:=by ring
  have shared : halfPages h≤R:=Nat.le_add_left ..
  calc
    _ ≤ 4096*ratio*(rows+1)*((7+6*u)*R)+4096*ratio*R+512*ratio*(rows+1)*((3+2*u)*R):=
      Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul_left _ a) (Nat.mul_le_mul_left _ shared)) (Nat.mul_le_mul_left _ b)
    _ = _:=by unfold retileFactor;ring

theorem retile_factor_le {r u z : ℕ} (rows : r≤z) (digit : u≤z) :
    retileFactor r u≤100000*(z+1)^2:=by
  unfold retileFactor
  calc
    _ ≤ 4096*(z+1)*(7+6*z)+4096+512*(z+1)*(3+2*z):=by gcongr
    _ ≤ _:=by nlinarith only [Nat.zero_le z,Nat.zero_le (z*z)]

end Hierarchy.DescentDatedAddressBook.MaterialProgram

end OAI
