import OAI.Hierarchy.DescentSignedReturnPopulation
import OAI.Hierarchy.DescentDateBillVolume

namespace OAI
/-! # Charging each successor rectangle to its original host and group counts -/
namespace Hierarchy.DescentDatedAddressBook.MaterialProgram
open DescentPacking.PackedMatch.Local.Stage.DateBill
private theorem components {A G H N h g : ℕ} (live : 0<A) (hosts : H≤A*g) (groups : N≤G) :
    let P:=purchased A G h
    h≤P ∧ H*h≤g*P ∧ H*N≤g*P ∧ 2^(h/2)*h≤P ∧ halfPages h≤P :=by
  intro P
  have x : A*h≤P:=by change A*h≤A*h+A*G+halfPages h;omega
  have y : A*G≤P:=by change A*G≤A*h+A*G+halfPages h;omega
  have z : halfPages h≤P:=Nat.le_add_left ..
  have one : 0<2*(h+1)^2:=by positivity
  refine ⟨(Nat.le_mul_of_pos_left h live).trans x,?_,?_,?_,z⟩
  · exact (Nat.mul_le_mul_right h hosts).trans (by simpa only [Nat.mul_left_comm,Nat.mul_assoc,Nat.mul_comm] using Nat.mul_le_mul_left g x)
  · exact (Nat.mul_le_mul hosts groups).trans (by simpa only [Nat.mul_left_comm,Nat.mul_assoc,Nat.mul_comm] using Nat.mul_le_mul_left g y)
  · exact (Nat.mul_le_mul_right h (Nat.le_mul_of_pos_left (2^(h/2)) one)).trans z

def rectangleFactor (g u : ℕ) :=1+2*g+2*g*u
def volumeFactor (g u : ℕ) :=2+g+4*g*u

theorem rectangle_paid {A G H N h g : ℕ} (live : 0<A) (hosts : H≤A*g) (groups : N≤G) (u : ℕ) :
    h+2*H*h+2*H*N*u≤rectangleFactor g u*purchased A G h :=by
  obtain ⟨x,y,z,_,_⟩:=components (h:=h) live hosts groups
  calc
    _ = h+2*(H*h)+2*(H*N)*u :=by ring
    _ ≤ purchased A G h+2*(g*purchased A G h)+2*(g*purchased A G h)*u:=by gcongr
    _ = _ :=by unfold rectangleFactor;ring

theorem return_volume_paid {A G H N h g : ℕ} (live : 0<A) (hosts : H≤A*g) (groups : N≤G) (u : ℕ) :
    volumeBits H N h u≤volumeFactor g u*purchased A G h :=by
  obtain ⟨x,y,z,t,_⟩:=components (h:=h) live hosts groups
  calc
    _ = h+H*h+4*(H*N)*u+2^(h/2)*h:=by unfold volumeBits;ring
    _ ≤ purchased A G h+g*purchased A G h+4*(g*purchased A G h)*u+purchased A G h:=by gcongr
    _ = _ :=by unfold volumeFactor;ring

def tailFactor (growth u r D cap nodes arity : ℕ) :=
  let venue:=4096*(r*(2*cap)+1+2*(r+1))+1024*(r+D+1)
  let shared:=3*2048+115*r
  let shelves:=400000*(1+(r+nodes+arity+7))^4
  venue*rectangleFactor growth u+shared+2*shelves*volumeFactor growth u+
    4000*(1+2*r)*volumeFactor 2 u

/-- All age-dependent coefficients are polynomial in the public dimensions; the fourth power
accounts for the compiled metadata and seven emitted operand fields. -/
theorem tailFactor_le {Q growth u r D cap nodes arity : ℕ} (hg : growth≤Q) (hu : u≤Q) (hr : r≤Q)
    (hD : D≤Q) (hc : cap≤Q) (hn : nodes≤Q) (ha : arity≤Q) :
    tailFactor growth u r D cap nodes arity ≤ 1000000000000*(Q+1)^6 :=by
  calc
    _ ≤ tailFactor Q Q Q Q Q Q Q:=by
      dsimp only [tailFactor,rectangleFactor,volumeFactor]
      gcongr
    _ ≤ _ :=by
      dsimp only [tailFactor,rectangleFactor,volumeFactor]
      ring_nf
      omega

end Hierarchy.DescentDatedAddressBook.MaterialProgram

end OAI
