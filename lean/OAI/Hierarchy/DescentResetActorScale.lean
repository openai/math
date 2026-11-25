import OAI.Hierarchy.DescentResetActorInvoice
import OAI.Hierarchy.DescentResetActorCalendar

namespace OAI
/-! Only the local actor-arity polynomial and the numerical program roster multiply
the per-host bill. -/
namespace Hierarchy.DescentDatedAddressBook.ActorSetup
open DescentCompiler.TerminalScale DescentResetNewActorDirectory
noncomputable section

def shapeCoeff (Y d T : ℕ) := 2*(2*((Y+1)+((2*d+4)*Y+(Y+1)*2^(T+1))))
def arityCoeff (Y D : ℕ) := (D+1)*(Y+1)^2
def actorLead (Y d D T : ℕ) :=
  let ar:=arityCoeff Y D
  let q:=shapeCoeff Y d T
  4096*(1+1+D*2^T+(ar+1)*(scoreBound D (2^T)+1))+
    2*(8192+7*Layout.fixedScatter)*(q+1)+65536*(q+1)+1024*(q+2)

theorem factor_scale {n d : ℕ} (board : NonlinearExpanders.Graph n d) (v : ActorSetup)
    (D T k j rate : ℕ) (shapes : v.shapes=(DescentDenseHostOrder.roster board k T).card)
    (arity : v.arity=DescentSharedBookScan.width k (2^n) D) (counts : v.maxCount=D*2^T)
    (bits : v.oldWidth≤ scale j rate) (blocks : 2^k≤ scale j rate) :
    v.actorFactor D (2^T)≤actorLead (2^n) d D T*scale j (4*rate) := by
  let x:=scale j rate
  let z:=x^4
  let Y:=2^n
  let ar:=arityCoeff Y D
  let q:=shapeCoeff Y d T
  let score:=scoreBound D (2^T)
  have pos : 0<x := Nat.two_pow_pos _
  have zpos : 0<z := pow_pos pos _
  have xz : x≤z := by simpa only [pow_one] using (Nat.pow_le_pow_right pos (by decide : 1≤4) : x^1≤x^4)
  have kz : k+1≤x := (Nat.lt_two_pow_self (n:=k)).trans_le blocks
  have rawRows : DescentFallbackShapeTable.rows k Y ≤ x*x*(Y+1) :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul kz blocks)
  have number : v.arity ≤ ar*z := by
    rw [arity]
    change DescentFallbackShapeTable.rows k Y*((D+1)*DescentFallbackShapeTable.rows k Y)≤_
    calc
      _≤(x*x*(Y+1))*((D+1)*(x*x*(Y+1))) := Nat.mul_le_mul rawRows (Nat.mul_le_mul_left _ rawRows)
      _=ar*z := by dsimp [ar,arityCoeff,z]; ring
  have jobs : v.shapes≤q*z := by
    rw [shapes]
    have r:=DescentDenseHostOrder.roster_bound board k T
    rw [show 2^(k+1)=2^k*2 by rw [pow_succ]] at r
    calc
      _ ≤ (2*((Y+1)+((2*d+4)*Y+(Y+1)*2^(T+1))))*(2^k*2) := r
      _ = q*2^k := by unfold q shapeCoeff; ring
      _ ≤ q*z := Nat.mul_le_mul_left _ (blocks.trans xz)
  have all (a : ℕ) : a≤a*z := Nat.le_mul_of_pos_right a zpos
  have low : v.oldWidth ≤ z := bits.trans xz
  have mul : x^4=scale j (4*rate) := by
    change (2^(rate*(j+1)))^4=2^((4*rate)*(j+1))
    rw [←pow_mul];congr 1;ring
  rw [←mul]
  change _ ≤ actorLead Y d D T*z
  calc
    _ ≤ 4096*(z+z+(D*2^T)*z+(ar*z+z)*(score+1))+
        2*((8192+7*Layout.fixedScatter)*(q*z+z))+65536*(q*z+z)+1024*(q*z+2*z) := by
      unfold actorFactor headerFactor directoryFactor
      rw [counts]
      have head := Nat.add_le_add (Nat.add_le_add (Nat.add_le_add zpos low) (all (D*2^T)))
        (Nat.mul_le_mul_right (score+1) (Nat.add_le_add number zpos))
      have sh := Nat.add_le_add jobs zpos
      have sh₂ := Nat.add_le_add jobs (Nat.mul_le_mul_left 2 zpos)
      exact Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul_left 4096 head)
        (Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left (8192+7*Layout.fixedScatter) sh)))
        (Nat.mul_le_mul_left 65536 sh)) (Nat.mul_le_mul_left 1024 sh₂)
    _ = _ := by dsimp only [actorLead,score,ar,q]; ring

end
end Hierarchy.DescentDatedAddressBook.ActorSetup

end OAI
