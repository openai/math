import OAI.Hierarchy.DescentOriginalPeerRegions
import OAI.Hierarchy.DescentResetSelectedPrimitivePrice

namespace OAI
/-! # All ten primitive-scan dimensions on the original public reset calendar -/
namespace Hierarchy.DescentDatedAddressBook.ResetOutput
open DescentCompiler DescentCompiler.TerminalScale DescentSixParty Filter
noncomputable section
variable {F : Type} [Field F] {n d : ℕ} (G : PoweredGadget F) (board : NonlinearExpanders.Graph n d)
variable (op : RotorSpec) (t f g reset D : ℕ)
local notation "η" => hostRate t reset
local notation "κ" => 1+(η+capRate G t g)*(t+1)+8+cutRate t f g
local notation "Ht" => GroupStage.depthBound D n f g
local notation "shapePrice" => 2*(2*((2^n+1)+((2*d+4)*2^n+(2^n+1)*2^(Ht+1))))
local notation "rate" => localExponent G board op t f g reset D

def primitiveLocalExponent := rate+κ+(shapePrice+2*2^n+2^η+101)

private theorem constant_times_blocks (J blocks factor coefficient c : ℕ)
    (wk : blocks≤c*(J+1)) (small : factor≤coefficient) :
    factor*2^blocks≤ scale J (c+coefficient):=by
  calc
    factor*2^blocks≤2^coefficient*2^(c*(J+1)):= Nat.mul_le_mul
      (small.trans (Nat.lt_two_pow_self (n:=coefficient)).le) (Nat.pow_le_pow_right (by decide) wk)
    _≤ scale J (c+coefficient):=by
      rw [←pow_add]
      apply Nat.pow_le_pow_right (by decide)
      rw [Nat.add_mul]
      exact (Nat.add_le_add_right (Nat.le_mul_of_pos_right coefficient (by omega : 0<J+1)) _).trans_eq (Nat.add_comm ..)

local notation "exp₀" => primitiveLocalExponent G board op t f g reset D

theorem original_primitive_limits (τ drift B : ℕ) (positive : 0<B) (branch : G.b≤2^(capRate G t g)) (bound : ℕ) :
    ∀ᶠ h : ℕ in atTop,let J:=Nat.log 2 h/(2*B);
    ∀sites age p degree e previous lanes nextM base old,p≤h→degree≤bound→
      let z:=originalSample G op t f g reset τ D drift J sites age p degree h e previous lanes nextM base old
      PrimitiveLimits (z.output G board D f g op.C op.w) (scale J exp₀) (2^z.sched.hostGain*z.sched.radix) 100:=by
  filter_upwards [original_fields G board op t f g reset τ D drift B positive branch bound] with h paid
  let J:=Nat.log 2 h/(2*B)
  let k:=groupBits t J η (capRate G t g) (cutRate t f g)
  let a:=shapePrice+2*2^n+2^η+101
  have wk:k≤κ*(J+1):=groupBits_linear ..
  have weaken {u v : ℕ} (uBound : u≤ scale J v) (fits : v≤exp₀) : u≤ scale J exp₀:=
    uBound.trans (Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ fits))
  have product (factor : ℕ) (ok : factor≤a) : factor*2^k≤ scale J exp₀:=
    weaken (constant_times_blocks J k factor a κ wk ok) (Nat.add_le_add_right (Nat.le_add_left κ rate) a)
  have blocks:2^k≤ scale J exp₀:=by simpa using product 1 ((by decide : 1≤101).trans (Nat.le_add_left ..))
  have nodes {u : ℕ} (ok:u≤ scale J rate) : u≤ scale J exp₀:=weaken ok ((Nat.le_add_right rate κ).trans (Nat.le_add_right _ a))
  dsimp only
  intro sites age p degree e previous lanes nextM base old hp hd
  have dims:=paid sites age p degree e previous lanes nextM base old hp hd
  refine ⟨nodes dims.nodes,nodes dims.arguments,?_,Nat.lt_two_pow_self.le.trans blocks,?_,blocks,
    nodes dims.nodes,blocks,product (2^η) (by dsimp only [a]; omega),?_⟩
  · change 2*(2^k*2^n)≤ scale J exp₀
    simpa [Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm] using product (2*2^n) (((Nat.le_add_left ..).trans (Nat.le_add_right _ _)).trans (Nat.le_add_right _ _))
  · change (DescentDenseHostOrder.roster board k Ht).card≤ scale J exp₀
    apply (DescentDenseHostOrder.roster_bound board k Ht).trans
    simpa only [pow_succ,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using product shapePrice (((Nat.le_add_right _ _).trans (Nat.le_add_right _ _)).trans (Nat.le_add_right _ _))
  · exact (Nat.le_mul_of_pos_right 100 (Nat.two_pow_pos k)).trans (product 100 ((by decide : 100≤101).trans (Nat.le_add_left ..)))

end
end Hierarchy.DescentDatedAddressBook.ResetOutput

end OAI
