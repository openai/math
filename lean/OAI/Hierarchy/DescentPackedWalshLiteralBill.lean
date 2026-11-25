import OAI.Hierarchy.DescentPackedWalshStatePrice
import OAI.Hierarchy.DescentWalshPrecision

namespace OAI
/-! # The actual populated bit-cost of the packed estimator's fixed literal prefix -/
namespace Hierarchy.DescentPackedWalsh.EstimatorArena
open DescentPackedWalsh DescentPackedWalshReduction DescentSIMDLookup DescentWalshPrecision
noncomputable section
variable (E : EstimatorArena)
local notation "k" => E.dim
local notation "H" => E.hosts
local notation "h" => E.payload
local notation "b" => E.precision

def staticBill (W K : ℕ) :=
  let slab:=H*h+16*H*2^k*b
  let rom:=2^(h/2)*W
  (2*K*(slab+h)+2*rom) +
    (4*W+2008*(H+1)*W+25600*K*(H+1)*2^k*(b+1)+12800*K*2^k*(W+1)^2+2*E.plan.depth*rom) +
    (2*2^k*W+rom) +
    K*(6*k*(slab+h)+(2*k+1)*2^(h/2)*h)

/-- The static prefix contains no blank dynamic pages. Its three site-origin/gain tables,
all levels of dyadic headers, the final inverse permutation and both transforms are all charged. -/
theorem static_bill (W K : ℕ) (width : W≤K*h) (hosts : H≤2^W) (digits : b≤W+1)
    (lanes : laneBits k h b=E.low) (small : 8*b≤h/2) (gain : E.gainBits≤b) :
    (E.staticEnd-E.origin)*W≤E.staticBill W K := by
  have full : 8*b≤h:=small.trans (Nat.div_le_self ..)
  have split : k-E.low=E.high:=by unfold dim;omega
  have threshold := packed_key (m:=k) E.positive small gain
  rw [lanes] at threshold
  have lut : 2^(E.gainBits+b*2^E.low)≤ 2^(h/2):=Nat.pow_le_pow_right (by decide) threshold
  have gainLut : 2^E.gainBits ≤ 2^(h/2) := Nat.pow_le_pow_right (by decide) ((Nat.le_add_right ..).trans threshold)
  have pages:=Nat.mul_le_mul_right W (page_le H E.high)
  have short:=per_layer (m:=k) H E.positive full
  dsimp only at short
  rw [lanes,split] at short
  have slab : H*2^E.high*W≤K*(H*h+16*H*2^k*b) := by
    calc
      _ ≤ H*2^E.high*(K*h) := Nat.mul_le_mul_left _ width
      _ = K*(H*2^E.high*h) := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ short
  have weight : Weight.footprint H E.high E.low b E.gainBits*W ≤
      2*K*((H*h+16*H*2^k*b)+h)+2*(2^(h/2)*W) := by
    unfold Weight.footprint
    nlinarith only [pages,slab,width,Nat.mul_le_mul_right W lut,Nat.mul_le_mul_right W gainLut]
  have reduceBill:=E.plan.header_bill E.reduceAt W K width hosts digits
  have ext : Column.size k (b+E.plan.depth) (E.plan.laneBits E.plan.depth)*W ≤ 2*2^k*W+2^(h/2)*W := by
    unfold Column.size
    split
    · simp
    · rename_i neq
      have cap := E.plan.extract_key_room E.plan.depth (Nat.pos_of_ne_zero neq)
      have e : E.plan.laneBits E.plan.depth+(b+E.plan.depth)*2^(E.plan.laneBits E.plan.depth)≤h/2 := by
        simpa only [Plan.lanes,Nat.add_comm,show E.plan.height = E.payload from rfl,
          show E.plan.bits = E.precision from rfl] using cap
      rw [Nat.add_mul]
      exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide) e)) _
  have transforms:=header_price H k E.positive full width
  dsimp only at transforms
  rw [lanes,split] at transforms
  have monotone := E.areas.2.1
  have size : E.staticEnd-E.origin=Weight.footprint H E.high E.low b E.gainBits+
      (E.plan.headerAt E.reduceAt E.plan.depth-E.reduceAt)+Column.size k (b+E.plan.depth) (E.plan.laneBits E.plan.depth)+
        (k*span H E.high E.low b+2^(smallKey E.low b)) := by
    have start : E.reduceAt = E.origin + Weight.footprint H E.high E.low b E.gainBits := rfl
    change E.orderAt + Column.size k (b+E.plan.depth) (E.plan.laneBits E.plan.depth) +
        k*span H E.high E.low b + 2^(smallKey E.low b) - E.origin =
      Weight.footprint H E.high E.low b E.gainBits + (E.orderAt-E.reduceAt) +
        Column.size k (b+E.plan.depth) (E.plan.laneBits E.plan.depth) +
        (k*span H E.high E.low b + 2^(smallKey E.low b))
    have telescope (base weight middle column transform table : ℕ) (order : base+weight ≤ middle) :
        middle + column + transform + table - base =
          weight + (middle - (base+weight)) + column + (transform+table) := by omega
    rw [start]
    apply telescope
    rw [←start]
    exact monotone
  rw [size,Nat.add_mul,Nat.add_mul,Nat.add_mul]
  unfold staticBill
  exact Nat.add_le_add (Nat.add_le_add (Nat.add_le_add weight (by
    simpa only [Nat.mul_assoc,show E.plan.height = E.payload from rfl,
      show E.plan.axis = E.dim from rfl,show E.plan.bits = E.precision from rfl,
      show E.plan.sites = E.hosts from rfl] using reduceBill)) ext) transforms

end
end Hierarchy.DescentPackedWalsh.EstimatorArena

end OAI
