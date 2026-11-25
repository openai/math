import OAI.Hierarchy.DescentMatchLaneNumbers
import OAI.Hierarchy.DescentPackedMatchChunk

namespace OAI
/-! # One shared profile window indexed by the topology and two dense advice words -/

namespace Hierarchy.DescentPacking.PackedMatch.ProfileTable
open DescentSIMDLookup DescentPackedProfileWindow
noncomputable section

def pair (a b : ℕ) : Cell a × Cell b ≃ Cell (a+b) :=
  finProdFinEquiv.trans (finCongr (pow_add 2 a b).symm)

@[simp] theorem pair_val {a b : ℕ} (x : Cell a) (y : Cell b) : (pair a b (x,y)).val=y.val+2^b*x.val := rfl

def bits (a b : ℕ) := a+(b+(b+b))
def key {a b : ℕ} (src : Cell a) (offset low high : Cell b) : Cell (bits a b) :=
  pair a (b+(b+b)) (src,pair b (b+b) (offset,pair b b (low,high)))

theorem key_val {a b : ℕ} (src : Cell a) (offset low high : Cell b) :
    (key src offset low high).val=2^(b+(b+b))*src.val+(2^(b+b)*offset.val+(2^b*low.val+high.val)) := by
  simp only [key,pair_val]
  omega

def table (s : Shape) (M R : ℕ) (z : Cell (bits (s.outputBits*M) (s.digit*R))) : Cell (s.digit*(M*s.pairs)) :=
  let b:=s.digit*R
  let u:=(pair (s.outputBits*M) (b+(b+b))).symm z
  let v:=(pair b (b+b)).symm u.2
  let both:=(pair b b).symm v.2
  if admissible : v.1.val<R then
    localProfile s.digit s.pairs M R (laneCounts s M u.1) ⟨_,admissible⟩ both.1 both.2
  else 0

theorem decode (s : Shape) (M R : ℕ) (src : Cell (s.outputBits*M)) (offset low high : Cell (s.digit*R))
    (small : offset.val<R) :
    table s M R (key src offset low high)=localProfile s.digit s.pairs M R (laneCounts s M src) ⟨_,small⟩ low high := by
  simp only [table,key,Equiv.symm_apply_apply,dite_eq_left small]


theorem width_eq (s : Shape) (M : ℕ) :
    bits (s.outputBits*M) (s.digit*(M*s.pairs))≤M*envelope s := by
  have output := Nat.mul_le_mul_right M (le_max_right s.inputBits s.outputBits)
  change s.outputBits*M≤ s.bits*M at output
  unfold bits envelope
  nlinarith only [output]

theorem key_budget (s : Shape) (payload : ℕ) :
    let M:=lanes payload (envelope s)
    bits (s.outputBits*M) (s.digit*(M*s.pairs))≤payload/2 :=
  (width_eq s _).trans (lanes_fit ..)

end
end Hierarchy.DescentPacking.PackedMatch.ProfileTable

end OAI
