import OAI.Hierarchy.DescentDatedSignedFields
import OAI.Hierarchy.DescentDatedResetArea

namespace OAI
/-! # The fresh paid reset pass on the actual previous signed-port words -/
namespace Hierarchy.DescentGLPacked.BankImage.SignedFields
open DescentGLPacked DescentGLNielsen DescentGLControlCode ProtocolRAM
noncomputable section

/-- The first rounded control shelf also accommodates the separate offsets and switches
used by SignedFields.issue, without any overlap with its grouped old-token input. -/
abbrev chart (origin D H h l b : ℕ) := Dated.chart origin (D*H) h l b
def stop (origin D H h l b : ℕ) := Dated.endAddress origin (D*H) h l b

theorem after_data (origin D H h l b : ℕ) :
    endAddress (chart origin D H h l b) (h+l)≤ stop origin D H h l b := by
  let C:=chart origin D H h l b
  change C.heap (h+l)+(schedule (h+l)).length*C.page≤C.heap (h+l)+((schedule (h+l)).length+1)*C.page
  exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (Nat.le_succ _)) _

theorem allocation (origin D H h l b w : ℕ) (room : stop origin D H h l b<2^w) :
    let C:=chart origin D H h l b
    let cols:=controlBanks origin (h+l)
    Size C (D*H) h l b w ∧ controlEnd origin (h+l)≤C.input.base ∧
    cols.offsets.Fits w C.input.base ∧ cols.switches.Fits w C.input.base ∧
    C.input.base+C.input.size≤C.flags := by
  intro C cols
  have real:=Dated.sized origin (D*H) h l b w room
  let d:=h+l
  have key : Dated.keys d=2^(d*d) := by simp [Dated.keys,Nat.pow_mul]
  have upper : C.input.base<2^w := by
    change origin+4*(Dated.controlSize h l+1)<2^w
    have cap:=room
    unfold stop at cap
    rw [Dated.extent] at cap
    exact lt_of_le_of_lt (((Nat.le_add_right _ _).trans (Nat.le_add_right _ _)).trans
      (Nat.le_add_right _ _)) cap
  have fit (B : Bank) (safe : B.base+B.size≤C.input.base) : B.Fits w C.input.base :=
    ⟨Nat.two_pow_pos _,by omega,safe⟩
  have first:=Dated.rounded (Count d)
  have second:=Dated.rounded (Count d*2^(d*d))
  have post : C.input.base=origin+4*(Dated.keys d+Count d+Count d*Dated.keys d+d*2^h+1) :=rfl
  rw [key] at post
  refine ⟨real.1,?_,fit _ ?_,fit _ ?_,real.2.2.1⟩
  · change origin+Count d+Count d*2^(d*d)≤_
    omega
  · change origin+2^(Nat.clog 2 (Count d))≤_
    omega
  · change origin+Count d+2^(Nat.clog 2 (Count d*2^(d*d)))≤_
    omega

theorem span_price (origin D H h l b payload : ℕ)
    (word : (b+b)*2^l≤payload/2) (square : (h+l)*(h+l)≤payload/2) :
    let d:=h+l
    let n:=Count d
    let root:=2^(payload/2)
    stop origin D H h l b≤origin+4*((1+n)*root+n+d*2^h+1)+2*(D*H*2^h+1)+n+
      (7*n+1)*(2*(D*H*2^h+1)+root) := Dated.paid_extent origin (D*H) h l b payload word square

end
end Hierarchy.DescentGLPacked.BankImage.SignedFields

end OAI
