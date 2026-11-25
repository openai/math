import OAI.Hierarchy.DescentWideHostArithmetic
import OAI.Hierarchy.DescentEarlyMatrixBudget
import OAI.Hierarchy.DescentTerminalScheduleScale

namespace OAI
/-! # The external ISA, census observations and executable text at the original word price -/
namespace Hierarchy.DescentSixParty.SeedNamed
open DescentCompiler DescentCompiler.TerminalScale Filter
noncomputable section

/-- The copy address has enough high digits to pay the fixed ISA inventory even
when the input site count takes its smallest permitted dyadic value. -/
theorem paid_isa_inventory {F:Type} [Field F] (G:PoweredGadget F) (t f g reset τ B:ℕ)
    (large:20≤ B) (reserve:2*localSocketRate G t g≤τ)
    (budget:2*(localSocketRate G t g+(τ+groupRate G t f g reset+4))+Nat.clog 2 G.b*(t+1)≤ B) :
    ∀ᶠ h:ℕ in atTop,let J:=Nat.log 2 h/(2*B)
      ∀M E:ℕ, let S:=stageNumbers G t J f g reset M (tail τ J)
      let k:=groupBits t J S.hostGain S.capGain (cutRate t f g)
      let j:=Nat.clog 2 (NativeBranch.localLimit G S)
      let q:=2^j*(G.b^(t*J)*G.b)
      let W:=NativeBranch.binLimit (k:=k) S
      let s:=S.firstWidth G.b (W*(h/(16*(q*W))))
      M*(h+1)*2^J≤64*((S.copies*s)*(M+2^J*E)) :=by
  filter_upwards [early_native_packing G t f g reset τ B large reserve budget,
    eventually_late 2 B (by omega),eventually_ge_atTop 1] with h packing late hp
  intro J M E S k j q W s
  let dim:=S.groupWidth k (tail τ J) 0+k
  let r:=dim-2*j
  obtain ⟨shape,copy,_,_,width⟩:=packing M
  change dim=j+(j+r) at shape
  change S.copies=2^(j+(j+r)) at copy
  change h≤32*(2^j*s) at width
  change 2≤ J at late
  have lk : J≤ k:=by change J≤ J+_+8+_;omega
  have stages : 2≤ S.length:=by
    change 2≤(t+1)*J
    exact late.trans (Nat.le_mul_of_pos_left _ (Nat.succ_pos _))
  have span : 2*k≤ dim:=by
    have :=Nat.mul_le_mul_left k stages
    dsimp only [dim,AtomSchedule.groupWidth,Nat.sub_zero]
    rw [Nat.mul_comm 2 k]
    omega
  have saved : J≤ j+r:=by omega
  have extent : 2^j*2^J≤ S.copies:=by
    rw [copy,←Nat.pow_add]
    exact Nat.pow_le_pow_right (by decide) (Nat.add_le_add_left saved _)
  have twice:h+1≤2*h:=by omega
  have full : (h+1)*2^J≤64*(S.copies*s):=calc
    _ ≤ (2*(32*(2^j*s)))*2^J := Nat.mul_le_mul_right _ (twice.trans (Nat.mul_le_mul_left _ width))
    _ =64*((2^j*2^J)*s):=by ring
    _ ≤ _:=Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ extent)
  calc
    _ = M*((h+1)*2^J):=Nat.mul_assoc ..
    _ ≤ M*(64*(S.copies*s)):=Nat.mul_le_mul_left _ full
    _ = 64*((S.copies*s)*M):=by ring
    _ ≤ _:=Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.le_add_right ..))

end
end Hierarchy.DescentSixParty.SeedNamed

end OAI
