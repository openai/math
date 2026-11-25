import OAI.Hierarchy.DescentNativeSocketScale

namespace OAI
/-! # Width of the frozen terminal cohort list at the calibrated physical word -/
namespace Hierarchy.DescentSixParty
open DescentCompiler DescentCompiler.TerminalScale Filter

variable {F : Type} [Field F] (G : PoweredGadget F)

/-- The frozen list and the terminal socket ordinal both fit the original physical
widths. The two schedule purchases depend only on the given compiler rates. -/
theorem terminal_snapshot_bit_room (t f g reset τ B : ℕ)
    (tailRoom : 2*localSocketRate G t g≤τ) (bought : 2*(localSocketRate G t g+3)≤B) :
    ∀ᶠ h : ℕ in atTop,∀ M : ℕ,
      let J:=Nat.log 2 h/(2*B)
      let S:=stageNumbers G t J f g reset M (tail τ J)
      let k:=groupBits t J S.hostGain S.capGain (cutRate t f g)
      let j:=Nat.clog 2 (NativeBranch.localLimit G S)
      32*((k*S.length+1)*2^(8+S.capGain*S.length))≤h ∧
        j≤S.groupWidth k (tail τ J) S.length+k :=by
  let a:=localSocketRate G t g
  let κ:=1+(hostRate t reset+capRate G t g)*(t+1)+8+cutRate t f g
  let c:=κ*(t+1)+1
  have hB : 0<B:=by omega
  have budget : 2*(0+0+(a+3))≤B:=by simpa only [Nat.zero_add] using bought
  filter_upwards [eventually_late c B hB,eventually_home 0 0 (a+3) B hB budget] with h late home
  intro M J S k j
  obtain ⟨_,cap,sockets,_,_,_,_,tailFit⟩:=native_socket_scale G t J f g reset M τ
  refine ⟨?_,(tailFit tailRoom).1⟩
  let X:=2^(J+1)
  have grown : J+1≤X:=Nat.lt_two_pow_self.le
  have coef : c≤X:=le_trans late ((Nat.le_succ J).trans grown)
  have keys : k≤κ*(J+1):=groupBits_linear ..
  have age : S.length≤(t+1)*(J+1):=Nat.mul_le_mul_left (t+1) (Nat.le_succ J)
  have poly : k*S.length+1≤c*(J+1)^2:=by
    have scaled:=Nat.mul_le_mul keys age
    have one : 1≤(J+1)^2:=Nat.pow_pos (Nat.succ_pos J)
    dsimp only [c]
    nlinarith only [scaled,one]
  have digits : k*S.length+1≤ scale J 3:=calc
    _ ≤ c*(J+1)^2 := poly
    _ ≤ X*X^2 := Nat.mul_le_mul coef (Nat.pow_le_pow_left grown 2)
    _ = scale J 3 := by
      change 2^(J+1)*(2^(J+1))^2=2^(3*(J+1))
      rw [←pow_mul,←pow_add]
      congr 1
      ring
  have pos : 0<G.b:=by have paid:=G.paid;omega
  have records : 2^(8+S.capGain*S.length)≤ scale J a:=
    (Nat.le_mul_of_pos_left _ (Nat.mul_pos (by decide : 0<2) pos)).trans (cap.trans sockets)
  have bound : (k*S.length+1)*2^(8+S.capGain*S.length)≤ scale J (a+3):=by
    rw [Nat.add_comm a 3,←scale_mul]
    exact Nat.mul_le_mul digits records
  simpa only [Nat.one_mul] using
    home.2 0 1 _ (by simp [tail]) (Nat.zero_le _) bound

end Hierarchy.DescentSixParty

end OAI
