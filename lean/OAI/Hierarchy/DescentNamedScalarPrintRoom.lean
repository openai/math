import OAI.Hierarchy.DescentNativeSocketScale
import OAI.Hierarchy.DescentIncomingCalendarFactors
import OAI.Hierarchy.DescentSignedCableFields

namespace OAI
/-! # Printed socket and signed cable bits on the terminal book -/
namespace Hierarchy.DescentSixParty
open DescentCompiler DescentCompiler.TerminalScale DescentSharedCableNames Filter
variable {F : Type} [Field F] (G : PoweredGadget F)

private theorem scalar_clog_bound {n a : ℕ} (limit : n≤2^a) : Nat.clog 2 (n+1)≤a+1:=by
  apply Nat.clog_le_of_le_pow
  rw [pow_succ]
  have pos:=Nat.two_pow_pos a
  omega

/-- The terminal book prints the chosen socket and four numerical signed edge
fields for every final group. The physical calibration pays for all groups. -/
theorem named_scalar_print_room (t f g reset τ B : ℕ) (budget : 2*(τ+2)≤B) :
    ∀ᶠ h : ℕ in atTop,∀M : ℕ,
      let J:=Nat.log 2 h/(2*B)
      let S:=stageNumbers G t J f g reset M (tail τ J)
      let cap:=(capCalendar G.b S.rounds g S.height).prod*256
      let q:=2^Nat.clog 2 (NativeBranch.localLimit G S)*(G.b^(t*J)*G.b)
      32*(2+S.groupCount S.length*max (max 1 (Nat.clog 2 (q+1))) (DescentSignedCableCodec.width 3 cap))≤h :=by
  let qr:=localSocketRate G t g+Nat.clog 2 G.b*(t+1)
  let gain:=capRate G t g*(t+1)
  let c:=qr+3*gain+38
  have positive : 0<B:=by omega
  filter_upwards [eventually_late c B positive,eventually_home τ 0 2 B positive (by simpa using budget)] with h late home
  intro M J S cap q
  let book:=max (max 1 (Nat.clog 2 (q+1))) (DescentSignedCableCodec.width 3 cap)
  let groups:=S.groupCount S.length
  have sockets:=native_socket_scale G t J f g reset M τ
  have socket : q≤2^(qr*(J+1)):=sockets.2.2.2.2.2.2.1
  have capRead:=NativePitch.all_caps G t g J (capCalendar G.b t g J).length
  have signed : cap≤2^(8+gain*J):=by
    change (capCalendar G.b t g J).prod*256≤2^(8+gain*J)
    simpa only [List.take_length,Nat.mul_assoc,gain] using capRead
  have cb : Packed.bits cap≤8+gain*J+1:=scalar_clog_bound signed
  have qb:=scalar_clog_bound socket
  have side : DescentSignedCableCodec.width 3 cap=2+(Packed.bits cap+(Packed.bits cap+(Packed.bits cap+2))):=rfl
  have digits : book+2≤c*(J+1):=by
    dsimp only [book,c]
    rw [side]
    simp only [Nat.add_mul,Nat.mul_add,Nat.mul_assoc,Nat.mul_one] at qb ⊢
    omega
  have jBound : J+1≤2^(J+1):=Nat.lt_two_pow_self.le
  have cBound : c≤2^(J+1):=late.trans ((Nat.le_succ J).trans jBound)
  have small : book+2≤ scale J 2:=calc
    _ ≤ c*(J+1) := digits
    _ ≤ 2^(J+1)*2^(J+1) := Nat.mul_le_mul cBound jBound
    _ = _ :=by rw [←pow_add];apply congrArg (fun i:ℕ=>2^i);omega
  have gr : groups=2^(tail τ J):=by
    dsimp only [groups,AtomSchedule.groupCount]
    simp only [Nat.sub_self,pow_zero,Nat.mul_one]
    rfl
  have grPos : 0<groups:=by rw [gr];exact Nat.two_pow_pos _
  have site : groups≤2^(tail τ J)*2^0:=by rw [gr,pow_zero,Nat.mul_one]
  have measured : 32*(groups*(book+2))≤h:=home.2 0 groups _ site (Nat.zero_le _) small
  apply le_trans _ measured
  apply Nat.mul_le_mul_left
  change 2+groups*book≤groups*(book+2)
  rw [Nat.mul_add]
  omega

end Hierarchy.DescentSixParty

end OAI
