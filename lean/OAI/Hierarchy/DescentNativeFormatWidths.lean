import OAI.Hierarchy.DescentNativeSocketScale
import OAI.Hierarchy.DescentSeedEpochRoom
import OAI.Hierarchy.DescentTerminalScheduleScale
import OAI.Hierarchy.DescentTerminalBinFormat

namespace OAI
/-! # Paid widths of the dense decoder and the transposed socket route -/
namespace Hierarchy.DescentSixParty
open DescentCompiler DescentCompiler.TerminalScale Filter
noncomputable section
variable {F : Type} [Field F] (G : PoweredGadget F)

/-- The real dense-menu lengths and the common routing pointer use the same paid sockets. -/
theorem native_format_bits (h W q piece : ℕ) (hw : 0 < W) (hq : 0 < q)
    (control : 32*((W*q)*(Nat.log 2 h+2)) ≤ h) (packed : 16*(q*(W*piece)) ≤ h) :
    q*(Nat.clog 2 (2*(q*(W*piece))+1)+Nat.clog 2 (W*piece+1))+2*(q*(W*piece)) ≤ h/2 ∧
      DescentTerminalBinFormat.controlBits W q+DescentTerminalBinReaddress.sliceWidth W q piece ≤ h/2 := by
  let p:=W*piece
  let lg:=Nat.log 2 h
  have sockets : q ≤ W*q := Nat.le_mul_of_pos_left _ hw
  have payload : p ≤ q*p := Nat.le_mul_of_pos_left _ hq
  have row : W*q ≤ (W*q)*(lg+2) := Nat.le_mul_of_pos_right _ (by omega)
  have upper := Nat.lt_pow_succ_log_self (by decide : 1 < 2) h
  have short (x : ℕ) (small : x ≤ h+1) : Nat.clog 2 x ≤ lg+1 :=
    Nat.clog_le_of_le_pow (small.trans upper)
  have l₁:=short (2*(q*p)+1) (by change 16*(q*p) ≤ h at packed; omega)
  have l₂:=short (p+1) (by change 16*(q*p) ≤ h at packed; omega)
  have l₃:=short (W*q) (by change 32*((W*q)*(lg+2)) ≤ h at control; omega)
  have twice : Nat.clog 2 (2*(q*p)+1)+Nat.clog 2 (p+1) ≤ 2*(lg+2) := by omega
  have dense := Nat.mul_le_mul sockets twice
  have route := Nat.mul_le_mul_left (W*q) (show Nat.clog 2 (W*q)+1 ≤ lg+2 by omega)
  rw [show W*q*(2*(lg+2))=2*((W*q)*(lg+2)) by ring] at dense
  change 32*((W*q)*(lg+2)) ≤ h at control
  change 16*(q*p) ≤ h at packed
  constructor
  · change q*(Nat.clog 2 (2*(q*p)+1)+Nat.clog 2 (p+1))+2*(q*p) ≤ h/2
    omega
  · rw [DescentTerminalBinReaddress.sliceWidth_eq]
    change (W*q)*(Nat.clog 2 (W*q)+1)+q*p ≤ h/2
    omega

/-- A fixed socket rate covers the literal routing and dense format widths at every sufficiently late height. -/
theorem native_format_widths (t f g reset τ B : ℕ)
    (positive : 0 < B)
    (routingBudget : 2*((τ+groupRate G t f g reset+4)+
      (localSocketRate G t g+Nat.clog 2 G.b*(t+1))+2) ≤ B) :
    ∀ᶠ h : ℕ in atTop, let J:=Nat.log 2 h/(2*B)
      ∀M : ℕ, let S:=stageNumbers G t J f g reset M (tail τ J)
        let k:=groupBits t J S.hostGain S.capGain (cutRate t f g)
        let W:=NativeBranch.binLimit (k:=k) S
        let q:=2^Nat.clog 2 (NativeBranch.localLimit G S)*(G.b^(t*J)*G.b)
        let piece:=h/(16*(q*W))
        let p:=W*piece
        32*W ≤ h ∧ 16*(q*p) ≤ h ∧ p ≤ h ∧ q ≤ h ∧
          q*(Nat.clog 2 (2*(q*p)+1)+Nat.clog 2 (p+1))+2*(q*p) ≤ h/2 ∧
          DescentTerminalBinFormat.controlBits W q+DescentTerminalBinReaddress.sliceWidth W q piece ≤ h/2 := by
  let ar:=τ+groupRate G t f g reset+4
  let qr:=localSocketRate G t g+Nat.clog 2 G.b*(t+1)
  have bought : 2*(0+0+(ar+qr+2)) ≤ B := by simpa only [Nat.zero_add] using routingBudget
  filter_upwards [eventually_home 0 0 (ar+qr+2) B positive bought,
    eventually_late (2*B+1) B positive] with h controls late
  let J:=Nat.log 2 h/(2*B)
  dsimp only
  intro M
  let S:=stageNumbers G t J f g reset M (tail τ J)
  let k:=groupBits t J S.hostGain S.capGain (cutRate t f g)
  let W:=NativeBranch.binLimit (k:=k) S
  let q:=2^Nat.clog 2 (NativeBranch.localLimit G S)*(G.b^(t*J)*G.b)
  let piece:=h/(16*(q*W))
  let p:=W*piece
  have sock:=native_socket_scale G t J f g reset M τ
  have hw : 0 < W := sock.2.2.2.1
  have qpos : 0 < q := Nat.mul_pos (Nat.two_pow_pos _) sock.2.2.2.2.2.1
  have ws : W ≤ scale J ar := sock.2.2.2.2.1
  have qs : q ≤ scale J qr := sock.2.2.2.2.2.2.1
  have jl : J ≤ scale J 1 := by
    change J ≤ 2^(1*(J+1))
    rw [one_mul]
    exact (Nat.le_succ _).trans (Nat.lt_two_pow_self.le)
  have one : 1 ≤ scale J 1 := Nat.two_pow_pos _
  have bscale : 2*B+1 ≤ scale J 1 := late.trans jl
  have logh:=DescentDatedSeedStartup.log_epoch h B positive
  change Nat.log 2 h+1 ≤ (2*B)*scale J 1 at logh
  have logs : Nat.log 2 h+2 ≤ scale J 2 := calc
    _ ≤ (2*B+1)*scale J 1 := by rw [Nat.add_mul,Nat.one_mul]; omega
    _ ≤ scale J 1*scale J 1 := Nat.mul_le_mul_right _ bscale
    _ = _ := scale_mul J 1 1
  have wide : (W*q)*(Nat.log 2 h+2) ≤ scale J (ar+qr+2) := by
    rw [←scale_mul,←scale_mul]
    exact Nat.mul_le_mul (Nat.mul_le_mul ws qs) logs
  have toll:=controls.2 0 1 _ (by simp [tail]) (by simp) wide
  have bill : 32*((W*q)*(Nat.log 2 h+2)) ≤ h := by simpa only [one_mul] using toll
  have packed : 16*(q*p) ≤ h := calc
    _ = piece*(16*(q*W)) := by dsimp only [p]; ring
    _ ≤ h := Nat.div_mul_le_self h _
  have sockets : W ≤ W*q := Nat.le_mul_of_pos_right _ qpos
  have socketCount : q ≤ W*q := Nat.le_mul_of_pos_left _ hw
  have logPos : W*q ≤ (W*q)*(Nat.log 2 h+2) := Nat.le_mul_of_pos_right _ (by omega)
  have wp : 32*W ≤ h := (Nat.mul_le_mul_left 32 (sockets.trans logPos)).trans bill
  have qbound : q ≤ h := by omega
  have pbound : p ≤ h := by have psmall:=Nat.le_mul_of_pos_left p qpos; omega
  exact ⟨wp,packed,pbound,qbound,native_format_bits h W q piece hw qpos bill packed⟩

end
end Hierarchy.DescentSixParty

end OAI
