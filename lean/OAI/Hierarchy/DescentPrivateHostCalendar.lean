import OAI.Hierarchy.DescentPrivateGateCalendar
import OAI.Hierarchy.DescentTerminalPackingScale

namespace OAI
/-! # The authenticated terminal lookup on every actual common host and radix block -/

namespace Hierarchy.DescentSixParty.NativeBranch
open DescentCompiler DescentCompiler.TerminalScale Filter
variable {F : Type} [Field F] (G : PoweredGadget F)

/-- The actual packed site ledger works at any granularity with enough total row width. -/
theorem stage_host_gate_budget (t J f g reset e τ h M socket p : ℕ)
    (reserve : 5+(hostRate t reset*(t+1)+1)+e≤τ) (size : socket≤ scale J e)
    (lower : h≤32*(p*socket)) :
    let S:=stageNumbers G t J f g reset M (tail τ J)
    S.hostSize S.length*S.radix*h*S.epochPower≤(M*S.copies)*p := by
  let S:=stageNumbers G t J f g reset M (tail τ J)
  let T:=2^J
  let v:=hostRate t reset*(t+1)
  have unit : 32≤ scale J 5 := by
    change 2^5≤2^(5*(J+1))
    exact Nat.pow_le_pow_right (by decide : 0<(2:ℕ)) (by omega)
  have growth : T^(v+1)≤ scale J (v+1) := by
    change (2^J)^(v+1)≤2^((v+1)*(J+1))
    rw [←pow_mul]
    apply Nat.pow_le_pow_right (by decide : 0<(2:ℕ))
    rw [Nat.mul_comm J]
    exact Nat.mul_le_mul_left _ (Nat.le_succ _)
  have enough : 32*T^(v+1)*socket≤S.baseGroups := by
    calc
      _ ≤ (scale J 5*scale J (v+1))*scale J e := Nat.mul_le_mul (Nat.mul_le_mul unit growth) size
      _ = scale J (5+(v+1)+e) := by rw [scale_mul,scale_mul]
      _ ≤ scale J τ := Nat.pow_le_pow_right (by decide : 0<(2:ℕ)) (Nat.mul_le_mul_right _ reserve)
      _ = _ := rfl
  have capacity : S.hostSize S.length*(S.baseGroups*S.radix)=(M*S.copies)*T^v :=
    (Reached.siteLimit_by_home S).trans (packedSiteLimit S)
  have hb : 0<S.baseGroups := Nat.two_pow_pos _
  change S.hostSize S.length*S.radix*h*T≤(M*S.copies)*p
  apply Nat.le_of_mul_le_mul_right _ hb
  calc
    (S.hostSize S.length*S.radix*h*T)*S.baseGroups
      = (S.hostSize S.length*(S.baseGroups*S.radix))*(T*h) := by ring
    _ = ((M*S.copies)*T^v)*(T*h) := by rw [capacity]
    _ ≤ ((M*S.copies)*T^v)*(T*(32*(p*socket))) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ lower)
    _ = ((M*S.copies)*p)*(32*T^(v+1)*socket) := by rw [pow_succ];ring
    _ ≤ _ := Nat.mul_le_mul_left _ enough

/-- Reading all genuine terminal position blocks, even when each word is billed
at the full equipment width, is covered by the physical original copies and stack.
The residual tail uses the same age parameter as the rest of the terminal scan. -/
theorem stage_host_gate (t f g reset e τ B : ℕ)
    (reserve : 5+(hostRate t reset*(t+1)+1)+e≤τ)
    (bought : 2*e≤B) (positive : 0<B) :
    ∀ᶠ h : ℕ in atTop, let J:=Nat.log 2 h/(2*B)
      ∀M socket : ℕ, 0< socket → socket≤ scale J e →
      let S:=stageNumbers G t J f g reset M (tail τ J)
      let p:=h/(16*socket)
      S.hostSize S.length*S.radix*h*S.epochPower≤(M*S.copies)*p := by
  filter_upwards [age_room B positive] with h viable
  let J:=Nat.log 2 h/(2*B)
  let T:=2^J
  change 0<J ∧ 32*T^B≤h at viable
  dsimp only
  intro M socket occupied size
  let S:=stageNumbers G t J f g reset M (tail τ J)
  let p:=h/(16*socket)
  let v:=hostRate t reset*(t+1)
  have cap : socket≤T^(2*e) := by
    apply size.trans
    change 2^(e*(J+1))≤(2^J)^(2*e)
    rw [←pow_mul]
    apply Nat.pow_le_pow_right (by decide : 0<(2:ℕ))
    have c:=Nat.mul_le_mul_left e (show J+1≤2*J by omega)
    nlinarith only [c]
  have frame : 32*socket≤h :=
    (Nat.mul_le_mul_left _ (cap.trans (Nat.pow_le_pow_right (Nat.two_pow_pos _) bought))).trans viable.2
  have lower : h≤32*(p*socket) := by
    simpa [p] using (packing_width (h:=h) (U:=socket) (q:=1) occupied (by decide) (by simpa using frame)).2.2.2
  exact stage_host_gate_budget G t J f g reset e τ h M socket p reserve size lower

end Hierarchy.DescentSixParty.NativeBranch

end OAI
