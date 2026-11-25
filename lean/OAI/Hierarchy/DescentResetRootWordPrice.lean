import OAI.Hierarchy.DescentResetRootWord

namespace OAI
/-! # Per-group bit price of the issued root word along a genuine reset -/
namespace Hierarchy.DescentDatedAddressBook.ResetMiddle
open DescentSixParty

noncomputable section
variable {n h : ℕ} (board : NonlinearExpanders.Graph n h)

/-- Board-only coefficient after the measured cap and low cells share their paid grain bound. -/
def rootCoefficient (Ht f C packet : ℕ) :=
  let Y := 2^n
  let slots := max (Fintype.card (DescentCommonPalette.rotor board).Edge) (2^(Ht+1))
  let roster := 2*((Y+1)+((2*h+4)*Y+(Y+1)*2^(Ht+1)))
  let price := max (C*packet) ((2+2*h*C)*packet)
  3*(Y*Y)+(4+2*roster+2*(42*2^f+1)*price)*(slots*5)

theorem rootWord_linear (k Ht f cap C packet instruction batches V : ℕ) (one : 1≤V)
    (room : 2^k*(2*cap)≤V) (low : 2^k≤V) :
    rootWord board k Ht f cap C packet instruction batches ≤
      rootCoefficient board Ht f C packet*V+instruction*batches := by
  let Y:=2^n
  let slots:=max (Fintype.card (DescentCommonPalette.rotor board).Edge) (2^(Ht+1))
  let R:=2*((Y+1)+((2*h+4)*Y+(Y+1)*2^(Ht+1)))
  let price:=max (C*packet) ((2+2*h*C)*packet)
  let N:=2^k*(2*cap)
  have small : cap≤V := by
    have keep : 2*cap ≤ N := Nat.le_mul_of_pos_left _ (Nat.two_pow_pos _)
    omega
  have l0 : N+2≤3*V := by change 2^k*(2*cap)+2≤_; omega
  have l1 : N+3≤4*V := by change 2^k*(2*cap)+3≤_; omega
  have l2 : R*2^(k+1) ≤ (2*R)*V := by
    rw [pow_succ]
    simpa only [Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm] using Nat.mul_le_mul_left (2*R) low
  have l3 : 2*(21*2^f*(cap+1)+1) ≤ (2*(42*2^f+1))*V := by
    have cap2 : cap+1≤2*V := by omega
    have charge:=Nat.mul_le_mul_left (21*2^f) cap2
    nlinarith
  have step : N+3+R*2^(k+1)+2*(21*2^f*(cap+1)+1)*price ≤
      (4+2*R+2*(42*2^f+1)*price)*V := by
    calc
      _ ≤ 4*V+(2*R)*V+((2*(42*2^f+1))*V)*price :=
        Nat.add_le_add (Nat.add_le_add l1 l2) (Nat.mul_le_mul_right _ l3)
      _ = _ := by ring
  apply (rootWord_poly board k Ht f cap C packet instruction batches).trans
  calc
    _ ≤ (3*V)*(Y*Y)+instruction*batches+((4+2*R+2*(42*2^f+1)*price)*V)*(slots*5) :=
      Nat.add_le_add (Nat.add_le_add_right (Nat.mul_le_mul_right _ l0) _) (Nat.mul_le_mul_right _ step)
    _ = _ := by unfold rootCoefficient; dsimp only [R,Y,price,slots]; ring

end
end Hierarchy.DescentDatedAddressBook.ResetMiddle

namespace Hierarchy.DescentSixParty.ClosedReset
open DescentCompiler DescentDatedAddressBook.ResetMiddle
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {G : PoweredGadget F}
  {q ε : ℝ} {S : AtomSchedule} {k i z wire hist : ℕ} {W : MarkedWorld F d P bits}
  {D n h C f g cut tail : ℕ} {input : Reached W G q ε S k i z D wire hist}
  {ctl : ResetRates G S k D n h C f g cut tail} (B : ClosedReset input ctl)
local notation "Ht₀" => GroupStage.depthBound D n f g

include B in
/-- The only additional output beside the literal matrix and private headers is the
chosen instruction menu's own bits per packed group. -/
theorem root_word_paid (instruction batches roleExponent : ℕ)
    (roles : instruction*batches ≤ S.epochPower^roleExponent) :
    rootWord ctl.board k Ht₀ f input.placement.cap C ctl.bitsR instruction batches ≤
      S.epochPower^(Nat.clog 2 (rootCoefficient ctl.board Ht₀ f C ctl.bitsR+1) +
        max (S.fallbackExponent cut) roleExponent) := by
  let e:= max (S.fallbackExponent cut) roleExponent
  let V:=S.epochPower^e
  let K:=rootCoefficient ctl.board Ht₀ f C ctl.bitsR
  have big : 2≤S.epochPower := Nat.one_lt_two_pow ctl.height.ne'
  have one : 1≤V := Nat.pow_pos (by omega)
  have parent : S.epochPower^(S.fallbackExponent cut)≤V := Nat.pow_le_pow_right (by omega) (le_max_left ..)
  have used : 2^k*(2*input.placement.cap)≤V := (S.fallback_slots ctl.height B.age.le input.valid.capacity ctl.fixed).trans parent
  have low : 2^k≤V := by
    have paid:=S.fallback_slots (cap:=1) ctl.height B.age.le (Nat.two_pow_pos _) ctl.fixed
    exact (by omega : 2^k≤2^k*(2*1)).trans (paid.trans parent)
  have role : instruction*batches≤V := roles.trans (Nat.pow_le_pow_right (by omega) (le_max_right ..))
  have coeff : K+1≤S.epochPower^(Nat.clog 2 (K+1)) :=
    (Nat.le_pow_clog (by decide : 1<2) _).trans (Nat.pow_le_pow_left big _)
  calc
    _ ≤ K*V+instruction*batches := rootWord_linear ctl.board k Ht₀ f input.placement.cap C ctl.bitsR instruction batches V one used low
    _ ≤ (K+1)*V := by rw [Nat.add_mul,one_mul]; omega
    _ ≤ S.epochPower^(Nat.clog 2 (K+1))*V := Nat.mul_le_mul_right _ coeff
    _ = _ := (pow_add ..).symm

end
end Hierarchy.DescentSixParty.ClosedReset

end OAI
