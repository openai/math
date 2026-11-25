import OAI.Hierarchy.DescentIncomingPitchBounds
import OAI.Hierarchy.DescentIncomingWalshWidth
import OAI.Hierarchy.DescentCalibratedResetChart

namespace OAI
/-! # Density of the common root, operand and primitive pitch returned by each genuine reset -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset
open DescentCompiler DescentSixParty DescentPackedWalsh DescentCompiler.TerminalScale
open DescentPacking.PackedMatch.Local.Stage ProtocolRAM Filter
noncomputable section
set_option maxHeartbeats 1400000

/-- First Walsh packs the old block coordinate. The new receiver then clips it
to the remaining group byte and the widest actual lookup on that date. -/
theorem receiver_density (c z k h b u : ℕ) (next : z≤c) (bpos : 0<b) (upos : 0<u)
    (old : 8*b≤h) (fresh : 8*u≤h) :
    let cut:=laneBits (c+k) h b-k
    let e:=laneBits (min cut (min cut z)) h u
    2^z≤2^e ∨ h≤2^e*(16*(2^k*b+u)) :=by
  let cut := laneBits (c+k) h b-k
  let s := min cut (min cut z)
  let e := laneBits s h u
  have prior:= (NativePitch.reset_density c k h b bpos old).2.2
  have after : 2^s≤2^e ∨ h≤2^e*(16*u):=by
    simpa only [e, laneBits, Nat.add_zero,Nat.sub_zero,pow_zero,Nat.mul_one] using
      (NativePitch.reset_density s 0 h u upos fresh).2.2
  have right : 16*u≤16*(2^k*b+u):=Nat.mul_le_mul_left _ (Nat.le_add_left ..)
  have left : 16*2^k*b≤16*(2^k*b+u):=by rw [Nat.mul_assoc];exact Nat.mul_le_mul_left _ (Nat.le_add_right ..)
  rcases after with cover|wide
  · rcases le_total z cut with all|truncated
    · left
      simpa only [s,min_eq_right all] using cover
    · have used : 2^cut≤2^e:=by simpa only [s,min_eq_left truncated,min_self] using cover
      rcases prior with fit|paid
      · exact Or.inl ((Nat.pow_le_pow_right (by decide) next).trans (fit.trans used))
      · exact Or.inr (paid.trans (Nat.mul_le_mul used left))
  · exact Or.inr (wide.trans (Nat.mul_le_mul_left _ right))

variable {F : Type} [Field F] (G : PoweredGadget F) {n d : ℕ} (board : NonlinearExpanders.Graph n d)
    (op : RotorSpec) (t f g reset τ D drift : ℕ)
local notation "κ" => (1+(hostRate t reset+capRate G t g)*(t+1)+8+cutRate t f g)
local notation "ρ" => ResetOutput.receiverRate G board op t f g reset D
def densityRate := 5+max (κ+3) (ρ)

/-- The exponent is fixed before the tail, payload denominator, or original
site population. It applies also when the reset happens to be the final date. -/
theorem scheduled_density (B : ℕ) (den : 0<B) (bought : 2*ρ≤B)
    (branch : G.b≤2^(capRate G t g)) (bound : ℕ) :
    ∀ᶠ h:ℕ in atTop,let J:=Nat.log 2 h/(2*B);
    ∀sites age p degree : ℕ, let S:=stageNumbers G t J f g reset sites (tail τ J)
    let k:=groupBits t J S.hostGain S.capGain (cutRate t f g)
    ∀(ordinary : ℕ→Dated.Ordinary) (old : StageVenueTail.Date) (A M base : ℕ) (addr : ℕ→ℕ→Bank) (roster : Bank),
    age≤S.length→p≤h→degree≤bound→ old.degree=D→ old.cap=((capCalendar G.b t g J).take age).prod*256→ old.paidBits=S.censusBits p→
    let a:=scheduled G S board k (tail τ J) age p f g drift degree h ordinary op
      (S.firstWidth G.b p) (S.grainAt G.b p 0) A M old addr roster base
    let L:=a.successor.receiver.lanes
    (S.groupCount (age+1)≤L ∨ h≤L*TerminalScale.scale J (densityRate G board op t f g reset D)) ∧
      a.successor.middle.rootLanes=L ∧ a.successor.primitive.chart.lanes=L :=by
  filter_upwards [NativePitch.walsh_rate G t f g reset τ B den,
    scheduled_scale G board op t f g reset τ D drift B den branch bound,
    scheduled_short G board op t f g reset τ D drift B den bought branch bound] with h ws sizes enough
  dsimp only
  intro sites age p degree ordinary old A M base addr roster live hp hd hD cap paid
  let J:=Nat.log 2 h/(2*B)
  let tb:=tail τ J
  let S := stageNumbers G t J f g reset sites tb
  let k := groupBits t J S.hostGain S.capGain (cutRate t f g)
  let a:=scheduled G S board k tb age p f g drift degree h ordinary op
    (S.firstWidth G.b p) (S.grainAt G.b p 0) A M old addr roster base
  let v:=a.successor
  let c:=S.groupWidth k tb age
  let z:=S.groupWidth k tb (age+1)
  let b:=S.localWalshBits p (c+k) f (quota t)
  have w:=ws sites p age hp live
  have words:=sizes sites age p degree ordinary old A M base addr roster hp hd hD cap paid
  have bits:=enough sites age p degree ordinary old A M base addr roster hp hd hD cap paid
  have down : z≤c:=by
    dsimp only [z,c,AtomSchedule.groupWidth]
    exact Nat.add_le_add_left (Nat.mul_le_mul_left k (Nat.sub_le_sub_left (Nat.le_succ age) S.length)) _
  let previous := NativePitch.resetCut S k tb p f h age
  let nextM := NativePitch.incoming S k tb p f h ordinary (age+1)
  let code := DescentPrimitivePalette.printedBits G (S.firstWidth G.b p) (S.grainAt G.b p 0) op
  let prior := ResetOutput.Prior.atDate G S age p drift A M code old
  let sample := ResetOutput.fromBoard G S board k tb age p f g drift degree h 0 previous 1 nextM op.C op.w prior 0
  have inventory := selected_inventory G S board k tb age p f g drift degree h previous nextM op.C op.w
    A M code old addr roster base
  have width : v.groupWidth=sample.groupWidth :=
    congrArg₂ (fun (rows tailRows : List ℕ) => 1+(rows++tailRows).sum) inventory.1 inventory.2.1
  have lanes := inventory.2.2.1
  change v.receiver.lanes = 2^(laneBits (min previous (min previous z)) h sample.groupWidth) at lanes
  rw [←width] at lanes
  have disj : 2^z≤v.receiver.lanes ∨ h≤v.receiver.lanes*(16*(2^k*b+v.groupWidth)) := by
    rw [lanes]
    exact receiver_density c z k h b v.groupWidth down
      (by unfold b AtomSchedule.localWalshBits DescentWalshPrecision.bits; omega)
      v.groupWidth_pos w.1 bits
  refine ⟨?_,rfl,rfl⟩
  rcases disj with full|clipped
  · exact Or.inl (by rw [←S.group_power (k:=k) (tail:=tb) rfl rfl];exact full)
  · apply Or.inr (clipped.trans (Nat.mul_le_mul_left _ ?_))
    have block : 2^k≤ TerminalScale.scale J κ:=Nat.pow_le_pow_right (by decide : 0<(2:ℕ)) (groupBits_linear ..)
    have x : 2^k*b≤ TerminalScale.scale J (κ+3):=(Nat.mul_le_mul block w.2).trans_eq (scale_mul J κ 3)
    let R:=max (κ+3) (ρ)
    have up {e : ℕ} (le : e≤R) : TerminalScale.scale J e≤ TerminalScale.scale J R:=Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ le)
    have sum:=Nat.add_le_add (x.trans (up (le_max_left ..))) (words.trans (up (le_max_right ..)))
    calc
      16*(2^k*b+v.groupWidth) ≤ 16*(TerminalScale.scale J R+TerminalScale.scale J R) :=Nat.mul_le_mul_left _ sum
      _ = 32*TerminalScale.scale J R:=by ring
      _ ≤ TerminalScale.scale J 5*TerminalScale.scale J R:=Nat.mul_le_mul_right _ (by
        change 2^5≤2^(5*(J+1));exact Nat.pow_le_pow_right (by decide) (Nat.le_mul_of_pos_right _ (Nat.succ_pos _)))
      _ = _:=scale_mul J 5 R

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI
