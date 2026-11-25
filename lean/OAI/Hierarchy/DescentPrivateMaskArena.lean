import OAI.Hierarchy.DescentPrivateHomeArena

namespace OAI
/-! # Word room for the physically installed nine-field terminal mask ROM -/
namespace Hierarchy.DescentSixParty.NativeBranch
open DescentCompiler DescentCompiler.TerminalScale Filter

variable {F : Type} [Field F] (G : PoweredGadget F)

def privateMaskArenaRate (t f g reset τ prior : ℕ) :=
  let limbs:=τ+privateGroupRate t (hostRate t reset) (capRate G t g) (cutRate t f g)
  privateArenaRate G t f g reset τ (max prior (max 1 limbs)+4)

theorem stage_mask_arena (t f g reset τ B prior : ℕ)
    (reserve : 5+(hostRate t reset*(t+1)+1)≤τ) (positive : 0<B) :
    ∀ᶠ h : ℕ in atTop, let J:=Nat.log 2 h/(2*B)
      ∀M base cells capacity : ℕ,let S:=stageNumbers G t J f g reset M (tail τ J)
      M≤2^(2*h) → base≤2^(prior*h) → capacity≤2^(h/2) → cells≤2*capacity+9*S.radix →
      base+cells+capacity+S.hostSize S.length+S.hostSize S.length+3<2^(privateMaskArenaRate G t f g reset τ prior*h) := by
  let limbs:=τ+privateGroupRate t (hostRate t reset) (capRate G t g) (cutRate t f g)
  let A:=max prior (max 1 limbs)
  filter_upwards [stage_home_arena G t f g reset τ B (A+4) reserve positive,eventually_ge_atTop (1:ℕ)] with h next hh
  dsimp only
  intro M base cells capacity size old page printed
  let J:=Nat.log 2 h/(2*B)
  let S:=stageNumbers G t J f g reset M (tail τ J)
  let X:=2^(A*h)
  have age : (J+1)^2≤h :=private_age_square h B hh positive
  have grown : tail τ J≤τ*h := Nat.mul_le_mul_left τ (show J+1≤h by nlinarith only [age])
  have copies : S.copies≤2^(limbs*h) :=stage_copies_word G t J f g reset M (tail τ J) τ h hh age grown
  have radix : 0<S.radix := Nat.two_pow_pos _
  have groups : 0<S.baseGroups :=Nat.two_pow_pos _
  have sub : S.radix≤S.copies :=by
    unfold AtomSchedule.copies
    rw [pow_succ]
    exact (Nat.le_mul_of_pos_left _ (Nat.pow_pos radix)).trans (Nat.le_mul_of_pos_left _ groups)
  have under (d : ℕ) (e : d≤A) : 2^(d*h)≤X :=Nat.pow_le_pow_right (by decide : 0<(2:ℕ)) (Nat.mul_le_mul_right h e)
  have count : S.radix≤X :=sub.trans (copies.trans (under _ ((le_max_right ..).trans (le_max_right ..))))
  have prev : base≤X :=old.trans (under _ (le_max_left ..))
  have room : capacity≤X :=page.trans ((Nat.pow_le_pow_right (by decide : 0<(2:ℕ)) (Nat.div_le_self h 2)).trans
    (by simpa only [one_mul] using under 1 ((le_max_left ..).trans (le_max_right ..))))
  change cells ≤ 2 * capacity + 9 * S.radix at printed
  apply next M (base+cells) capacity size _ page
  calc
    _ ≤ 16*X :=by omega
    _ = 2^(4+A*h) :=by change (2:ℕ)^4*2^(A*h)=_;rw [pow_add]
    _ ≤ _ :=Nat.pow_le_pow_right (by decide : 0<(2:ℕ)) (by rw [Nat.add_mul];omega)

end Hierarchy.DescentSixParty.NativeBranch

end OAI
