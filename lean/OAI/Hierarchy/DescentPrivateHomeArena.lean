import OAI.Hierarchy.DescentPrivateHostCalendar
import OAI.Hierarchy.DescentPrivateMeterClock

namespace OAI
/-! # Address room for the terminal counter appended to the dated machine's arena -/
namespace Hierarchy.DescentSixParty.NativeBranch
open DescentCompiler DescentCompiler.TerminalScale Filter

variable {F : Type} [Field F] (G : PoweredGadget F)

def privateArenaRate (t f g reset τ prior : ℕ) :=
  max prior (2+(τ+privateGroupRate t (hostRate t reset) (capRate G t g) (cutRate t f g)))+3

/-- The real ROM, two host-sized banks, and the final scalar registers extend any
previously placed arena by a fixed linear amount of address width. -/
theorem stage_home_arena (t f g reset τ B prior : ℕ)
    (reserve : 5+(hostRate t reset*(t+1)+1)≤τ) (positive : 0<B) :
    ∀ᶠ h : ℕ in atTop, let J:=Nat.log 2 h/(2*B)
      ∀ M base capacity : ℕ, let S:=stageNumbers G t J f g reset M (tail τ J)
      M≤2^(2*h) → base≤2^(prior*h) → capacity≤2^(h/2) →
      base+capacity+S.hostSize S.length+S.hostSize S.length+3<
        2^(privateArenaRate G t f g reset τ prior*h) := by
  have stock:=stage_host_gate G t f g reset 0 τ B (by simpa using reserve) (by omega) positive
  filter_upwards [stock,Filter.eventually_ge_atTop (1:ℕ)] with h cap hh
  dsimp only
  intro M base capacity slots old rom
  let J:=Nat.log 2 h/(2*B)
  let S:=stageNumbers G t J f g reset M (tail τ J)
  let K:=privateGroupRate t (hostRate t reset) (capRate G t g) (cutRate t f g)
  let A:=max prior (2+(τ+K))
  let X:=2^(A*h)
  have age : (J+1)^2≤h :=private_age_square h B hh positive
  have grown : tail τ J≤τ*h := Nat.mul_le_mul_left τ (show J+1≤h by nlinarith only [age])
  have copies : S.copies≤2^((τ+K)*h) :=stage_copies_word G t J f g reset M _ τ h hh age grown
  have count : M*S.copies≤X :=calc
    _ ≤ 2^(2*h)*2^((τ+K)*h) :=Nat.mul_le_mul slots copies
    _ = 2^((2+(τ+K))*h) := by rw [Nat.add_mul 2 (τ+K) h,pow_add]
    _ ≤ _ := Nat.pow_le_pow_right (by decide : 0<(2:ℕ)) (Nat.mul_le_mul_right h (Nat.le_max_right ..))
  have hs := cap M 1 (by decide) (show 1≤ scale J 0 by exact Nat.two_pow_pos _)
  have radix : 0<S.radix := Nat.two_pow_pos _
  have ht : 0<S.epochPower := Nat.two_pow_pos _
  have raw : S.hostSize S.length*h ≤ M*S.copies*h :=calc
    _ ≤ ((S.hostSize S.length*S.radix)*h)*S.epochPower :=
      (Nat.mul_le_mul_right h (Nat.le_mul_of_pos_right _ radix)).trans (Nat.le_mul_of_pos_right _ ht)
    _ ≤ _ := hs.trans (Nat.mul_le_mul_left _ (Nat.div_le_self h _))
  have hosts : S.hostSize S.length≤X :=(Nat.le_of_mul_le_mul_right raw hh).trans count
  have baseBound : base≤X := old.trans (Nat.pow_le_pow_right (by decide : 0<(2:ℕ))
    (Nat.mul_le_mul_right h (Nat.le_max_left ..)))
  have ha : 1≤A := (show 1≤2+(τ+K) by omega).trans (Nat.le_max_right ..)
  have romBound : capacity≤X := rom.trans (Nat.pow_le_pow_right (by decide : 0<(2:ℕ))
    ((Nat.div_le_self ..).trans (Nat.le_mul_of_pos_left h ha)))
  have x : 0<X := Nat.two_pow_pos _
  calc
    _ < 8*X := by
      change base + capacity + S.hostSize S.length + S.hostSize S.length + 3 < 8 * X
      omega
    _ = 2^(3+A*h) := by change (2:ℕ)^3*2^(A*h)=_;rw [pow_add]
    _ ≤ _ := by
      apply Nat.pow_le_pow_right (by decide : 0<(2:ℕ))
      change 3+A*h≤(A+3)*h
      rw [Nat.add_mul]
      omega

end Hierarchy.DescentSixParty.NativeBranch

end OAI
