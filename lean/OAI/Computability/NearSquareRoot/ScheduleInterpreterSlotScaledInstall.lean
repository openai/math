import OAI.Computability.NearSquareRoot.ScheduleInterpreterSlotScaledRuler
import OAI.Computability.NearSquareRoot.ScheduleInterpreterSlotScaledBroadcast

/-! # Installing an arbitrary fixed multiple of the input length as a fence -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Uniform.SlotScaledInstall
open IntegerMultiplication TM SlotInstall
variable {A I : Type} [DecidableEq I]

abbrev PC (D : ℕ) := Bool ⊕ (SlotScaledRuler.PC D ⊕ SlotScaledBroadcast.PC)

def start (D : ℕ) : PC D := .inl false
def done (D : ℕ) : PC D := .inr (.inr SlotScaledBroadcast.done)

def rule [DecidableEq A] (D : ℕ) (inp aux : I) (blank : A) : Rule (Fence.Symbol A) (PC D) I :=
  TapeSequence.rule (originRule true)
    (TapeSequence.rule (SlotScaledRuler.rule D inp aux blank) (SlotScaledBroadcast.rule inp aux)
      SlotScaledBroadcast.start) (.inl (SlotScaledRuler.start D))

def time (D L : ℕ) := 9*D*L+2*D+11

theorem time_le (D L : ℕ) (hD : 0<D) : time D L ≤ 20*D*(L+1) := by
  unfold time
  nlinarith only [hD,Nat.zero_le (D*L)]

private theorem plain_eq_scaled {Q : Type} (inp : I) (blank : A) (s : List A) (L : ℕ) (q : Q) :
    (⟨q,plain inp blank s⟩ : Config (Fence.Symbol A) Q I) =
      base q (paint (fun j => (loaded inp blank s j).view) L false false (fun _ => false)) := by
  rw [plain_eq]
  rfl

private theorem marked_eq_scaled {Q : Type} (inp : I) (blank : A) (s : List A) (L : ℕ) (q : Q) :
    base q (paint (fun j => (loaded inp blank s j).view) L false true (fun _ => true)) =
      ⟨q,fun j => Fence.markedTape (-(L : ℤ)) L (loaded inp blank s j)⟩ := by
  apply congrArg (Config.mk q)
  funext j
  apply congrArg (Tape.mk 0)
  funext p
  simp [paint,loaded,Tape.loaded,Fence.bits]

/-- All raw tapes acquire the two fence markers at distance `D*s.length`
from their original heads. The allocator preserves every payload and restores
every head to zero. Its finite controller depends only on `D`. -/
theorem install [DecidableEq A] (D : ℕ) (inp aux : I) (blank : A) (s : List A)
    (distinct : inp ≠ aux) (hD : 0<D) (hL : 0<s.length) (clean : blank∉s) :
    let L := D*s.length
    let last : Config (Fence.Symbol A) (PC D) I :=
      ⟨done D,fun j => Fence.markedTape (-(L:ℤ)) L (loaded inp blank s j)⟩
    Trace (advance (rule D inp aux blank)) ⟨start D,plain inp blank s⟩ (time D s.length) last ∧
      advance (rule D inp aux blank) last = none := by
  let f := fun j => (loaded inp blank s j).view
  let L := D*s.length
  have hp : 0<L := Nat.mul_pos hD hL
  have o := origin_run f L hp true false false (fun _ => false)
  obtain ⟨r,rh⟩ := SlotScaledRuler.run D inp aux blank s distinct hD hL clean
  obtain ⟨b,bh⟩ := SlotScaledBroadcast.run inp aux distinct f L hp
  have tb := TapeSequence.run _ _ SlotScaledBroadcast.start r rh b bh
  have whole := TapeSequence.run _ _ (.inl (SlotScaledRuler.start D)) o (origin_halt true _) tb.1 tb.2
  have ticks : 1+1+(D*(2*s.length+2)+1+D*s.length+1+(6*L+7)) = time D s.length := by
    dsimp [L,time]; ring
  rw [ticks] at whole
  dsimp only
  rw [plain_eq_scaled inp blank s L (start D),←marked_eq_scaled inp blank s L (done D)]
  exact whole

end Uniform.SlotScaledInstall

end NearSquareRoot
end Computability
end OAI
