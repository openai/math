import OAI.ThreeFlat.RAM.PhysicalPinsNat
import OAI.ThreeFlat.Diagonal.ApproximateAddress
import OAI.ThreeFlat.Diagonal.AlignedChunks

namespace OAI
/-! # Evaluation of the physical source-address expressions -/

namespace ThreeFlat.RAM.PhysicalPinsExpr

open Diagonal Diagonal.BoundaryWire Computability.VPVNP.BurstRAM

structure Shape where
  advice : ℕ
  teamBits : ℕ
  timeBits : ℕ
  parameterBits : ℕ
  bits : ℕ
  inside : ℕ
  teams : ℕ
  period : ℕ
  last : ℕ
  parameterBase : ℕ
  templateBase : ℕ

def Shape.words (s : Shape) : Param → ℕ
  | .advice => s.advice | .teamBits => s.teamBits | .timeBits => s.timeBits
  | .parameterBits => s.parameterBits | .chunkBits => s.bits | .ticks => s.inside+1
  | .teams => s.teams | .period => s.period | .finalBlock => s.last
  | .parameterBase => s.parameterBase | .templateBase => s.templateBase

def Shape.chunks (s : Shape) := s.period*(s.inside+1)
def Shape.halfBits (s : Shape) := s.chunks*s.bits

variable {m w : ℕ} (s : Shape) (mem : ℕ → ℕ) (v : Fin m → ℕ)

abbrev nat (f : Formula m) := f.natural w s.words mem v

theorem nat_half : nat (w:=w) s mem v half = s.halfBits := rfl

theorem nat_state : nat (w:=w) s mem v state = stateWidth s.chunks s.bits := by
  change 2 * s.halfBits + s.bits = _
  simp [stateWidth, Shape.halfBits, Nat.two_mul]

theorem nat_hiddenStart : nat (w:=w) s mem v hiddenStart =
    BitLayout.hiddenBase (pinWidth s.chunks s.bits s.advice) := by
  change 2+(s.advice+2*nat (w:=w) s mem v state) = _
  rw [nat_state]
  simp [BitLayout.hiddenBase,pinWidth,Nat.two_mul]

theorem nat_endpoint (side : Bool) (i j : Formula m) :
    nat (w:=w) s mem v (endpoint side i j) = ApproximateAddress.endpoint s.chunks s.bits
      s.last s.advice side (nat (w:=w) s mem v i) (nat (w:=w) s mem v j) := by
  let ix := nat (w:=w) s mem v i
  let jx := nat (w:=w) s mem v j
  cases side with
  | false =>
    change (if decide (ix=0) then 2+s.advice+jx else
      nat (w:=w) s mem v hiddenStart+(ix-1)*nat (w:=w) s mem v state+jx) = _
    simp [ApproximateAddress.endpoint, nat_hiddenStart, nat_state, ix, jx]
  | true =>
    change (if decide (ix=s.last) then 2+s.advice+jx+nat (w:=w) s mem v state else
      nat (w:=w) s mem v hiddenStart+ix*nat (w:=w) s mem v state+jx) = _
    simp [ApproximateAddress.endpoint, nat_hiddenStart, nat_state, ix, jx, Nat.add_assoc,
      Nat.add_left_comm,Nat.add_comm]

theorem nat_middle (i k j : Formula m) :
    nat (w:=w) s mem v (middle i k j) =
      ApproximateAddress.interior s.chunks s.bits s.last s.inside s.advice
        (nat (w:=w) s mem v i) (nat (w:=w) s mem v k) (nat (w:=w) s mem v j) := by
  change nat (w:=w) s mem v hiddenStart+s.last*nat (w:=w) s mem v state+
    nat (w:=w) s mem v i*((s.inside+1-1)*s.bits)+nat (w:=w) s mem v k*s.bits+nat (w:=w) s mem v j = _
  simp [nat_hiddenStart, nat_state, ApproximateAddress.interior]

theorem nat_active (i : Formula m) :
    nat (w:=w) s mem v (active i) =
      (AlignedChunks.active s.period (nat (w:=w) s mem v i)).toNat := by
  let x := nat (w:=w) s mem v i / s.period
  change x%2=(x.testBit 0).toNat
  rw [Nat.toNat_testBit]
  simp

theorem shift_digit (x j : ℕ) (hx : x<2^w) :
    (if j<w then x>>>j else 0)%2 = (x.testBit j).toNat := by
  rw [Nat.toNat_testBit, Nat.shiftRight_eq_div_pow]
  by_cases hj : j<w
  · simp [hj]
  · have hl := hx.trans_le (Nat.pow_le_pow_right (by decide : 0<2) (Nat.le_of_not_gt hj))
    simp [hj, Nat.div_eq_of_lt hl]

/-- The same two comparison rows update every aligned half of external memory. -/
theorem nat_guard (right : Bool) (i j : Formula m) :
    nat (w:=w) s mem v (guardFormula right i j) =
      let block := nat (w:=w) s mem v i
      let raw := nat (w:=w) s mem v j
      if raw/s.bits/(s.inside+1) = block%s.period then 0 else
        ApproximateAddress.endpoint s.chunks s.bits s.last s.advice right block
          ((AlignedChunks.active s.period block).toNat*s.halfBits + raw) := by
  change (if decide (nat (w:=w) s mem v j/s.bits/(s.inside+1)=nat (w:=w) s mem v i%s.period)
    then 0 else nat (w:=w) s mem v (endpoint right i _)) = _
  rw [nat_endpoint]
  simp only [decide_eq_true_eq]
  congr 2
  change nat (w:=w) s mem v (active i)*nat (w:=w) s mem v half+_ = _
  rw [nat_active,nat_half]

end ThreeFlat.RAM.PhysicalPinsExpr

end OAI
