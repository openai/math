import OAI.Hierarchy.GridDescription
import OAI.Hierarchy.GridBandwidth
import OAI.Hierarchy.FactorThresholds
import Mathlib.Algebra.BigOperators.Fin

namespace OAI
/-! # Receiving program, public parameters, thresholds and selector in one header -/

noncomputable section
namespace Hierarchy.GridReceiverHeader
open ThreeFlat
open Computability.VPVNP.BurstRAM PrivateRAM
open GridDescription Diagonal
open scoped Fin.CommRing

variable {w p r k n ell : ℕ}

def wordBits (W : ℕ) {d : ℕ} (f : Fin d → Word W) (i : Fin (d*W)) : Bool :=
  let x := finProdFinEquiv.symm i
  (f x.1).val.testBit (W-1-x.2.val)

@[simp] theorem word_at {W d : ℕ} (f : Fin d → Word W) (i : Fin d) (j : Fin W) :
    wordBits W f (finProdFinEquiv (i,j)) = (f i).val.testBit (W-1-j.val) := by
  simp [wordBits]

def count (w : ℕ) := 20*(w+1)+1
def thresholdWords (w : ℕ) (i : Fin (count w)) : Word (64*w) := FactorBucket.threshold i.val

@[simp] theorem threshold_at (pos : 0<w) (i : Fin (count w)) :
    (thresholdWords w i).val = FactorBucket.threshold i.val := by
  apply Fin.val_cast_of_lt
  exact FactorBucket.threshold_word pos (by have := i.isLt; unfold count at this; omega)

variable (text : ℕ) (fits : text≤w^2) (raw : Fin (w^2)→Bool)
variable (index : Word (64*w)) (params : Fin n → Word (64*w)) (sel : Fin ell → Bool)

/-- The first field is copied from the controller input. All other nonselector
fields consist of a tick ordinal and explicit structural integer operands;
the universal machine fetches its instruction table from address zero. -/
def header : List Bool :=
  List.ofFn (fun i : Fin text => raw (i.castLE fits)) ++
  (List.ofFn (wordBits (64*w) (Fin.cons index params)) ++
  (List.ofFn (wordBits (64*w) (thresholdWords w)) ++ List.ofFn sel))

theorem length : (header text fits raw index params sel).length =
    text+((n+1)*(64*w)+(count w*(64*w)+ell)) := by simp [header]

theorem program_at (i : Fin text) :
    (header text fits raw index params sel)[i.val]'(by rw [length]; omega) = raw (i.castLE fits) := by
  unfold header
  rw [List.getElem_append_left (by simp)]
  simp

theorem selector_at (i : Fin ell) :
    (header text fits raw index params sel)[text+((n+1)*(64*w)+count w*(64*w))+i.val]'(by
      rw [length]; omega) = sel i := by
  simp [header,List.getElem_append_right,Nat.add_assoc]

/-- On the final, self-programmed input this precise prefix is the executable
whose padded instruction and public tables the tick fetches. -/
theorem authentic {p' r' k' : ℕ}
    (recv : Machine (64*w) p r k) (eval : Machine (64*w) p' r' k')
    (room : RAM.SelfAdvice.Fits (64*w) p k p' k' 0 (w^2))
    (i : Fin (RAM.SelfAdvice.textSize (64*w) p k)) :
    let fit : RAM.SelfAdvice.textSize (64*w) p k≤w^2 := by have := room.room; omega
    let a := GridDescription.code (q:=w^2) recv eval
    (header _ fit a index params sel)[i.val]'(by rw [length]; omega) = NativeTrace.executable recv i := by
  intro fit a
  rw [program_at,NativeTrace.executable_bits]
  exact RAM.SelfAdvice.tick_bits recv eval _ room i

open Filter GridScale

/-- The native local gate table, its ports, and the chronological directory
can all travel with the public header when they have any fixed polynomial
word count. This estimate includes both self-program fields. -/
theorem structural_words (w coeff degree n : ℕ) (words : n≤coeff*(w+1)^degree) :
    2*w^2+2+(n+1)*(64*w)+count w*(64*w)≤(1500+64*coeff)*(w+1)^(degree+2) := by
  let D := (w+1)^degree
  let Z := (w+1)^2
  have pos : 1≤D := Nat.pow_pos (Nat.succ_pos _)
  have baseline : 2*w^2+2+64*w+count w*(64*w)≤1500*Z := by
    dsimp [Z,count]; nlinarith only [Nat.zero_le w]
  have squared : w≤Z := by dsimp [Z]; nlinarith only [Nat.zero_le w]
  have block : n*w≤(coeff*D)*Z := Nat.mul_le_mul words squared
  have rectangle := Nat.mul_le_mul_left (1500*Z) pos
  rw [pow_add]
  change _≤(1500+64*coeff)*(D*Z)
  nlinarith only [baseline,block,rectangle]

theorem eventual_room_of_poly {Q : ℕ→ℕ} {D : ℕ→ℝ} (env : Envelopes Q D) (k A coeff degree : ℕ) :
    ∀ᶠ w : ℕ in atTop, ∀ q, 0<q → q≤Q w → let a := overhead Q D w
      ∀ n≤coeff*(w+1)^degree, ∀ text≤w^2, 4*(text+((n+1)*(64*w)+(count w*(64*w)+selector k w a))) ≤ pins w a := by
  let H := 1500+64*coeff
  filter_upwards [budgets env k A (4*(H+1)) (degree+2)] with w book
  intro q hq htop a n num text fit
  have avail := (book q hq htop).density.2.2.1
  have pos : 1 ≤ selector k w a := Nat.two_pow_pos _
  have packed : text+(n+1)*(64*w)+count w*(64*w) ≤ H*(w+1)^(degree+2) := by
    have all := structural_words w coeff degree n num
    dsimp only [H]; omega
  have large : text+(n+1)*(64*w)+count w*(64*w) ≤ H*(w+1)^(degree+2)*selector k w a :=
    packed.trans (Nat.le_mul_of_pos_right _ pos)
  have weak : selector k w a ≤ (w+1)^(degree+2)*selector k w a :=
    Nat.le_mul_of_pos_left _ (by positivity)
  change 4*(H+1)*(w+1)^(degree+2)*selector k w a ≤ pins w a at avail
  exact le_trans (by nlinarith only [large,weak]) avail

theorem eventual_room_of_linear {Q : ℕ→ℕ} {D : ℕ→ℝ} (env : Envelopes Q D) (k A coeff : ℕ) :
    ∀ᶠ w : ℕ in atTop, ∀ q, 0<q → q≤Q w → let a := overhead Q D w
      ∀ n≤coeff*(w+1), ∀ text≤w^2, 4*(text+((n+1)*(64*w)+(count w*(64*w)+selector k w a))) ≤ pins w a := by
  simpa only [pow_one] using eventual_room_of_poly env k A coeff 1

theorem eventual_room {Q : ℕ→ℕ} {D : ℕ→ℝ} (env : Envelopes Q D) (k A n : ℕ) :
    ∀ᶠ w : ℕ in atTop, ∀ q, 0<q → q≤Q w → let a := overhead Q D w
      ∀ text≤w^2, 4*(text+((n+1)*(64*w)+(count w*(64*w)+selector k w a))) ≤ pins w a := by
  filter_upwards [eventual_room_of_linear env k A n] with w room
  intro q qp qt
  exact room q qp qt n (Nat.le_mul_of_pos_right _ (Nat.succ_pos _))

end Hierarchy.GridReceiverHeader
end

end OAI
