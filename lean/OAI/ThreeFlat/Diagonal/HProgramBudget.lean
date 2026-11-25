import OAI.ThreeFlat.Diagonal.DefectBudget
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Ring

namespace OAI
/-! # Cost of the native weighted evaluator for the block product

The private variables are boundary states, internal auxiliary words, and
one copy of the entry network for each block. The cells check preserved
coordinates and evaluate those entry networks. The formula below uses the
native descriptor program's counts of guesses, row reads and table lookups.
-/

namespace ThreeFlat.Diagonal

/-- Read-only descriptor initialization followed by the fuel bound of the
expression-contraction program, with every one of its eleven row fields. -/
def evaluatorCost (prep hidden cells binds : ℕ) : ℕ :=
  prep + 13 + 5 * hidden + 22 * cells + (11 * cells) * (2 * binds + 4)

/-- Resource count before substituting the large dyadic scales. -/
theorem evaluator_cost_le {t n a B X Y m z prep hidden cells binds : ℕ}
    (hB : B ≤ m) (ha : a ≤ m) (hLa : n*a ≤ m) (hX : X + Y ≤ m*z)
    (hz : 1 ≤ z) (hprep : prep ≤ 128*((t+1)*(m*z))) (hm : 1 ≤ m)
    (hhidden : hidden ≤ t*(2*B+a) + (t+1)*(n*a) + (t+1)*X)
    (hcells : cells ≤ (t+1)*(Y+B)) :
    evaluatorCost prep hidden cells binds ≤ 600 * (t+1) * m * z * (binds+1) := by
  have mz : m ≤ m*z := Nat.le_mul_of_pos_right _ hz
  have mz' : 1 ≤ m*z := hm.trans mz
  have hb : t*(2*B+a) ≤ (t+1)*(2*m+m) := by gcongr; omega
  have hh : hidden ≤ (t+1)*(5*(m*z)) := by
    calc
      _ ≤ (t+1)*(2*m+m) + (t+1)*m + (t+1)*(m*z) := by
        apply hhidden.trans; gcongr; omega
      _ ≤ (t+1)*(2*(m*z)+(m*z)) + (t+1)*(m*z) + (t+1)*(m*z) := by gcongr
      _ = _ := by ring
  have hc : cells ≤ (t+1)*(2*(m*z)) := by
    apply hcells.trans; gcongr
    omega
  have h₁ : 1 ≤ (t+1)*(m*z) := mz'.trans (Nat.le_mul_of_pos_left _ (by omega))
  unfold evaluatorCost
  calc
    _ ≤ 128*((t+1)*(m*z)) + 13*((t+1)*(m*z)) + 5*((t+1)*(5*(m*z))) +
      22*((t+1)*(2*(m*z))) + (11*((t+1)*(2*(m*z))))*(2*binds+4) := by
        gcongr; exact Nat.le_mul_of_pos_right _ h₁
    _ ≤ _ := by ring_nf; omega

/-- A whole block of auxiliary words and a half of external memory both fit
within one collapse entry's time allowance. -/
theorem block_data_le_collapse_cap {w A L : ℕ} (hw : A+8 ≤ w) (hL : 1 ≤ L) :
    let V := 2^(w^10)
    let q := 2^(w^3)
    let a := 2^(w^10-w^4)
    let cap := q*V*L/w^A
    q*V*L/w^(A+2) ≤ cap ∧ L*a ≤ cap ∧ a ≤ cap ∧ 1 ≤ cap := by
  dsimp only
  have hwpos : 0 < w := by omega
  have hp : w^A ≤ 2^(w^4) := (width_pow_le_two_pow_sq (by omega : A ≤ w)).trans
    (Nat.pow_le_pow_right (by decide) (Nat.pow_le_pow_right hwpos (by decide : 2 ≤ 4)))
  have hs : (w^10-w^4) + w^4 = w^10 := Nat.sub_add_cancel (Nat.pow_le_pow_right hwpos (by decide))
  have ha : 2^(w^10-w^4) * w^A ≤ 2^(w^10) := by
    calc
      _ ≤ 2^(w^10-w^4)*2^(w^4) := Nat.mul_le_mul_left _ hp
      _ = _ := by rw [← Nat.pow_add, hs]
  have hblock : L * 2^(w^10-w^4) ≤ 2^(w^3)*2^(w^10)*L / w^A := by
    apply (Nat.le_div_iff_mul_le (Nat.pow_pos hwpos)).mpr
    calc
      (L * 2^(w^10-w^4)) * w^A = L * (2^(w^10-w^4)*w^A) := Nat.mul_assoc _ _ _
      _ ≤ L * 2^(w^10) := Nat.mul_le_mul_left _ ha
      _ ≤ _ := by rw [Nat.mul_comm L]; gcongr; exact Nat.le_mul_of_pos_left _ (Nat.two_pow_pos _)
  have ha' := (Nat.le_mul_of_pos_left _ hL).trans hblock
  exact ⟨Nat.div_le_div_left (Nat.pow_le_pow_right hwpos (by omega)) (Nat.pow_pos hwpos),
    hblock, ha', (Nat.two_pow_pos _).trans_le ha'⟩

/-- Running all aligned blocks and constructing the shared table loses only
a fixed polynomial in word precision. -/
theorem evaluator_at_scales {w A c e L t n hidden cells prep binds X Y : ℕ}
    (hw : 1200 ≤ w) (hA : A+8 ≤ w) (hsave : c+e+1 ≤ A) (hL : 1 ≤ L)
    (hn : n ≤ L) (ht : (t+1)*L ≤ 2^(w^6))
    (hX : X+Y ≤ (2^(w^3)*2^(w^10)*L/w^A)*w^c)
    (hprep : prep ≤ 128*((t+1)*((2^(w^3)*2^(w^10)*L/w^A)*w^c))) (hbind : binds ≤ w^e)
    (hh : hidden ≤ t*(2*(2^(w^3)*2^(w^10)*L/w^(A+2))+2^(w^10-w^4)) +
      (t+1)*(n*2^(w^10-w^4)) + (t+1)*X)
    (hc : cells ≤ (t+1)*(Y+2^(w^3)*2^(w^10)*L/w^(A+2))) :
    evaluatorCost prep hidden cells binds ≤ 2^(w^3)*2^(w^10)*2^(w^6)/w^(A-(c+e+1)) := by
  let qV := 2^(w^3)*2^(w^10)
  let cap := qV*L/w^A
  have wp : 0 < w := by omega
  obtain ⟨hb, hla, ha, hm⟩ := block_data_le_collapse_cap hA hL
  have he : 1 ≤ w^e := Nat.pow_pos wp
  have base := evaluator_cost_le (binds := binds) hb ha
    ((Nat.mul_le_mul_right _ hn).trans hla) hX (Nat.pow_pos wp) hprep hm hh hc
  have poly : 600*(binds+1) ≤ w*w^e := calc
    _ ≤ 1200*w^e := by omega
    _ ≤ _ := Nat.mul_le_mul_right _ hw
  have cost : evaluatorCost prep hidden cells binds ≤ (t+1)*cap*w^(c+e+1) := by
    apply base.trans
    calc
      _ = ((t+1)*cap*w^c)*(600*(binds+1)) := by ring
      _ ≤ ((t+1)*cap*w^c)*(w*w^e) := Nat.mul_le_mul_left _ poly
      _ = _ := by rw [Nat.pow_add, Nat.pow_add, Nat.pow_one]; ring
  apply (Nat.le_div_iff_mul_le (Nat.pow_pos wp)).mpr
  calc
    _ ≤ ((t+1)*cap*w^(c+e+1))*w^(A-(c+e+1)) := Nat.mul_le_mul_right _ cost
    _ = (t+1)*(cap*w^A) := by
      rw [Nat.mul_assoc, ← Nat.pow_add, Nat.add_sub_of_le hsave, Nat.mul_assoc]
    _ ≤ (t+1)*(qV*L) := Nat.mul_le_mul_left _ (Nat.div_mul_le_self _ _)
    _ = qV*((t+1)*L) := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ ht

/-- The external inputs, one template image and scratch space bounded by
constant multiples of the running time all fit the native address space. -/
theorem evaluator_address_space {w input template scratch field params : ℕ} (hw : 8 ≤ w)
    (hi : input ≤ 8 * (2^(w^3)*2^(w^10)*2^(w^6)))
    (ht : template ≤ 11 * (2^(w^3)*2^(w^10)*2^(w^6)))
    (hs : scratch ≤ 32 * (2^(w^3)*2^(w^10)*2^(w^6)))
    (hf : field ≤ 2^(w^3)*2^(w^10)*2^(w^6))
    (hp : params ≤ 2^(w^3)*2^(w^10)*2^(w^6)) :
    input + template + scratch + field + params < 2^(16*w^10) := by
  have wp : 0 < w := by omega
  have h₁ : w^3 ≤ w^10 := Nat.pow_le_pow_right wp (by decide)
  have h₂ : w^6 ≤ w^10 := Nat.pow_le_pow_right wp (by decide)
  have hw10 := Nat.le_self_pow (by decide : 10 ≠ 0) w
  calc
    _ ≤ 64 * (2^(w^3)*2^(w^10)*2^(w^6)) := by omega
    _ = 2^(6+(w^3+w^10+w^6)) := by rw [Nat.pow_add, Nat.pow_add, Nat.pow_add]
    _ < _ := Nat.pow_lt_pow_right (by decide) (by omega)

/-- One uniform bound covers the memory-segment bases and the operands of
native public coordinate arithmetic, with room for five such operands and
128 fixed control bits in the paper's word. -/
theorem evaluator_coordinate_bits {w x : ℕ} (hw : 4 ≤ w)
    (hx : x ≤ 64 * (2^(w^3)*2^(w^10)*2^(w^6))) :
    x < 2^(3*w^10) ∧ 5*(3*w^10)+128 ≤ 16*w^10 := by
  have wp : 0 < w := by omega
  have h₁ : w^3 ≤ w^6 := Nat.pow_le_pow_right wp (by decide)
  have h₂ : 4*w^6 ≤ w^10 := by
    calc
      _ ≤ w^4*w^6 := Nat.mul_le_mul_right _ (hw.trans (Nat.le_self_pow (by decide) _))
      _ = _ := (Nat.pow_add w 4 6).symm
  have h₃ : 128 ≤ w^10 := by
    have h := Nat.pow_le_pow_left hw 10
    omega
  refine ⟨hx.trans_lt ?_, by omega⟩
  calc
    _ = 2^(6+(w^3+w^10+w^6)) := by rw [Nat.pow_add, Nat.pow_add, Nat.pow_add]
    _ < _ := Nat.pow_lt_pow_right (by decide) (by omega)

end ThreeFlat.Diagonal

end OAI
