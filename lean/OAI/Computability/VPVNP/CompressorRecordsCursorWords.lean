import OAI.Computability.VPVNP.CompressorRecordsCursorRAM
import OAI.Computability.VPVNP.CompressorRecordsCursorCoordinates

/-!
# Exact binary arithmetic of a level-zero descriptor visit

Decode the three mixed-radix quotients of the persistent row. The two integer
divisions of the slot gate select respectively the flip slot and the genuine
payload slots. Splitting the one-bit mask by the low-block radix gives the
base translation and the remaining-lane displacement in the cursor state.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.CursorRAM

open BurstRAM BurstRAM.PrivateRAM CursorNetwork

variable {w : ℕ}

/-- Encode a natural cursor parameter as a machine word by reduction modulo the word modulus. -/
abbrev encode (w : ℕ) (n : ℕ) : Word w := Fin.ofNat (2 ^ w) n

private theorem enc_add (x y : ℕ) :
    encode w x + encode w y = encode w (x+y) := by
  apply Fin.ext
  simp only [Fin.val_add, Fin.val_ofNat, Nat.add_mod_mod, Nat.mod_add_mod]

private theorem enc_mul (x y : ℕ) :
    encode w x * encode w y = encode w (x*y) := by
  apply Fin.ext
  simp only [Fin.val_mul, Fin.val_ofNat, Nat.mul_mod_mod, Nat.mod_mul_mod]

private theorem enc_div {x y : ℕ} (hx : x < 2^w) (hy : y < 2^w) :
    BinaryOp.div.eval (encode w x) (encode w y) = encode w (x/y) := by
  change encode w (x % (2^w) / (y % (2^w))) = _
  rw [Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy]

private theorem enc_mod {x y : ℕ} (hx : x < 2^w) (hy : y < 2^w) :
    BinaryOp.mod.eval (encode w x) (encode w y) = encode w (x%y) := by
  change encode w (x % (2^w) % (y % (2^w))) = _
  rw [Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy]

private theorem enc_xor {x y : ℕ} (hx : x < 2^w) (hy : y < 2^w) :
    BinaryOp.bitXor.eval (encode w x) (encode w y) = encode w (x ^^^ y) := by
  change encode w ((x % (2^w)) ^^^ (y % (2^w))) = _
  rw [Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy]

private theorem enc_shift {x j : ℕ} (hx : x < 2^w) (hj : j < w) :
    BinaryOp.shiftLeft.eval (encode w x) (encode w j) = encode w (x * 2^j) := by
  have hj' : j < 2^w := hj.trans Nat.lt_two_pow_self
  simp [BinaryOp.eval, encode, Nat.mod_eq_of_lt hj', Nat.mod_eq_of_lt hx, hj, Nat.shiftLeft_eq]

theorem packed_lt {v x m n : ℕ} (hv : v < m) (hx : x < n) : v*n + x < m*n := by
  have h := Nat.mul_le_mul_right n (Nat.succ_le_of_lt hv)
  rw [Nat.succ_mul] at h
  omega

private theorem unpack_div {v x n : ℕ} (hx : x < n) : (v*n+x)/n = v := by
  rw [Nat.mul_comm, Nat.mul_add_div (by omega), Nat.div_eq_of_lt hx, Nat.add_zero]

private theorem gate (s : ℕ) : 2 / (s+1) % 2 = (if s = 1 then 1 else 0) ∧
    (2 / (s+1) + 1) / 2 = (if s < 2 then 1 else 0) := by
  rcases s with _ | _ | s
  · decide
  · decide
  · simp [Nat.div_eq_of_lt (show 2 < s+2+1 by omega)]

private theorem mask_split (b j s : ℕ) :
    ((if s = 1 then 1 else 0) * 2^j) % 2^b = (if s = 1 ∧ j < b then 2^j else 0) ∧
    ((if s = 1 then 1 else 0) * 2^j) / 2^b = cursorLaneMask b j s := by
  by_cases hs : s = 1
  · by_cases hj : j < b
    · have h := Nat.pow_lt_pow_right Nat.one_lt_two hj
      simp [hs, hj, Nat.not_le.mpr hj, cursorLaneMask, Nat.mod_eq_of_lt h, Nat.div_eq_of_lt h]
    · have hbj : b ≤ j := by omega
      have he : 2^j = 2^(j-b)*2^b := by rw [← pow_add, Nat.sub_add_cancel hbj]
      simp [hs, hj, hbj, cursorLaneMask, he]
  · simp [hs, cursorLaneMask]

/-- The first five public words are shared by all six column writes. -/
structure Parameters (p : Fin 11 → Word w) (b l a W : ℕ) : Prop where
  degree : p 0 = encode w (2^a)
  cursors : p 1 = encode w (b+l)
  low : p 2 = encode w (2^b)
  lanes : p 3 = encode w (2^l)
  width : p 4 = encode w W

/-- Number of scanned source slots including the parallel padding. -/
def rowCount (b l a : ℕ) := ((b+l) * 2^b * 2^l) * 2^a

private theorem radix_bounds {b l a : ℕ} (hD : 1 < b+l)
    (fit : rowCount b l a < 2^w) :
    b+l ≤ w ∧ b+l < 2^w ∧ 2^a < 2^w ∧ 2^b < 2^w ∧ 2^l < 2^w ∧
      2^(b+l) < 2^w ∧ (b+l)*2^b < 2^w ∧ (b+l)*2^b*2^l < 2^w := by
  have ha := Nat.two_pow_pos a
  have hb := Nat.two_pow_pos b
  have hl := Nat.two_pow_pos l
  unfold rowCount at fit
  have hBL := (Nat.le_mul_of_pos_right _ ha).trans_lt fit
  have hB := (Nat.le_mul_of_pos_right _ hl).trans_lt hBL
  have hDc := (Nat.le_mul_of_pos_right _ hb).trans_lt hB
  have hB' := (Nat.le_mul_of_pos_left _ (by omega : 0 < b+l)).trans_lt hB
  have hL' := (Nat.le_mul_of_pos_left _ (Nat.mul_pos (by omega) hb)).trans_lt hBL
  have ha' := (Nat.le_mul_of_pos_left _ (Nat.mul_pos (Nat.mul_pos (by omega) hb) hl)).trans_lt fit
  have hpow : 2^(b+l) < 2^w := by
    rw [pow_add]
    exact (Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_left _ (by omega : 0 < b+l))).trans_lt hBL
  exact ⟨((Nat.pow_lt_pow_iff_right Nat.one_lt_two).mp hpow).le, hDc, ha', hB', hL', hpow, hB, hBL⟩

/-- All arithmetic in the native template agrees with the cursor's endpoint, lane
shift and width formulas. The room hypothesis is on the number of actual rows. -/
theorem wordRow_exact {p : Fin 11 → Word w} {b l a W : ℕ}
    (hparam : Parameters p b l a W) (hD : 1 < b+l) (hd : 2 ≤ 2^a)
    (fit : rowCount b l a < 2^w)
    {j x g s : ℕ} (hj : j < b+l) (hx : x < 2^b) (hg : g < 2^l) (hs : s < 2^a) :
    wordRow p (encode w (((j*2^b+x)*2^l+g)*2^a+s)) =
      ⟨encode w ((j*2^b+x)*2^a+s),
       encode w (cursorNextBase b l j x s * 2^a+s), encode w (cursorLaneMask b j s),
       encode w ((cursorNextBase b l j x s * 2^l+(g ^^^ cursorLaneMask b j s))*2^a+s),
       encode w (if s < 2 then W else 0)⟩ := by
  obtain ⟨hdw, hcw, haw, hbw, hlw, hpw, hbn, hsn⟩ := radix_bounds hD fit
  have hbase := packed_lt hj hx
  have hsite := packed_lt hbase hg
  have hrow := packed_lt hsite hs
  have hsw : s + 1 < 2^w := (Nat.succ_le_of_lt hs).trans_lt haw
  have hjw : j + 1 < 2^w := (Nat.succ_le_of_lt hj).trans_lt hcw
  have h2w : 2 < 2^w := hd.trans_lt haw
  have h3w : 3 < 2^w := by
    have h := Nat.pow_le_pow_right Nat.zero_lt_two (show 2 ≤ b+l by omega)
    omega
  have hquot : 2/(s+1) ≤ 2 := Nat.div_le_self ..
  have hmask : (if s=1 then 1 else 0)*2^j < 2^w := by
    split <;> simp [((Nat.pow_lt_pow_right Nat.one_lt_two hj).trans hpw)]
  have hm := mask_split b j s
  have hlow : (if s=1 ∧ j<b then 2^j else 0) < 2^w := by
    split <;> simp [((Nat.pow_lt_pow_right Nat.one_lt_two hj).trans hpw)]
  have hlane : cursorLaneMask b j s < 2^w := by
    rw [← hm.2]; exact (Nat.div_le_self ..).trans_lt hmask
  have h1 : (1 : Word w) = encode w 1 := rfl
  have h2 : (2 : Word w) = encode w 2 := rfl
  unfold wordRow
  simp only [hparam.degree, hparam.low, hparam.cursors, hparam.lanes, hparam.width, h1, h2,
    enc_div (hrow.trans fit) haw, enc_mod (hrow.trans fit) haw, unpack_div hs, Nat.mul_add_mod_of_lt hs,
    enc_div (hsite.trans hsn) hlw, enc_mod (hsite.trans hsn) hlw, unpack_div hg, Nat.mul_add_mod_of_lt hg,
    enc_div (hbase.trans hbn) hbw, enc_mod (hbase.trans hbn) hbw, unpack_div hx, Nat.mul_add_mod_of_lt hx,
    enc_add, enc_div h2w hsw, enc_mod (hquot.trans_lt h2w) h2w, (gate s).1,
    enc_shift (show (if s = 1 then 1 else 0) < 2^w by split <;> omega) (hj.trans_le hdw),
    enc_div hmask hbw, enc_mod hmask hbw, hm.1, hm.2, enc_xor (hx.trans hbw) hlow,
    enc_xor (hg.trans hlw) hlane, enc_mod hjw hcw, enc_mul, cursorNextBase,
    enc_div (show 2/(s+1)+1 < 2^w by omega) h2w, (gate s).2]
  by_cases h : s < 2 <;> simp [h]

end CompressorRecords.CursorRAM

end VPVNP
end Computability
end OAI
