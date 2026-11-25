import OAI.Computability.BorderVNP.ParseBatchRawWord

/-! # Address and label words emitted by a binary parse record -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace ParseRecords

open VPVNP VerifierNetwork ParseBatchSort
open BinPackingGames.Foundations.Complexity.CookLevin

/-- Three extra address bits suffice for all intermediate calculations on a whole tree. -/
def workingWidth (m g n : ℕ) := recordWidth m g n + 3

/-- The widened word range contains all input bounds and all addresses up to four
times the largest field bound. -/
theorem workingWidth_bound (m g n : ℕ) :
    4*max m (max g n) + 2 < 2 ^ workingWidth m g n := by
  have h : max m (max g n)+1 ≤ 2^recordWidth m g n :=
    Nat.le_pow_clog (by decide) _
  simp only [workingWidth, pow_add]
  omega

/-- Six most-significant-bit-first output words: left address, layer, state and then
right address, layer, state. These outputs are consumed only on a binary record. -/
def requestWordExpr (m g n u : ℕ) :
    Fin 6 → Fin (workingWidth m g n) → Expr (BitSlot (recordWidth m g n)) :=
  let w := workingWidth m g n
  let b := rawWord w 2
  ![constWord w (u+1), b, rawWord w 3,
    addWord (constWord w (u+2)) (doubleWord b),
    subWord (rawWord w 1) (incWord b), rawWord w 4]

/-- Mathematical payload of the six words from one binary production. -/
def requestValues {g n : ℕ} (u : ℕ) (d : Fin n) (b : Fin d.val) (i j : Fin g) : Fin 6 → ℕ :=
  ![u+1, b.val, i.val, u+2*(b.val+1), d.val-1-b.val, j.val]

/-- Every word of the two requests decodes to its unbounded natural number. In particular
no wrapping address or borrow changes a lookup in a valid block. -/
theorem requestWordExpr_eval {m g n : ℕ} (u : ℕ) (hu : u < 2*n)
    (a : Fin n) (h i j : Fin g) (b : Fin a.val)
    (z : BitSlot (recordWidth m g n) → Bool)
    (hz : fieldsOfBits z = pack (.inr ⟨a, h, b, i, j⟩ : GrammarLabel (Fin m × Bool) (Fin g) n))
    (k : Fin 6) :
    wordValue z (requestWordExpr m g n u k) = requestValues u a b i j k := by
  let w := workingWidth m g n
  have hh := workingWidth_bound m g n
  have ha := a.isLt
  have hb := b.isLt
  have hw : recordWidth m g n ≤ w := by dsimp [w, workingWidth]; omega
  have val (l : Fin 6) : wordValue z (rawWord w l) =
      (pack (.inr ⟨a,h,b,i,j⟩ : GrammarLabel (Fin m × Bool) (Fin g) n)).word l := by
    rw [rawWord_value hw, hz]
  have hsplit : wordValue z (rawWord w 2) = b.val := val 2
  have hlayer : wordValue z (rawWord w 1) = a.val := val 1
  have hdouble := doubleWord_value z (rawWord w 2) (by rw [hsplit]; dsimp [w]; omega)
  have hinc := incWord_value z (rawWord w 2) (by rw [hsplit]; dsimp [w]; omega)
  have hc := constWord_value z w (u+2) (by dsimp [w]; omega)
  have hadd := addWord_value z (constWord w (u+2)) (doubleWord (rawWord w 2))
    (by rw [hc, hdouble, hsplit]; dsimp [w]; omega)
  have hsub := subWord_value z (rawWord w 1) (incWord (rawWord w 2)) (by rw [hinc, hlayer, hsplit]; omega)
  fin_cases k
  · exact constWord_value z w _ (by dsimp [w]; omega)
  · exact val 2
  · exact val 3
  · change wordValue z (addWord (constWord w (u+2)) (doubleWord (rawWord w 2))) = u+2*(b.val+1)
    rw [hadd, hc, hdouble, hsplit]
    omega
  · change wordValue z (subWord (rawWord w 1) (incWord (rawWord w 2))) = a.val-1-b.val
    rw [hsub, hlayer, hinc, hsplit]
    omega
  · exact val 4

/-- Every request bit has quadratic formula size even if its ripple carry is copied.
There are six words of these bits per row. -/
theorem requestWordExpr_size (m g n u : ℕ) (k : Fin 6) (j : Fin (workingWidth m g n)) :
    (requestWordExpr m g n u k j).size ≤ 300*(workingWidth m g n+1)^2 := by
  let w := workingWidth m g n
  have raw (a : Fin 6) (i : Fin w) : ((rawWord (v := recordWidth m g n) w a i).size) ≤ 1 :=
    (rawWord_size ..).le
  have con (a : ℕ) (i : Fin w) : ((constWord w a i : Expr (BitSlot (recordWidth m g n))).size) ≤ 1 := le_rfl
  have inc (i : Fin w) : ((incWord (rawWord (v := recordWidth m g n) w 2) i).size) ≤ 16*w+22 :=
    sumWord_size_le true _ _ 1 (raw 2) (fun _ => le_rfl) i
  have hd (i : Fin w) : ((doubleWord (rawWord (v := recordWidth m g n) w 2) i).size) ≤ 1 :=
    doubleWord_size_le _ 1 (raw 2) i
  have hsum := sumWord_size_le false _ _ 1 (con (u+2)) hd j
  have hsub := subWord_size_le (rawWord w 1) (incWord (rawWord w 2)) (16*w+22)
    (fun i => (raw 1 i).trans (by omega)) inc j
  change _ ≤ 300*(w+1)^2
  fin_cases k
  · change 1 ≤ _; nlinarith
  · exact (raw 2 j).trans (by nlinarith)
  · exact (raw 3 j).trans (by nlinarith)
  · exact hsum.trans (by nlinarith)
  · exact hsub.trans (by nlinarith)
  · exact (raw 4 j).trans (by nlinarith)

end ParseRecords

end BorderVNP
end Computability
end OAI
