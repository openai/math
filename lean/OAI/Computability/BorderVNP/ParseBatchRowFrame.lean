import OAI.Computability.BorderVNP.ParseBatchRawFormat
import OAI.Computability.BorderVNP.ParseBatchChildWords
import OAI.Computability.BorderVNP.ParseBatchRecordsCheck

/-!
# Physical Boolean frame for the rows of a parse block

The first output flag tests the canonical encoding, the record interval, and the label
of the root. The second flag identifies rows that emit child reads. The six output
words give the two addresses and their expected layer/state payloads. The raw inputs
remain available to the other parts of the batched verifier for leaf and weight checks.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace ParseRecords

open VPVNP VerifierNetwork ParseBatchSort
open BinPackingGames.Foundations.Complexity.CookLevin

private def eqWord {ι : Type*} {w : ℕ} (a b : Fin w → Expr ι) : Expr ι :=
  (wordLE a b).and (wordLE b a)

private theorem eqWord_eval {ι : Type*} {w : ℕ} (a b : Fin w → Expr ι) (z : ι → Bool) :
    (eqWord a b).eval z = true ↔ wordValue z a = wordValue z b := by
  simp only [eqWord, StatementCircuit.Expr.eval, wordLE_eval, Bool.and_eq_true, decide_eq_true_eq]
  exact le_antisymm_iff.symm

private theorem eqWord_size {ι : Type*} {w : ℕ} (a b : Fin w → Expr ι)
    (ha : ∀ k, (a k).size ≤ 1) (hb : ∀ k, (b k).size ≤ 1) :
    (eqWord a b).size ≤ 30*w+3 := by
  have h := wordLE_size a b (by decide : 1 ≤ 1) ha hb
  have h' := wordLE_size b a (by decide : 1 ≤ 1) hb ha
  simp only [eqWord, StatementCircuit.Expr.size]
  omega

/-- Actual AND/OR/NOT check on one raw row, including the fixed state at index zero. -/
def localFlag {n g : ℕ} (m : ℕ) (d : Fin n) (h : Fin g) (u : Fin (2*d.val+1)) :
    Expr (BitSlot (recordWidth m g n)) :=
  let w := workingWidth m g n
  let root := if u.val = 0 then
    (eqWord (rawWord w 1) (constWord w d.val)).and (eqWord (rawWord w 0) (constWord w h.val))
    else .const true
  let inside := wordLE (rawWord w 1) (constWord w ((2*d.val - u.val)/2))
  (rawFormat m g n).and (inside.and root)

/-- The three local tests hold exactly when this row is a canonical label, fits in
its interval, and has the prescribed layer and state if it is at the root. -/
theorem localFlag_eval {n g : ℕ} (m : ℕ) (d : Fin n) (h : Fin g) (u : Fin (2*d.val+1))
    (z : BitSlot (recordWidth m g n) → Bool) :
    (localFlag m d h u).eval z = true ↔
      ∃ t, unpack m g n (fieldsOfBits z) = some t ∧ u.val + 2*depth t < 2*d.val+1 ∧
        (u.val = 0 → depth t = d.val ∧ state t = h) := by
  let w := workingWidth m g n
  have hw : recordWidth m g n ≤ w := by dsimp [w, workingWidth]; omega
  have hW := workingWidth_bound m g n
  have hidx := u.isLt
  have hd := d.isLt
  have hg := h.isLt
  have layer := rawWord_value hw 1 z
  have parent := rawWord_value hw 0 z
  change wordValue z (rawWord w 1) = (fieldsOfBits z).layer at layer
  change wordValue z (rawWord w 0) = (fieldsOfBits z).parent at parent
  have cb := constWord_value z w ((2*d.val-u.val)/2) (by dsimp [w]; omega)
  have cd := constWord_value z w d.val (by dsimp [w]; omega)
  have ch := constWord_value z w h.val (by dsimp [w]; omega)
  have payload {t : GrammarLabel (Fin m × Bool) (Fin g) n} (ht : unpack m g n (fieldsOfBits z) = some t) :
      (fieldsOfBits z).layer = depth t ∧ (fieldsOfBits z).parent = (state t).val := by
    rw [unpack_eq_some_iff.mp ht]
    rcases t with t | ⟨a,i,b,j,k⟩ <;> exact ⟨rfl,rfl⟩
  change ((rawFormat m g n).and ((wordLE (rawWord w 1) (constWord w ((2*d.val-u.val)/2))).and
    (if u.val = 0 then (eqWord (rawWord w 1) (constWord w d.val)).and
      (eqWord (rawWord w 0) (constWord w h.val)) else .const true))).eval z = true ↔ _
  by_cases hu : u.val = 0
  · simp only [hu, ite_true, StatementCircuit.Expr.eval, Bool.and_eq_true, rawFormat_eval,
      wordLE_eval, decide_eq_true_eq, eqWord_eval, layer, parent, cd, ch, true_implies,
      Nat.sub_zero, Nat.zero_add] at cb ⊢
    rw [cb]
    constructor
    · rintro ⟨⟨t,ht⟩, hl, he, hs⟩
      obtain ⟨hL,hS⟩ := payload ht
      exact ⟨t,ht,by omega, by omega, Fin.ext (hS.symm.trans hs)⟩
    · rintro ⟨t,ht,hl,he,hs⟩
      obtain ⟨hL,hS⟩ := payload ht
      exact ⟨⟨t,ht⟩, by omega, hL.trans he, hS.trans (congrArg Fin.val hs)⟩
  · simp only [hu, ite_false, StatementCircuit.Expr.eval, Bool.and_eq_true, rawFormat_eval,
      wordLE_eval, decide_eq_true_eq, layer, cb, and_true, false_implies]
    constructor
    · rintro ⟨⟨t, ht⟩, hle⟩
      have hh := (payload ht).1
      exact ⟨t, ht, by omega⟩
    · rintro ⟨t, ht, hle⟩
      have hh := (payload ht).1
      exact ⟨⟨t,ht⟩, by omega⟩

private theorem localFlag_size {n g : ℕ} (m : ℕ) (d : Fin n) (h : Fin g) (u : Fin (2*d.val+1)) :
    (localFlag m d h u).size ≤ 300*(workingWidth m g n + 1)^2 := by
  let w := workingWidth m g n
  have raw (a : Fin 6) (i : Fin w) : ((rawWord (v := recordWidth m g n) w a i).size) ≤ 1 :=
    (rawWord_size ..).le
  have con (a : ℕ) (i : Fin w) : ((constWord w a i : Expr (BitSlot (recordWidth m g n))).size) ≤ 1 := le_rfl
  have hf : (rawFormat m g n).size ≤ 165*w+40 := rawFormat_size ..
  have hi := wordLE_size _ _ (by decide : 1 ≤ 1) (raw 1) (con ((2*d.val-u.val)/2))
  have hd := eqWord_size _ _ (raw 1) (con d.val)
  have hh := eqWord_size _ _ (raw 0) (con h.val)
  change _ ≤ 300*(w+1)^2
  unfold localFlag
  split <;> simp only [StatementCircuit.Expr.size] <;> nlinarith

/-- The outputs for one row. Words are ordered as left and right address/layer/state
triples, with the most significant bit first. -/
def rowExpressions {n g : ℕ} (m : ℕ) (d : Fin n) (h : Fin g) (u : Fin (2*d.val+1)) :
    BitSlot (workingWidth m g n) → Expr (BitSlot (recordWidth m g n))
  | .inl false => localFlag m d h u
  | .inl true => .input (.inl false)
  | .inr (k,j) => requestWordExpr m g n u.val k j

/-- Parallel local frame over one tree's entire block, taking the raw record bits as its inputs. -/
noncomputable def rowFrame {n g : ℕ} (m : ℕ) (d : Fin n) (h : Fin g) :
    Frame (Fin (2*d.val+1) × BitSlot (recordWidth m g n))
      (Fin (2*d.val+1) × BitSlot (workingWidth m g n)) :=
  (Frame.initial id).step fun (t : Fin (2*d.val+1) × BitSlot (workingWidth m g n)) =>
    (rowExpressions m d h t.1 t.2).rename (fun i => (t.1,i))

/-- Each row is read directly from its own physical bits. -/
theorem rowFrame_eval {n g : ℕ} (m : ℕ) (d : Fin n) (h : Fin g) (u : Fin (2*d.val+1))
    (z : Fin (2*d.val+1) × BitSlot (recordWidth m g n) → Bool) (i : BitSlot (workingWidth m g n)) :
    (rowFrame m d h).eval z (u,i) = (rowExpressions m d h u i).eval (fun j => z (u,j)) := by
  simp [rowFrame]

/-- The frame's format/interval/root output is equivalent to the exact local conditions. -/
theorem rowFrame_valid {n g : ℕ} (m : ℕ) (d : Fin n) (h : Fin g) (u : Fin (2*d.val+1))
    (z : Fin (2*d.val+1) × BitSlot (recordWidth m g n) → Bool) :
    (rowFrame m d h).eval z (u,.inl false) = true ↔
      ∃ t, unpack m g n (fieldsOfBits fun j => z (u,j)) = some t ∧
        u.val + 2*depth t < 2*d.val+1 ∧ (u.val = 0 → depth t = d.val ∧ state t = h) := by
  rw [rowFrame_eval]
  exact localFlag_eval ..

/-- The second flag is the raw row's binary-production tag. -/
theorem rowFrame_tag {n g : ℕ} (m : ℕ) (d : Fin n) (h : Fin g) (u : Fin (2*d.val+1))
    (z : Fin (2*d.val+1) × BitSlot (recordWidth m g n) → Bool) :
    (rowFrame m d h).eval z (u,.inl true) = z (u,.inl false) :=
  rowFrame_eval ..

/-- The selected word on a checked production has the exact address, layer, or state
of the appropriate child. -/
theorem rowFrame_requestWords {n g : ℕ} (m : ℕ) (d : Fin n) (h : Fin g) (u : Fin (2*d.val+1))
    (z : Fin (2*d.val+1) × BitSlot (recordWidth m g n) → Bool)
    (a : Fin n) (v i j : Fin g) (b : Fin a.val)
    (hz : unpack m g n (fieldsOfBits fun k => z (u,k)) = some (.inr ⟨a,v,b,i,j⟩)) (k : Fin 6) :
    value (fun t => (rowFrame m d h).eval z (u,.inr (k,t))) = requestValues u.val a b i j k := by
  simp only [rowFrame_eval]
  exact requestWordExpr_eval u.val (by have := u.isLt; have := d.isLt; omega) a v i j b _
    (unpack_eq_some_iff.mp hz) k

/-- The total AND/OR/NOT gate count is linear in the number of rows times a cubic
polynomial in the working width. -/
theorem rowFrame_size {n g : ℕ} (m : ℕ) (d : Fin n) (h : Fin g) :
    let w := workingWidth m g n
    (rowFrame m d h).size ≤ (2*d.val+1) * (2+6*w) * (300*(w+1)^2) := by
  let w := workingWidth m g n
  apply (Frame.step_size_le _ _ (300*(w+1)^2) ?_).trans
  · simp only [Frame.initial_size, zero_add, Fintype.card_prod, Fintype.card_fin, card_bitSlot]
    rfl
  · rintro ⟨u, flag | ⟨k,j⟩⟩ <;> rw [StatementCircuit.Expr.size_rename]
    · cases flag
      · exact localFlag_size ..
      · exact Nat.succ_le_of_lt (Nat.mul_pos (by decide) (pow_pos (Nat.succ_pos w) _))
    · exact requestWordExpr_size ..

end ParseRecords

end BorderVNP
end Computability
end OAI
