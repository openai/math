import OAI.ThreeFlat.Diagonal.TraceWordOrder
import OAI.ThreeFlat.Diagonal.TraceRowCode
import OAI.Computability.VPVNP.LiveHeaderBits

namespace OAI
/-! # Terminal scalars from addressed CPU-row bits -/

namespace ThreeFlat.Diagonal.TraceTerminal

open BinPackingGames.Foundations.Complexity.CookLevin.StatementCircuit (Expr)
open Computability.VPVNP.BurstRAM TraceWords
open Computability.VPVNP.VerifierNetwork (Frame)

variable {σ F : Type*} [Fintype F] {w : ℕ}

private def literal {n : ℕ} (v : Word n) (j : Fin n) : Expr σ := .const (bits v j)

/-- Valid field IDs form the initial segment of the word space of length
`card F`. If the whole space is occupied every ID is valid. -/
private def validWord (size : ℕ) (data : Fin w → Expr σ) : Expr σ :=
  if hs : size < 2^w then lessWord data (literal ⟨size,hs⟩) else .const true

private theorem validWord_at (size : ℕ) (data : Fin w → Expr σ) (x : σ → Bool) (d : Word w)
    (h : ∀ j, (data j).eval x = bits d j) :
    (validWord size data).eval x = decide (d.val < size) := by
  by_cases hs : size < 2^w
  · simp only [validWord, dite_true, hs]
    have e : d < (⟨size,hs⟩ : Word w) ↔ d.val < size := Iff.rfl
    rw [lessWord_at data (literal ⟨size,hs⟩) x d ⟨size,hs⟩ h (fun _ => rfl)]
    exact Bool.eq_iff_iff.mpr (by simpa only [decide_eq_true_eq] using e)
  · simp [validWord, hs, Expr.eval, show d.val < size from d.isLt.trans_le (Nat.le_of_not_gt hs)]

/-- The `none` output detects an invalid return. Each field-labeled output
detects a return of that field element. Only the word-tag and data pins are read. -/
noncomputable def flag [Zero F] (hF : Fintype.card F ≤ 2^w)
    (returnTag : Word (w+1)) (tag : Fin (w+1) → Expr σ) (data : Fin w → Expr σ) :
    Option F → Expr σ
  | none => .or (.not (sameWord tag (literal returnTag))) (validWord (Fintype.card F) data)
  | some a => .and (sameWord tag (literal returnTag))
      (sameWord data (literal ((RAM.FieldCode.ofCardLe hF).encode a)))

theorem flag_eval [Zero F] (hF : Fintype.card F ≤ 2^w)
    (returnTag t : Word (w+1)) (d : Word w) (tag : Fin (w+1) → Expr σ) (data : Fin w → Expr σ)
    (x : σ → Bool) (ht : ∀ j, (tag j).eval x = bits t j)
    (hd : ∀ j, (data j).eval x = bits d j) :
    ∀ i, (flag hF returnTag tag data i).eval x = match i with
      | none => decide (t ≠ returnTag ∨ d.val < Fintype.card F)
      | some a => decide (t = returnTag ∧ d = (RAM.FieldCode.ofCardLe hF).encode a) := by
  have eq (n : ℕ) (a b : Word n) (as : Fin n → Expr σ) (h : ∀ j, (as j).eval x = bits a j) :
      (sameWord as (literal b)).eval x = decide (a = b) :=
    Bool.eq_iff_iff.mpr (by simpa only [decide_eq_true_eq] using sameWord_at as (literal b) x h (fun _ => rfl))
  intro i
  cases i <;> simp [flag, Expr.eval, eq _ t returnTag tag ht, validWord_at _ _ x d hd, eq _ d _ data hd]

/-- One unary scalar table per flag. The validity table annihilates invalid
returns and a true element flag contributes its field element. -/
def unary [Zero F] [One F] : Option F → Bool → F
  | none, b => if b then 1 else 0
  | some a, b => if b then a else 1

theorem product_eval [CommSemiring F] (hF : Fintype.card F ≤ 2^w)
    (returnTag t : Word (w+1)) (d : Word w) (tag : Fin (w+1) → Expr σ) (data : Fin w → Expr σ)
    (x : σ → Bool) (ht : ∀ j, (tag j).eval x = bits t j)
    (hd : ∀ j, (data j).eval x = bits d j) :
    (∏ i : Option F, unary i ((flag hF returnTag tag data i).eval x)) =
      if t = returnTag then (RAM.FieldCode.ofCardLe hF).decode d else 1 := by
  classical
  rw [Fintype.prod_option]
  simp only [flag_eval hF returnTag t d tag data x ht hd, unary, decide_eq_true_eq]
  by_cases he : t = returnTag
  · by_cases hs : d.val < Fintype.card F
    · let a := (Fintype.equivFin F).symm ⟨d.val,hs⟩
      have ha : d = (RAM.FieldCode.ofCardLe hF).encode a := by
        apply Fin.ext
        simp [a]
      have inj := Function.LeftInverse.injective (RAM.FieldCode.ofCardLe hF).decode_encode
      have hmatch (b : F) : d = (RAM.FieldCode.ofCardLe hF).encode b ↔ a = b :=
        ha ▸ inj.eq_iff
      have hdec : (RAM.FieldCode.ofCardLe hF).decode d = a := by
        rw [ha, RAM.FieldCode.decode_encode]
      simp [he, hs, hmatch, hdec]
    · simp [he, hs, RAM.FieldCode.decode_of_card_le hF d (Nat.le_of_not_gt hs)]
  · simp [he]

theorem flag_size [Zero F] (hF : Fintype.card F ≤ 2^w) (returnTag : Word (w+1))
    (tag : Fin (w+1) → Expr σ) (data : Fin w → Expr σ)
    (ht : ∀ j, (tag j).size ≤ 1) (hd : ∀ j, (data j).size ≤ 1) (i : Option F) :
    (flag hF returnTag tag data i).size ≤ 34*(w+1)+4 := by
  have hl {n : ℕ} (v : Word n) (j : Fin n) : (literal (σ := σ) v j).size ≤ 1 := by rfl
  have he := sameWord_size_le tag (literal returnTag) ht (hl _)
  cases i with
  | none =>
    have hc : (validWord (Fintype.card F) data).size ≤ w*24+1 := by
      unfold validWord
      split
      · rename_i hc
        exact lessWord_size data (literal (⟨Fintype.card F,hc⟩ : Word w)) (s := 1) hd (hl _)
      · simp [Expr.size]
    simp only [flag, Expr.size]
    omega
  | some a =>
    have he' := sameWord_size_le data (literal ((RAM.FieldCode.ofCardLe hF).encode a)) hd (hl _)
    simp only [flag, Expr.size]
    omega

/-- Reusable finite Boolean frame for the unary tables, with one live wire per table. -/
noncomputable def frame [Zero F] [Fintype σ] (hF : Fintype.card F ≤ 2^w) (returnTag : Word (w+1))
    (tag : Fin (w+1) → σ) (data : Fin w → σ) : Frame σ (Option F) :=
  (Frame.initial (id : σ → σ)).step (flag hF returnTag (.input ∘ tag) (.input ∘ data))

theorem frame_size [Zero F] [Fintype σ] (hF : Fintype.card F ≤ 2^w) (returnTag : Word (w+1))
    (tag : Fin (w+1) → σ) (data : Fin w → σ) :
    (frame hF returnTag tag data).size ≤ (Fintype.card F+1)*(34*(w+1)+4) := by
  simpa [frame] using (Frame.initial (id : σ → σ)).step_size_le
    (flag hF returnTag (.input ∘ tag) (.input ∘ data)) (34*(w+1)+4)
    (fun i => flag_size hF returnTag (.input ∘ tag) (.input ∘ data) (fun _ => by rfl) (fun _ => by rfl) i)

open TraceRows TraceBanks Computability.VPVNP.RAMSerialization

variable {p r : ℕ}

/-- Flattened little-endian header pin within the row format. -/
def headerAddr (r : ℕ) (i : Fin 5) (j : Fin (w+1)) : Fin ((5+r)*(w+1)) :=
  finProdFinEquiv (i.castAdd r,j)

theorem headerAddr_read (hw : 3 ≤ w+1) (hp : p ≤ 2^(w+1))
    (row : Row (w+1) (Snapshot w p r)) (i : Fin 5) (j : Fin (w+1)) :
    (rowFormat hw hp).encode row (headerAddr r i j) = bits (header hw hp row i) j := by
  rw [Format.encode, headerAddr, arrayBits_at, rowFormat_header]
  exact (Computability.VPVNP.LiveHeader.testBit_wordBits _ _).symm

/-- The top bit is dropped by the exposed machine's terminal decoder. -/
theorem narrow_bits (v : Word (w+1)) (j : Fin w) :
    bits (narrow v) j = bits v j.castSucc := by
  simp [bits, narrow, Fin.ofNat, Nat.testBit_mod_two_pow, j.isLt]

noncomputable def rowFrame [Zero F] (hF : Fintype.card F ≤ 2^w) (hw : 3 ≤ w+1) (r : ℕ) :
    Frame (Fin ((5+r)*(w+1))) (Option F) :=
  frame hF (tagWord hw 7) (headerAddr r 0) (fun j => headerAddr r 4 j.castSucc)

theorem rowFrame_size [Zero F] (hF : Fintype.card F ≤ 2^w) (hw : 3 ≤ w+1) (r : ℕ) :
    (rowFrame hF hw r).size ≤ (Fintype.card F+1)*(34*(w+1)+4) :=
  frame_size ..

/-- On every canonical CPU row, the unary cells multiply to the factor used
by the weighted path product. This includes invalid IDs and all non-return
rows. -/
theorem rowFrame_eval [CommSemiring F] (hF : Fintype.card F ≤ 2^w) (hw : 3 ≤ w+1)
    (hp : p ≤ 2^(w+1)) (row : Row (w+1) (Snapshot w p r)) :
    (∏ i : Option F, unary i ((rowFrame hF hw r).eval ((rowFormat hw hp).encode row) i)) =
      match row with
      | .halt _ out => (wideCode (RAM.FieldCode.ofCardLe hF)).terminal out
      | _ => 1 := by
  let x := (rowFormat hw hp).encode row
  have he : (Frame.initial (id : Fin ((5+r)*(w+1)) → _)).eval x = x := funext fun i => by simp
  change (∏ i : Option F, unary i ((rowFrame hF hw r).eval x i)) = _
  simp only [rowFrame, frame, Frame.step_eval, he]
  rw [product_eval hF (tagWord hw 7) (header hw hp row 0) (narrow (header hw hp row 4))
    (.input ∘ headerAddr r 0) (.input ∘ fun j => headerAddr r 4 j.castSucc) x
    (fun j => headerAddr_read hw hp row 0 j)
    (fun j => (headerAddr_read hw hp row 4 j.castSucc).trans (narrow_bits _ _).symm)]
  cases row with
  | pad => simp [header, tagWord, Fin.ext_iff]
  | halt s out =>
    cases out <;> simp [header, tagWord, Fin.ext_iff, wideCode, RAM.FieldCode.terminal]
  | move s e =>
    cases e with
    | choice b => cases b <;> simp [header, tagWord, Fin.ext_iff]
    | tick | read | write => simp [header, tagWord, Fin.ext_iff]

end ThreeFlat.Diagonal.TraceTerminal

end OAI
