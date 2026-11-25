import OAI.LinearAlgebra.SpectralBooks.SignedProgram.SignedProgramUnary
import OAI.Computability.QuantumFactoring.BooleanFold

/-! # Boolean verification of a self-delimiting sequence of fields

The input bits, unary field indicators, and cursor guesses are supplied by wire
selectors or Boolean subcircuits. The verifier tests the value of each cursor
and every consumed input bit. An out-of-range transition always rejects.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

noncomputable section

namespace SignedProgram.Unary

open ExactQuantumFactoring BooleanNetwork
open scoped Classical

variable {n s m : ℕ}

def andOver {ι : Type*} [Fintype ι] (f : ι → BooleanNetwork m 1) : BooleanNetwork m 1 :=
  all (List.ofFn (fun i => f ((Fintype.equivFin ι).symm i)))

def orOver {ι : Type*} [Fintype ι] (f : ι → BooleanNetwork m 1) : BooleanNetwork m 1 :=
  any (List.ofFn (fun i => f ((Fintype.equivFin ι).symm i)))

theorem andOver_eval {ι : Type*} [Fintype ι] (f : ι → BooleanNetwork m 1) (x : Basis m) :
    (andOver f).eval x 0 = true ↔ ∀ i, (f i).eval x 0 = true := by
  simp only [andOver, all_eval, List.mem_ofFn, forall_exists_index, forall_apply_eq_imp_iff]
  exact (Fintype.equivFin ι).symm.forall_congr_right (q := fun i => (f i).eval x 0 = true)

theorem orOver_eval {ι : Type*} [Fintype ι] (f : ι → BooleanNetwork m 1) (x : Basis m) :
    (orOver f).eval x 0 = true ↔ ∃ i, (f i).eval x 0 = true := by
  simp only [orOver, any_eval, List.mem_ofFn, exists_exists_eq_and]
  exact (Fintype.equivFin ι).symm.exists_congr_right (q := fun i => (f i).eval x 0 = true)

theorem andOver_count {ι : Type*} [Fintype ι] {C : ℕ} (f : ι → BooleanNetwork m 1)
    (hf : ∀ i, (f i).net.count ≤ C) : (andOver f).net.count ≤ Fintype.card ι*(C+1)+1 := by
  apply (all_count _ (c := C) ?_).trans (by simp)
  intro a ha
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp ha
  exact hf _

theorem orOver_count {ι : Type*} [Fintype ι] {C : ℕ} (f : ι → BooleanNetwork m 1)
    (hf : ∀ i, (f i).net.count ≤ C) : (orOver f).net.count ≤ Fintype.card ι*(C+4)+1 := by
  apply (any_count _ (c := C) ?_).trans (by simp)
  intro a ha
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp ha
  exact hf _

private def equalBit (g : BooleanNetwork m 1) (b : Bool) := if b then g else g.bnot

private theorem equalBit_eval (g : BooleanNetwork m 1) (b : Bool) (x : Basis m) :
    (equalBit g b).eval x 0 = true ↔ g.eval x 0 = b := by cases b <;> simp [equalBit]

private theorem equalBit_count (g : BooleanNetwork m 1) (b : Bool) :
    (equalBit g b).net.count ≤ g.net.count + 1 := by cases b <;> simp [equalBit]

private def hot (markers : Fin (n+1) → BooleanNetwork m 1) (t : Fin (n+1)) :=
  andOver fun j => equalBit (markers j) (decide (j=t))

private theorem hot_eval (g : Fin (n+1) → BooleanNetwork m 1) (t : Fin (n+1)) (x : Basis m) :
    (hot g t).eval x 0 = true ↔ ∀ j, (g j).eval x 0 = true ↔ j = t := by
  rw [hot, andOver_eval]
  apply forall_congr'
  intro j
  rw [equalBit_eval, Bool.eq_iff_iff, decide_eq_true_eq]

private theorem hot_count (g : Fin (n+1) → BooleanNetwork m 1) (t : Fin (n+1)) {C : ℕ}
    (hg : ∀ i, (g i).net.count ≤ C) : (hot g t).net.count ≤ (n+1)*(C+2)+1 := by
  apply (andOver_count _ (C := C+1) (fun j => (equalBit_count _ _).trans (Nat.add_le_add_right (hg j) 1))).trans
  simp

/-- Bounds on the input and cursor domains prevent a field from running past the last bit. -/
private def matchWord (inp : Fin n → BooleanNetwork m 1) (b : Fin (n+1)) (z : Slot n)
    (hi : b.val + (emit z).length ≤ n) :=
  andOver fun j : Fin (emit z).length =>
    equalBit (inp ⟨b.val+j.val, by have := j.isLt; omega⟩) ((emit z)[j.val])

private theorem matchWord_eval (inp : Fin n → BooleanNetwork m 1) (b : Fin (n+1))
    (z : Slot n) (hi) (x : Basis m) :
    (matchWord inp b z hi).eval x 0 = true ↔
      emit z <+: (List.ofFn fun i => (inp i).eval x 0).drop b.val := by
  rw [matchWord, andOver_eval, List.prefix_iff_getElem]
  constructor
  · intro hf
    refine ⟨by simp only [List.length_drop, List.length_ofFn]; omega, fun j hj => ?_⟩
    rw [List.getElem_drop, List.getElem_ofFn]
    exact ((equalBit_eval _ _ _).mp (hf ⟨j,hj⟩)).symm
  · rintro ⟨_,h⟩ j
    apply (equalBit_eval _ _ _).mpr
    simpa only [List.getElem_drop, List.getElem_ofFn] using (h j j.isLt).symm

private theorem matchWord_count (inp : Fin n → BooleanNetwork m 1) (b : Fin (n+1)) (z : Slot n) (hi)
    {C : ℕ} (h : ∀ i, (inp i).net.count ≤ C) : (matchWord inp b z hi).net.count ≤ (n+1)*(C+2)+1 := by
  apply (andOver_count _ (C := C+1) (fun _ => (equalBit_count _ _).trans (Nat.add_le_add_right (h _) 1))).trans
  simp only [Fintype.card_fin]
  gcongr
  omega

/-- The Boolean wires supplied to the verifier. Each option-valued slot uses
one indicator for each possible value, including the disabled value. -/
structure Wires (m n s : ℕ) where
  input : Fin n → BooleanNetwork m 1
  field : Fin s → Slot n → BooleanNetwork m 1
  cursor : Fin (s+1) → Fin (n+1) → BooleanNetwork m 1

private def branch (W : Wires m n s) (i : Fin s) (b : Fin (n+1)) (z : Slot n) :
    BooleanNetwork m 1 :=
  if hb : b.val + (emit z).length ≤ n then
    (((W.cursor i.castSucc b).band (W.field i z)).band (matchWord W.input b z hb)).band
      (hot (W.cursor i.succ) ⟨_, Nat.lt_succ_iff.mpr hb⟩)
  else constant false

private theorem branch_eval (W : Wires m n s) (i : Fin s) (b : Fin (n+1)) (z : Slot n) (x : Basis m) :
    (branch W i b z).eval x 0 = true ↔
      (W.field i z).eval x 0 = true ∧ ∃ t, (W.cursor i.castSucc b).eval x 0 = true ∧
        Step (fun j => (W.input j).eval x 0) b t z ∧
        ∀ j, (W.cursor i.succ j).eval x 0 = true ↔ j = t := by
  by_cases hb : b.val + (emit z).length ≤ n
  · simp only [branch, hb, ↓reduceDIte, eval_band, Bool.and_eq_true, matchWord_eval, hot_eval, Step]
    constructor
    · rintro ⟨⟨⟨h1,h2⟩,h3⟩,h4⟩
      exact ⟨h2,_,h1,⟨rfl,h3⟩,h4⟩
    · rintro ⟨h2,t,h1,⟨ht,h3⟩,h4⟩
      have eq : t = ⟨_, Nat.lt_succ_iff.mpr hb⟩ := Fin.ext ht
      exact ⟨⟨⟨h1,h2⟩,h3⟩,eq ▸ h4⟩
  · simp only [branch, hb, ↓reduceDIte, eval_constant, Bool.false_eq_true, false_iff]
    rintro ⟨_,t,_,ht,_⟩
    exact hb (ht.1 ▸ Nat.lt_succ_iff.mp t.isLt)

def check (W : Wires m n s) : BooleanNetwork m 1 :=
  (hot (W.cursor 0) 0).band (andOver fun i => orOver fun b => orOver fun z => branch W i b z)

/-- Correctness holds on every proposed Boolean cursor array. Thus malformed
or multiply-marked cursor guesses also reject. -/
theorem check_correct (W : Wires m n s) (x : Basis m) (f : Fin s → Slot n)
    (hf : ∀ i z, (W.field i z).eval x 0 = true ↔ z = f i) :
    (check W).eval x 0 = true ↔ LocalCheck (fun j => (W.input j).eval x 0) f
      (fun i j => (W.cursor i j).eval x 0 = true) := by
  simp only [check, eval_band, Bool.and_eq_true, hot_eval, andOver_eval, orOver_eval,
    branch_eval, hf, exists_eq_left, LocalCheck]

private theorem branch_count (W : Wires m n s) (i : Fin s) (b : Fin (n+1)) (z : Slot n)
    {C : ℕ} (hi : ∀ j, (W.input j).net.count ≤ C) (hf : ∀ i z, (W.field i z).net.count ≤ C)
    (hc : ∀ i j, (W.cursor i j).net.count ≤ C) :
    (branch W i b z).net.count ≤ 2*C + 2*((n+1)*(C+2)+1) + 3 := by
  by_cases hb : b.val + (emit z).length ≤ n
  · rw [branch, dite_eq_left hb]
    simp only [count_band]
    have hm := matchWord_count _ _ _ hb hi
    have hh := hot_count (W.cursor i.succ) ⟨_, Nat.lt_succ_iff.mpr hb⟩ (hc i.succ)
    have := hf i z
    have := hc i.castSucc b
    omega
  · rw [branch, dite_eq_right hb, count_constant]
    omega

/-- The gate bound is cubic in input length, linear in slot count and linear
in the largest input-selector cost. -/
theorem check_count (W : Wires m n s) (C : ℕ)
    (hi : ∀ j, (W.input j).net.count ≤ C) (hf : ∀ i z, (W.field i z).net.count ≤ C)
    (hc : ∀ i j, (W.cursor i j).net.count ≤ C) :
    (check W).net.count ≤ 200*(s+1)*(n+2)^3*(C+1) := by
  let H := (n+1)*(C+2)+1
  let T := 2*C+2*H+3
  have hz i b : (orOver (fun z => branch W i b z)).net.count ≤ (n+2)*(T+4)+1 := by
    apply (orOver_count _ (C := T) (fun z => branch_count _ _ _ _ hi hf hc)).trans
    simp [Slot]
  have hb i : (orOver (fun b => orOver fun z => branch W i b z)).net.count ≤
      (n+1)*((n+2)*(T+4)+1+4)+1 := by
    simpa only [Fintype.card_fin] using orOver_count _ (hz i)
  have ha := andOver_count _ hb
  have hh := hot_count (W.cursor 0) 0 (hc 0)
  rw [check, count_band]
  simp only [Fintype.card_fin] at ha
  calc
    _ ≤ H + (s*((n+1)*((n+2)*(T+4)+1+4)+1+1)+1) + 1 :=
      Nat.add_le_add_right (Nat.add_le_add hh ha) 1
    _ ≤ _ := by
      dsimp only [H,T]
      zify
      rw [← sub_nonneg]
      ring_nf
      positivity

/-- A body of length `b` follows its `b+1`-bit header. The verifier reads
the last cursor at the resulting combined length, rejecting overflow. -/
def frameTest (frame last : Fin (n+1) → BooleanNetwork m 1) : BooleanNetwork m 1 :=
  orOver fun r : Fin (n+1) =>
    if h : 2*r.val+1 ≤ n then (frame r).band (last ⟨_,Nat.lt_succ_iff.mpr h⟩) else constant false

theorem frameTest_correct (frame last : Fin (n+1) → BooleanNetwork m 1) (x : Basis m)
    (r e : Fin (n+1)) (hr : ∀ j, (frame j).eval x 0 = true ↔ j = r)
    (he : ∀ j, (last j).eval x 0 = true ↔ j = e) :
    (frameTest frame last).eval x 0 = true ↔ e.val = 2*r.val+1 := by
  rw [frameTest, orOver_eval]
  constructor
  · rintro ⟨j,hj⟩
    by_cases h : 2*j.val+1 ≤ n
    · simp only [dite_eq_left h, eval_band, Bool.and_eq_true, hr, he] at hj
      obtain ⟨rfl,hh⟩ := hj
      exact (congrArg Fin.val hh).symm
    · simp only [dite_eq_right h, eval_constant, Bool.false_eq_true] at hj
  · intro hh
    have h : 2*r.val+1 ≤ n := hh ▸ Nat.lt_succ_iff.mp e.isLt
    exact ⟨r, by simp only [dite_eq_left h, eval_band, Bool.and_eq_true, hr, he, true_and]
                 exact Fin.ext hh.symm⟩

theorem frameTest_count (frame last : Fin (n+1) → BooleanNetwork m 1) {C : ℕ}
    (hr : ∀ i, (frame i).net.count ≤ C) (he : ∀ i, (last i).net.count ≤ C) :
    (frameTest frame last).net.count ≤ (n+1)*(2*C+5)+1 := by
  apply (orOver_count (f := fun r : Fin (n+1) => if h : 2*r.val+1 ≤ n then (frame r).band (last ⟨_,Nat.lt_succ_iff.mpr h⟩) else constant false) (C := 2*C+1) ?_).trans
  · simp
  · intro r
    by_cases h : 2*r.val+1 ≤ n
    · rw [dite_eq_left h, count_band]
      have := hr r
      have := he ⟨_,Nat.lt_succ_iff.mpr h⟩
      omega
    · rw [dite_eq_right h, count_constant]
      omega

end SignedProgram.Unary

end

end SpectralBooks
end LinearAlgebra
end OAI
