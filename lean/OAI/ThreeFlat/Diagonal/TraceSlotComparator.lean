import OAI.ThreeFlat.Diagonal.TraceWordOrder
import OAI.ThreeFlat.Diagonal.TraceSlotOrder

namespace OAI
/-! # Gate verification of a bitonic comparator on two transcript records -/

namespace ThreeFlat.Diagonal.TraceSlots

open Computability.VPVNP.BurstRAM Computability.VPVNP.RAMSerialization
open Computability.VPVNP.VerifierNetwork (Frame)
open BinPackingGames.Foundations.Complexity.CookLevin.StatementCircuit (Expr)
open TraceWords

variable {w : ℕ}

/-- Two old slots followed by the two proposed output slots. Each field has
exactly `w` binary pins. -/
abbrev Pin (w : ℕ) := Fin 4 × Fin 7 × Fin w

def word (s : Fin 4) (f : Fin 7) (i : Fin w) : Expr (Pin w) := .input (s,f,i)

def lexCheck (a b : Fin 4) : List (Fin 7) → Expr (Pin w)
  | [] => .const false
  | i :: l => (lessWord (word a i) (word b i)).or
      ((sameWord (word a i) (word b i)).and (lexCheck a b l))

def Represents (hw : 2 ≤ w) (x : Pin w → Bool) (s : Fin 4) (r : Option (WordRecord w)) : Prop :=
  ∀ f i, x (s,f,i) = bits (fields hw r f) i

theorem lexCheck_true (hw : 2 ≤ w) (x : Pin w → Bool) (a b : Fin 4)
    (ra rb : Option (WordRecord w)) (ha : Represents hw x a ra) (hb : Represents hw x b rb)
    (l : List (Fin 7)) :
    (lexCheck a b l).eval x = true ↔ keyLess (fields hw ra) (fields hw rb) l := by
  induction l with
  | nil => simp [lexCheck, keyLess, Expr.eval]
  | cons i l ih =>
    have hlt := lessWord_at (word a i) (word b i) x _ _ (ha i) (hb i)
    have he := sameWord_at (word a i) (word b i) x (ha i) (hb i)
    simp [lexCheck, keyLess, Expr.eval, hlt, he, ih]

def sameSlot (a b : Fin 4) : Expr (Pin w) :=
  allBits fun f => sameWord (word a f) (word b f)

theorem sameSlot_at (hw : 2 ≤ w) (x : Pin w → Bool) (a b : Fin 4) (r : Option (WordRecord w))
    (hb : Represents hw x b r) :
    (sameSlot a b).eval x = true ↔ Represents hw x a r := by
  unfold Represents at hb ⊢
  simp [sameSlot, sameWord_true, word, Expr.eval, hb]

/-- Test both complete proposed outputs, including the padding bits. -/
def compareSwap : Expr (Pin w) :=
  Expr.mux (lexCheck 1 0 keyIndices)
    ((sameSlot 2 1).and (sameSlot 3 0)) ((sameSlot 2 0).and (sameSlot 3 1))

theorem compareSwap_at (hw : 2 ≤ w) (x : Pin w → Bool)
    (a b : Option (WordRecord w)) (ha : Represents hw x 0 a) (hb : Represents hw x 1 b) :
    compareSwap.eval x = true ↔
      Represents hw x 2 (if toOrdered b < toOrdered a then b else a) ∧
      Represents hw x 3 (if toOrdered b < toOrdered a then a else b) := by
  have lt := (lexCheck_true hw x 1 0 b a hb ha keyIndices).trans (keyLess_iff hw b a)
  simp [compareSwap, lt, Expr.eval_mux]
  split <;> simp [Expr.eval, sameSlot_at hw x _ _ a ha, sameSlot_at hw x _ _ b hb]

theorem lexCheck_size (a b : Fin 4) (l : List (Fin 7)) :
    (lexCheck (w := w) a b l).size ≤ l.length * (34*w+4) + 1 := by
  induction l with
  | nil => simp [lexCheck, Expr.size]
  | cons i l ih =>
    have hl := lessWord_size (word (w := w) a i) (word b i) (s := 1)
      (fun _ => le_rfl) (fun _ => le_rfl)
    have he := sameWord_size_le (word (w := w) a i) (word b i) (s := 1) (t := 1)
      (fun _ => le_rfl) (fun _ => le_rfl)
    rw [List.length_cons, Nat.succ_mul]
    simp only [lexCheck, Expr.size]
    omega

theorem sameSlot_size (a b : Fin 4) : (sameSlot (w := w) a b).size ≤ 7*(10*w+2)+1 := by
  apply allBits_size_le (s := 10*w+1)
  intro i
  have h := sameWord_size_le (word (w := w) a i) (word b i) (s := 1) (t := 1)
    (fun _ => le_rfl) (fun _ => le_rfl)
  omega

theorem compareSwap_size (w : ℕ) : (compareSwap (w := w)).size ≤ 800*(w+1) := by
  have hc := lexCheck_size (w := w) 1 0 keyIndices
  have h₁ := sameSlot_size (w := w) 2 1
  have h₂ := sameSlot_size (w := w) 3 0
  have h₃ := sameSlot_size (w := w) 2 0
  have h₄ := sameSlot_size (w := w) 3 1
  change _ ≤ 7*(34*w+4)+1 at hc
  simp only [compareSwap, Expr.mux, Expr.size]
  omega

noncomputable def comparatorFrame (w : ℕ) : Frame (Pin w) Unit :=
  (Frame.initial id).step fun _ => compareSwap

noncomputable def comparatorCircuit (w : ℕ) := (comparatorFrame w).circuit ()

theorem comparatorCircuit_size (w : ℕ) :
    (comparatorFrame w).circuitSize () ≤ 3200*(w+1) := by
  have h := (comparatorFrame w).circuitSize_le ()
  have q := (Frame.initial (id : Pin w → Pin w)).step_size_le (fun _ : Unit => compareSwap)
    (800*(w+1)) (fun _ => compareSwap_size w)
  simp only [Frame.initial_size, Fintype.card_unit, one_mul, zero_add] at q
  change (comparatorFrame w).size ≤ 800*(w+1) at q
  omega

theorem comparatorCircuit_at (hw : 2 ≤ w) (x : Pin w → Bool)
    (a b : Option (WordRecord w)) (ha : Represents hw x 0 a) (hb : Represents hw x 1 b) :
    (comparatorCircuit w).eval x = true ↔
      Represents hw x 2 (if toOrdered b < toOrdered a then b else a) ∧
      Represents hw x 3 (if toOrdered b < toOrdered a then a else b) := by
  have hi : (Frame.initial (id : Pin w → Pin w)).eval x = x := funext (fun i => Frame.initial_eval id x i)
  simpa [comparatorCircuit, comparatorFrame, hi] using compareSwap_at hw x a b ha hb

/-- A physical pin block is the unique encoding of a given sorted record. -/
def RepresentsOrdered (hw : 2 ≤ w) (x : Pin w → Bool) (s : Fin 4)
    (r : Computability.VPVNP.RAMMemory.OrderedSlot (Word w)) : Prop :=
  ∃ t, toOrdered t = r ∧ Represents hw x s t

theorem representsOrdered_iff (hw : 2 ≤ w) (x : Pin w → Bool) (s : Fin 4)
    (r : Option (WordRecord w)) : RepresentsOrdered hw x s (toOrdered r) ↔ Represents hw x s r := by
  constructor
  · rintro ⟨t,h,ht⟩
    have he := congrArg Computability.VPVNP.RAMMemory.OrderedSlot.record h
    have hr : t = r := by cases t <;> cases r <;> simp_all [toOrdered, WordRecord.record_injective.eq_iff]
    simpa [hr] using ht
  · exact fun hr => ⟨r,rfl,hr⟩

/-- The bit-level AND/NOT verifier recognizes precisely the min/max pair in
the same order used by the bitonic network on whole memory records. -/
theorem comparatorCircuit_min_max (hw : 2 ≤ w) (x : Pin w → Bool)
    (a b : Option (WordRecord w)) (ha : Represents hw x 0 a) (hb : Represents hw x 1 b) :
    (comparatorCircuit w).eval x = true ↔
      RepresentsOrdered hw x 2 (min (toOrdered a) (toOrdered b)) ∧
      RepresentsOrdered hw x 3 (max (toOrdered a) (toOrdered b)) := by
  rw [comparatorCircuit_at hw x a b ha hb]
  by_cases h : toOrdered b < toOrdered a
  · simp [h, min_eq_right h.le, max_eq_left h.le, representsOrdered_iff]
  · have hab := le_of_not_gt h
    simp [h, min_eq_left hab, max_eq_right hab, representsOrdered_iff]

end ThreeFlat.Diagonal.TraceSlots

end OAI
