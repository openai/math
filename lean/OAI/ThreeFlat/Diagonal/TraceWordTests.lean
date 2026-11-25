import OAI.Computability.VPVNP.RAMProgram
import OAI.ThreeFlat.Diagonal.TraceFetchCircuit

namespace OAI
/-! # Local bit tests on a RAM register -/

namespace ThreeFlat.Diagonal.TraceWords

open BinPackingGames.Foundations.Complexity.CookLevin.StatementCircuit (Expr)
open Computability.VPVNP.BurstRAM

variable {σ : Type*} {w : ℕ}

/-- Little-endian bit representation of a machine word. -/
def bits (a : Word w) (j : Fin w) : Bool := a.val.testBit j.val

theorem bits_injective : Function.Injective (bits (w := w)) := by
  intro a b h
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j < w
  · exact congrFun h ⟨j,hj⟩
  · have hpow := Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.le_of_not_gt hj)
    rw [Nat.testBit_lt_two_pow (a.isLt.trans_le hpow), Nat.testBit_lt_two_pow (b.isLt.trans_le hpow)]

def allList : List (Expr σ) → Expr σ
  | [] => .const true
  | a :: l => a.and (allList l)

theorem allList_true (l : List (Expr σ)) (x : σ → Bool) :
    (allList l).eval x = true ↔ ∀ a ∈ l, a.eval x = true := by
  induction l with
  | nil => simp [allList, Expr.eval]
  | cons a l ih => simp [allList, Expr.eval, ih]

theorem allList_size_le (l : List (Expr σ)) {s : ℕ} (h : ∀ a ∈ l, a.size ≤ s) :
    (allList l).size ≤ l.length * (s + 1) + 1 := by
  induction l with
  | nil => simp [allList, Expr.size]
  | cons a l ih =>
    have ha := h a List.mem_cons_self
    have hl := ih fun b hb => h b (List.mem_cons_of_mem a hb)
    simp only [allList, Expr.size, List.length_cons, Nat.succ_mul]
    omega

def allBits {n : ℕ} (g : Fin n → Expr σ) : Expr σ := allList (List.ofFn g)

@[simp] theorem allBits_true {n : ℕ} (g : Fin n → Expr σ) (x : σ → Bool) :
    (allBits g).eval x = true ↔ ∀ i, (g i).eval x = true := by
  simp [allBits, allList_true, List.mem_ofFn]

theorem allBits_size_le {n s : ℕ} (g : Fin n → Expr σ) (h : ∀ i, (g i).size ≤ s) :
    (allBits g).size ≤ n * (s+1) + 1 := by
  simpa [allBits] using allList_size_le (List.ofFn g) (s := s) (by
    intro a ha
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp ha
    exact h i)

/-- Test equality of Boolean wires. -/
def same (a b : Expr σ) : Expr σ := Expr.mux a b (.not b)

@[simp] theorem same_true (a b : Expr σ) (x : σ → Bool) :
    (same a b).eval x = true ↔ a.eval x = b.eval x := by
  cases ha : a.eval x <;> cases hb : b.eval x <;> simp [same, ha, hb, Expr.eval]

theorem same_size (a b : Expr σ) : (same a b).size = 2*a.size + 2*b.size + 5 := by
  simp [same, Expr.mux, Expr.size]
  omega

def sameWord (a b : Fin w → Expr σ) : Expr σ := allBits fun j => same (a j) (b j)

@[simp] theorem sameWord_true (a b : Fin w → Expr σ) (x : σ → Bool) :
    (sameWord a b).eval x = true ↔ ∀ j, (a j).eval x = (b j).eval x := by
  simp [sameWord]

theorem sameWord_at {a b : Word w} (as bs : Fin w → Expr σ) (x : σ → Bool)
    (ha : ∀ j, (as j).eval x = bits a j) (hb : ∀ j, (bs j).eval x = bits b j) :
    (sameWord as bs).eval x = true ↔ a = b := by
  rw [sameWord_true]
  simpa [ha, hb, ← funext_iff] using (bits_injective (w := w)).eq_iff (a := a) (b := b)

theorem sameWord_size_le (a b : Fin w → Expr σ) {s t : ℕ} (ha : ∀ j, (a j).size ≤ s)
    (hb : ∀ j, (b j).size ≤ t) : (sameWord a b).size ≤ w * (2*s + 2*t + 6) + 1 := by
  apply allBits_size_le (s := 2*s + 2*t + 5)
  intro i
  rw [same_size]
  have := ha i
  have := hb i
  omega

end ThreeFlat.Diagonal.TraceWords

end OAI
