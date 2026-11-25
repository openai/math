import Mathlib.Tactic

namespace OAI
/-! # Ordered thin packs of indivisible vertex occurrences -/

namespace Hierarchy.DescentPacking

variable {I : Type*}

def amount (load : I → ℕ) (xs : List I) := (xs.map load).sum

/-- The head of the accumulator is the unique unfinished pack. Reading from
right to left preserves the order of both the packs and the old occurrences
inside every pack. -/
def thinPacks (load : I → ℕ) (B : ℕ) : List I → List (List I)
  | [] => []
  | x::xs =>
    match thinPacks load B xs with
    | [] => [[x]]
    | p::ps =>
      if B≤amount load p then [x]::p::ps
      else (x::p)::ps

theorem thinPacks_flatten (load : I → ℕ) (B : ℕ) (xs : List I) :
    (thinPacks load B xs).flatten=xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [thinPacks]
    cases h : thinPacks load B xs with
    | nil => simpa [h] using congrArg (fun z => x::z) ih
    | cons p ps =>
      rw [h] at ih
      change (if B≤amount load p then [x]::p::ps else (x::p)::ps).flatten=x::xs
      split <;> simp [←ih]

theorem thinPacks_small (load : I → ℕ) {B : ℕ} (xs : List I) (small : ∀x∈xs,load x≤B) :
    ∀p∈thinPacks load B xs, amount load p≤2*B := by
  induction xs with
  | nil => simp [thinPacks]
  | cons x xs ih =>
    have one := small x List.mem_cons_self
    have tailSmall := ih (fun i hi => small i (List.mem_cons_of_mem _ hi))
    simp only [thinPacks]
    cases h : thinPacks load B xs with
    | nil => simpa [amount] using (show load x≤2*B by omega)
    | cons p ps =>
      rw [h] at tailSmall
      change ∀z∈(if B≤amount load p then [x]::p::ps else (x::p)::ps), amount load z≤2*B
      split <;> rename_i test
      · simpa [amount] using And.intro (show amount load [x]≤2*B by simp [amount]; omega) tailSmall
      · intro z hz
        rcases List.mem_cons.mp hz with rfl | hp
        · simp only [amount,List.map_cons,List.sum_cons]
          change load x+amount load p≤2*B
          omega
        · exact tailSmall _ (List.mem_cons_of_mem _ hp)

theorem thinPacks_closed (load : I → ℕ) (B : ℕ) (xs : List I) :
    ∀p∈(thinPacks load B xs).tail, B≤amount load p := by
  induction xs with
  | nil => simp [thinPacks]
  | cons x xs ih =>
    rw [thinPacks]
    cases h : thinPacks load B xs with
    | nil => simp
    | cons p ps =>
      rw [h] at ih
      change ∀z∈(if B≤amount load p then [x]::p::ps else (x::p)::ps).tail,B≤amount load z
      split <;> simp_all

private theorem enough (load : I → ℕ) (B : ℕ) (ys : List (List I))
    (full : ∀s∈ys,B≤amount load s) : ys.length*B≤amount load ys.flatten := by
  induction ys with
  | nil => simp [amount]
  | cons p ps ih =>
    have rest := ih (fun z hz => full z (List.mem_cons_of_mem _ hz))
    have head := full p List.mem_cons_self
    simp [amount,List.map_append,List.sum_append,Nat.succ_mul] at *
    omega

/-- A colony of total load at most AB has at most A+1 actual thin packs.
The possible unfinished pack, including a zero-load collection, is counted. -/
theorem thinPacks_count (load : I → ℕ) {A B : ℕ} (positive : 0<B) (xs : List I)
    (total : amount load xs≤A*B) : (thinPacks load B xs).length≤A+1 := by
  have closed := thinPacks_closed load B xs
  have flat := thinPacks_flatten load B xs
  cases h : thinPacks load B xs with
  | nil => simp
  | cons p ps =>
    rw [h] at closed flat
    have bound := enough load B ps closed
    have tail : amount load ps.flatten≤amount load xs := by
      rw [←flat]
      simp [amount,List.map_append,List.sum_append]
    have cnt := Nat.le_of_mul_le_mul_right ((bound.trans tail).trans total) positive
    simpa using Nat.succ_le_succ cnt

end Hierarchy.DescentPacking

end OAI
