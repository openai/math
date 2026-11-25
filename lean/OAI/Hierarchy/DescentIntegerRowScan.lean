import OAI.Hierarchy.DescentGLNativeSelection
import Mathlib.Data.List.MinMax
import Mathlib.Data.Prod.Lex

namespace OAI
/-! # One scan for the least-index minimizing legal integer score -/

namespace Hierarchy.DescentGL

private abbrev ScoreKey (n : ℕ) := ℤ ×ₗ Fin n

/-- A mark excludes this row. Read its scored entry once if eligible, storing
both score and row index in the current best. Entry reads carry their actual cost. -/
def scanMeasured {n : ℕ} (masked : Vector Bool n) (read : Fin n → ℤ × ℕ) :
    List (Fin n) → Option (ScoreKey n) → Option (ScoreKey n) × ℕ
  | [],best => (best,0)
  | i::is,best =>
    let step := if masked[i.val] then (best,0) else
      let entry := read i
      (List.argAux (· < ·) best (toLex (entry.1,i)),entry.2)
    let rest := scanMeasured masked read is step.1
    (rest.1,rest.2+step.2+1)

def scanRows {n : ℕ} (masked : Vector Bool n) (score : Fin n → ℤ) :=
  scanMeasured masked (fun i => (score i,0))

def leastRowMeasured {n : ℕ} (masked : Vector Bool n) (read : Fin n → ℤ × ℕ) :
    Option (Fin n) × ℕ :=
  let scan := scanMeasured masked read (List.finRange n) none
  (scan.1.map (fun p => (ofLex p).2),scan.2)

def leastRow {n : ℕ} (masked : Vector Bool n) (score : Fin n → ℤ) : Option (Fin n) × ℕ :=
  leastRowMeasured masked (fun i => (score i,0))

theorem scanMeasured_cost_le {n cap : ℕ} (masked : Vector Bool n) (read : Fin n → ℤ × ℕ)
    (bound : ∀ i,(read i).2≤cap) (xs : List (Fin n)) (best : Option (ScoreKey n)) :
    (scanMeasured masked read xs best).2≤xs.length*(cap+1) := by
  induction xs generalizing best with
  | nil => simp [scanMeasured]
  | cons i xs ih =>
    cases eqn : masked[i.val] <;> simp only [scanMeasured,eqn,Bool.false_eq_true,ite_false,
      ite_true,List.length_cons,Nat.succ_mul]
    · have a := ih (List.argAux (· < ·) best (toLex ((read i).1,i)))
      have b := bound i
      omega
    · have a := ih best
      omega

theorem scanMeasured_same {n : ℕ} (masked : Vector Bool n) (read : Fin n → ℤ × ℕ)
    (xs : List (Fin n)) (best : Option (ScoreKey n)) :
    (scanMeasured masked read xs best).1=(scanRows masked (fun i => (read i).1) xs best).1 := by
  induction xs generalizing best with
  | nil => rfl
  | cons i xs ih =>
    cases eqn : masked[i.val] <;> simpa only [scanMeasured,scanRows,eqn,Bool.false_eq_true,
      ite_false,ite_true] using ih _

theorem leastRowMeasured_same {n : ℕ} (masked : Vector Bool n) (read : Fin n → ℤ × ℕ) :
    (leastRowMeasured masked read).1=(leastRow masked (fun i => (read i).1)).1 :=
  congrArg (Option.map fun p : ScoreKey n => (ofLex p).2) (scanMeasured_same masked read _ _)

theorem leastRowMeasured_bound {n cap : ℕ} (masked : Vector Bool n) (read : Fin n → ℤ × ℕ)
    (bound : ∀ i,(read i).2≤cap) : (leastRowMeasured masked read).2≤n*(cap+1) := by
  simpa only [leastRowMeasured,List.length_finRange] using
    scanMeasured_cost_le masked read bound (List.finRange n) none

theorem scanRows_cost {n : ℕ} (masked : Vector Bool n) (score : Fin n → ℤ)
    (xs : List (Fin n)) (best : Option (ScoreKey n)) : (scanRows masked score xs best).2=xs.length := by
  induction xs generalizing best with
  | nil => rfl
  | cons i xs ih =>
    cases e : masked[i.val] <;> simp only [scanRows,scanMeasured,e,Bool.false_eq_true,ite_false,
      ite_true,Nat.add_zero,List.length_cons] <;> exact congrArg (·+1) (ih _)

theorem leastRow_cost {n : ℕ} (masked : Vector Bool n) (score : Fin n → ℤ) :
    (leastRow masked score).2=n := by
  change (scanRows masked score (List.finRange n) none).2=n
  simp [scanRows_cost]

private theorem scanRows_fold {n : ℕ} (masked : Vector Bool n) (score : Fin n → ℤ)
    (xs : List (Fin n)) (best : Option (ScoreKey n)) :
    (scanRows masked score xs best).1 =
      ((xs.filter (fun i => !masked[i.val])).map (fun i => toLex (score i,i))).foldl
        (List.argAux (· < ·)) best := by
  induction xs generalizing best with
  | nil => rfl
  | cons i xs ih => cases h : masked[i.val] <;> simp only [scanRows,scanMeasured,h,List.filter_cons,Bool.false_eq_true,
      Bool.not_true,Bool.not_false,ite_true,ite_false,List.map_cons,List.foldl_cons] <;> exact ih _

/-- Any legal candidate with a minimal lexicographic key is returned.
The score is the first key and the binary row index breaks ties. -/
theorem leastRow_of_min {n : ℕ} (masked : Vector Bool n) (score : Fin n → ℤ) (a : Fin n)
    (legal : masked[a.val]=false)
    (best : ∀ b : Fin n, masked[b.val]=false →
      (toLex (score a,a) : ScoreKey n) ≤ toLex (score b,b)) :
    (leastRow masked score).1=some a := by
  let rows := ((List.finRange n).filter (fun i => !masked[i.val])).map (fun i => toLex (score i,i))
  have inside (i : Fin n) (hi : masked[i.val]=false) : toLex (score i,i)∈rows := by
    exact List.mem_map.mpr ⟨i,by simp [hi],rfl⟩
  have present := inside a legal
  have nonempty : rows ≠ [] := fun empty => by simp [empty] at present
  have fold_eq : (scanRows masked score (List.finRange n) none).1=rows.argmin id :=
    scanRows_fold _ _ _ _
  have notnone : rows.argmin id ≠ none := fun eqn => nonempty (List.argmin_eq_none.mp eqn)
  obtain ⟨winner,hw⟩ := Option.ne_none_iff_exists'.mp notnone
  have hw' : winner∈rows.argmin id := hw
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp (List.argmin_mem hw')
  have hi' : masked[i.val]=false := by simpa using (List.mem_filter.mp hi).2
  have small : toLex (score i,i) ≤ toLex (score a,a) :=
    List.le_of_mem_argmin present hw'
  have eqn := le_antisymm small (best i hi')
  have index : i=a := congrArg (fun p : ScoreKey n => (ofLex p).2) eqn
  change Option.map (fun p : ScoreKey n => (ofLex p).2) (scanRows masked score (List.finRange n) none).1 = _
  simp only [fold_eq,hw,Option.map_some]
  exact congrArg some index

/-- Integer comparisons agree with the real conditional objective, so the
array scan returns exactly the prescribed minimizer in the GL menu. -/
theorem leastRow_eq_chosenIndex {h k : ℕ} (hk : h<k) (base : Layout k)
    (masked : Vector Bool (2^k)) (score : Fin (2^k) → ℤ) (realScore : Row k → ℝ)
    (legal : ∀ a : Fin (2^k),masked[a.val]=false ↔ a∈legalMenu hk base)
    (compares : ∀ a b : Fin (2^k), score a≤score b ↔
      realScore ((rowIndex k).symm a) ≤ realScore ((rowIndex k).symm b)) :
    (leastRow masked score).1=some (chosenIndex hk base realScore) := by
  let a := chosenIndex hk base realScore
  have hi := DescentRowScore.nextRow_spec (legalMenu hk base) (legalMenu_nonempty hk base)
    (fun i => realScore ((rowIndex k).symm i))
  change a∈legalMenu hk base ∧ _ at hi
  refine leastRow_of_min masked score a ((legal a).mpr hi.1) ?_
  intro b hb
  have member := (legal b).mp hb
  have leq := (compares a b).mpr (hi.2.1 b member)
  apply Prod.Lex.toLex_le_toLex.mpr
  rcases leq.lt_or_eq with strict | tie
  · exact Or.inl strict
  · exact Or.inr ⟨tie,hi.2.2 b member (le_antisymm ((compares b a).mp tie.ge) (hi.2.1 b member))⟩

end Hierarchy.DescentGL

end OAI
