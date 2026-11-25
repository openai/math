import OAI.Computability.BorderVNP.FiniteOutputProduct
import OAI.Computability.BorderVNP.TeamPrivateValue

/-! # Selecting a field-valued private return in §7.2

Select one numbered field element by binary choices. The ordinary private tape
verifier then checks that the native accepting halt returns that element. Each
accepted path has a unique successful selection. A zero return still has its
successful verifier path and contributes zero to the field sum.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FieldSelect

open VPVNP.RAMTape TeamPrivateTape TeamPrivateValue
open scoped BigOperators

variable {F : Type*} [Field F] [Fintype F] {Q Γ : Type} {m : ℕ}

/-- Native field return can depend on the final control, scanned symbols, and sign flag. -/
abbrev Return (Q Γ F : Type*) (m : ℕ) := Q → (Fin m → Γ) → Bool → F

/-- Accept a native halt exactly in its selected output class. A source rejection
remains a rejection in every class. -/
noncomputable def selectTable (P : TapeTable Q Γ m) (w : Return Q Γ F m) (v : F) :
    TapeTable Q Γ m := by
  classical
  exact fun q h => match P q h with
    | .halt ok sign => .halt (ok && decide (w q h sign = v)) false
    | .one c => .one c
    | .two l r => .two l r

/-- The field-valued sum over the native multitape paths, with arbitrary finite
field output for each accepting halt. -/
def tapeValue (P : TapeTable Q Γ m) (blank : Γ) (w : Return Q Γ F m) :
    ℕ → Q → (Fin m → SymbolTape Γ) → F
  | 0, _, _ => 0
  | t+1, q, ts => match P q (fun i => (ts i).head) with
    | .halt ok sign => if ok then w q (fun i => (ts i).head) sign else 0
    | .one c => tapeValue P blank w t c.next (c.apply blank ts)
    | .two l r => tapeValue P blank w t l.next (l.apply blank ts) + tapeValue P blank w t r.next (r.apply blank ts)

omit [Field F] [Fintype F] in
/-- Selecting an output class has no effect on the native path clock. -/
theorem stops_iff (P : TapeTable Q Γ m) (blank : Γ) (w : Return Q Γ F m)
    (t : ℕ) (q : Q) (ts : Fin m → SymbolTape Γ) (v : F) :
    TapeStops (selectTable P w v) blank t q ts ↔ TapeStops P blank t q ts := by
  induction t generalizing q ts with
  | zero => rfl
  | succ t ih =>
    rw [TapeStops, TapeStops]
    cases h : P q (fun i => (ts i).head) <;> simp only [selectTable, h, ih]

/-- Partitioning the signed verifier sums by the actual finite field output recovers
the native path sum, including repeated branches arriving at the same halt. -/
theorem tapeValue_eq_select (P : TapeTable Q Γ m) (blank : Γ) (w : Return Q Γ F m)
    (t : ℕ) (q : Q) (ts : Fin m → SymbolTape Γ) :
    tapeValue P blank w t q ts = ∑ v : F, (tapePaths (selectTable P w v) blank t q ts : F) * v := by
  classical
  induction t generalizing q ts with
  | zero => simp [tapeValue,tapePaths]
  | succ t ih =>
    rw [tapeValue]
    cases hp : P q (fun i => (ts i).head) with
    | halt ok sg =>
      cases ok <;> simp [tapePaths, selectTable, hp, TeamTape.haltWeight, ite_mul]
    | one cmd => simpa only [tapePaths, selectTable, hp] using ih _ _
    | two l r => simp only [tapePaths, selectTable, hp, Int.cast_add, add_mul, Finset.sum_add_distrib, ih]

variable {K S : Type} [DecidableEq K] {k : ℕ}

/-- Selector phase or a verifier running in the selected class. -/
inductive State (k : ℕ) (S : Type) where
  | select (remaining : Fin (k+1))
  | body (idx : Fin k) (q : S)
  deriving Fintype

/-- Guess at most one output class and run its ordinary bounded verifier. The
unused final selector branch rejects without producing an additional value. -/
def code (program : Fin k → StackCode K S) (start : S) : StackCode K (State k S)
  | .select j => if h : j.val = 0 then .halt false else
      let i : Fin k := ⟨j.val-1,by have := j.isLt; omega⟩
      .choose (.body i start) (.select i.castSucc)
  | .body i q => (program i q).rename id (.body i)

/-- Only a successful verifier halt supplies a field output. -/
def output (w : Fin k → S → F) : State k S → F
  | .select _ => 0
  | .body i q => w i q

omit [Fintype F] in
private theorem body_value (p : Fin k → StackCode K S) (w : Fin k → S → F) (start : S)
    (t : ℕ) (i : Fin k) (q : S) (s : Stacks K) :
    FieldStack.paths (code p start) (output w) t (.body i q) s = FieldStack.paths (p i) (w i) t q s := by
  induction t generalizing q s with
  | zero => rfl
  | succ t ih => cases h : p i q <;> simp [FieldStack.paths, code, h, StackOp.rename, ih, output]

omit [Fintype F] in
/-- Each numbered class occurs once, and the fixed number of choice steps is
sufficient for every class verifier's unchanged physical budget. -/
theorem selection_value (p : Fin k → StackCode K S) (w : Fin k → S → F) (start : S)
    (s : Stacks K) (target : Fin k → F) (budget : ℕ)
    (each : ∀ i, ∀ ticks ≥ budget, FieldStack.paths (p i) (w i) ticks start s = target i) :
    ∀ j (hj : j ≤ k) ticks, budget+j ≤ ticks →
      FieldStack.paths (code p start) (output w) ticks (.select ⟨j,by omega⟩) s =
        ∑ i : Fin j, target (i.castLE hj) := by
  intro j
  induction j with
  | zero => intro hj ticks _; cases ticks <;> simp [FieldStack.paths, code]
  | succ j ih =>
    intro hj ticks hb
    obtain ⟨ticks,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : ticks ≠ 0)
    let i : Fin k := ⟨j,by omega⟩
    change FieldStack.paths (code p start) (output w) (ticks+1) (.select i.succ) s = _
    simp only [FieldStack.paths, code, Fin.val_succ, Nat.succ_ne_zero, dite_false, Nat.add_sub_cancel]
    rw [body_value, each _ ticks (by omega), Fin.sum_univ_castSucc]
    have h := ih (by omega : j ≤ k) ticks (by omega)
    exact (congrArg (target i + ·) h).trans (add_comm ..)

omit [Fintype F] in
/-- Multiplying each selected signed path by a fixed field element commutes with
the bounded stack semantics, with no division in characteristic two. -/
theorem signed_scalar (p : StackCode K S) (neg : S → Bool) (v : F) (t : ℕ) (q : S) (s : Stacks K) :
    FieldStack.paths p (fun r => if neg r then -v else v) t q s =
      (TeamStack.paths p neg t q s : F) * v := by
  induction t generalizing q s with
  | zero => simp [FieldStack.paths,TeamStack.paths]
  | succ t ih =>
    cases hp : p q with
    | push | pop | goto => simpa only [FieldStack.paths,TeamStack.paths,hp] using ih _ _
    | choose l r => simp [FieldStack.paths,TeamStack.paths,hp,ih,add_mul]
    | halt ok => cases ok <;> cases hn : neg q <;> simp [FieldStack.paths,TeamStack.paths,hp,hn,TeamTape.haltWeight]

end FieldSelect

end BorderVNP
end Computability
end OAI
