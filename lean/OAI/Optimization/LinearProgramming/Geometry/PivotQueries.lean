import Mathlib.Data.Fin.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Logic.Function.Basic

/-! Finite rational query trees used when a minor-compression request may restart an oracle run. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Geometry

/-- A continuing answer is a rational. The external oracle may interrupt at every request. -/
inductive MinorQuery (κ α : Type*) where
  | done (x : α)
  | query (key : κ) (next : ℚ → MinorQuery κ α)

namespace MinorQuery

variable {κ α β : Type*}

def bind (p : MinorQuery κ α) (k : α → MinorQuery κ β) : MinorQuery κ β :=
  match p with
  | .done x => k x
  | .query key next => .query key (fun y => (next y).bind k)

def eval (assign : κ → ℚ) : MinorQuery κ α → α
  | .done x => x
  | .query key next => eval assign (next (assign key))

@[simp] theorem eval_bind (p : MinorQuery κ α) (k : α → MinorQuery κ β) (f : κ → ℚ) :
    eval f (p.bind k) = eval f (k (eval f p)) := by
  induction p with
  | done => rfl
  | query a next ih => exact ih (f a)

/-- Both successful answers and the request triggering an interruption occur in sequence. -/
inductive Run : MinorQuery κ α → List (κ × ℚ) → Sum κ α → Prop where
  | done (v : α) : Run (.done v) [] (.inr v)
  | restart (key : κ) (next : ℚ → MinorQuery κ α) : Run (.query key next) [] (.inl key)
  | answer (key : κ) (next : ℚ → MinorQuery κ α) (v : ℚ) {log out} (tail : Run (next v) log out) :
      Run (.query key next) ((key,v) :: log) out

/-- Any common extension of the recorded answers reproduces the same successful result. -/
theorem Run.eval_of_extends {p : MinorQuery κ α} {log x} (h : Run p log (.inr x)) (f : κ → ℚ)
    (hlog : ∀ entry ∈ log, f entry.1 = entry.2) : eval f p = x := by
  generalize hout : (Sum.inr x : Sum κ α) = out at h
  induction h with
  | done => cases hout; rfl
  | restart => cases hout
  | answer key next v tail ih =>
    have he : f key = v := hlog (key,v) (List.mem_cons_self ..)
    simpa only [eval, he] using ih (fun e he' => hlog e (List.mem_cons_of_mem _ he')) hout

/-- A syntactic depth bound covers all rational answers, including inconsistent ones. -/
def Bounded : MinorQuery κ α → ℕ → Prop
  | .done _, _ => True
  | .query _ _, 0 => False
  | .query _ next, n+1 => ∀ v, Bounded (next v) n

private theorem bounded_succ (p : MinorQuery κ α) {n : ℕ} (h : p.Bounded n) : p.Bounded (n+1) := by
  induction n generalizing p with
  | zero => cases p <;> simp_all [Bounded]
  | succ n ih => cases p with
    | done => exact True.intro
    | query key next => exact fun v => ih _ (h v)

theorem bounded_mono {p : MinorQuery κ α} {n m : ℕ} (h : p.Bounded n) (hn : n ≤ m) : p.Bounded m := by
  induction hn with
  | refl => exact h
  | step hn ih => exact bounded_succ p ih

theorem bounded_bind (p : MinorQuery κ α) (k : α → MinorQuery κ β) {n m : ℕ}
    (hp : p.Bounded n) (hk : ∀ a, (k a).Bounded m) : (p.bind k).Bounded (n+m) := by
  induction n generalizing p with
  | zero => cases p with
    | done a => simpa [bind] using hk a
    | query => exact False.elim hp
  | succ n ih => cases p with
    | done a => exact bounded_mono (hk a) (by omega)
    | query key next =>
      rw [Nat.succ_add]
      exact fun v => ih _ (hp v)

def restartCost : Sum κ α → ℕ
  | .inl _ => 1
  | .inr _ => 0

/-- A restarting call counts as one request in addition to the answered prefix. -/
theorem Run.call_bound {p : MinorQuery κ α} {log out} (h : Run p log out) {n}
    (hb : p.Bounded n) : log.length + restartCost out ≤ n := by
  induction h generalizing n with
  | done => simp [restartCost]
  | restart => cases n with
    | zero => exact False.elim hb
    | succ => simp [restartCost]
  | answer key next v h ih => cases n with
    | zero => exact False.elim hb
    | succ n => have hh := ih (hb v); simp only [List.length_cons]; omega

/-- Request exactly the listed coordinates, preserving their specified order. -/
def readColumns {n : ℕ} (key : Fin n → κ) (J : List (Fin n)) (values : Fin n → ℚ) :
    MinorQuery κ (Fin n → ℚ) :=
  match J with
  | [] => .done values
  | j :: tail => .query (key j) fun q => readColumns key tail (Function.update values j q)

theorem readColumns_bounded {n : ℕ} (key : Fin n → κ) (J : List (Fin n)) (values : Fin n → ℚ) :
    (readColumns key J values).Bounded J.length := by
  induction J generalizing values with
  | nil => exact True.intro
  | cons j tail ih => exact fun v => ih (Function.update values j v)

theorem readColumns_eval {n : ℕ} (key : Fin n → κ) (J : List (Fin n)) (values : Fin n → ℚ)
    (f : κ → ℚ) (i : Fin n) :
    eval f (readColumns key J values) i = if i ∈ J then f (key i) else values i := by
  induction J generalizing values with
  | nil => simp [eval, readColumns]
  | cons j tail ih =>
    change eval f (readColumns key tail (Function.update values j (f (key j)))) i = _
    rw [ih]
    by_cases hij : i = j <;> by_cases ht : i ∈ tail <;> simp [hij, ht, Function.update]

end MinorQuery
end Geometry
end LinearProgramming
end Optimization
end OAI
