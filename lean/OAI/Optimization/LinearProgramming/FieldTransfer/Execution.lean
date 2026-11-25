import OAI.Optimization.LinearProgramming.RAM.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Logic.Function.Basic

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace FieldTransfer

variable {K : Type*}

open OAI.Optimization.LinearProgramming.RAM

variable {K L : Type*} [Field K] [Field L]

/-- Only scalar registers change along an embedding. In particular all indirect
addresses, program counters, and returned output tags are preserved. -/
def mapState (f : K →+* L) (s : State K) : State L :=
  ⟨s.pc, f ∘ s.data, s.index, s.output⟩

@[simp] theorem mapState_start (f : K →+* L) (dims : List Nat) (xs : List K) :
    mapState f (start dims xs) = start dims (xs.map f) := by
  unfold mapState start
  congr 1
  funext i
  simp only [Function.comp_apply, List.getElem?_map]
  cases xs[i]? <;> simp

private theorem map_putData (f : K →+* L) (s : State K) (d : Nat) (a : K) :
    mapState f (s.putData d a) = (mapState f s).putData d (f a) := by
  simp [State.putData, mapState, Function.comp_update]

private theorem map_putIndex (f : K →+* L) (s : State K) (d n : Nat) :
    mapState f (s.putIndex d n) = (mapState f s).putIndex d n := rfl

variable [LinearOrder K] [IsStrictOrderedRing K] [LinearOrder L] [IsStrictOrderedRing L]

/-- Field embeddings preserving order preserve both the legal instruction
and every failing instruction, including attempted zero divisions. -/
theorem execInstr_map (f : K →+* L) (hf : StrictMono f) (inst : Instr) (s : State K) :
    execInstr inst (mapState f s) = (execInstr inst s).map (mapState f) := by
  have hz (k : Nat) : f (s.data k) = 0 ↔ s.data k = 0 := map_eq_zero f
  have hl (a b : Nat) : f (s.data a) < f (s.data b) ↔ s.data a < s.data b := hf.lt_iff_lt
  cases inst <;> simp only [execInstr, Option.map_some, map_putData, map_putIndex,
    Rat.cast_def, map_div₀, map_intCast, map_natCast, map_mul, map_add, map_sub]
  all_goals first | rfl | simp [mapState, hz, hl, apply_ite, Function.comp_update, State.putData]

theorem step_map (f : K →+* L) (hf : StrictMono f) (program : Program) (s : State K) :
    step program (mapState f s) = (step program s).map (mapState f) := by
  have ho : (mapState f s).output = s.output := rfl
  have hp : (mapState f s).pc = s.pc := rfl
  cases h : s.output <;> cases hj : program[s.pc]? <;>
    simp only [step, ho, hp, h, hj, Option.map_none]
  exact execInstr_map f hf _ _

/-- Run exactly the requested number of instructions. An illegal instruction,
or an early halt followed by a request for another step, gives no result. -/
def runExactly (program : Program) (s : State K) : Nat → Option (State K)
  | 0 => some s
  | n + 1 => (runExactly program s n).bind (step program)

theorem runExactly_succ_first (p : Program) (s : State K) (n : Nat) :
    runExactly p s (n + 1) = (step p s).bind (fun t => runExactly p t n) := by
  induction n with
  | zero =>
    simp only [runExactly, Option.bind_some]
    cases step p s <;> rfl
  | succ n ih =>
    change (runExactly p s (n+1)).bind (step p) = _
    rw [ih]
    cases step p s <;> rfl

theorem runExactly_map (f : K →+* L) (hf : StrictMono f) (p : Program) (s : State K)
    (n : Nat) : runExactly p (mapState f s) n = (runExactly p s n).map (mapState f) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [runExactly, ih]
    cases h : runExactly p s n with
    | none => rfl
    | some t => exact step_map f hf p t

theorem runExactly_of_trace {p : Program} {s : State K} {k : Nat}
    {t : Fin (k + 1) → State K} (h : Trace p s k t) (i : Fin (k + 1)) :
    runExactly p s i.val = some (t i) := by
  induction i using Fin.induction with
  | zero => exact congrArg some h.1.symm
  | succ i hi =>
    change (runExactly p s i.castSucc.val).bind (step p) = _
    rw [hi]
    exact h.2 i

/-- Every bounded legal execution starting over the smaller field descends
from the larger field, preserving the entire trace and its exact length. -/
theorem descends_trace (f : K →+* L) (hf : StrictMono f) (p : Program) (s : State K)
    {k : Nat} {u : Fin (k + 1) → State L} (h : Trace p (mapState f s) k u) :
    ∃ t : Fin (k + 1) → State K, Trace p s k t ∧ ∀ i, mapState f (t i) = u i := by
  let t (i : Fin (k + 1)) : State K := (runExactly p s i.val).getD s
  have ht (i : Fin (k + 1)) :
      runExactly p s i.val = some (t i) ∧ mapState f (t i) = u i := by
    have hi := runExactly_of_trace h i
    rw [runExactly_map f hf] at hi
    cases e : runExactly p s i.val with
    | none => simp [e] at hi
    | some v => simpa [t, e] using hi
  refine ⟨t, ⟨rfl, ?_⟩, fun i => (ht i).2⟩
  intro i
  have hs := (ht i.succ).1
  change (runExactly p s i.castSucc.val).bind (step p) = _ at hs
  rw [(ht i.castSucc).1] at hs
  exact hs

theorem map_trace (f : K →+* L) (hf : StrictMono f) {p : Program} {s : State K} {k : Nat}
    {t : Fin (k + 1) → State K} (h : Trace p s k t) :
    Trace p (mapState f s) k (mapState f ∘ t) := by
  refine ⟨congrArg (mapState f) h.1, fun i => ?_⟩
  change step p (mapState f (t i.castSucc)) = _
  rw [step_map f hf, h.2]
  rfl

private theorem prefix_succeeds {p : Program} {s z : State K} {k : Nat}
    (h : runExactly p s k = some z) (i : Nat) (hi : i ≤ k) :
    ∃ y, runExactly p s i = some y := by
  induction k generalizing z i with
  | zero =>
    have : i = 0 := Nat.eq_zero_of_le_zero hi
    exact ⟨s, this ▸ rfl⟩
  | succ k ih =>
    rcases Nat.eq_or_lt_of_le hi with he | hlt
    · exact ⟨z, he ▸ h⟩
    · change (runExactly p s k).bind (step p) = some z at h
      cases hk : runExactly p s k with
      | none => simp [hk] at h
      | some y => exact ih hk i (Nat.le_of_lt_succ hlt)

theorem runExactly_iff_trace {p : Program} {s z : State K} (k : Nat) :
    runExactly p s k = some z ↔
      ∃ t : Fin (k + 1) → State K, Trace p s k t ∧ t (Fin.last k) = z := by
  constructor
  · intro hz
    let t (i : Fin (k+1)) := (runExactly p s i.val).getD s
    have ht (i : Fin (k+1)) : runExactly p s i.val = some (t i) := by
      obtain ⟨y, hy⟩ := prefix_succeeds hz i (Nat.le_of_lt_succ i.isLt)
      simp [t, hy]
    refine ⟨t, ⟨rfl, fun i => ?_⟩, ?_⟩
    · have hs := ht i.succ
      change (runExactly p s i.castSucc.val).bind (step p) = _ at hs
      rw [ht i.castSucc] at hs
      exact hs
    · simp [t, hz]
  · rintro ⟨t, h, rfl⟩
    exact runExactly_of_trace h (Fin.last k)

end FieldTransfer
end LinearProgramming
end Optimization
end OAI
