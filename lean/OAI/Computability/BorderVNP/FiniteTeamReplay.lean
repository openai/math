import OAI.Computability.BorderVNP.FiniteOutputStack
import OAI.Computability.BorderVNP.TeamContractionReplay

/-! # Exact field-valued replay leaves

A dictionary key records exactly the binary instructions taken on a bounded stack
execution. Its value is the field element returned by the accepting state. An accepted
zero is a dictionary entry. A rejecting instruction or a timeout has no entry.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FieldReplay

open VPVNP.RAMTape TeamPrivateFragment
open scoped BigOperators

variable {K Q : Type} [DecidableEq K] {F : Type*}

private def consChoice {V : Type*} (b : Bool) : (List Bool × V) ↪ List Bool × V where
  toFun z := (b :: z.1, z.2)
  inj' := by rintro ⟨xs,u⟩ ⟨ys,v⟩ eq; simpa using eq

private theorem disjoint_prefix {V : Type*} (lo hi : Finset (List Bool × V)) :
    Disjoint (lo.map (consChoice false)) (hi.map (consChoice true)) := by
  rw [Finset.disjoint_left]
  intro p hp hq
  obtain ⟨⟨xs,u⟩,_,rfl⟩ := Finset.mem_map.mp hp
  obtain ⟨⟨ys,v⟩,_,eq⟩ := Finset.mem_map.mp hq
  change (true :: ys,v) = (false :: xs,u) at eq
  simp at eq

private theorem mem_prefix {V : Type*} (b : Bool) (bs : List Bool) (v : V)
    (l : Finset (List Bool × V)) :
    (bs,v) ∈ l.map (consChoice b) ↔ ∃ tail, bs = b :: tail ∧ (tail,v) ∈ l := by
  constructor
  · intro h
    obtain ⟨⟨ys,u⟩,hu,he⟩ := Finset.mem_map.mp h
    change (b :: ys,u) = (bs,v) at he
    cases he
    exact ⟨ys,rfl,hu⟩
  · rintro ⟨tail,rfl,h⟩
    exact Finset.mem_map.mpr ⟨(tail,v),h,rfl⟩

/-- Exact choice strings paired with their field output, up to the given tick bound.
The leading choice bit keeps the child dictionaries disjoint. -/
def leaves (C : StackCode K Q) (w : Q → F) : ℕ → Q → Stacks K → Finset (List Bool × F)
  | 0, _, _ => ∅
  | n+1, q, s => match C q with
    | .push i b u => leaves C w n u (Function.update s i (b :: s i))
    | .pop i f => leaves C w n (f (s i).head?) (Function.update s i (s i).tail)
    | .goto u => leaves C w n u s
    | .choose l h => (leaves C w n l s).map (consChoice false) |>.disjUnion
        ((leaves C w n h s).map (consChoice true)) (disjoint_prefix ..)
    | .halt ok => if ok then {([],w q)} else ∅

/-- At a binary row the first consumed bit uniquely determines the child dictionary. -/
theorem mem_choose_iff (C : StackCode K Q) (w : Q → F) (t : ℕ) (q : Q)
    (s : Stacks K) (l h : Q) (op : C q = .choose l h) (bs : List Bool) (v : F) :
    (bs,v) ∈ leaves C w (t+1) q s ↔
      (∃ tail, bs = false :: tail ∧ (tail,v) ∈ leaves C w t l s) ∨
      (∃ tail, bs = true :: tail ∧ (tail,v) ∈ leaves C w t h s) := by
  rw [leaves,op]
  simp only [Finset.mem_disjUnion,mem_prefix]

/-- The sum of the accepting dictionary entries is the native stack field value. -/
theorem paths_eq_sum [Field F] (C : StackCode K Q) (w : Q → F) (t : ℕ) (q : Q) (s : Stacks K) :
    FieldStack.paths C w t q s = ∑ p ∈ leaves C w t q s, p.2 := by
  induction t generalizing q s with
  | zero => simp [FieldStack.paths, leaves]
  | succ t ih =>
    cases op : C q with
    | choose l h => simp only [FieldStack.paths, leaves, op, ih, Finset.sum_disjUnion, Finset.sum_map]; rfl
    | halt b => cases b <;> simp [FieldStack.paths, leaves, op]
    | _ => simp [FieldStack.paths, leaves, op, ih]

private theorem mem_test_iff [DecidableEq F] (C : StackCode K Q) (w : Q → F)
    (t : ℕ) (q : Q) (s : Stacks K) (bs : List Bool) (v : F) :
    (bs,v) ∈ leaves C w t q s ↔
      (bs,true) ∈ TeamContraction.Replay.leaves C (fun u => decide (w u = v)) t q s := by
  induction t generalizing q s bs with
  | zero => simp [leaves,TeamContraction.Replay.leaves]
  | succ t ih =>
    cases op : C q with
    | choose l h =>
      let check := fun u => decide (w u = v)
      rw [leaves,TeamContraction.Replay.leaves,op]
      change (bs,v) ∈ ((leaves C w t l s).map (consChoice false)).disjUnion
        ((leaves C w t h s).map (consChoice true)) _ ↔
        (bs,true) ∈ (TeamContraction.Replay.leaves C check t l s).map (consChoice false) ∪
          (TeamContraction.Replay.leaves C check t h s).map (consChoice true)
      simp only [Finset.mem_disjUnion,Finset.mem_union,mem_prefix,ih,check]
    | halt b => cases b <;> simp [leaves, TeamContraction.Replay.leaves,op,eq_comm]
    | _ => simp [leaves,TeamContraction.Replay.leaves,op,ih]

/-- A dictionary entry is exactly a native accepting replay at the stated clock, with
all of its choice bits consumed and the indicated scalar returned by its terminal state. -/
theorem mem_leaves_iff (C : StackCode K Q) (w : Q → F) (t : ℕ) (q : Q)
    (s : Stacks K) (bs : List Bool) (v : F) :
    (bs,v) ∈ leaves C w t q s ↔ ∃ k < t, ∃ u out,
      StackRuns (replay C) k (q,bs) s (u,[]) out ∧ C u = .halt true ∧ w u = v := by
  classical
  rw [mem_test_iff, TeamContraction.Replay.mem_leaves_iff]
  simp

/-- A complete consumed choice tape determines at most one field output, including zero. -/
theorem output_unique (C : StackCode K Q) (w : Q → F) (t : ℕ) (q : Q)
    (s : Stacks K) (bs : List Bool) {v v' : F}
    (hv : (bs,v) ∈ leaves C w t q s) (hv' : (bs,v') ∈ leaves C w t q s) : v = v' := by
  obtain ⟨_,_,u,_,run,halt,rfl⟩ := (mem_leaves_iff ..).mp hv
  obtain ⟨_,_,u',_,run',halt',rfl⟩ := (mem_leaves_iff ..).mp hv'
  have he := TeamContraction.Replay.terminal_unique run run'
    (show replay C (u,[]) = .halt true by simp [replay,halt])
    (show replay C (u',[]) = .halt true by simp [replay,halt'])
  exact congrArg w (congrArg Prod.fst he.2.1)

end FieldReplay

end BorderVNP
end Computability
end OAI
