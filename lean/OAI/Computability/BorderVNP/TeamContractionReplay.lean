import OAI.Computability.BorderVNP.TeamContractionReplayRun

/-! # Finite dictionary of signed accepting stack witnesses

The dictionary contains only the exact consumed bits of a branch, with its actual terminal
sign. Distinct children of the same binary instruction keep different leading bits even
when their destinations and all subsequent tape contents agree. -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction.Replay

open VPVNP.RAMTape TeamPrivateFragment
open scoped BigOperators

variable {K Q : Type} [DecidableEq K]

private def prepend (b : Bool) : (List Bool × Bool) ↪ List Bool × Bool where
  toFun p := (b :: p.1,p.2)
  inj' := by rintro ⟨x,s⟩ ⟨y,t⟩ h; simpa using h

private theorem branches_disjoint (l h : Finset (List Bool × Bool)) :
    Disjoint (l.map (prepend false)) (h.map (prepend true)) := by
  rw [Finset.disjoint_left]
  rintro _ hl hh
  obtain ⟨⟨xs,s⟩,_,rfl⟩ := Finset.mem_map.mp hl
  obtain ⟨⟨ys,t⟩,_,eq⟩ := Finset.mem_map.mp hh
  change (true::ys,t) = (false::xs,s) at eq
  simp at eq

private theorem mem_branch (b c : Bool) (bs : List Bool) (z : Bool) (l : Finset (List Bool × Bool)) :
    (c::bs,z) ∈ l.map (prepend b) ↔ b = c ∧ (bs,z) ∈ l := by
  constructor
  · intro h; obtain ⟨⟨x,y⟩,hm,eq⟩ := Finset.mem_map.mp h
    simp [prepend] at eq
    obtain ⟨⟨rfl,rfl⟩,rfl⟩ := eq
    exact ⟨rfl,hm⟩
  · rintro ⟨rfl,h⟩; exact Finset.mem_map.mpr ⟨(bs,z),h,rfl⟩

private theorem nil_not_branch (b z : Bool) (l : Finset (List Bool × Bool)) :
    ([],z) ∉ l.map (prepend b) := by
  intro h; obtain ⟨⟨xs,s⟩,_,eq⟩ := Finset.mem_map.mp h
  change (b :: xs,s) = ([],z) at eq
  simp at eq

/-- All actual accepting leaves at this clock, retaining each branch's consumed bit list
and the negative flag of its terminal control state. -/
def leaves (C : StackCode K Q) (negative : Q → Bool) : ℕ → Q → Stacks K → Finset (List Bool × Bool)
  | 0, _, _ => ∅
  | n+1, q, s => match C q with
    | .push i b u => leaves C negative n u (Function.update s i (b::s i))
    | .pop i f => leaves C negative n (f (s i).head?) (Function.update s i (s i).tail)
    | .goto u => leaves C negative n u s
    | .choose low high => (leaves C negative n low s).map (prepend false) ∪
        (leaves C negative n high s).map (prepend true)
    | .halt ok => if ok then {([],negative q)} else ∅

/-- Signed stack value is exactly the integer sum over this finite dictionary. -/
theorem paths_eq_sum (C : StackCode K Q) (negative : Q → Bool) (t : ℕ) (q : Q) (s : Stacks K) :
    TeamStack.paths C negative t q s = ∑ x ∈ leaves C negative t q s, TeamTape.haltWeight true x.2 := by
  induction t generalizing q s with
  | zero => simp [TeamStack.paths,leaves]
  | succ n ih =>
    cases op : C q with
    | choose low high =>
      simp only [TeamStack.paths,leaves,op,ih]
      rw [Finset.sum_union (branches_disjoint _ _), Finset.sum_map, Finset.sum_map]
      rfl
    | halt b => cases b <;> simp [TeamStack.paths,leaves,op,TeamTape.haltWeight]
    | _ => simp [TeamStack.paths,leaves,op,ih]

private def signAt (negative : Q → Bool) (q : Q × List Bool) : Option Bool :=
  if q.2.isEmpty then some (negative q.1) else none

private theorem mem_iff_observe (C : StackCode K Q) (negative : Q → Bool) (t : ℕ) (q : Q) (s : Stacks K)
    (bs : List Bool) (z : Bool) :
    (bs,z) ∈ leaves C negative t q s ↔ observe (replay C) (signAt negative) t (q,bs) s = some z := by
  induction t generalizing q s bs with
  | zero => simp [leaves,observe]
  | succ n ih =>
    cases op : C q with
    | choose low high =>
      cases bs with
      | nil =>
        simp only [leaves,op,Finset.mem_union,nil_not_branch,false_or,observe,replay]
        simp
      | cons b bs =>
        simp only [leaves,op,Finset.mem_union,mem_branch,observe,replay]
        cases b <;> simp [ih]
    | halt ok => cases ok <;> cases bs <;> simp [leaves,op,observe,replay,signAt,eq_comm]
    | _ => simp [leaves,op,observe,replay,Function.comp_def,ih]

/-- Membership is equivalent to a literal deterministic replay consuming exactly this
choice string and reaching the indicated sign at an accepting control, before timeout. -/
theorem mem_leaves_iff (C : StackCode K Q) (negative : Q → Bool) (t : ℕ) (q : Q)
    (s : Stacks K) (bs : List Bool) (z : Bool) :
    (bs,z) ∈ leaves C negative t q s ↔ ∃ m < t, ∃ u out,
      StackRuns (replay C) m (q,bs) s (u,[]) out ∧ C u = .halt true ∧ negative u = z := by
  rw [mem_iff_observe,observe_iff]
  constructor
  · rintro ⟨m,hm,⟨u,tail⟩,out,run,hr,hz⟩
    cases tail with
    | cons b bs => simp [signAt] at hz
    | nil =>
      have hneg : negative u = z := by simpa [signAt] using hz
      have hsrc : C u = .halt true := by
        cases h : C u <;> simp [replay,h] at hr ⊢
        exact hr
      exact ⟨m,hm,u,out,run,hsrc,hneg⟩
  · rintro ⟨m,hm,u,out,run,hr,hz⟩
    exact ⟨m,hm,(u,[]),out,run,by simp [replay,hr],by simp [signAt,hz]⟩

/-- No consumed tape has two accepting terminal signs. -/
theorem sign_unique (C : StackCode K Q) (negative : Q → Bool) (t : ℕ) (q : Q)
    (s : Stacks K) (bs : List Bool) {x y : Bool} (hx : (bs,x) ∈ leaves C negative t q s)
    (hy : (bs,y) ∈ leaves C negative t q s) : x = y :=
  Option.some.inj (((mem_iff_observe ..).mp hx).symm.trans ((mem_iff_observe ..).mp hy))

end TeamContraction.Replay

end BorderVNP
end Computability
end OAI
