import OAI.Computability.IntegerMultiplication.Spindle.Orbit
import OAI.Computability.IntegerMultiplication.Code.Altitude

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Strip
open Code
variable {A B S : Type}
-- monotone padded series s into t, replicated s K times
variable (s : Series A) (t : Series B) (C : ℕ)
def widen (l : List A) := (List.replicate C l).flatten
theorem lw (l : List A) : (widen C l).length=l.length*C := by
  induction C with
  | zero => simp [widen]
  | succ C ih =>
    simp only [widen,List.replicate_succ,List.flatten_cons,List.length_append,Nat.mul_add,Nat.mul_one]
    change l.length+(widen C l).length=l.length*C+_
    rw [ih,Nat.add_comm]
theorem subw (l : List A) (d : 1≤C) (b : ℕ) (h : b≥l.length) :
    ((widen C l).take b).take l.length=l := by
  obtain ⟨C,e⟩ := Nat.exists_eq_add_of_le d
  subst e
  rw [Nat.add_comm 1,widen,List.replicate_succ,List.flatten_cons,List.take_take]
  simp [Nat.min_eq_left h]

theorem easy_cloud [Codec A] :
    Easy (fun x : Tally × List A => (widen C x.2).take x.1.length) := by
  have u : Easy (widen (A:=A) C) := by
    induction C with
    | zero => exact Easy.const []
    | succ C ih =>
      suffices e : Easy (fun x : List A => x ++ widen C x) from by rw [show widen (A:=A) (C+1)=(fun l : List A => l ++ (List.replicate C l).flatten) by ext; simp [widen,List.replicate_succ]]; simpa [widen,List.replicate_succ] using e
      fun_prop
  exact (easy_cut (Easy.pair Easy.fst (Easy.snd.compose u))).fstCompose

structure Gap where
  fit : s.count ≤ t.count
  maxfold : t.count ≤ s.count*C
  step : 1≤C

noncomputable def intro_ (e : Gap s t C) : A → B :=
  fun i => t.index.symm ⟨(s.index i).val, lt_of_lt_of_le (s.index i).isLt e.fit⟩
noncomputable def expand (e : Gap s t C) : B→A :=
  t.untab ((widen C s.explore).take t.count) (by simp [lw]; exact e.maxfold)
theorem material (e : Gap s t C) (v : A→S) :
    t.tab (v ∘ expand s t C e) = (widen C (s.tab v)).take t.count := by
  rw [← Series.map_tab,expand,Series.recover, List.map_take] -- lemma orientation
  unfold widen Series.tab
  simp [List.map_flatten]
theorem cede (e : Gap s t C) (v : B→S) :
    s.tab (v ∘ intro_ s t C e)=(t.tab v).take s.count := by
  apply List.ext_getElem
  · simp [Nat.min_eq_left e.fit]
  intro i h y
  let j : Fin s.count := ⟨i,by simpa using h⟩
  rw [s.get _ j,List.getElem_take]
  rw [t.get _ (show Fin t.count from ⟨i,lt_of_lt_of_le j.isLt e.fit⟩)]
  simp [intro_,j]

@[simp] theorem home (e : Gap s t C) (i : A) : expand s t C e (intro_ s t C e i)=i := by
  apply congrFun (s.faithful (show s.tab (expand s t C e ∘ intro_ s t C e)=s.tab id from ?_)) i
  rw [cede,show t.tab (expand s t C e)=t.tab (id ∘ expand s t C e) from rfl,material]
  have h := subw C (s.explore) e.step t.count (show t.count ≥ s.explore.length from e.fit)
  simpa only [Series.count,Series.tab_id] using h
end Strip

end IntegerMultiplication
end Computability
end OAI
