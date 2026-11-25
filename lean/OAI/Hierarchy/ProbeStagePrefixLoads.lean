import OAI.Hierarchy.ProbeStageMask

namespace OAI
/-! # Prefix counters and first saturations for the actual chronological allocation -/

namespace Hierarchy.ProbeStage.Greedy
open Finset

variable {n B : ℕ} {E L H : Type*} [DecidableEq E] [DecidableEq L] [DecidableEq H]

/-- Use the final colors only on the prefix already processed. -/
def prefixCount (key : Fin n → E) (color : Fin n → Fin B) (k : ℕ) (x : E) (c : Fin B) :=
  load key (before n k) color x c

def prefixFull (key : Fin n → E) (color : Fin n → Fin B) (k : ℕ) (x : E) :=
  univ.filter fun c => quota B ≤ prefixCount key color k x c

@[simp] theorem prefix_zero (key : Fin n → E) (color : Fin n → Fin B) (x : E) (c : Fin B) :
    prefixCount key color 0 x c=0 := by simp [prefixCount,load,before]

theorem prefix_step (key : Fin n → E) (color : Fin n → Fin B) (i : Fin n) (x : E) (c : Fin B) :
    prefixCount key color (i.val+1) x c=prefixCount key color i.val x c +
      (if key i=x ∧ color i=c then 1 else 0) := by
  have eqn : before n (i.val+1)=insert i (before n i.val) := by
    ext j; simp only [before,mem_insert,Fin.ext_iff,mem_filter,mem_univ,true_and];omega
  have outside : i∉before n i.val := by simp [before]
  simp only [prefixCount,load,eqn,filter_insert]
  split <;> simp [*]

theorem full_step (key : Fin n → E) (color : Fin n → Fin B) (i : Fin n) (x : E)
    (safe : prefixCount key color i.val (key i) (color i)<quota B) :
    prefixFull key color (i.val+1) x =
      if key i=x ∧ prefixCount key color i.val (key i) (color i)+1=quota B
      then insert (color i) (prefixFull key color i.val x) else prefixFull key color i.val x := by
  ext c
  simp only [prefixFull,mem_filter,mem_univ,true_and,prefix_step]
  by_cases h : key i=x <;> by_cases hc : color i=c <;> simp_all <;> split_ifs <;> simp_all <;> omega

theorem first_color (pos : 0<B) (pick : Fin n → Finset (Fin B) → Fin B)
    (left : Fin n → L) (right : Fin n → H) (i : Fin n) :
    colors pos pick left right n i = pick i (available left right (before n i.val)
      (colors pos pick left right i.val) i) := by
  rw [colors_stable pos pick left right (k:=i.val+1) (by omega) i (by omega),colors]
  simp [i.isLt]

theorem stable_prefix (key : Fin n → E) (pos : 0<B) (pick : Fin n → Finset (Fin B) → Fin B)
    (left : Fin n → L) (right : Fin n → H) (k : ℕ) (hk : k≤n) (x : E) (c : Fin B) :
    prefixCount key (colors pos pick left right n) k x c =
      load key (before n k) (colors pos pick left right k) x c := by
  unfold prefixCount load
  congr 1
  ext i
  by_cases prior : i.val<k
  · simp [before,prior,colors_stable pos pick left right hk i prior]
  · simp [before,prior]

theorem available_prefix (pos : 0<B) (pick : Fin n → Finset (Fin B) → Fin B)
    (left : Fin n → L) (right : Fin n → H) (i : Fin n) (c : Fin B) :
    c∈available left right (before n i.val) (colors pos pick left right i.val) i ↔
      c∉prefixFull left (colors pos pick left right n) i.val (left i)∪
        prefixFull right (colors pos pick left right n) i.val (right i) := by
  simp [available,prefixFull,stable_prefix _ pos pick left right i.val i.isLt.le,not_or]

theorem rank_eq_prefix (key : Fin n → E) (color : Fin n → Fin B) (i : Fin n) :
    rank (fun j => (key j,color j)) i = prefixCount key color i.val (key i) (color i) := by
  simp only [rank,load,prefixCount,Prod.mk.injEq]

end Hierarchy.ProbeStage.Greedy

end OAI
