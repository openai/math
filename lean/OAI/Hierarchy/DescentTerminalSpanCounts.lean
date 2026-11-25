import OAI.Hierarchy.DescentTerminalRecipeRows

namespace OAI
/-! # One marker per charged site identifies both occupied and unused rows -/
namespace Hierarchy.DescentTerminalSpanBook
open DescentTerminalBinPack DescentTerminalRecipeRows
open scoped BigOperators Classical
noncomputable section
variable {S W q : ℕ} (sites : Fin S→Site) (pos : 0<W) (fit : ∀i,(sites i).rows q≤W)
local notation "C" => counts (q:=q) sites
local notation "start" => first W C
def prior (t : ℕ) := Finset.univ.filter (fun i:Fin S=>start i<t)
def count (t : ℕ) := (prior (W:=W) (q:=q) sites t).card
def mark (t : ℕ) := if ∃i:Fin S,start i=t then 1 else 0

theorem increasing : StrictMono (first W C) := by
  intro i j less
  have h:=ordered W C less
  have hi:0<C i:=by simp [counts,Site.rows]
  omega

theorem step (t : ℕ) : count (W:=W) (q:=q) sites (t+1) =
    count (W:=W) (q:=q) sites t + mark (W:=W) (q:=q) sites t := by
  classical
  by_cases h:∃i:Fin S,start i=t
  · obtain ⟨i,hi⟩:=h
    have eqn:prior (W:=W) (q:=q) sites (t+1)=insert i (prior (W:=W) (q:=q) sites t):=by
      ext j
      simp only [prior,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_insert]
      constructor
      · intro v
        rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp v) with low|eq
        · exact Or.inr low
        · exact Or.inl ((increasing (W:=W) (q:=q) sites).injective (eq.trans hi.symm))
      · rintro (rfl|lo) <;>omega
    have off:i∉prior (W:=W) (q:=q) sites t:=by simp [prior,hi]
    simp [count,eqn,Finset.card_insert_of_notMem off,mark,show ∃k,start k=t from ⟨i,hi⟩]
  · have eqn:prior (W:=W) (q:=q) sites (t+1)=prior (W:=W) (q:=q) sites t:=by
      ext j;simp only [prior,Finset.mem_filter,Finset.mem_univ,true_and]
      have neq:start j≠t:=fun x=>h ⟨j,x⟩
      omega
    simp [count,eqn,mark,h]

theorem at_owner (v : Fin S) (y : Fin (C v)) :
    count (W:=W) (q:=q) sites (start v+y.val+1)=v.val+1 := by
  have eqn : prior (W:=W) (q:=q) sites (start v+y.val+1)=Finset.Iic v:=by
    ext i
    simp only [prior,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_Iic]
    constructor
    · intro h
      by_contra! late
      have bound:=ordered W C late;have:=y.isLt;omega
    · intro h
      have lo: start i≤ start v:=(increasing (W:=W) (q:=q) sites).monotone h
      omega
  simp [count,eqn]

def resolve (p : ℕ) : Option (Fin S×Fin W) :=
  let n:=count (W:=W) (q:=q) sites (p+1)
  if h : 0<n ∧ n-1<S then
    let v:Fin S:=⟨n-1,h.2⟩
    if inRow : start v≤p ∧ p-start v<C v then some (v,⟨p-start v,inRow.2.trans_le (fit v)⟩) else none
  else none

theorem resolve_iff (p : ℕ) (v : Fin S) (u : Fin W) :
    resolve sites fit p=some (v,u) ↔ ∃j:Fin (C v),p=start v+j.val ∧ u.val=j.val := by
  constructor
  · intro yes
    unfold resolve at yes
    dsimp only at yes
    split at yes <;> try contradiction
    split at yes <;> try contradiction
    rename_i h
    have both:=Prod.mk.inj (Option.some.inj yes)
    rcases both with ⟨rfl,rfl⟩
    exact ⟨⟨_,h.2⟩,(Nat.add_sub_of_le h.1).symm,rfl⟩
  · rintro ⟨j,rfl,hu⟩
    have eqn:=at_owner (W:=W) (q:=q) sites v j
    have live:start v≤ start v+j.val ∧ start v+j.val-start v<C v:=by simp
    have same : u = ⟨j.val,j.isLt.trans_le (fit v)⟩ := Fin.ext hu
    subst u
    simp [resolve,eqn,v.isLt,live,j.isLt]

end
end Hierarchy.DescentTerminalSpanBook

end OAI
