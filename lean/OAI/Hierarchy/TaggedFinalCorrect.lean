import OAI.Hierarchy.TaggedFinalRows
import OAI.Hierarchy.TaggedData
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.List.Perm.Basic

namespace OAI
/-! # Sorted flagged records characterize the original tagged tensor -/

namespace Hierarchy.Tagged.FinalScan

open scoped Classical
variable {n : ℕ} {α : Type*}

abbrev Entry (n : ℕ) (α : Type*) := Bool × (Fin n × α)

def sources (s : Fin n → α) := List.ofFn fun i => (i,s i)
def targets (a : Fin n → Fin n) (t : Fin n → α) := List.ofFn fun i => (a i,t i)
def input (s : Fin n → α) (a : Fin n → Fin n) (t : Fin n → α) : List (Entry n α) :=
  (sources s).map (Prod.mk false) ++ (targets a t).map (Prod.mk true)

def select {β : Type*} (b : Bool) (xs : List (Bool × β)) := xs.filterMap fun p => if p.1 = b then some p.2 else none

private theorem select_input (s : Fin n → α) (a : Fin n → Fin n) (t : Fin n → α) (b : Bool) :
    select b (input s a t) = if b then targets a t else sources s := by
  cases b <;> simp [select,input,List.filterMap_map]

private theorem paired_select {β : Type*} (xs : List (Bool × β)) (ok : paired xs) :
    select false xs = select true xs := by
  match xs with
  | [] => rfl
  | [_] => exact ok.elim
  | (f,x)::(g,y)::rest =>
    change f = false ∧ g = true ∧ x = y ∧ paired rest at ok
    obtain ⟨rfl,rfl,rfl,hs⟩ := ok
    have tail := paired_select rest hs
    simpa [select] using congrArg (List.cons x) tail

private theorem valid_of_perm (s : Fin n → α) (a : Fin n → Fin n) (t : Fin n → α)
    (p : (sources s).Perm (targets a t)) : Valid s a t := by
  have surj : Function.Surjective a := by
    intro i
    have found := p.mem_iff.mp (show (i,s i) ∈ sources s from List.mem_ofFn.mpr ⟨i,rfl⟩)
    obtain ⟨j,e⟩ := List.mem_ofFn.mp found
    exact ⟨j,congrArg Prod.fst e⟩
  refine ⟨Finite.surjective_iff_bijective.mp surj, ?_⟩
  intro j
  have found := p.mem_iff.mpr (show (a j,t j) ∈ targets a t from List.mem_ofFn.mpr ⟨j,rfl⟩)
  obtain ⟨i,e⟩ := List.mem_ofFn.mp found
  have id : i = a j := congrArg Prod.fst e
  exact (congrArg Prod.snd e).symm.trans (congrArg s id)

private def canonical (s : Fin n → α) : List (Entry n α) :=
  (sources s).flatMap fun p => [(false,p),(true,p)]

private theorem paired_pairs {β : Type*} (xs : List β) :
    paired (xs.flatMap fun a => [(false,a),(true,a)]) := by
  induction xs <;> simp [paired, *]

private theorem normal_perm (s : Fin n → α) (a : Fin n → Fin n) (t : Fin n → α)
    (valid : Valid s a t) : (input s a t).Perm (canonical s) := by
  let e := Equiv.ofBijective a valid.1
  have pt : (targets a t).Perm (sources s) := by
    have same : targets a t = List.ofFn ((fun i => (i,s i)) ∘ e) := by
      unfold targets
      congr 1
      funext i
      exact Prod.ext rfl (valid.2 i)
    rw [same]
    exact Equiv.Perm.ofFn_comp_perm e (fun i => (i,s i))
  apply (List.Perm.append_left _ (pt.map (Prod.mk true))).trans
  simpa [canonical, ← List.map_eq_flatMap] using
    List.flatMap_append_perm (sources s) (fun p => [(false,p)]) (fun p => [(true,p)])

def sortKey (p : Entry n α) : (Fin n ×ₗ Bool) := toLex (p.2.1,p.1)

private theorem canonical_order (s : Fin n → α) :
    ((canonical s).map sortKey).Pairwise (· ≤ ·) := by
  rw [List.pairwise_map]
  apply List.pairwise_flatMap.mpr
  constructor
  · intro p _
    simp [sortKey, Prod.Lex.toLex_le_toLex]
  · apply List.pairwise_ofFn.mpr
    intro i j ij x hx y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;>
      exact Prod.Lex.toLex_le_toLex.mpr (Or.inl ij)

/-- In a valid permutation each sorted `(tag, flag)` key fixes the entire
record, including its payload. -/
private theorem canonical_determined (s : Fin n → α) (p : Entry n α) (mem : p ∈ canonical s) :
    (p.1,(p.2.1,s p.2.1)) = p := by
  obtain ⟨row,found,which⟩ := List.mem_flatMap.mp mem
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp found
  simp only [List.mem_cons, List.not_mem_nil, or_false] at which
  rcases which with rfl | rfl <;> rfl

theorem valid_iff_terminal (s : Fin n → α) (a : Fin n → Fin n) (t : Fin n → α)
    (out : List (Entry n α)) (perm : out.Perm (input s a t))
    (ordered : (out.map sortKey).Pairwise (· ≤ ·)) : Valid s a t ↔ paired out := by
  constructor
  · intro h
    have p := perm.trans (normal_perm s a t h)
    have sameKeys := (p.map sortKey).eq_of_pairwise' ordered (canonical_order s)
    let decode (k : (Fin n ×ₗ Bool)) : Entry n α := ((ofLex k).2,(ofLex k).1,s (ofLex k).1)
    have normalize (xs : List (Entry n α)) (inside : ∀ v ∈ xs, v ∈ canonical s) :
        (xs.map sortKey).map decode = xs := by
      rw [List.map_map]
      calc
        _ = xs.map id := List.map_congr_left fun v hv => canonical_determined s v (inside v hv)
        _ = _ := by simp
    have equal := congrArg (List.map decode) sameKeys
    rw [normalize out (fun _ hx => p.mem_iff.mp hx), normalize _ (fun _ h => h)] at equal
    rw [equal]
    exact paired_pairs _
  · intro h
    have side (b : Bool) : (select b out).Perm (select b (input s a t)) := perm.filterMap _
    have left := side false
    have right := side true
    rw [select_input] at left right
    rw [paired_select out h] at left
    exact valid_of_perm s a t (left.symm.trans right)

end Hierarchy.Tagged.FinalScan

end OAI
