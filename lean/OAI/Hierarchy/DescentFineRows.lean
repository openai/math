import OAI.Hierarchy.DescentCumulativeInputRows
import OAI.Hierarchy.DescentFineTerminals
import OAI.Hierarchy.DescentInputTerminals

namespace OAI
/-! # The whole-occupant row assignment in every actual refined leaf -/

namespace Hierarchy.DescentFineTerminals
open DescentColonies DescentBaseProfile DescentGL
open scoped Classical BigOperators
noncomputable section
variable {V : Type} [Fintype V] [DecidableEq V] {k D f Y B : ℕ}
variable (near : V→Finset V) (wt : V→Block k→ℕ) (room : ∀v x,wt v x≤B) (b : V→ℕ)

def leafKey (v : V) (x : Block k) :=
  let d := leaf (D:=D) (f:=f) near wt room b v x
  (d,group d x)

local notation "key" => leafKey (D:=D) (f:=f) near wt room b

def occupants (v : V) (p : ℕ×ℕ) := Finset.univ.filter fun x : Block k=>key v x=p
local notation "occ" => occupants (D:=D) (f:=f) near wt room b

omit [Fintype V] [DecidableEq V] in
theorem occupant_mem (v : V) (x : Block k) : x∈occ v (key v x) := by simp [occupants]

omit [Fintype V] [DecidableEq V] in
/-- The extra base refinement only shrinks the first unsplit interval.
The load of its actual occupant list is consequently at most 2 F B. -/
theorem occupants_mass (v : V) (p : ℕ×ℕ) : (∑x∈occ v p,wt v x)≤2*(2^f*B) := by
  by_cases h : (occ v p).Nonempty
  · obtain ⟨x,hx⟩ := h
    let d := depth wt (fun v w=>w∈near v) D (f+1) B room v x
    let e := leaf (D:=D) (f:=f) near wt room b v x
    have key_x : key v x=p := (Finset.mem_filter.mp hx).2
    have sub : occ v p⊆interval d x := by
      intro y hy
      have same : key v y=key v x := ((Finset.mem_filter.mp hy).2).trans key_x.symm
      have dep := congrArg Prod.fst same
      change leaf (D:=D) (f:=f) near wt room b v y=e at dep
      have addr := congrArg Prod.snd same
      change group (leaf (D:=D) (f:=f) near wt room b v y) y=group e x at addr
      rw [dep] at addr
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,group_ancestor (d:=d) (e:=e) (le_max_right ..) addr⟩
    calc
      _ ≤ mass wt v d x := Finset.sum_le_sum_of_subset sub
      _ ≤ 2^(f+1)*B := leaf_load wt _ D (f+1) B room v x
      _ = _ := by ring
  · simp [Finset.not_nonempty_iff_eq_empty.mp h]

variable [NeZero Y] (enough : Y≤2^f)

/-- Every true dyadic leaf is scanned in its literal block order. -/
def leafRow (v : V) (p : ℕ×ℕ) : ↥(occ v p)→Fin Y :=
  Cumulative.row (Function.Embedding.subtype _) (fun x=>(wt v x.val:ℝ)) ((2^f*B:ℕ):ℝ)

include enough in
omit [Fintype V] [DecidableEq V] in
theorem leafRow_bound (v : V) (p : ℕ×ℕ) (j : Fin Y) :
    inputLoad Finset.univ (fun x : ↥(occ v p)=>(wt v x.val:ℝ))
      (leafRow (D:=D) near wt room b v p) j≤3*((2^f*B:ℕ):ℝ)/Y := by
  refine Cumulative.bound (Function.Embedding.subtype _) _ ((2^f*B:ℕ):ℝ) (B:ℝ) (by positivity)
    (fun _=>Nat.cast_nonneg _) ?_ ?_ ?_ j
  · intro i;exact_mod_cast room v i.val
  · exact_mod_cast (show (∑a : ↥(occ v p),wt v a.val)≤2*(2^f*B) by
      simpa only [Finset.sum_coe_sort] using occupants_mass (D:=D) near wt room b v p)
  · exact_mod_cast Nat.mul_le_mul_right B enough

local notation "R" => leafRow (D:=D) near wt room b
def row (o : V×Block k) : Fin Y :=
  (fun _ : Y≤2^f => R o.1 (key o.1 o.2) ⟨o.2,occupant_mem near wt room b o.1 o.2⟩) enough

omit [Fintype V] [DecidableEq V] in
/-- The native row function has precisely the proved per-terminal load, not
merely the same row-count convention as the local existential assignment. -/
theorem row_bound (v : V) (p : ℕ×ℕ) (j : Fin Y) :
    inputLoad (occ v p) (fun x=>(wt v x:ℝ)) (fun x=>row (D:=D) near wt room b enough (v,x)) j≤
      3*((2^f*B:ℕ):ℝ)/Y := by
  have localBound := leafRow_bound (D:=D) near wt room b enough v p j
  unfold inputLoad at localBound ⊢
  rw [←Finset.sum_coe_sort]
  apply le_trans _ localBound
  apply le_of_eq
  apply Finset.sum_congr rfl
  rintro ⟨x,hx⟩ _
  have same : key v x=p := (Finset.mem_filter.mp hx).2
  subst p
  rfl

/-- The raw old block remains the public input. Layout inversion is internal
to the allocation, so all ports of an original tensor receive a single row. -/
def oldRow (L : Layout k) (_ : Bool) (o : V×Block k) : Fin Y :=
  row (D:=D) near wt room b enough (o.1,rearrange L o.2)

end
end Hierarchy.DescentFineTerminals

end OAI
