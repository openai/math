import OAI.Computability.MultitapeWeakETH.SparseIteration

/-! # A completed run of the tape worklist has the disjoint traversal's visit bound -/

namespace OAI.Computability.MultitapeWeakETH.SparseIteration

open IntegerMultiplication Code Bits Algorithms.SubexponentialSAT SqrtLogSpace.DisjointReuse
open SparseDFSRefinement SparsePriorityProgram
open private positive positive_eq clipped prepend answer test front from OAI.Computability.MultitapeWeakETH.SparseIteration
open private data? present from OAI.Computability.MultitapeWeakETH.WitnessWalk
open scoped Classical
noncomputable section

variable {n : ℕ} (split : Word × Word → Option (List Word)) (leaf : NativeGrid.CountQuery → Word)
    (N h : ℕ) (w : Word)

def parameters (n N h : ℕ) (w : Word) : Param × Tally :=
  ((((tally N,tally n),tally h),w),tally (SparseCountProgram.formulaBound n 3))

def work (s : Frontier n) : Work :=
  (s.pending.map (fun x => SparseCountProgram.encodeBody x.formula),decide (0<s.total))

private theorem full_body (F : RawCNF n) (valid : Valid 3 F) :
    clipped (tally (SparseCountProgram.formulaBound n 3)) (SparseCountProgram.encodeBody F) =
      SparseCountProgram.encodeBody F := by
  have enough := SparseCountProgram.encodeBody_length_le F 3 valid.literal_nodup valid.clause_nodup
    (formulaSet_width_le F valid.width)
  simp [clipped,cutLists,List.take_of_length_le enough]

def Branches (n : ℕ) (split : Word × Word → Option (List Word)) (w : Word) :=
  ∀ F : RawCNF n, Valid 3 F →
    let out := split (w,SparseCountProgram.encodeBody F)
    (out=none ∧ SparsePriority.select (ExecCNF.formulaSet F) (BinaryArithmetic.toNat w)=none) ∨
    ∃ c H, RawPriority 3 F (BinaryArithmetic.toNat w) c H ∧
      out=some [SparseCountProgram.encodeBody (childA F c H),SparseCountProgram.encodeBody (childB F c H)]

def Leaves (n : ℕ) (leaf : NativeGrid.CountQuery → Word) (N h : ℕ) (w : Word) :=
  ∀ F : RawCNF n, Valid 3 F → SparsePriority.select (ExecCNF.formulaSet F) (BinaryArithmetic.toNat w)=none →
    value (leaf ((tally N,tally n,SparseCountProgram.encodeBody F),tally h)) = rawCount F

private theorem one_visit (branches : Branches n split w) (counts : Leaves n leaf N h w)
    (two : 2≤BinaryArithmetic.toNat w) (node : Node n) (rest : List (Node n)) (total : ℕ)
    (valid : Valid 3 node.formula) :
    ∃ next, Transition 3 (BinaryArithmetic.toNat w) ⟨node::rest,total⟩ next ∧
      visit split leaf (parameters n N h w,work ⟨node::rest,total⟩) = work next := by
  let F := node.formula
  rcases branches F valid with ⟨no,term⟩ | ⟨c,H,priority,found⟩
  · refine ⟨_,.leaf node rest total term,?_⟩
    have eq := counts F valid term
    change split (w,SparseCountProgram.encodeBody node.formula) = none at no
    simp only [visit,work,parameters,List.map_cons,List.isEmpty_cons,Bool.cond_false,test,front,
      List.headD_cons,no,present,Option.elim_none,List.tail_cons,answer,positive_eq]
    change (_,decide (0<total) || decide (0<value (leaf ((tally N,tally n,SparseCountProgram.encodeBody F),tally h)))) = _
    rw [eq]
    have sum : (0<total+rawCount F) ↔ (0<total ∨ 0<rawCount F) := by omega
    change (_,decide (0<total) || decide (0<rawCount F)) = (_,decide (0<total+rawCount F))
    simp [sum]
  · refine ⟨_,.branch node rest total c H valid priority,?_⟩
    obtain ⟨vA,vB⟩ := valid.children priority (by omega)
    change split (w,SparseCountProgram.encodeBody node.formula) = _ at found
    simp only [visit,work,parameters,List.map_cons,List.isEmpty_cons,Bool.cond_false,test,front,
      List.headD_cons,found,present,Option.elim_some,Bool.cond_true,data?,List.tail_cons,prepend,id_eq]
    rw [full_body _ vA,full_body _ vB]

/-- Every accepted step decreases the mathematical DFS potential. The
natural visit count below is both a completed trace and a sufficient tape
clock for every larger externally constructed cutoff. -/
theorem completed (branches : Branches n split w) (counts : Leaves n leaf N h w)
    (two : 2≤BinaryArithmetic.toNat w) (F : RawCNF n) (valid : Valid 3 F) :
    ∃ j, Transitions 3 (BinaryArithmetic.toNat w) j ⟨[⟨F,0⟩],0⟩ ⟨[],rawCount F⟩ ∧
      ∀ u, j≤u → execute split leaf (tally u,parameters n N h w,([SparseCountProgram.encodeBody F],false)) =
        decide (0<rawCount F) := by
  let step (a : Work) := visit split leaf (parameters n N h w,a)
  have finish (s : Frontier n) (good : ∀ a ∈ s.pending, Valid 3 a.formula) :
      ∃ j b, Transitions 3 (BinaryArithmetic.toNat w) j s ⟨[],b⟩ ∧
        step^[j] (work s) = work (n:=n) ⟨[],b⟩ := by
    generalize hm : DFSCompletedTree.potential s = m
    induction m using Nat.strong_induction_on generalizing s with
    | h m ih =>
      rcases s with ⟨pending,b⟩
      cases pending with
      | nil => exact ⟨0,b,.refl _,rfl⟩
      | cons a rest =>
        obtain ⟨next,move,eq⟩ := one_visit split leaf N h w branches counts two a rest b (good a List.mem_cons_self)
        have dec := DFSCompletedTree.transition_potential_lt move two
        obtain ⟨j,t,path,run⟩ := ih _ (hm ▸ dec) next (move.pending_valid (by omega) good) rfl
        exact ⟨j+1,t,.cons move path,by rw [Function.iterate_succ_apply]; exact (congrArg (step^[j]) eq).trans run⟩
  obtain ⟨j,b,trace,run⟩ := finish ⟨[⟨F,0⟩],0⟩ (by simpa using valid)
  obtain rfl := trace.finished_count
  refine ⟨j,trace,?_⟩
  intro u le
  have fixed : step (work (n:=n) ⟨[],rawCount F⟩) = work (n:=n) ⟨[],rawCount F⟩ := rfl
  have frozen := Function.iterate_fixed (f:=step) (x:=work (n:=n) ⟨[],rawCount F⟩) fixed (u-j)
  change (step^[(tally u).length] (work (n:=n) ⟨[⟨F,0⟩],0⟩)).2 = _
  rw [tally_length,show u = u-j+j by omega,Function.iterate_add_apply,run,frozen]
  rfl

end
end OAI.Computability.MultitapeWeakETH.SparseIteration
