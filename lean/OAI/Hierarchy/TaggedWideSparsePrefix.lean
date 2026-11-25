import OAI.Hierarchy.TaggedWidePrefixNative

namespace OAI
/-! # Original sparse paid, goods and reserve keys in the native prefix scan -/

noncomputable section
namespace Hierarchy.Tagged.PassiveWindow
open scoped Classical BigOperators
variable {n g D : ℕ} (key : Fin n → Fin g) (width : Fin n → ℕ)

/-- A native comparison may skip arbitrary inactive row numbers. -/
theorem local_prefix_key (tag : Fin n → ℕ) (strict : StrictMono tag)
    (head : Fin n) (ch : Fin g) (ord other value : Fin D → ℕ) (target : ℕ)
    (place : {i : Fin n // 0<width i ∧ key i=ch} ↪ Fin D)
    (observed : ∀i,ord (place i)=tag i.val ∧ other (place i)=target ∧ value (place i)=width i.val)
    (empty : ∀q,q∉Set.range place → other q≠target ∨ value q=0) :
    (∑q : Fin D,if ord q<tag head ∧ other q=target then value q else 0)=
      TaggedShorterCommonScan.earlier key width head.val ch := by
  rw [original_prefix]
  let used := fun i : Fin n=>0<width i ∧ key i=ch
  let load := fun q : Fin D=>if ord q<tag head ∧ other q=target then value q else 0
  calc
    _ = ∑q∈Finset.univ.map place,load q := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro q _ outside
      have miss : q∉Set.range place := by
        simpa only [Finset.mem_map,Finset.mem_univ,true_and,Set.mem_range] using outside
      rcases empty q miss with h|h <;> simp [load,h]
    _ = ∑i : {i : Fin n // used i},if i.val.val<head.val then width i.val else 0 := by
      rw [Finset.sum_map]
      apply Finset.sum_congr rfl
      intro i _
      simp only [load,(observed i).1,(observed i).2.1,(observed i).2.2,and_true,strict.lt_iff_lt,Fin.lt_def]
    _ = _ := by
      apply Finset.sum_bij_ne_zero (fun i _ _=>i.val)
      · simp
      · intro a _ _ b _ _ h
        exact Subtype.ext h
      · intro i _ nonzero
        split_ifs at nonzero with test
        · have pos := Nat.pos_of_ne_zero nonzero
          exact ⟨⟨i,pos,test.2⟩,Finset.mem_univ _,by simpa [test.1] using nonzero,rfl⟩
        · contradiction
      · intro i _ _
        simp only [i.property.2,and_true]

end Hierarchy.Tagged.PassiveWindow

namespace Hierarchy.ProtocolRAM.LocalPrefix
open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM DescriptorExpr
open scoped Fin.CommRing BigOperators Classical
theorem read_sparse {W n g D : ℕ} (row : Fin D → Columns) (head : Columns) (m : Memory W) (r : Word W)
    (key : Fin n → Fin g) (width : Fin n→ℕ) (tag : Fin n → ℕ) (strict : StrictMono tag) (i : Fin n)
    (place : {j : Fin n // 0<width j ∧ key j=key i} ↪ Fin D)
    (headOrd : (head.ordinal.eval m r).val=tag i)
    (localRows : ∀j,((row (place j)).ordinal.eval m r).val=tag j.val ∧
      ((row (place j)).opposite.eval m r).val=(head.opposite.eval m r).val ∧
      ((row (place j)).width.eval m r).val=width j.val)
    (blanks : ∀q,q∉Set.range place → ((row q).opposite.eval m r).val≠(head.opposite.eval m r).val ∨
      ((row q).width.eval m r).val=0) :
    (expr row head).eval m r=(TaggedShorterCommonScan.earlier key width i.val (key i):Word W) := by
  let ord := fun q=>((row q).ordinal.eval m r).val
  let other := fun q=>((row q).opposite.eval m r).val
  let value := fun q=>((row q).width.eval m r).val
  rw [←Tagged.PassiveWindow.local_prefix_key key width tag strict i (key i) ord other value
    (head.opposite.eval m r).val place localRows blanks,Nat.cast_sum,expr,total_eval]
  apply Finset.sum_congr rfl
  intro q _
  by_cases earlier : ord q<tag i <;> by_cases same : other q=(head.opposite.eval m r).val <;>
    simp_all [term,Expr.eval,Comparison.test,ord,other,value,←Fin.ext_iff,Fin.lt_def]

end Hierarchy.ProtocolRAM.LocalPrefix

end
end OAI
