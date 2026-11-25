import OAI.ThreeFlat.Diagonal.ShrinkSupplyNative
import OAI.ThreeFlat.RAM.TerminalWireArchive

namespace OAI
/-! # The interleaved integer score prefix and its native two-way layout comparison -/

namespace ThreeFlat.Diagonal.ShrinkStageNav

open Computability.VPVNP.BurstRAM PrivateRAM RAM RAM.HeaderScan RAM.PhysicalPinsExpr RAM.MotifRows RAM.DescriptorScan
open RefreshDemandRows RefreshStageNav ShrinkMotif
open scoped Classical BigOperators Fin.CommRing
noncomputable section

def rowCost (w : Fin 8→ℕ) (b : Bool) := ∑ j : Fin 4,multiplier (survivor b j)*w (survivor b j)^2

def scorePrefix (w : ℕ→Fin 8→ℕ) (r : ℕ) (b : Bool) := ∑ i∈Finset.range r,rowCost (w i) b

theorem scorePrefix_succ (w : ℕ→Fin 8→ℕ) (r : ℕ) (b : Bool) :
    scorePrefix w (r+1) b=scorePrefix w r b+rowCost (w r) b := Finset.sum_range_succ ..

/-- At the final address every motif has contributed exactly once. -/
theorem scorePrefix_total {M : Type} [Fintype M] {n : ℕ} (order : M ≃ Fin n) (width : M→Fin 8→ℕ)
    (w : ℕ→Fin 8→ℕ) (same : ∀ a,w (order a).val=width a) (b : Bool) :
    scorePrefix w n b=layoutCost width b := by
  unfold scorePrefix
  rw [←Fin.sum_univ_eq_sum_range]
  rw [←order.sum_comp]
  simp only [same,rowCost,layoutCost]

variable {W : ℕ} (cur : Word W) (mem : Memory W) (arg : Word W)
open private nativeMemory nativeInput nativeValue nativeFits from
  OAI.ThreeFlat.Diagonal.ShrinkChoiceNative

private theorem eval_row_cost (p : Formula 1) (b : Bool) (w : Fin 8→ℕ) (wp : nativeFits mem arg p)
    (cap : nativeValue mem arg p+8≤2^W) (read : ∀ e : Fin 8,(nativeMemory mem) (nativeValue mem arg p+e.val)=w e) :
    nativeFits mem arg (localCost p b) ∧ nativeValue mem arg (localCost p b)=rowCost w b := by
  have wf (e : Fin 8) : nativeFits mem arg (RAM.MotifRows.field p e.val) := by
    refine ⟨⟨wp,trivial,trivial⟩,?_⟩
    change nativeValue mem arg p+e.val<_
    have := e.isLt
    omega
  constructor
  · apply RefreshDemandRows.total_fit (fun _ : Param => 0) (nativeMemory mem) (nativeInput arg)
    intro f hf
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hf
    exact ⟨trivial,⟨wf _,wf _,trivial⟩,trivial⟩
  · unfold nativeValue
    rw [localCost,totals_value,List.map_map]
    simp only [←List.ofFn_id,List.map_ofFn,Function.comp_def,List.sum_ofFn,id_eq,rowCost]
    apply Finset.sum_congr rfl
    intro j _
    let e := survivor b j
    change multiplier e * (nativeMemory mem (nativeValue mem arg p+e.val) *
      nativeMemory mem (nativeValue mem arg p+e.val)) = multiplier e * (w e)^2
    rw [read,pow_two]

theorem prefix_native (w : ℕ→Fin 8→ℕ) (row : ℕ) (f : Fin 2)
    (head : (mem cur.val).val+30<2^W) (two : 2<2^W) (addr : arg.val=nativeValue mem arg (ptr cur 30)+(row*2+f.val))
    (old : ∀ e : Fin 8,0<row → (nativeMemory mem) (nativeValue mem arg (ptr cur 3)+(row-1)*8+e.val)=w (row-1) e)
    (valid : 0<row → nativeValue mem arg (ptr cur 3)+(row-1)*8+8≤2^W)
    (prev : 0<row → (nativeMemory mem) (arg.val-2)=scorePrefix w (row-1) (decide (f.val=1))) :
    (HeaderScan.closed (prefixWords cur)).eval Fin.elim0 mem (fun _=>arg)=
      (scorePrefix w row (decide (f.val=1)):Word W) := by
  let x := rel cur 30
  let r := Formula.cut (.op .div x (.lit 2)) (.lit 1)
  let p := atRow (ptr cur 3) r 8
  have fpos := rel_fit cur mem arg 30 head
  have bp : nativeValue mem arg x<2^W := (Nat.sub_le ..).trans_lt arg.isLt
  have ix : nativeValue mem arg x=row*2+f.val := by change arg.val-nativeValue mem arg (ptr cur 30)=_; omega
  have rq : nativeValue mem arg r=row-1 := by change nativeValue mem arg x/2-1=_; rw [ix,(parts row 2 f).1]
  have pq : nativeValue mem arg p=nativeValue mem arg (ptr cur 3)+(row-1)*8 := congrArg (fun r=>nativeValue mem arg (ptr cur 3)+r*8) rq
  have fs : nativeFits mem arg r := ⟨⟨fpos,trivial,bp,two⟩,trivial,(Nat.div_le_self ..).trans_lt bp,(by change 1<_; omega)⟩
  have fp : nativeFits mem arg p := ⟨ptr_fit cur mem arg 3 (by omega),⟨fs,trivial,trivial⟩,trivial⟩
  have rowWord (b) (hp : 0<row) := eval_row_cost mem arg p b (w (row-1)) fp (by rw [pq]; exact valid hp) (fun e=>by rw [pq]; exact old e hp)
  have tail : nativeFits mem arg (.load (.cut (.reg 0) (.lit 2)) : Formula 1) :=
    ⟨⟨trivial,trivial,arg.isLt,two⟩,(Nat.sub_le ..).trans_lt arg.isLt⟩
  have key : nativeValue mem arg (.op .mod x (.lit 2))=f.val := by change nativeValue mem arg x%2=_; rw [ix,(parts row 2 f).2]
  apply closed_read mem (fun _=>arg)
  · refine ⟨fpos,trivial,bp,two,?_⟩
    split
    · trivial
    · rename_i bigger
      have hr : 0<row := by change ¬decide (nativeValue mem arg x<2)=true at bigger; have := f.isLt; simp at bigger; omega
      refine ⟨tail,⟨⟨fpos,trivial,bp,two⟩,trivial,lt_of_eq_of_lt key (f.isLt.trans two),(by change 0<_; omega),?_⟩,trivial⟩
      split <;> exact (rowWord _ hr).1
  · change (if decide (nativeValue mem arg x<2) then 0 else (nativeMemory mem) (arg.val-2)+
      (if decide (nativeValue mem arg x%2=0) then nativeValue mem arg (localCost p false) else nativeValue mem arg (localCost p true)))=_
    cases row with
    | zero => have := f.isLt; simp [ix,scorePrefix,this]
    | succ row =>
      have hi : ¬nativeValue mem arg x<2 := by rw [ix]; omega
      rw [ite_eq_right (by simpa using hi),prev (by omega),(rowWord false (by omega)).2,(rowWord true (by omega)).2,
        scorePrefix_succ]
      change nativeValue mem arg x%2=f.val at key
      rw [key]
      fin_cases f <;> rfl


end
end ThreeFlat.Diagonal.ShrinkStageNav

end OAI
