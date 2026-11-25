import OAI.ThreeFlat.Diagonal.RefreshGraphWork
import OAI.ThreeFlat.Diagonal.RefreshFormulaWork
import OAI.ThreeFlat.Diagonal.RefreshKernelRecords

namespace OAI
/-! # A fixed static instruction bound for the nine native refresh passes -/

namespace ThreeFlat.Diagonal.RefreshStageNav

open Computability.VPVNP.BurstRAM Computability.VPVNP.Compression RAM RAM.HeaderScan RAM.DescriptorExpr RAM.PhysicalPinsExpr
open RAM.MotifRows RefreshDemandRows CompressorPacking.Native RefreshDemandRows.Static
open scoped BigOperators

variable {W U a h k : ℕ}

private theorem choiceWord_work (c : Word W) (c' : Word U)
    (base : Fin (k+1) → (Bool × Fin (mPort a) × Fin (mPort a)) → ℕ)
    (size : Fin (k+1) → ℕ) : Same (choiceWords c base size) (choiceWords c' base size) := by
  let z := fun {w} (p : Word w) => refreshChoice (input p) (field p 8) (.op .div (index p 2) (.lit 3)) base
  have eq : PairSame (z c) (z c') :=
    refresh_work (input c) (input c') (field c 8) (field c' 8)
      (.op .div (index c 2) (.lit 3)) (.op .div (index c' 2) (.lit 3)) rfl rfl rfl base
  have ls : Same (rowAt (k+1) (fun i => .lit (size i)) (z c).2)
      (rowAt (k+1) (fun i => .lit (size i)) (z c').2) := lookup_work _ _ eq.2 (fun _=>rfl)
  change _+_+(z c).1.work+(_+_+(z c).2.work+_+1)+1 =
    _+_+(z c').1.work+(_+_+(z c').2.work+_+1)+1
  rw [eq.1,eq.2,ls]
  rfl

private theorem graphWord_work (c : Word W) (c' : Word U) (E : SlotGraph (Fin (mPort a)) h) (pad : ℕ) :
    (graphWords c E pad).binds=(graphWords c' E pad).binds := by
  unfold graphWords
  apply Refresh.columns_work
  · rw [binds_closed,binds_closed]; rfl
  · rw [binds_closed,binds_closed]; rfl
  all_goals intro b; cases b <;> simp only [binds_closed] <;> rfl

private theorem motifWord_work (c : Word W) (c' : Word U) (m K : ℕ) : Same (Records.motif c m K) (Records.motif c' m K) := by
  unfold Records.motif
  apply lookup_work _ _ rfl
  intro i; fin_cases i <;> first | rfl | exact lookup_work _ _ rfl (fun _=>rfl)

private theorem halfWord_work (c : Word W) (c' : Word U) (d : ℕ) : Same (Records.halves c d) (Records.halves c' d) := by
  let r := fun {W} (c : Word W) => Formula.op .div (index c 40) (.lit 4)
  let s := fun {W} (c : Word W) => Formula.op .div (r c) (.lit (2*d))
  let i := fun {W} (c : Word W) => Formula.op .mod (r c) (.lit (2*d))
  let summand {w} (p : Word w) (j : Fin (2*d)) : Formula 1 :=
    .select .lt (.lit j.val) (i p)
      (ShrinkStage.Halves.half (Records.halfColumns p) d (s p) (.lit j.val)).width (.lit 0)
  have pre : Same (ShrinkStage.Halves.prefix (Records.halfColumns c) d (s c) (i c))
      (ShrinkStage.Halves.prefix (Records.halfColumns c') d (s c') (i c')) :=
    (folds (List.finRange (2*d)) (summand c) (summand c') (fun _ => rfl)).1
  change _+_+_+(_+_+_+(_+_+_+(ShrinkStage.Halves.prefix _ _ _ _).work+1)+1)+1=_
  rw [pre]
  rfl

/-- Program fragments in their invocation order, including the four persistent
site-record scans executed after width publication. -/
noncomputable def compiledRows (current : Word W) (E : SlotGraph (Fin (mPort a)) h) (pad stride : ℕ)
    (base : Fin (k+1) → (Bool × Fin (mPort a) × Fin (mPort a)) → ℕ)
    (size bits : Fin (k+1) → ℕ) (pool : ∀ j, Fin (size j) → Fin (mPort a) → Fin h → ℕ) : Fin 9 → Term W 0 1 :=
  ![closed (splitShifts (mPort a) current),closed (choiceWords current base size),graphWords current E pad,
    closed (generateWidth (input current) (field current 8) (index current 19) (field current 1)
      pad stride base size bits pool),
    closed (sparseCopy (mPort a) h pad current),closed (Records.kernel current),
    closed (Records.motif current (mPort a) stride),closed (Records.halfHeader current (1+h+pad)),
    closed (Records.halves current (1+h+pad))]

private theorem vec_binds {n : ℕ} {x : Term W 0 1} {y : Term U 0 1}
    {xs : Fin n → Term W 0 1} {ys : Fin n → Term U 0 1}
    (first : x.binds=y.binds) (rest : ∀ j, (xs j).binds=(ys j).binds) :
    ∀ i, (Matrix.vecCons x xs i).binds=(Matrix.vecCons y ys i).binds := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa only [Matrix.cons_val_zero] using first
  · simpa only [Matrix.cons_val_succ] using rest j

private theorem closed_binds_of_work {x y : Formula 1} (h : Same x y) :
    (closed x : Term W 0 1).binds=(closed y : Term U 0 1).binds := by
  simpa only [binds_closed] using h

set_option maxHeartbeats 1000000 in
theorem compiledRows_work (c : Word W) (c' : Word U) (E : SlotGraph (Fin (mPort a)) h) (pad stride : ℕ)
    (base : Fin (k+1) → (Bool × Fin (mPort a) × Fin (mPort a)) → ℕ)
    (size bits : Fin (k+1) → ℕ) (pool : ∀ j, Fin (size j) → Fin (mPort a) → Fin h → ℕ) (i : Fin 9) :
    (compiledRows c E pad stride base size bits pool i).binds=(compiledRows c' E pad stride base size bits pool i).binds := by
  revert i
  unfold compiledRows
  refine vec_binds (closed_binds_of_work rfl) ?_
  refine vec_binds (closed_binds_of_work (choiceWord_work c c' base size)) ?_
  refine vec_binds (graphWord_work c c' E pad) ?_
  refine vec_binds (closed_binds_of_work ?_) ?_
  · exact width_work (input c) (input c') (field c 8) (field c' 8)
      (index c 19) (index c' 19) (field c 1) (field c' 1) rfl rfl rfl rfl
      pad stride base size bits pool
  refine vec_binds (closed_binds_of_work rfl) ?_
  refine vec_binds (closed_binds_of_work rfl) ?_
  refine vec_binds (closed_binds_of_work (motifWord_work c c' (mPort a) stride)) ?_
  refine vec_binds (closed_binds_of_work rfl) ?_
  exact vec_binds (closed_binds_of_work (halfWord_work c c' (1+h+pad))) (fun j => Fin.elim0 j)

private theorem rows_cost (rows : ∀ u, Word u → Fin 9 → Term u 0 1)
    (same : ∀ u (c : Word u) i, (rows u c i).binds=(rows 1 0 i).binds) :
    ∃ B : ℕ, ∀ u (c : Word u) (i : Fin 9),
      let e := rows u c i
      13+e.labels ≤ B ∧ 4+e.binds ≤ B ∧ 2*e.binds+4 ≤ B := by
  let work := ∑ i, (rows 1 0 i).binds
  refine ⟨14+3*work,?_⟩
  intro u c i
  have bound : (rows 1 0 i).binds ≤ work :=
    Finset.single_le_sum (f:=fun j : Fin 9 => (rows 1 0 j).binds) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  dsimp only
  rw [Term.labels_eq,same]
  omega

set_option maxHeartbeats 1000000 in
/-- One constant simultaneously bounds labels, registers, and loop cost per
word at every diagonal scale. Its only arguments are the finite spectral
table, the fixed expander, and fixed slot/histogram degree bounds. -/
theorem uniform_row_cost (E : SlotGraph (Fin (mPort a)) h) (pad stride : ℕ)
    (base : Fin (k+1) → (Bool × Fin (mPort a) × Fin (mPort a)) → ℕ)
    (size bits : Fin (k+1) → ℕ) (pool : ∀ j, Fin (size j) → Fin (mPort a) → Fin h → ℕ) :
    ∃ B : ℕ, ∀ W (c : Word W) (i : Fin 9),
      let e := compiledRows c E pad stride base size bits pool i
      13+e.labels ≤ B ∧ 4+e.binds ≤ B ∧ 2*e.binds+4 ≤ B := by
  exact rows_cost (fun _ c => compiledRows c E pad stride base size bits pool)
    (fun _ c i => compiledRows_work c (0:Word 1) E pad stride base size bits pool i)

private theorem nine_scan_cost {X : Type*} (x₀ x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ : X) (f : X → ℕ) {B : ℕ}
    (rowBound : ∀ i : Fin 9, f (![x₀,x₁,x₂,x₃,x₄,x₅,x₆,x₇,x₈] i) ≤ B) :
    ((f x₀+f x₁)+(f x₂+(f x₃+f x₄)))+(f x₅+(f x₆+(f x₇+f x₈))) ≤ 9*B := by
  have b₀ : f x₀ ≤ B := rowBound 0
  have b₁ : f x₁ ≤ B := rowBound 1
  have b₂ : f x₂ ≤ B := rowBound 2
  have b₃ : f x₃ ≤ B := rowBound 3
  have b₄ : f x₄ ≤ B := rowBound 4
  have b₅ : f x₅ ≤ B := rowBound 5
  have b₆ : f x₆ ≤ B := rowBound 6
  have b₇ : f x₇ ≤ B := rowBound 7
  have b₈ : f x₈ ≤ B := rowBound 8
  omega

set_option maxHeartbeats 900000 in
/-- Cost bound for the exact three pieces installed by NavigationPass.refresh;
the choice parser and outer advance have their own independent costs. -/
theorem uniform_pass_cost (E : SlotGraph (Fin (mPort a)) h) (pad stride : ℕ)
    (base : Fin (k+1) → (Bool × Fin (mPort a) × Fin (mPort a)) → ℕ)
    (size bits : Fin (k+1) → ℕ) (pool : ∀ j, Fin (size j) → Fin (mPort a) → Fin h → ℕ) :
    ∃ B : ℕ, ∀ W (c : Word W),
      let before := prepare c base size
      let after := commit c E pad stride base size bits pool
      let records := (Records.pipeline c (mPort a) (1+h+pad) stride).program
      before.labels+after.labels+records.labels≤B ∧ before.registers+after.registers+records.registers≤B := by
  obtain ⟨B,cap⟩ := uniform_row_cost E pad stride base size bits pool
  refine ⟨9*B,?_⟩
  intro W c
  let x₀ : Term W 0 1 := closed (splitShifts (mPort a) c)
  let x₁ : Term W 0 1 := closed (choiceWords c base size)
  let x₂ : Term W 0 1 := graphWords c E pad
  let x₃ : Term W 0 1 := closed (generateWidth (input c) (field c 8) (index c 19) (field c 1)
    pad stride base size bits pool)
  let x₄ : Term W 0 1 := closed (sparseCopy (mPort a) h pad c)
  let x₅ : Term W 0 1 := closed (Records.kernel c)
  let x₆ : Term W 0 1 := closed (Records.motif c (mPort a) stride)
  let x₇ : Term W 0 1 := closed (Records.halfHeader c (1+h+pad))
  let x₈ : Term W 0 1 := closed (Records.halves c (1+h+pad))
  have labels := nine_scan_cost x₀ x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ (fun e => 13+e.labels)
    (fun i => (cap W c i).1)
  have registers := nine_scan_cost x₀ x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ (fun e => 4+e.binds)
    (fun i => (cap W c i).2.1)
  have joinLabels (x y : PhysicalProcedure.Procedure W) : (x.seq y).labels=x.labels+y.labels := rfl
  have joinRegs (x y : PhysicalProcedure.Procedure W) : (x.seq y).registers=x.registers+y.registers := rfl
  have joinProgram (x y : Pipeline W) : (x.thenDo y).program=x.program.seq y.program := rfl
  have scanProgram (i j : ℕ) (e : Term W 0 1) :
      (Pipeline.scan c i j e).program=HeaderScan.procedure c i j e := rfl
  have scanLabels (i j : ℕ) (e : Term W 0 1) : (HeaderScan.procedure c i j e).labels=13+e.labels := rfl
  have scanRegs (i j : ℕ) (e : Term W 0 1) : (HeaderScan.procedure c i j e).registers=4+e.binds := rfl
  simp only [prepare,commit,Records.pipeline,joinProgram,scanProgram,joinLabels,joinRegs,scanLabels,scanRegs]
  exact ⟨labels,registers⟩

end ThreeFlat.Diagonal.RefreshStageNav

end OAI
