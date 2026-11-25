import OAI.ThreeFlat.RAM.PhysicalProcedureSize
import OAI.ThreeFlat.Diagonal.NavigationBody
import OAI.ThreeFlat.Diagonal.RefreshStageWork
import OAI.ThreeFlat.Diagonal.ShrinkRowScan

namespace OAI
/-! # Uniform hardware size of one native repeated shrink-and-refresh block -/
namespace ThreeFlat.Diagonal.NavigationPass
open Computability.VPVNP.BurstRAM RAM RAM.PhysicalProcedure RAM.DescriptorExpr RAM.PhysicalPinsExpr
open RAM.HistoryStageBody.Physical (resources resources_seq resources_scan)
open CompressorPacking CompressorPacking.Native PhysicalStage
open scoped BigOperators Classical
noncomputable section
variable {F : Type} [Field F] {W U : ℕ}

theorem parser_resources (cur : Word W) (K : ℕ) : resources (admit cur K)=14+4*AdmissionBank.cost 0 K := by
  change 9+((AdmissionBank.rowTerm cur.val K : Term W 0 1).labels)+(4+(AdmissionBank.rowTerm cur.val K : Term W 0 1).binds)+0=_
  rw [Term.labels_eq,AdmissionBank.binds_row,AdmissionBank.cost_eq]
  omega

private theorem recipe_shape (r : ShrinkStage.Recipe) (x : Word W) (y : Word U) :
    (r.install x).labels=(r.install y).labels ∧ (r.install x).regs=(r.install y).regs := by
  induction r with
  | one f a b =>
    simp only [ShrinkStage.Recipe.install,ShrinkStage.Pass.labels,ShrinkStage.Pass.regs,Term.labels_eq,ShrinkStage.Template.emit_work]
    all_goals constructor <;> first | rfl | trivial
  | seq a b ia ib =>
    simp only [ShrinkStage.Recipe.install,ShrinkStage.Pass.labels,ShrinkStage.Pass.regs,ia.1,ib.1,ia.2,ib.2,true_and]

private theorem recipe_resources (p : ShrinkStage.Recipe) (x : Word W) (y : Word U) :
    resources (scan x (p.install x))=resources (scan y (p.install y)) := by
  change (p.install x).labels+(p.install x).regs+1 = (p.install y).labels+(p.install y).regs+1
  rw [(recipe_shape p x y).1,(recipe_shape p x y).2]

theorem shrink_text (cur : Word W) (K s D : ℕ) (T : ShrinkMotif.Table F) :
    resources (shrink cur K s D T)=resources (shrink (0:Word 1) K s D T) := by
  let size := fun i => Fintype.card (T.block (T.row i)).Alphabet
  let bits := fun i => (T.block (T.row i)).bits
  let table := fun i (j : Fin (size i)) e => (T.block (T.row i)).output ((Fintype.equivFin _).symm j) e
  have e := ShrinkStageNav.scan_work (T.base ∘ T.row) size bits table K cur (0:Word 1)
  simp only [shrink,ShrinkStage.pre,resources_seq,ShrinkStageNav.prepare,ShrinkStageNav.commit,resources_scan,
    HeaderScan.binds_closed,parser_resources]
  rw [recipe_resources _ cur (0:Word 1),recipe_resources _ cur (0:Word 1),e.1,e.2.1,e.2.2.1,e.2.2.2]
  all_goals rfl

theorem refresh_text (K s h pad : ℕ) {c : Fin (2^s)→Fin (2^s)→ℕ} {C : ℝ}
    (T : RefreshMotif.Table F c (1+h+pad) C) (sym : ∀i j,c i j=c j i)
    (rows : ∀i,∑j,c i j=h) (zero : ∀i,c i i=0) :
    ∃ N : ℕ,∀ W (cur : Word W),resources (refresh cur K s h pad T sym rows zero)≤N := by
  let size := fun i=>Fintype.card (T.block i).Alphabet
  let bits := fun i=>(T.block i).bits
  let number := DoublePorts.arcNumber (Equiv.refl _) c rows
  let table := fun i (j : Fin (size i)) a b=>(T.block i).output ((Fintype.equivFin _).symm j) (number.symm (a,b))
  let E := DoublePorts.ofMatrix (Equiv.refl _) c sym rows zero
  obtain ⟨N,hn⟩ := RefreshStageNav.uniform_pass_cost E pad K T.base size bits table
  let own := resources (RefreshNodeOwners.procedure (0:Word 1) (2^s))
  refine ⟨2*N+14+4*AdmissionBank.cost 0 K+own+9,?_⟩
  intro W cur
  let pre := RefreshStageNav.prepare cur T.base size
  let post := RefreshStageNav.commit cur E pad K T.base size bits table
  let records := (RefreshStageNav.Records.pipeline cur (2^s) (1+h+pad) K).program
  have sizes : pre.labels+post.labels+records.labels≤N ∧ pre.registers+post.registers+records.registers≤N := hn W cur
  have slots : pre.slots+post.slots+records.slots=0 := rfl
  have arch : resources (RefreshNodeOwners.procedure cur (2^s))=own := by
    simp only [own,RefreshNodeOwners.procedure,resources_seq,resources_scan,HeaderScan.binds_closed]
    all_goals rfl
  change resources (pre.seq ((admit cur K).seq (post.seq (records.seq ((RefreshNodeOwners.procedure cur (2^s)).seq _)))))≤_
  simp only [resources_seq,arch,parser_resources]
  change resources pre+(_+(resources post+(resources records+(own+9))))≤_
  unfold resources
  omega

theorem compile_text {s : ℕ} (P : Program F s) (K : ℕ) :
    ∃ N : ℕ,∀ W (cur : Word W),resources (compile cur K P)≤N := by
  induction P with
  | done => exact ⟨2,fun _ _=>le_rfl⟩
  | shrink s t T sm tail ih =>
    obtain ⟨n,hn⟩ := ih
    refine ⟨resources (shrink (0:Word 1) K s (2^t) T)+n,?_⟩
    intro W c
    rw [compile,resources_seq,shrink_text c]
    exact Nat.add_le_add_left (hn W c) _
  | refresh s t h p c C H T a b sym rows loop hC h' tail ih =>
    obtain ⟨n,hn⟩ := ih
    obtain ⟨m,hm⟩ := refresh_text K s h p T sym rows loop
    exact ⟨m+n,fun W cur=>by rw [compile,resources_seq];exact Nat.add_le_add (hm W cur) (hn W cur)⟩

/-- One deterministic block is stored once, at any repetition count and word width. -/
theorem repeated_hardware (B : Block F) (K : ℕ) :
    ∃ N : ℕ,∀ W (current counter : Word W),resources (repeated current counter K B)≤N := by
  obtain ⟨N,hn⟩:=compile_text (B.prefix (.done _)) K
  refine ⟨10+N,?_⟩
  intro W current counter
  rw [repeated,loop_size]
  exact Nat.add_le_add_left (hn W current) 10


end
end ThreeFlat.Diagonal.NavigationPass

end OAI
