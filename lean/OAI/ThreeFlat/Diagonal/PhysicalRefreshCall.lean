import OAI.ThreeFlat.RAM.PhysicalExactRun
import OAI.ThreeFlat.Diagonal.PhysicalRefreshBank
import OAI.ThreeFlat.Diagonal.RefreshOwnerImage
import OAI.ThreeFlat.RAM.AdmissionPost

namespace OAI
/-! # The exact native suffix invoked after the refresh count guard -/

namespace ThreeFlat.Diagonal.PhysicalStage

open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.Compression RAM RAM.HeaderScan RAM.PhysicalProcedure NavigationDirectory
open CompressorPacking Native RefreshDemandRows RefreshTies RefreshStageNav
open scoped Classical BigOperators Fin.CommRing
noncomputable section

variable {F : Type} [Field F] {W s h pad K : ℕ} {c : Fin (2^s)→Fin (2^s)→ℕ} {C : ℝ}
    (T : RefreshMotif.Table F c (1+h+pad) C) (sym : ∀ i j,c i j=c j i)
    (rows : ∀ i,∑ j,c i j=h) (zero : ∀ i,c i i=0)
    (cur : Word W)
local notation "m" => 2^s
local notation "d" => 1+h+pad

def refreshPre := preScans cur T.base (fun j=>Fintype.card (T.block j).Alphabet)

def refreshPost (K : ℕ) := postScans cur (DoublePorts.ofMatrix (Equiv.refl _) c sym rows zero) pad K
  T.base (fun j=>Fintype.card (T.block j).Alphabet) (fun j=>(T.block j).bits) (poolOf T rows)

def refreshSuffix (K : ℕ) : Procedure W :=
  ((refreshPost T sym rows zero cur K).pipeline cur).program.seq
    (((recordScans cur m d K).pipeline cur).program.seq
      (((RefreshNodeOwners.both cur m).pipeline cur).program.seq (NextStage.procedure cur)))

def refreshAfter (K : ℕ) (mem : Memory W) : Memory W :=
  let p := ((refreshPost T sym rows zero cur K).pipeline cur).run mem
  let r := ((recordScans cur m d K).pipeline cur).run p
  NextStage.memory cur (((RefreshNodeOwners.both cur m).pipeline cur).run r)

def refreshTailTime (K : ℕ) (word : ℕ→ℕ) :=
  (refreshPost T sym rows zero cur K).time word+((recordScans cur m d K).time word+
    ((RefreshNodeOwners.both cur m).time word+6))

@[simp] theorem refresh_native_code (K : ℕ) : NavigationPass.refresh cur K s h pad T sym rows zero=
    ((refreshPre T cur).pipeline cur).program.seq ((NavigationPass.admit cur K).seq (refreshSuffix T sym rows zero cur K)) := by
  simp only [NavigationPass.refresh, refreshPre, refreshSuffix, refreshPost, pre_pipeline, post_pipeline,
    record_pipeline, RefreshNodeOwners.both_program, prepare, preparation, commit, publication,
    Pipeline.thenDo, Pipeline.scan]
  delta RefreshDemandRows.poolOf RefreshTies.numbering
  rfl

private theorem exact_return (program : Procedure W) (first last : Memory W)
    (extra : Memory W → Prop) (budget : ℕ)
    (run : program.Spec (fun x=>x=first) (fun _ out=>out=last ∧ extra out) budget) :
    program.Exec first last budget :=
  Procedure.Spec.mono (A:=program) (pre:=fun x=>x=first)
    (post:=fun _ out=>out=last ∧ extra out) (budget:=budget)
    run (fun _=>id) (fun _ _ r=>r.1) le_rfl

theorem refresh_tail_returns {v t : ℕ} (K : ℕ) (mem : Memory W) (csr : Cursor)
    (u : CursorSpace cur mem csr K v s t h pad) :
    let entry := allocate K csr (.refresh v m (2^t) h pad)
    (refreshSuffix T sym rows zero cur K).Spec (fun x=>x=mem)
      (fun _ out=>out=refreshAfter T sym rows zero cur K mem) (refreshTailTime T sym rows zero cur K entry.words) := by
  let entry := allocate K csr (.refresh v m (2^t) h pad)
  let w := entry.words
  let out := fun i : ℕ=>i<csr.heap ∨ entry.next.heap≤ i
  let p := refreshPost T sym rows zero cur K
  let rs := recordScans cur m d K
  let os := RefreshNodeOwners.both cur m
  let a := (p.pipeline cur).run mem
  let b := (rs.pipeline cur).run a
  let z := (os.pipeline cur).run b
  have sp : p.every (Scans.Safe 63 w out) :=
    u.post_safe (DoublePorts.ofMatrix (Equiv.refl _) c sym rows zero) T.base _ _ (poolOf T rows)
  have pf : (p.pipeline cur).program.Exec mem a (p.time w) :=
    exact_return _ _ _ _ _ (u.call p sp)
  have fr := p.run_spec cur mem csr.header 63 w out u.header (.inr u.controls) u.start_live sp
  have ua : CursorSpace cur a csr K v s t h pad := u.frame _ fr.2.2
  have rf : (rs.pipeline cur).program.Exec a b (rs.time w) :=
    exact_return _ _ _ _ _ (ua.call rs ua.recorder_safe)
  have rfr := rs.run_spec cur a csr.header 63 w out ua.header (.inr ua.controls) ua.start_live ua.recorder_safe
  have ub : CursorSpace cur b csr K v s t h pad := ua.frame _ rfr.2.2
  have ofn : (os.pipeline cur).program.Exec b z (os.time w) :=
    exact_return _ _ _ _ _ (ub.call os (RefreshNodeOwners.safe ub))
  dsimp only
  intro P R J M pc reg pub exit installed data cfg initial start input
  exact (pf.then (rf.then (ofn.then (NextStage.spec cur z)))) M pc reg pub exit installed data cfg initial start input


end
end ThreeFlat.Diagonal.PhysicalStage

end OAI
