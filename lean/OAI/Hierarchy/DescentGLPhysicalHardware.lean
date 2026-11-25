import OAI.Hierarchy.DescentGLPhysicalTrajectory
import OAI.Hierarchy.ProtocolRAMCheapCode

namespace OAI
/-! # Permitted instructions and storage of the compiled physical mixing program -/

namespace Hierarchy.DescentGL.PhysicalTrajectory
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section

private def size {w : ℕ} (p : Procedure w) := p.labels+p.registers+p.slots

private theorem size_seq {w : ℕ} (p q : Procedure w) : size (p.seq q)=size p+size q := by
  simp only [Procedure.seq,size]
  omega

private theorem scan_bound (w base n : ℕ) (e : Expr) (hn : 0<n) :
    size (scan w base n e)≤2*(4+n*(2*e.work+4)) := by
  obtain ⟨ls,rs,ps⟩ := scan_size w base n e
  have one := Nat.mul_le_mul_right (2*e.work+4) hn
  unfold size
  rw [ls,rs,ps]
  omega

private theorem row_cheap {h r : ℕ} (w : ℕ) (s : RowStageRAM.Shelf)
    (p : Fin (h+1+r)→ℕ) (banks : Fin (r+1)→ℕ) : CheapCode (RowStageRAM.program w s p banks) := by
  let k := h+1+r
  let input := DescentGLInputRAM.pass w s.data p banks
  let score := DescentGLScoreRAM.program w s.scores k s.data
  let choice := RowRAM.procedure w s.row (2^k) ⟨s.mask,k⟩ ⟨s.scores,k⟩
  let mask := scan w s.nextMask (2^k) (SpanRAM.next k s.mask s.row)
  have hin : CheapCode input :=
    @scan_cheap w s.data (2^k) (DescentGLInputRAM.terms p banks)
  have hscore : CheapCode score :=
    @scan_cheap w s.scores (2^k) (DescentGLScoreRAM.score k s.data)
  have hchoice : CheapCode choice :=
    @scan_cheap w s.row 1 (RowRAM.term ⟨s.mask,k⟩ ⟨s.scores,k⟩ (2^k))
  have hmask : CheapCode mask :=
    @scan_cheap w s.nextMask (2^k) (SpanRAM.next k s.mask s.row)
  exact @cheap_seq w input (score.seq (choice.seq mask)) (@hin)
    (@cheap_seq w score (choice.seq mask) (@hscore)
      (@cheap_seq w choice mask (@hchoice) (@hmask)))

private theorem row_size {h r : ℕ} (w : ℕ) (s : RowStageRAM.Shelf)
    (p : Fin (h+1+r)→ℕ) (banks : Fin (r+1)→ℕ) :
    size (RowStageRAM.program w s p banks) ≤ 2*RowStageRAM.ticks s p banks := by
  let k := h+1+r
  have a := scan_bound w s.data (2^k) (DescentGLInputRAM.terms p banks) (Nat.two_pow_pos _)
  have b := scan_bound w s.scores (2^k) (DescentGLScoreRAM.score k s.data) (Nat.two_pow_pos _)
  have c := scan_bound w s.row 1 (RowRAM.term ⟨s.mask,k⟩ ⟨s.scores,k⟩ (2^k)) (by decide)
  have d := scan_bound w s.nextMask (2^k) (SpanRAM.next k s.mask s.row) (Nat.two_pow_pos _)
  rw [SpanRAM.next_work] at d
  simp only [RowStageRAM.program,RowStageRAM.ticks,DescentGLInputRAM.pass,DescentGLScoreRAM.program,
    RowRAM.procedure,size_seq]
  dsimp [k] at *
  omega

private theorem prefix_cheap (w k base : ℕ) (bank : ℕ→ℕ) (t : ℕ) : CheapCode (rowProgram w k base bank t) := by
  induction t with
  | zero => exact @scan_cheap w base (2^k) (SpanRAM.zero k)
  | succ t ih =>
    exact @cheap_seq w (rowProgram w k base bank t) (cpu w k base bank t) (@ih)
      (@row_cheap t (k-(t+1)) w (RowStageRAM.placed k base t)
        (fun i => pointer k base i.val) (fun j => bank (t+1+j.val)))

theorem program_cheap (w k base : ℕ) (bank : ℕ→ℕ) : CheapCode (program w k base bank) :=
  @cheap_seq w (rowProgram w k base bank k)
    (DescentGLPermutationRAM.program w (outputBase k base) (fun i : Fin k => pointer k base i.val))
    (@prefix_cheap w k base bank k) (@scan_cheap w (outputBase k base) (2^k)
      (DescentGLPermutationRAM.expression (fun i : Fin k => pointer k base i.val)))

private theorem prefix_size (w k base : ℕ) (bank : ℕ→ℕ) (t : ℕ) :
    size (rowProgram w k base bank t) ≤ 2*time k base bank t := by
  induction t with
  | zero => exact scan_bound w base (2^k) (SpanRAM.zero k) (Nat.two_pow_pos k)
  | succ t ih =>
    have curr : size (cpu w k base bank t)≤2*charge k base bank t := row_size ..
    simp only [rowProgram,size_seq,time]
    omega

theorem program_size (w k base : ℕ) (bank : ℕ→ℕ) :
    let compiled := program w k base bank
    compiled.labels+compiled.registers+compiled.slots ≤ 2*(time k base bank k+DescentGLPermutationRAM.clock k) := by
  have prev := prefix_size w k base bank k
  have final := scan_bound w (outputBase k base) (2^k)
    (DescentGLPermutationRAM.expression (fun i : Fin k=>pointer k base i.val)) (Nat.two_pow_pos k)
  rw [DescentGLPermutationRAM.work] at final
  change size _≤_
  rw [program,size_seq]
  unfold DescentGLPermutationRAM.program DescentGLPermutationRAM.clock
  omega

end
end Hierarchy.DescentGL.PhysicalTrajectory

end OAI
