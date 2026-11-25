import OAI.Optimization.LinearProgramming.Recovery.InitialPairTranspose
import OAI.Optimization.LinearProgramming.Recovery.PublicInput

/-! Normal public entry into the first row/complement computation. The input LP, slack
tableau and its transpose occupy separate actual scalar tape windows. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Recovery
namespace InitialPair

open RAM RAM.Tape Geometry
open scoped Matrix

def program : Block := .seq PublicInput.program transposeBlock

noncomputable def stepBound (m d : ℕ) := PublicInput.stepBound m d +
  transposeTime (PublicInput.matrixBase m d) (d+1) (m+1)

structure Ready {K : Type} [Field K] {m d : ℕ} (A : Matrix (Fin m) (Fin d) K) (b : Fin m → K) (t : Memory K) : Prop where
  header : Header (PublicInput.matrixBase m d) (d+1) (m+1) t
  original : SlackRAM.InputAt t (PublicInput.sourceBase m d) A b
  tableau : uniformRect (m+1) (d+1) (PublicInput.matrixBase m d) t = slackColumns A b
  transpose : uniformRect (d+1) (m+1) (cBase (PublicInput.matrixBase m d) (d+1) (m+1)) t =
    (slackColumns A b)ᵀ
  source : t.index 24 = PublicInput.sourceBase m d
  rows : t.index 28 = m
  cols : t.index 29 = d
  high : ∀ p, 512 ≤ p → t.index p=0

set_option maxRecDepth 60000 in
set_option maxHeartbeats 1000000 in
private theorem low_writes : program.indexWritesBelow 512 = true := by decide

variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- One closed RAM block starts at the comparator's two public dimensions and ordinary
scalar tape, then leaves all physical inputs of the first pair-builder job in place. -/
theorem program_spec {m d : ℕ} (A : Matrix (Fin m) (Fin d) K) (b : Fin m → K)
    (P : K → Prop) (h0 : P 0) (h1 : P 1) (hneg : ∀ x, P x → P (-x))
    (hinput : ∀ k : ℕ, P ((lpInput A b)[k]?.getD 0)) :
    ∃ t c, c ≤ stepBound m d ∧
      Block.Eval (Memory.AllData P) program (start [m,d] (lpInput A b)).memory c t ∧ Ready A b t := by
  let g := PublicInput.matrixBase m d
  let src := PublicInput.sourceBase m d
  have source_low : 7 ≤ src := by dsimp [src,PublicInput.sourceBase]; omega
  have split : g=src+PublicInput.words m d := rfl
  have g_low : 7 ≤ g := by omega
  obtain ⟨s,j,hj,load,original,G,s24,s28,s29,s31,s33,s35⟩ :=
    PublicInput.program_spec A b P h0 h1 hneg hinput
  obtain ⟨t,k,hk,tr,mat,hh,frame,t24,t28,t29,_⟩ :=
    transpose_spec P s g (d+1) (m+1) g_low load.safe_end s31 s33 s35
  have run := load.seq tr
  have cells (i : ℕ) (hi : i < PublicInput.words m d) : t.data (src+i)=s.data (src+i) := by
    apply frame _ (by omega) (Or.inl ?_)
    unfold cBase
    omega
  have orig : SlackRAM.InputAt t src A b := by
    constructor
    · intro i l
      have ht := rectOffset_lt i l
      exact (cells _ (by unfold PublicInput.words; omega)).trans (original.1 i l)
    · intro i
      have ht := i.isLt
      exact (cells _ (by unfold PublicInput.words; omega)).trans (original.2 i)
  have retained : uniformRect (m+1) (d+1) g t = slackColumns A b := by
    ext i l
    have ht := rectOffset_lt i l
    have e := frame (g+i.val*(d+1)+l.val) (by omega) (Or.inl (by unfold cBase; omega))
    exact e.trans (congrFun (congrFun G i) l)
  refine ⟨t,j+k,Nat.add_le_add hj hk,run,hh,orig,retained,?_,t24.trans s24,t28.trans s28,t29.trans s29,?_⟩
  · exact mat.trans (congrArg Matrix.transpose G)
  · intro p hp
    apply (run.index_frame low_writes hp).trans
    change ([m,d][p]?).getD 0 = 0
    have len : [m,d].length ≤ p := by simp; omega
    simp [List.getElem?_eq_none len]

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- The six literal input-register equations for the owner of the first pair builder. -/
theorem Ready.pairHeader {m d : ℕ} {A : Matrix (Fin m) (Fin d) K} {b : Fin m → K} {t : Memory K}
    (job : Ready A b t) :
    let g := PublicInput.matrixBase m d
    t.index 200=d+1 ∧ t.index 201=m+1 ∧ t.index 202=cBase g (d+1) (m+1) ∧
    t.index 203=outBase g (d+1) (m+1) ∧ t.index 204=scratchBase g (d+1) (m+1) ∧ t.index 205=0 :=
  ⟨job.header.height,job.header.dimension,job.header.input,job.header.output,job.header.scratch,job.header.clean⟩

omit [LinearOrder K] [IsStrictOrderedRing K] in
theorem Ready.pairMatrix {m d : ℕ} {A : Matrix (Fin m) (Fin d) K} {b : Fin m → K} {t : Memory K}
    (job : Ready A b t) : uniformRect (d+1) (m+1) (t.index 202) t=(slackColumns A b)ᵀ := by
  rw [job.header.input]
  exact job.transpose

omit [LinearOrder K] [IsStrictOrderedRing K] in
theorem Ready.pairLayout {m d : ℕ} {A : Matrix (Fin m) (Fin d) K} {b : Fin m → K} {t : Memory K}
    (job : Ready A b t) :
    256 ≤ t.index 202 ∧ t.index 202+(d+1)*(m+1) ≤ t.index 203 ∧
      t.index 203+(m+1)*(m+1) ≤ t.index 204 := by
  rw [job.header.input,job.header.output,job.header.scratch]
  simp only [scratchBase,outBase,cBase,PublicInput.matrixBase,PublicInput.sourceBase]
  omega

end InitialPair
end Recovery
end LinearProgramming
end Optimization
end OAI
