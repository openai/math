import OAI.Optimization.LinearProgramming.Recovery.InitialPairBounds
import OAI.Optimization.LinearProgramming.Recovery.PairBuilderProgram

/-! Public layout, retained source data, and the actual initial pair-building ROM
common to the rational and ordered-field executions. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Recovery
namespace InitialPair

open RAM RAM.Call RAM.Callable RAM.Tape Matrix Geometry
open scoped Matrix

variable {K : Type} [Field K]

def layout (m d : ℕ) : PairBuilder.Layout (d+1) (m+1) where
  src := cBase (PublicInput.matrixBase m d) (d+1) (m+1)
  out := outBase (PublicInput.matrixBase m d) (d+1) (m+1)
  scratch := scratchBase (PublicInput.matrixBase m d) (d+1) (m+1)
  previous := 0
  minimum := by unfold cBase PublicInput.matrixBase PublicInput.sourceBase; omega
  sourceRoom := le_rfl
  outputRoom := le_rfl

theorem Ready.inputRegs {m d : ℕ} {A : Matrix (Fin m) (Fin d) K} {b : Fin m → K} {t : Memory K}
    (ready : Ready A b t) : PairBuilder.InputRegs (layout m d) t :=
  ⟨ready.header.height,ready.header.dimension,ready.header.input,ready.header.output,
   ready.header.scratch,ready.header.clean⟩

def blank : Memory ℚ := (start [] ([] : List ℚ)).memory

structure Retained {m d : ℕ} (A : Matrix (Fin m) (Fin d) K) (b : Fin m → K) (back : Memory K) : Prop where
  original : SlackRAM.InputAt back (PublicInput.sourceBase m d) A b
  tableau : uniformRect (m+1) (d+1) (PublicInput.matrixBase m d) back=slackColumns A b
  transpose : uniformRect (d+1) (m+1) (layout m d).src back=(slackColumns A b)ᵀ
  source : back.index 24=PublicInput.sourceBase m d
  rows : back.index 28=m
  cols : back.index 29=d
  high : ∀ p, 512≤p → back.index p=0

theorem retained_after_pair {m d : ℕ} {A : Matrix (Fin m) (Fin d) K} {b : Fin m → K}
    {caller back : Memory K} (ready : Ready A b caller) (frame : PairBuilder.SourceFrame (layout m d) caller back) :
    Retained A b back := by
  let src := PublicInput.sourceBase m d
  let g := PublicInput.matrixBase m d
  let l := layout m d
  have src7 : 7 ≤ src := by unfold src PublicInput.sourceBase; omega
  have split : g=src+PublicInput.words m d := rfl
  have first : g+(m+1)*(d+1)=l.src := rfl
  have hroom := l.sourceRoom
  have oroom := l.outputRoom
  have read (p : ℕ) (hp : 7 ≤ p) (ho : p < l.out) : back.data p=caller.data p :=
    frame.2 p (by omega) (Or.inl ho) (Or.inl (show p < l.scratch by omega))
  have rect (r c a : ℕ) (lo : 7 ≤ a) (hi : a+r*c ≤ l.out) : uniformRect r c a back=uniformRect r c a caller := by
    ext i j
    have ht := rectOffset_lt i j
    exact read _ (by omega) (by omega)
  have raw (a : ℕ) (ha : a<PublicInput.words m d) := read (src+a) (by omega) (by omega)
  refine ⟨⟨?_,?_⟩,(rect _ _ g (by omega) (by omega)).trans ready.tableau,
    (rect _ _ l.src (by omega) hroom).trans ready.transpose,
    (frame.1 24 (by unfold PairBuilder.Held; omega)).trans ready.source,
    (frame.1 28 (by unfold PairBuilder.Held; omega)).trans ready.rows,
    (frame.1 29 (by unfold PairBuilder.Held; omega)).trans ready.cols,?_⟩
  · intro i j
    have ht := rectOffset_lt i j
    exact (raw _ (by unfold PublicInput.words; omega)).trans (ready.original.1 i j)
  · intro i
    have ht := i.isLt
    exact (raw _ (by unfold PublicInput.words; omega)).trans (ready.original.2 i)
  · intro p hp
    exact (frame.1 p (by unfold PairBuilder.Held; omega)).trans (ready.high p hp)

def fragment : Fragment := (Odd.leaf program).seq (PairBuilder.program false)

noncomputable def fragmentTime (m d : ℕ) :=
  4*stepPolynomial.eval (m+d) + PairBuilder.time (layout m d)

def fragmentWidth (m d e : ℕ) := max e (PairBuilder.pairWidth (d+1) (m+1) e)

end InitialPair
end Recovery
end LinearProgramming
end Optimization
end OAI
