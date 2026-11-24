import OAI.Computability.VPVNP.RankQueryPlainContracts
import OAI.Computability.VPVNP.RankQueryStackGramSpace

/-!
# Full fixed Schur computation for Cramer minors

At a top-degree query of an ordinary square minor, each coefficient callback
reads one scalar at degree zero. The same finite register bank, power-basis
arithmetic, and bounded continuation stack implement every level.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RankQuery.Stack.PlainEngine

open Dispatch RAMTape Engine

variable {K : Type} [DecidableEq K] {n w v d p e B A S : ℕ}
  [Fact p.Prime] [NeZero e] {c : SliceArithmetic.Vector p e}

/-- Schur stack machine for an ordinary square minor. Its entry callback reads a matrix scalar
at degree zero and supplies zero at higher degrees. -/
def machine (read : FiniteRoutine (MacaulayRead.Port K)) :=
  Engine.machine (GramEngine.actionsWith (PlainScalar.machine read))

/-- Time bound for describing one Schur node of an ordinary minor, allowing a plain scalar
callback whose matrix-entry reader has clock `B`. -/
def descriptorClock (w v e B : ℕ) := DescribeAdapter.timeWith w v e (PlainScalar.clock w v e B)

/-- Time bound for the bidegree `(n,0)` root query of an ordinary square minor, combining the
Schur traversal bound with the time per engine step. -/
def queryTime (n w v e B : ℕ) :=
  let depth := Nat.clog 2 n+4+Nat.clog 2 n
  (5+6*SchurKey.arityBound n n 0)^(depth+1) * boundedStepTime (descriptorClock w v e B) (Assembly.localBudget w e v) w v e + 1

/-- Per-stack height bound for the bidegree `(n,0)` query, accounting for the Schur
continuation depth, initial auxiliary height `A` and peak `S` of a matrix-entry read. -/
def querySpace (n w v e A S : ℕ) :=
  let depth := Nat.clog 2 n+4+Nat.clog 2 n
  let initial := GramEngine.entryCap w v e A depth
  let descriptor := max initial (DescribeAdapter.peakWith w v e initial (fun a => PlainScalar.space w v e a S))
  boundedSpace descriptor (w+v+e+e*v+A) depth (Assembly.localBudget w e v) w v e

/-- A true run of the fixed binary-stack machine, returning the top coefficient
of the minor pencil. The independent height bound of the input-entry reader
enters space, and its running time enters only the clock. -/
theorem top_query (read : FiniteRoutine (MacaulayRead.Port K)) (M : Matrix (Fin n) (Fin n) (Scalar c))
    {readerReady : Stacks K → Prop} (hc : MacaulayRead.CorrectSpace read M w v B S readerReady)
    (ha : ∀ s, readerReady s → ∀ i, (s i).length ≤ A)
    (hv : SliceArithmetic.Word.workingWidth p ≤ v) (hw₃ : 3 ≤ w) (hw : (d+1)*widthFactor ≤ w)
    (hd : d ≤ w) (hsize : n+n+0+n+8 < 2^d)
    (s : ℕ) (hn : n ≤ 2^s) (hs : 2*s+6 ≤ w) (hws : (2*s+6+1)*widthFactor ≤ w)
    (aux : Stacks (GramEngine.Aux K)) (haux : GramEngine.Ready w v n n c readerReady aux) :
    ∃ t ≤ queryTime n w v e B, ∃ out, GramEngine.Ready w v n n c readerReady out ∧
      (machine read).BoundedRun (querySpace n w v e A S) t
        (atControl (c := c) w v (.enter (SchurKey.root (n := n) (Fin.last n) (Fin.last 0))) [] aux)
        (atControl w v (.returned (SchurKey.compute (PlainScalar.entry M) n 0)) ([] : List (F n n 0 c)) out) := by
  let call := PlainScalar.machine read
  let ent := PlainScalar.entry M
  let depth := Nat.clog 2 n+4+Nat.clog 2 n
  let initial := GramEngine.entryCap w v e A depth
  let localSpace := fun a => PlainScalar.space w v e a S
  have cr := PlainScalar.callRuns (d := d) read M hc ha hv (by omega)
  have cs : DescribeAdapter.CallSpace call ent w v n d (PlainScalar.clock w v e B) localSpace readerReady :=
    PlainScalar.callSpace read M hc hv (by omega)
  have expand (a : ℕ) : a ≤ localSpace a := by dsimp [localSpace,PlainScalar.space]; omega
  have desc : DescribeBounded (GramEngine.actionsWith call)
      (SchurKey.program (U := n) (Z := 0) ent) w v (descriptorClock w v e B)
      (max initial (DescribeAdapter.peakWith w v e initial localSpace)) depth
      (GramEngine.Ready w v n n c readerReady) :=
    GramEngine.lift_boundedWith ha (DescribeAdapter.describe_entries_bounded call ent cr cs expand hv hw₃ hw hd hsize)
  let C := M.map Polynomial.C
  have he : ∀ i j z, ent i j z = (C i j).coeff z := by
    intro i j z; simp [C, ent, PlainScalar.entry,Polynomial.coeff_C]
  rw [SchurKey.compute_correct C _ he]
  exact eval_root_bounded (GramEngine.contractsWith call ent cr hv hw₃ hw hd hsize s hn hn (Nat.zero_le _) hs hws)
    desc (fun _ hr => GramEngine.ready_length hr ha) C he (Fin.last n) (Fin.last 0) aux haux

end RankQuery.Stack.PlainEngine

end VPVNP
end Computability
end OAI
