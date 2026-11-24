import OAI.Computability.VPVNP.RankCoordinateNativeReader
import OAI.Computability.VPVNP.RankQueryPlainRoot

/-! # Running two ordinary determinant queries inside the evaluator reader -/

namespace OAI
namespace Computability
namespace VPVNP

namespace RankQuery.Stack.Coordinate.NativeReader

open RAMTape UniversalCountStack SliceArithmetic Dispatch
open Cramer

variable {A H K L : Type} [DecidableEq A] [DecidableEq H] [Fintype H] [DecidableEq K] [DecidableEq L]

/-- Workspace of the two Schur determinant engines and their quotient routine. Each engine has
a Gram-engine auxiliary bank and reads ordinary entries of its own square minor. -/
abbrev PairedHost (K L : Type) := Workspace (GramEngine.Aux K) (GramEngine.Aux L)

/-- Construct the coordinate callback from the two literal matrix-entry routines and a common
preparation stage. -/
noncomputable def pairCore (host : PairedHost K L ↪ H) (scratch : H) (prepare : FiniteRoutine (Bus A H))
    (den : FiniteRoutine (MacaulayRead.Port K)) (num : FiniteRoutine (MacaulayRead.Port L)) :=
  core host scratch prepare (GramEngine.actionsWith (PlainScalar.machine den)) (GramEngine.actionsWith (PlainScalar.machine num))

/-- Clock allowance for preparation, both determinant queries, field division, result copying,
and workspace reclamation. -/
def pairTime (H : Type) [Fintype H] (setup r w v e B peak : ℕ) :=
  setup+2*PlainEngine.queryTime r w v e B + divideClock e v + returnClock H peak

variable {p e r w v d B S V s setup peak : ℕ} [Fact p.Prime] [NeZero e] {c : Vector p e}

/-- With the roots staged from advice and the matrix-address parameters
installed, the fixed reader makes the two determinant calls itself. -/
theorem pairCore_bounded (host : PairedHost K L ↪ H) (scratch : H) (disjoint : ∀ i, host i ≠ scratch)
    (prepare : FiniteRoutine (Bus A H)) (den : FiniteRoutine (MacaulayRead.Port K))
    (num : FiniteRoutine (MacaulayRead.Port L)) (D N : Matrix (Fin r) (Fin r) (Scalar c))
    {readyD : Stacks K → Prop} {readyN : Stacks L → Prop}
    (hD : MacaulayRead.CorrectSpace den D w v B S readyD) (hN : MacaulayRead.CorrectSpace num N w v B S readyN)
    (haD : ∀ a, readyD a → ∀ i, (a i).length ≤ V) (haN : ∀ a, readyN a → ∀ i, (a i).length ≤ V)
    (hv : Word.workingWidth p ≤ v) (hw₃ : 3 ≤ w) (hw : (d+1)*widthFactor ≤ w) (hd : d ≤ w)
    (hsize : r+r+0+r+8 < 2^d) (hn : r ≤ 2^s) (hs : 2*s+6 ≤ w) (hws : (2*s+6+1)*widthFactor ≤ w)
    (hquery : PlainEngine.querySpace r w v e V S ≤ peak) (hroom : (e+1)*(v+1) + divideClock e v ≤ peak)
    (label current next : List Bool) (advice : Stacks A) (work : Stacks H) (hscratch : work scratch = [])
    (denAux : Stacks (GramEngine.Aux K)) (numAux : Stacks (GramEngine.Aux L))
    (readyDen : GramEngine.Ready w v r r c readyD denAux) (readyNum : GramEngine.Ready w v r r c readyN numAux)
    (hhost : ∀ i, work (host i) = SchurPair.host (SchurPair.entryBank c r w v denAux)
      (SchurPair.entryBank c r w v numAux) (frame p e v (digits v c) [] [] []) i)
    (hsetup : prepare.BoundedRun peak setup (state label current next [] advice (fun _ => []))
      (state label current next [] advice work)) :
    ∃ t ≤ pairTime H setup r w v e B peak, (pairCore host scratch prepare den num).BoundedRun
      (peak+returnClock H peak) t (state label current next [] advice (fun _ => []))
      (state label current next (digits v (minorQuotient c N D)) advice (fun _ => [])) := by
  obtain ⟨td,htd,dout,_,rd⟩ := PlainEngine.top_query den D hD haD hv hw₃ hw hd hsize s hn hs hws denAux readyDen
  obtain ⟨tn,htn,nout,_,rn⟩ := PlainEngine.top_query num N hN haN hv hw₃ hw hd hsize s hn hs hws numAux readyNum
  let a := GramEngine.actionsWith (PlainScalar.machine den)
  let b := GramEngine.actionsWith (PlainScalar.machine num)
  obtain ⟨t,ht,both⟩ := SchurPair.query_runs a b c hv N D (rd.enlarge hquery) (rn.enlarge hquery) rfl rfl hroom
  obtain ⟨u,hu,run⟩ := core_bounded host scratch disjoint prepare a b label current next advice work hscratch
    _ _ hhost (digits v (minorQuotient c N D)) rfl hsetup both
  exact ⟨u,by unfold pairTime; omega,run⟩

end RankQuery.Stack.Coordinate.NativeReader

end VPVNP
end Computability
end OAI
