import OAI.Computability.MultitapeWeakETH.SwitchFactor
import OAI.Computability.MultitapeWeakETH.InitialIncidence
import OAI.Computability.VPVNP.PairSimulationLeafCoordinates

/-! # Decoding the stage, side, and lane of an original traversal row -/

namespace OAI.Computability.MultitapeWeakETH.CNFNetwork.SwitchFactor

open IntegerMultiplication Code NearSquareRoot.Benes VPVNP Compression PackedSwitches
open SyntaxProgram SiteCheck
open private stages from OAI.Computability.MultitapeWeakETH.PackedFormula
open private stages_axis stage_prev from OAI.Computability.MultitapeWeakETH.InitialIncidence

abbrev StageIndex := Tally × Tally

private def tail (s : Tally) : Tally := List.casesOn s [] (fun _ t => t)
private theorem tail_easy : Easy tail := Easy.listCase [] Easy.snd

private def lastIndex (d : Tally) := tail (d++d)
private theorem lastIndex_poly : Poly lastIndex := (Poly.identity.app Poly.identity).compose tail_easy.poly

def sideAxis (q : StageIndex) : Bool × Tally :=
  bif Iter.small q.swap then (false,q.2) else (true,(cutLists (q.2,lastIndex q.1)).2)

theorem sideAxis_poly : Poly sideAxis := by
  have remaining := (Easy.snd.poly.pair (Easy.fst.poly.compose lastIndex_poly)).compose (easy_cut Easy.identity).sndCompose.poly
  exact Poly.choose (Easy.exchange.compose Iter.small_easy).poly ((Code.Poly.const false).pair Easy.snd.poly)
    ((Code.Poly.const true).pair remaining)

def prevIndex (q : StageIndex) := bif Iter.small (q.2,[()]) then lastIndex q.1 else tail q.2

theorem prevIndex_poly : Poly prevIndex :=
  Poly.choose ((Easy.snd.pair (Easy.const [()])).compose Iter.small_easy).poly
    (Easy.fst.poly.compose lastIndex_poly) (Easy.snd.compose tail_easy).poly

private theorem tail_length (s : Tally) : (tail s).length = s.length-1 := by cases s <;> rfl

private theorem last_eq (d : ℕ) : lastIndex (tally d) = tally (2*d-1) := by
  rw [← recover_tally (lastIndex _)]
  simp only [lastIndex,tail_length,List.length_append,tally_length,two_mul]

theorem sideAxis_eq {d : ℕ} (hd : 1 ≤ d) (i : Fin (2*d-2+2)) :
    sideAxis (tally d,tally i.val) = ((stages d hd i).1,tally (stages d hd i).2) := by
  have side : (stages d hd i).1 = decide (d ≤ i.val) := by
    simp only [stages,executionOrder,List.getElem_append,List.length_map,List.length_range]
    split <;> rename_i h <;> simp [h]
    omega
  simp only [sideAxis,Iter.small,Prod.swap,tally_length,stages_axis,InitialIncidence.axis,side]
  by_cases lt : i.val < d
  · simp [lt,Nat.not_le.mpr lt]
  · simp only [lt,decide_false,Bool.cond_false,ite_false,Nat.le_of_not_gt lt,decide_true,last_eq,cutLists,tally_length]
    rw [← recover_tally ((tally (2*d-1)).drop i.val)]
    simp

theorem prevIndex_eq {d : ℕ} (hd : 1 ≤ d) (i : Fin (2*d-2+2)) :
    prevIndex (tally d,tally i.val) = tally ((finRotate _).symm i).val := by
  rw [stage_prev hd i]
  by_cases e : i.val=0
  · simp [prevIndex,Iter.small,e,last_eq,InitialIncidence.prevStage]
  · simp only [prevIndex,Iter.small,tally_length,List.length_singleton,Nat.lt_one_iff,decide_eq_false e,Bool.cond_false,
      InitialIncidence.prevStage,ite_eq_right e]
    rw [← recover_tally (tail _),tail_length,tally_length]

theorem axis_bound {d : ℕ} (hd : 1 ≤ d) (i : Fin (2*d-2+2)) : (stages d hd i).2 < d := by
  rw [stages_axis,InitialIncidence.axis]
  split <;> omega

theorem laneField_eq {g : ℕ} (v : BitWord g) :
    (field (tally g,tally (bitWordFinEquiv g v).val)).reverse = laneBytes v := by
  rw [field_eq]
  change (List.ofFn _).reverse = List.ofFn _
  apply List.ext_getElem
  · simp
  · intro j hj hj'
    have h : j<g := by simpa using hj'
    let i : Fin g := ⟨j,h⟩
    simp only [List.getElem_reverse,List.length_ofFn,List.getElem_ofFn]
    let k : Fin g := ⟨g-1-j,by omega⟩
    have ek : k = i.rev := Fin.ext (by simp [k,i,Fin.val_rev]; omega)
    change RAMSerialization.wordBits g (bitWordFinEquiv g v) k = finTwoEquiv (v i)
    rw [ek,← LiveHeader.testBit_wordBits,PairSimulation.LeafCoordinates.index_bit,Fin.rev_rev]

end OAI.Computability.MultitapeWeakETH.CNFNetwork.SwitchFactor
