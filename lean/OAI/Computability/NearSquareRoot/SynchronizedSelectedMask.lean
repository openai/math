import OAI.Computability.NearSquareRoot.SynchronizedPhysicalBits
import OAI.Computability.NearSquareRoot.SynchronizedBoxPlanProgram
import OAI.Computability.NearSquareRoot.SynchronizedRoutingProgram
import OAI.Computability.NearSquareRoot.PrecisionSlotSchedule

/-! # Computing all physical Walsh mask bits of an indexed row -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace ShortFourier.BatchWord

open IntegerMultiplication Code Strip Staff SynchronizedLayers.ScheduleProgram SynchronizedBlocks
open BoxFin

abbrev MaskInput := (Bool × Tally) × Tally
abbrev MaskHeader := List (Tally × Tally) × Row SlotDescriptor

/-- Add the widths of all earlier axes and the high-bit index in this block's first axis. -/
def bitAddress (p : List (Tally × Tally) × Tally) : Tally :=
  let i := 4*p.2.length
  ((p.1.take i).map Prod.fst).flatten ++ (Iter.pick ([],[]) (p.1,tally i)).1.tail

private def bitEntry (p : MaskHeader × Tally) : List Tally :=
  if (readBlock p.1.2 p.2.length).isSome then [bitAddress (p.1.1,p.2)] else []

/-- The set is produced as a list of positions in increasing block order. -/
def livePositions (p : MaskHeader) : List Tally :=
  (Iter.lineup (tally (p.1.length/4))).flatMap (fun j => bitEntry (p,j))

/-- A mask in physical bit order, with one Boolean per bit of the packed array address. -/
def emittedMask (p : MaskInput) : List Bool :=
  let row := (directedPlan p.1)[p.2.length]?.getD (false,(false,false),[])
  let used := livePositions (BoxProgram.encoded p.1.2,row.2)
  (Iter.lineup p.1.2).map (fun q => decide (q ∈ used))

private def maskRegime (X : Type) [Codec X] : Regime X := ⟨size,send,Dom.base _⟩

private theorem lengthHas {I X : Type} [Codec X] {r : Regime I} {f : I → List X}
    (H : r.Has f) : Realizes r (fun j => (f j).length) := by
  change r.Has (fun i => tally (f i).length)
  have he (i : I) : ruler (f i) = tally (f i).length := by
    rw [← recover_tally (ruler (f i)), ruler_length]
  simpa only [id_eq,he] using H.ez (Easy.ruler Easy.identity)

private theorem tailEasy {X : Type} [Codec X] : Easy (List.tail (α := X)) := by
  have e : List.tail (α := X) = (fun xs => List.casesOn xs [] fun _ t => t) := by
    funext xs
    cases xs <;> rfl
  rw [e]
  exact Easy.listCase [] Easy.snd

private theorem bitAddress_poly : Poly bitAddress := by
  let X := List (Tally × Tally) × Tally
  let R := maskRegime X
  have inp : R.Has id := R.self
  have J := lengthHas (inp.ez Easy.snd)
  have I := (Realizes.fix 4).times J
  have L := inp.ez Easy.fst
  have take := (I.pair L).ez (easy_cut Easy.identity).fstCompose
  have before := (take.thenDo (Poly.maps _ Easy.fst.poly)).ez Easy.flatten
  have atIndex := (L.pair I).ez (Iter.facile ([],[]))
  change R.Has bitAddress
  unfold bitAddress
  simpa only [cutLists,id_eq,Function.comp_def,box,tally_length] using
    (before.pair ((atIndex.ez Easy.fst).ez tailEasy)).ez Easy.append

private theorem bitEntry_poly : Poly bitEntry := by
  let R := maskRegime (MaskHeader × Tally)
  have inp : R.Has id := R.self
  have Q := PhaseTable.readBlockAvailable ((inp.ez Easy.fst).ez Easy.snd) (lengthHas (inp.ez Easy.snd))
  have H : Poly (fun p : MaskHeader × Tally => (readBlock p.1.2 p.2.length).isSome) := by
    have H := Q.ez (PhaseTable.easyOption false (fun _ : SlotDescriptor => true) (Easy.const _))
    change R.Has (fun p => (readBlock p.1.2 p.2.length).isSome)
    have he (o : Option SlotDescriptor) : o.elim false (fun _ => true) = o.isSome := by cases o <;> rfl
    simpa only [he,id_eq] using H
  have A : Poly (fun p : MaskHeader × Tally => bitAddress (p.1.1,p.2)) :=
    (show Poly (fun p : MaskHeader × Tally => (p.1.1,p.2)) by fun_prop).compose bitAddress_poly
  have answer := Code.Poly.choose H (A.compose (show Poly (fun x : Tally => [x]) by fun_prop)) (Code.Poly.const ([] : List Tally))
  convert answer using 1
  funext p
  cases h : (readBlock p.1.2 p.2.length).isSome <;> simp [bitEntry,h]

theorem livePositions_poly : Poly livePositions := by
  let R := maskRegime MaskHeader
  have H : R.Has id := R.self
  have n : Poly (fun p : MaskHeader => tally (p.1.length/4)) :=
    (lengthHas (H.ez Easy.fst)).dividing (Realizes.fix 4)
  exact ((Poly.identity.pair (n.compose Iter.poly_line)).compose
    (Poly.push ([],(false,false),[]) [] bitEntry_poly)).compose Easy.flatten.poly

theorem emittedMask_poly : Poly emittedMask := by
  let R := maskRegime MaskInput
  have H : R.Has id := R.self
  have boxes := ((H.ez Easy.fst).ez Easy.snd).thenDo BoxProgram.encoded_poly
  have rows := (H.ez Easy.fst).thenDo directedPlan_poly
  have one := PhaseTable.headerElement (false,(false,false),[]) rows (lengthHas (H.ez Easy.snd))
  have used := (boxes.pair (one.ez Easy.snd)).thenDo livePositions_poly
  have eqn : Poly (fun p : Tally × Tally => decide (p.1=p.2)) := by
    simpa only [← List.length_injective.eq_iff] using (Iter.linked (X := Unit) (Y := Unit)).poly
  have test := Easy.exchange.poly.compose (RoutingTable.contains_poly eqn)
  change R.Has emittedMask
  unfold emittedMask
  have answer := (used.pair (((H.ez Easy.fst).ez Easy.snd).thenDo Iter.poly_line)).thenDo (Poly.push [] [] test)
  simp only [polyPush,Prod.fst_swap,Prod.snd_swap,id_eq] at answer
  convert answer using 1
  funext p
  apply List.map_congr_left
  intro q _
  exact congrArg (fun d => @decide (q ∈ livePositions (BoxProgram.encoded p.1.2,
    ((directedPlan p.1)[p.2.length]?.getD (false,(false,false),[])).2)) d) (Subsingleton.elim _ _)

private theorem prefixWidth {b : List (ℕ × ℕ)} (i : Fin b.length) :
    (((b.take i.val).map Prod.fst).sum) = offset i := by
  have h : b.take i.val = List.ofFn (fun j : Fin i.val => b.get (Fin.castLE i.isLt.le j)) := by
    apply List.ext_getElem
    · simp [i.isLt.le]
    · intro j hj hj'
      simp
  rw [h,List.map_ofFn,List.sum_ofFn]
  rfl

theorem bitAddress_eq {k : ℕ} (hb : BoxShape.Valid k (BoxScale.width k) (CoprimeBox.box k))
    (j : Fin ((CoprimeBox.box k).length/4)) :
    bitAddress (BoxProgram.encoded (tally k),tally j.val) = tally ((selectedPosition hb j).val) := by
  let b := CoprimeBox.box k
  let i := axis j (firstAxis j)
  have ei : 4*j.val = i.val := by rfl
  have el : (BoxProgram.encoded (tally k)) = b.map (fun t => (tally t.1,tally t.2)) := by
    simp [BoxProgram.encoded,b]
  rw [bitAddress,el]
  apply List.length_injective
  simp only [tally_length, ei, List.length_append, List.length_flatten, ← List.map_take,
    List.map_map, Function.comp_def, List.length_tail]
  have hget : b[i.val]? = some (b.get i) := List.getElem?_eq_getElem i.isLt
  have hsum : ((b.map Prod.fst).take i.val).sum = offset i := by
    rw [← List.map_take]
    exact prefixWidth i
  simpa [Iter.pick,hsum,hget] using (show offset i + ((b.get i).1 - 1) = (selectedPosition hb j).val from rfl)

theorem emittedMask_eq {k : ℕ} (hb : BoxShape.Valid k (BoxScale.width k) (CoprimeBox.box k)) (dir : Bool)
    (t : Fin (directedPlan (dir,tally k)).length) :
    emittedMask ((dir,tally k),tally t.val) = List.ofFn (fun q : Fin k =>
      decide (q ∈ (Finset.univ.filter (fun j : Fin ((CoprimeBox.box k).length/4) =>
        (readBlock (directedPlan (dir,tally k))[t.val].2 j.val).isSome)).image (selectedPosition hb))) := by
  let r := (directedPlan (dir,tally k))[t.val].2
  have el : (BoxProgram.encoded (tally k)).length = (CoprimeBox.box k).length := by simp [BoxProgram.encoded]
  simp only [emittedMask,tally_length,List.getElem?_eq_getElem t.isLt,Option.getD_some,
    Iter.lined,List.map_ofFn,Function.comp_def]
  apply congrArg List.ofFn
  funext q
  simp only [decide_eq_decide]
  simp only [livePositions,el,Iter.lined,List.mem_flatMap,List.mem_ofFn, Finset.mem_image,Finset.mem_filter,
    Finset.mem_univ,true_and]
  constructor
  · rintro ⟨v,⟨j,rfl⟩,hj⟩
    simp only [bitEntry,tally_length] at hj
    split at hj
    · rename_i yes
      rw [List.mem_singleton,bitAddress_eq hb] at hj
      exact ⟨j,yes,Fin.ext (by simpa using congrArg List.length hj.symm)⟩
    · simp at hj
  · rintro ⟨j,hj,rfl⟩
    refine ⟨tally j.val,⟨j,rfl⟩,?_⟩
    simp only [bitEntry,tally_length,hj,ite_true,List.mem_singleton,bitAddress_eq hb]

end ShortFourier.BatchWord

end NearSquareRoot
end Computability
end OAI
