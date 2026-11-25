import OAI.Computability.NearSquareRoot.CRTTableNativePlanSpec
import OAI.Computability.NearSquareRoot.SynchronizedPermutationQuery
import OAI.Computability.NearSquareRoot.CRTControlledFlatNumber

/-! # Reading the prepared native row at the actual padded record address -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace CRTTable.Native
open IntegerMultiplication Code Adic Controlled Controlled.PermutationLayout

noncomputable section

variable {A b G low n L : ℕ} {box : List (ℕ × ℕ)}
    (hb : BoxShape.Valid (maskWidth A b G low) L box)
    [∀ g, NeZero (BoxFin.modulus box g)]

/-- Physical CRT axis value of the indicated tape record. -/
abbrev address (x : Block 2 (maskWidth A b G low)) :=
  (BoxFin.recordIndex hb).symm (flatAddress 2 _ x)

include hb in
omit [∀ g, NeZero (BoxFin.modulus box g)] in
theorem fitAxis (g : Fin box.length) : BoxFin.modulus box g ≤ 2^(axisWidth box g) :=
  (hb.axisBounds _ (List.get_mem box g)).2.2.2

abbrev localWord (x : Block 2 (maskWidth A b G low)) (g : Fin box.length) :=
  wordEquiv (axisWidth box g) (axisNumber (fitAxis hb g) (address hb x g))

theorem originalPort (x : Block 2 (maskWidth A b G low)) (g : Fin box.length) (i : Fin (axisWidth box g)) :
    Controlled.prefixBit x (finite hb g i) = localWord hb x g i := by
  have e := boxRecord_port hb (flatAddress 2 _ x) g i
  rw [complement hb] at e
  exact (by simpa only [Equiv.symm_apply_apply] using
    Controlled.prefixBit_address (flatAddress 2 _ x) (finite hb g i) :
      Controlled.prefixBit x (finite hb g i) = (flatAddress 2 _ x).val.testBit (finite hb g i).val) |>.trans e.symm

variable (sel : Fin b → Fin (targetOrder box.length n).length) (j : ℕ)
  (pos : 0<G)
  (fit : low+2*((b+1)*G)+(controlSlots (axisWidth box) sel j).length ≤ maskWidth A b G low)
  (π : Equiv.Perm (Fin (maskWidth A b G low)))
  (place : ∀ i, π (controlPos fit i) = controls _ (total hb) sel j i)

abbrev prefixCode (x : Block 2 (maskWidth A b G low)) :=
  List.ofFn (Controlled.prefixBit (prefixWord (PositionProgram.permuteNative π x)))

include pos place in
/-- Every port contributing to an external or local control is read from
its computed prefix coordinate after the address permutation. -/
theorem readPort (x : Block 2 (maskWidth A b G low)) {p : Port (axisWidth box)}
    (hp : p ∈ controlSlots (axisWidth box) sel j) :
    Benes.prefixBit (prefixCode π x,tally (offset π G low b (finite hb p.1 p.2))) =
      localWord hb x p.1 p.2 := by
  obtain ⟨i,hi⟩ := controls_covers _ (total hb) sel j hp
  have h : π (controlPos fit i) = finite hb p.1 p.2 := (place i).trans hi
  have off : offset π G low b (finite hb p.1 p.2) = (prefixIndex pos fit i).val := by
    rw [← h]
    simp [PermutationLayout.offset,controlPos,controlOffset,prefixIndex]
  rw [off]
  exact ((Iter.entry (Controlled.prefixBit (prefixWord (PositionProgram.permuteNative π x)))
    (prefixIndex pos fit i) false).trans (prefix_source pos fit π x i)).trans
      ((congrArg (Controlled.prefixBit x) h).trans (originalPort hb x p.1 p.2))

include pos place in
/-- The complete MSF control string recovered from the prepared prefix
is precisely the input to the CRT table program on the original record. -/
theorem readExternal (x : Block 2 (maskWidth A b G low)) :
    Benes.prefixBits (prefixCode π x,(externalSlots (axisWidth box) n).map
      (fun p => tally (offset π G low b (finite hb p.1 p.2)))) =
      packedControl n (List.finRange box.length)
        (addressField (BoxFin.modulus box) (axisWidth box) (fun _ => id) (address hb x)) := by
  let w := axisWidth box
  let all := CRTTree.controls n (List.finRange box.length)
  let atPos (g : Fin box.length) (i : Fin (w g)) := offset π G low b (finite hb g i)
  have shape : ((externalSlots w n).map (fun p => tally (atPos p.1 p.2))) =
      selectionPositions w atPos all := by
    simp [externalSlots,selectionPositions,List.sigma,List.map_flatMap,List.ofFn_eq_map,
      List.map_map,Function.comp_def,all]
  change Benes.prefixBits (_, (externalSlots w n).map (fun p => tally (atPos p.1 p.2))) = _
  rw [shape]
  apply prefixBits_selectionPositions
  intro g hg
  have words : Benes.prefixWordAt (atPos g) (prefixCode π x) = localWord hb x g := by
    funext i
    apply readPort hb sel j pos fit π place x (p := ⟨g,i⟩)
    exact List.mem_append_left _ ((externalSlots_mem _).mpr ((mem_controls_iff_external _ _ g).mp hg))
  rw [words,localWord,ofFn_wordEquiv]
  exact congrArg (fun s => (Bits.phrase (w g) s).reverse) (axisNumber_val (fitAxis hb g) (address hb x g))

include pos place in
theorem readLocal (x : Block 2 (maskWidth A b G low)) (q : Fin b) (i : Fin (axisWidth box (Chosen sel q)))
    (hi : i.val ≠ j) :
    Benes.prefixWordAt (fun i => offset π G low b (finite hb (Chosen sel q) i)) (prefixCode π x) i =
      localWord hb x (Chosen sel q) i := by
  apply readPort hb sel j pos fit π place x (p := ⟨Chosen sel q,i⟩)
  exact List.mem_append_right _ ((localSlots_mem _ _ _).mpr ⟨⟨q,rfl⟩,hi⟩)


abbrev nativeTable (inv : Bool) (x : Block 2 (maskWidth A b G low)) (r : TargetIndex box.length n) :=
  packedTables _ _ (fitAxis hb) n inv ((packAddress _ _ (fitAxis hb) n (address hb x)).1) r

private theorem nativeTable_eq (inv : Bool) (x : Block 2 (maskWidth A b G low))
    (r : TargetIndex box.length n) :
    targetWordRows (tagAt (BoxFin.modulus box) (axisWidth box) n r.1.val r.2.val inv,
      packedControl n (List.finRange box.length)
        (addressField (BoxFin.modulus box) (axisWidth box) (fun _ => id) (address hb x))) = nativeTable hb inv x r := by
  let a := BoxFin.modulus box
  let w := axisWidth box
  let y := address hb x
  let e := (packAddress a w (fitAxis hb) n y).1
  apply congrArg (fun bits => targetWordRows (tagAt a w n r.1.val r.2.val inv,bits))
  unfold packedControl packFields
  apply List.flatMap_congr
  intro g hg
  have he := (mem_controls_iff_external _ _ g).mp (List.mem_reverse.mp hg)
  have hv : representative a w (fitAxis hb) n e g = y g :=
    representative_external a w (fitAxis hb) n e ⟨g,he⟩
  exact congrArg (fun z => (Bits.phrase (w g) (coordinate id z)).reverse) hv.symm

/-- The switch vector controlled by the original record and the true raw
tables of the simultaneous CRT shear. -/
def flags (inv side : Bool) (x : Block 2 (maskWidth A b G low)) (q : Fin b) : Bool :=
  let raw := nativeTable hb inv x (targetRank _ _ (sel q))
  let s := Benes.rawSetting raw j (List.ofFn (localWord hb x (Chosen sel q)))
  if side then s.2 else s.1

include pos place in
/-- The entire row mask emitted by the native physical program agrees with
the switch settings of the padded CRT, even though target bits are omitted
from the prepared prefix. -/
theorem mask_spec (hn : n < Nat.clog 2 box.length)
    (wide : ∀ q, j < axisWidth box (Chosen sel q)) (inv side : Bool)
    (x : Block 2 (maskWidth A b G low)) :
    rowMask (model hb sel side inv j (offset π G low b),prefixCode π x) =
      List.ofFn (flags hb sel j inv side x) := by
  simp only [rowMask,model,Benes.buildBatch_plan,List.map_ofFn,Function.comp_def]
  apply congrArg List.ofFn
  funext q
  rw [readExternal hb sel j pos fit π place x, nativeTable_eq hb inv x (targetRank _ _ (sel q))]
  let r := targetRank _ _ (sel q)
  let g := Chosen sel q
  let s : Fin (axisWidth box g) := ⟨j,wide q⟩
  have covers (i : Fin (axisWidth box g)) (hi : i ≠ s) :
      ∃ a, π (controlPos fit a) = finite hb g i := by
    have hm : (⟨g,i⟩ : Port (axisWidth box)) ∈ localSlots (axisWidth box) sel j := by
      apply (localSlots_mem _ _ _).mpr
      exact ⟨⟨q,rfl⟩,fun h => hi (Fin.ext h)⟩
    obtain ⟨i,he⟩ := controls_covers _ (total hb) sel j (List.mem_append_right _ hm)
    exact ⟨i,(place i).trans he⟩
  have cert := packedTables_represents _ _ (fitAxis hb) (fun g => axis_half_full hb (List.get_mem box g))
    (BoxFin.pairwise hb) n hn inv ((packAddress _ _ (fitAxis hb) n (address hb x)).1) r
  have output := Benes.PackedBatchHeader.relocated_query pos fit π (finite hb g) cert side s covers x
  dsimp only at output
  change Benes.queryBit _ = _
  refine output.trans ?_
  have word : (fun i => Controlled.prefixBit x (finite hb g i)) = localWord hb x g :=
    funext (originalPort hb x g)
  rw [word]
  rfl

end
end CRTTable.Native

end NearSquareRoot
end Computability
end OAI
