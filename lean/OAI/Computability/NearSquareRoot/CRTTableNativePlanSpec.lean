import OAI.Computability.NearSquareRoot.CRTTableNativePlan

/-! # Correctness of the emitted CRT staging directory -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace CRTTable.Native
open IntegerMultiplication Code Benes.FieldDirectory Controlled Controlled.PermutationLayout

theorem reverse_lookup {k : ℕ} (f : Fin k → Tally) {p : ℕ} (hp : p < k) :
    Iter.pick [] ((List.ofFn f).reverse,tally p) = f (⟨p,hp⟩ : Fin k).rev := by
  rw [Iter.search _ _ p (by simpa using hp), List.getElem_reverse, List.getElem_ofFn]
  apply congrArg f
  apply Fin.ext
  simp [Fin.val_rev]
  omega

variable {box : List (ℕ × ℕ)} {k L b n : ℕ} (hb : BoxShape.Valid k L box)

include hb in
theorem total : ∑ g, axisWidth box g = k :=
  (Fin.sum_univ_fun_getElem box Prod.fst).trans hb.widthSum

abbrev finite (g : Fin box.length) (i : Fin (axisWidth box g)) : Fin k :=
  finitePort _ (total hb) ⟨g,i⟩

theorem complement (g : Fin box.length) (i : Fin (axisWidth box g)) :
    k - 1 - fieldPosition (axisWidth box) (List.finRange box.length) g i = (finite hb g i).val := by
  rw [finite,finitePort_val]
  exact fieldPosition_lsb hb g i

include hb in
theorem position_lt (g : Fin box.length) (i : Fin (axisWidth box g)) :
    fieldPosition (axisWidth box) (List.finRange box.length) g i < k := by
  have h := fieldPosition_lt (axisWidth box) (List.finRange box.length) g (by simp) i
  rwa [← List.ofFn_eq_map,List.sum_ofFn,total hb] at h

variable (sel : Fin b → Fin (targetOrder box.length n).length) (side inv : Bool) (j G low : ℕ)

include k box n sel side inv j G low in
def seed : Seed :=
  (((side,tally j),inv,tally n,(List.finRange box.length).map (descriptor (BoxFin.modulus box) (axisWidth box))),
    (tally low,tally G),tally k,List.ofFn fun q => tally (sel q).val)

noncomputable def model (lift : Fin k → ℕ) : Benes.BatchPlan TargetTag :=
  let a := BoxFin.modulus box
  let w := axisWidth box
  Benes.makePlan side j
    ((externalSlots w n).map fun e => tally (lift (finite hb e.1 e.2))) (w ∘ Chosen sel)
    (fun q => tagAt a w n (targetRank _ _ (sel q)).1.val (targetRank _ _ (sel q)).2.val inv)
    (fun q i => lift (finite hb (Chosen sel q) i))

/-- A directory indexed in numeric low-bit order becomes the MSF table-reader's
directory by reversal. Only bit positions belonging to actual fields are read. -/
theorem prepared_spec (hn : n ≤ Nat.clog 2 box.length) (lift : Fin k → ℕ) :
    preparedPlan ((seed (k:=k) sel side inv j G low).1,
      (List.ofFn fun g => tally (lift g)).reverse,(seed (k:=k) sel side inv j G low).2.2.2) =
      model hb sel side inv j lift := by
  let w := axisWidth box
  let axes := List.finRange box.length
  let transport (p : ℕ) := if h : p < k then lift (⟨p,h⟩ : Fin k).rev else 0
  have read (p : ℕ) (hp : p < k) :
      Iter.pick [] ((List.ofFn fun g => tally (lift g)).reverse,tally p) = tally (transport p) := by
    rw [reverse_lookup _ hp]
    simp [transport,hp]
  have slot (g : Fin box.length) (i : Fin (w g)) :
      transport (fieldPosition w (List.finRange box.length) g i) = lift (finite hb g i) := by
    have hlt : fieldPosition w (List.finRange box.length) g i < k := position_lt hb g i
    dsimp only [transport]
    rw [dite_eq_left hlt]
    apply congrArg lift
    apply Fin.ext
    simpa [Fin.val_rev, Nat.sub_sub, Nat.add_comm] using complement hb g i
  have H := preparedPlan_makePlan (BoxFin.modulus box) w n hn inv side j
    ((List.ofFn fun g => tally (lift g)).reverse) transport sel
  have outer (u : Tally) (hu : u ∈ levelPositions w axes n) : u.length < k := by
    rw [externalSlots_eq] at hu
    obtain ⟨p,_,rfl⟩ := List.mem_map.mp hu
    simpa only [tally_length] using position_lt hb p.1 p.2
  have out := H (fun u hu => by simpa only [recover_tally] using read u.length (outer u hu))
    (fun q i => read _ (position_lt hb _ _))
  refine out.trans ?_
  simp only [model, externalSlots_eq, List.map_map, Function.comp_def, tally_length,slot]
  rfl

theorem naturalPlan_spec (hn : n ≤ Nat.clog 2 box.length) :
    naturalPlan (seed (k:=k) sel side inv j G low) = model hb sel side inv j Fin.val := by
  simpa only [seed,naturalPlan,Iter.lined] using prepared_spec hb sel side inv j G low hn Fin.val

private theorem split_rows (w : Fin box.length → ℕ) (f : (g : Fin box.length) → Fin (w g) → ℕ)
    (tag : Fin b → TargetTag) (outer : List Tally)
    (wide : ∀ q, j < w (Chosen sel q)) :
    banks (Benes.makePlan side j outer (w ∘ Chosen sel) tag (fun q => f (Chosen sel q))) =
      (List.ofFn (fun q => tally (f (Chosen sel q) ⟨j,wide q⟩)),
        outer ++ (localSlots w sel j).map (fun z => tally (f z.1 z.2))) := by
  let row (q : Fin b) := (List.finRange (w (Chosen sel q))).eraseIdx j
  have split (q : Fin b) :
      Benes.FieldDirectory.split (tally j,List.ofFn (fun i => tally (f (Chosen sel q) i))) =
        ([tally (f (Chosen sel q) ⟨j,wide q⟩)], (row q).map fun r => tally (f (Chosen sel q) r)) := by
    rw [split_active _ _ (by simpa using wide q), List.getElem_ofFn, ← List.eraseIdx_eq_take_drop_succ]
    congr 1
    simp only [List.ofFn_eq_map, List.eraseIdx_map, row]
  simp only [List.ofFn_eq_map] at split
  simp [banks,Benes.makePlan,polyPush,localSlots,List.sigma,List.flatMap_def,List.map_map,
    Function.comp_def,List.ofFn_eq_map,split,row]
  induction List.finRange b with
  | nil => rfl
  | cons q qs ih => simp [ih]


private theorem bank_spec (wide : ∀ q, j < axisWidth box (Chosen sel q)) :
    banks (model hb sel side inv j Fin.val) =
      (List.ofFn (fun q => tally (targets _ (total hb) sel j wide q).val),
        List.ofFn fun i => tally (controls _ (total hb) sel j i).val) := by
  dsimp only [model]
  refine (split_rows sel side j _ (fun g i => (finite hb g i).val) _ _ wide).trans ?_
  congr 1
  let ps := controlSlots (axisWidth box) sel j
  change _ = List.ofFn (fun i => tally ((finitePort _ (total hb)) (ps.get i)).val)
  calc
    _ = ps.map (fun p => tally (finite hb p.1 p.2).val) := (List.map_append ..).symm
    _ = _ := by
      conv_lhs => rw [← List.ofFn_get ps, List.map_ofFn]
      rfl

/-- The two generated address tables move precisely the selected target bits
and the required control bits into their physical locations. Their prepared
row plan addresses the prefix using the inverse permutation. -/
theorem prepare_spec (hn : n ≤ Nat.clog 2 box.length) (hinj : Function.Injective sel)
    (wide : ∀ q, j < axisWidth box (Chosen sel q))
    (pos : 0 < G) (fit : low + 2*((b+1)*G) + (controlSlots (axisWidth box) sel j).length ≤ k) :
    ∃ π : Equiv.Perm (Fin k),
      (∀ q, π (targetPos pos fit q) = targets _ (total hb) sel j wide q) ∧
      (∀ i, π (controlPos fit i) = controls _ (total hb) sel j i) ∧
      (∀ i, offset π G low b (controls _ (total hb) sel j i) = i.val) ∧
      prepare (seed (k:=k) sel side inv j G low) =
        ((Reflections.table π,Reflections.table π.symm),model hb sel side inv j (offset π G low b)) := by
  obtain ⟨π,ht,hc,ho,hd⟩ := directory_spec (targets_injective _ (total hb) sel j hinj wide)
    (controls_injective _ (total hb) sel j hinj) (targets_ne_controls _ (total hb) sel j wide) pos fit
  refine ⟨π,ht,hc,ho,?_⟩
  have actual : placement (seed (k:=k) sel side inv j G low) =
      ((Reflections.table π,Reflections.table π.symm),List.ofFn fun i => tally (offset π G low b i)) := by
    unfold placement
    rw [naturalPlan_spec hb sel side inv j G low hn, bank_spec hb sel side inv j wide]
    exact hd
  rw [prepare,actual]
  exact congrArg (Prod.mk _) (prepared_spec hb sel side inv j G low hn (offset π G low b))

end CRTTable.Native

end NearSquareRoot
end Computability
end OAI
