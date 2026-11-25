import OAI.Hierarchy.DescentBundleLanes
import OAI.Hierarchy.DescentBundleTerminal

namespace OAI
namespace Hierarchy.DescentBundleHistory
open DescentKernelHistory DescentLaneGates
noncomputable section
set_option quotPrecheck false
variable {A : Type} {w : A→ℕ} {Y p : ℕ}
    (units : A→ℕ) (multiple : ∀a,w a=units a*p) (hp : 0<p)

/-- The block at the stated offset of a strided operand. -/
def laneBlock (l : Lane p w) (i : Fin (l.count units)) : BlockRef p w :=
  ⟨l.port,(l.block units multiple hp i).val,by
    rw [multiple]
    exact Nat.mul_le_mul_right p (l.block units multiple hp i).isLt⟩

variable (q : Program Y p w) (u : q.Node)
local notation "args" => List.ofFn (Op.arg (Program.op q u))
local notation "s" => ofProgram units multiple hp q

def laneProgramNames (l : Lane p w) : List (BlockRef p w ⊕ BlockRef p q.recipe.hiddenWidth) :=
  List.ofFn (fun i : Fin (l.count units)=>.inl (laneBlock units multiple hp l i))
local notation "names" => laneProgramNames units multiple hp q

theorem program_keys : ((s).keys u)=(args).flatMap names :=by
  have rows : (s).rows u=(args).map (fun l=>[laneSlice (hw:=q.recipe.hiddenWidth) units multiple hp l]) :=by
    rw [List.map_ofFn]
    apply congrArg List.ofFn
    funext j
    change List.ofFn (fun _ : Fin 1=>_)=[_]
    simp [List.ofFn_succ]; rfl
  simp only [Shape.keys,rows,List.flatMap_map,List.flatMap_cons,List.flatMap_nil,
    List.append_nil,Slice.names]; rfl

/-- The earlier lanes contribute all of their words before the selected lane. -/
theorem program_key_on (left right : List (Lane p w)) (l : Lane p w)
    (atLane : args=left++l::right) (i : Fin (l.count units)) :
    ((s).keys u)[(left.map (fun a=>a.count units)).sum+i.val]?=
      some (.inl (laneBlock units multiple hp l i)) :=by
  have size : (left.flatMap names).length=(left.map (fun a=>a.count units)).sum:=by
    simp [List.length_flatMap,laneProgramNames]
  have within : i.val<(names l).length:=by simp [laneProgramNames]
  rw [program_keys,atLane,List.flatMap_append,List.flatMap_cons,←size,
    List.getElem?_append_right (Nat.le_add_right ..),Nat.add_sub_cancel_left,
    List.getElem?_append_left within]
  simp [laneProgramNames]

/-- A formal argument and a bounded offset give its exact flattened recipe
slot, including the source port and the first full block number. -/
theorem program_key_at (j : Fin (q.op u).arity) (i : Fin (((q.op u).arg j).count units)) :
    ((s).keys u)[(((args).take j.val).map (fun l=>l.count units)).sum+i.val]?=
      some (.inl (laneBlock units multiple hp ((q.op u).arg j) i)) :=by
  have within : j.val<(args).length:=by simp
  have cut : args=(args).take j.val++((q.op u).arg j)::(args).drop (j.val+1):=by
    calc
      args=(args).take j.val++(args).drop j.val := (List.take_append_drop ..).symm
      _=_ :=by rw [List.drop_eq_getElem_cons within];simp [List.getElem_ofFn]
  exact program_key_on units multiple hp q u _ _ _ cut i

private theorem word_partition {α : Type} (width : α→ℕ) (rows : List α) (j : ℕ)
    (inside : j<(rows.map width).sum) :
    ∃ (left : List α) (a : α) (right : List α) (i : Fin (width a)),
      rows=left++a::right ∧ j=(left.map width).sum+i.val :=by
  induction rows generalizing j with
  | nil => simp at inside
  | cons a rows ih =>
    simp only [List.map_cons,List.sum_cons] at inside
    by_cases first : j<width a
    · exact ⟨[],a,rows,⟨j,first⟩,rfl,by simp⟩
    · obtain ⟨left,b,right,i,cut,word⟩:=ih (j-width a) (by omega)
      refine ⟨a::left,b,right,i,congrArg (a::·) cut,?_⟩
      simp only [List.map_cons,List.sum_cons]
      omega

/-- Every in-range word of an authored program has an actual lane and
a within-lane address at the same position of its recipe. -/
theorem program_key_cases (j : ℕ) (live : j<((s).keys u).length) :
    ∃ (left : List (Lane p w)) (l : Lane p w) (right : List (Lane p w)) (i : Fin (l.count units)),
      args=left++l::right ∧ j=(left.map (fun a=>a.count units)).sum+i.val ∧
      ((s).keys u)[j]?=some (.inl (laneBlock units multiple hp l i)) :=by
  rw [program_keys,List.length_flatMap] at live
  simp only [laneProgramNames,List.length_ofFn] at live
  obtain ⟨left,l,right,i,cut,index⟩:=word_partition (fun l : Lane p w=>l.count units) args j live
  exact ⟨left,l,right,i,cut,index,by rw [index];exact program_key_on units multiple hp q u left right l cut i⟩

end
end Hierarchy.DescentBundleHistory

end OAI
