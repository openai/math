import OAI.ThreeFlat.Diagonal.CompressorWordRows

namespace OAI
/-! # Interpretation of the linked chronological successor-row template -/
namespace ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkStage.Template
open Computability.VPVNP.BurstRAM Computability.VPVNP.BurstRAM.PrivateRAM RAM.PhysicalPinsExpr RAM.DescriptorExpr Placement
open scoped Fin.NatCast
variable {w : ℕ} (cell : Word w) (pub : Fin 1 → Word w) (mem : Memory w) (vs : Fin 1 → Word w)
local notation "V" => Formula.value (fun _ => cell) mem vs
local notation "e" => emit cell

theorem bind_value {n : ℕ} (f : Formula n) (vs : Fin n → Word w) (data : Param → Word w) :
    (bindCurrent cell.val f).value data mem vs = f.value (fun _ => cell) mem vs := by
  induction f <;> simp [bindCurrent,Formula.value, *]

@[simp] theorem program_value (x : F) : (e x).eval pub mem vs=V x := by
  rw [emit,Formula.eval_compile,bind_value]

theorem valueOps : OpMap o (words mem) (Formula.value (fun _ => cell) mem vs) where
  lit _ := rfl
  bin _ _ _ := rfl
  load _ := rfl
  choose x y a b := by simp [o,Demand.formulaOps,words,Formula.value,Comparison.test]

include pub in
theorem rank_value (one : (1:Word w)≠0) (k : F) (xs : List F) :
    V (below k xs)=((Rank.below (xs.map V) (V k)).card:Word w) := by
  rw [←program_value cell pub,emit_below]
  change Rank.val pub mem vs (Rank.rank (e k) (xs.map e)) = _
  rw [Rank.eval_rank pub mem vs one]
  simp [Rank.vals,Rank.val,List.map_map,Function.comp_def]

include pub in
theorem pick_value (one : (1:Word w)≠0) (k : F) (xs : List F) :
    V (pick k xs)=Rank.chosen (xs.map V) (V k) (xs.map V) := by
  rw [←program_value cell pub,emit_pick]
  change Rank.val pub mem vs (Rank.pick (e k) (xs.map e) (xs.map e)) = _
  rw [Rank.eval_pick pub mem vs one]
  simp [Rank.vals,Rank.val,List.map_map,Function.comp_def]

def physicalCandidates (S : Graph.Stage) (lay rev : Bool) (b : Word w) : List (Graph.Candidate (Word w)) :=
  Graph.allWords (words mem) (g.map V) ((radices o ptr S).map V) S lay rev b

theorem candidate_values (S : Graph.Stage) (lay rev : Bool) (b : F) :
    (candidates S lay rev b).map (Graph.Candidate.map V) = physicalCandidates cell mem vs S lay rev (V b) := by
  rw [Graph.template_candidates,Graph.map_allWords (valueOps cell mem vs)]
  rfl

private theorem map_keys (cs : List (Graph.Candidate F)) :
    (cs.map Graph.Candidate.key).map V = (cs.map (Graph.Candidate.map V)).map Graph.Candidate.key := by
  simp [List.map_map,Function.comp_def,Graph.Candidate.map]

private theorem field_value (cs : List (Graph.Candidate F)) (id : F)
    (f : Graph.Candidate F → F) (result : Graph.Candidate (Word w) → Word w)
    (commutes : ∀a,V (f a)=result (a.map V)) :
    V (cs.foldr (fun a z => .select .eq a.key id (f a) z) (.lit 0)) =
      Graph.readField result (V id) (cs.map (Graph.Candidate.map V)) := by
  induction cs with
  | nil => rfl
  | cons a xs ih =>
    by_cases h : V a.key=V id <;>
      simp [Formula.value,Comparison.test,Graph.readField,List.foldr_cons,Graph.Candidate.map,h,ih,commutes]

include pub in
theorem update_live (one : (1:Word w)≠0) (S : Graph.Stage) (lay rev : Bool) (j : Graph.Field)
    (dest : F) (b i : Word w) (site : V (.op .div (.op .sub (.reg 0) dest) (.lit S.outputDegree))=b)
    (slot : V (.op .mod (.op .sub (.reg 0) dest) (.lit S.outputDegree))=i)
    (live : i<(S.liveDegree:Word w)) :
    V (update S lay rev j dest) = Graph.liveQuery (physicalCandidates cell mem vs S lay) rev b i j := by
  let x := Formula.op .div (.op .sub (.reg 0) dest) (.lit S.outputDegree)
  let port := Formula.op .mod (.op .sub (.reg 0) dest) (.lit S.outputDegree)
  let cs := candidates S lay rev x
  let ids := cs.map Graph.Candidate.key
  let id := pick port ids
  let localList := physicalCandidates cell mem vs S lay rev b
  let vals := localList.map Graph.Candidate.key
  let key := Rank.chosen vals i vals
  have listEq : cs.map (Graph.Candidate.map V)=localList :=
    (candidate_values cell mem vs S lay rev x).trans (by rw [site])
  have valsEq : ids.map V=vals := by rw [map_keys,listEq]
  have idEq : V id=key := by rw [pick_value cell pub mem vs one,valsEq,slot]
  let get (f : Graph.Candidate F → F) : F := cs.foldr (fun a z => .select .eq a.key id (f a) z) (.lit 0)
  have getOther : V (get Graph.Candidate.otherBase)=Graph.readField Graph.Candidate.otherBase key localList := by
    rw [field_value cell mem vs cs id _ Graph.Candidate.otherBase (fun _ => rfl),idEq,listEq]
  have getShift : V (get Graph.Candidate.shift)=Graph.readField Graph.Candidate.shift key localList := by
    rw [field_value cell mem vs cs id _ Graph.Candidate.shift (fun _ => rfl),idEq,listEq]
  let other := get Graph.Candidate.otherBase
  have toList : ((candidates S lay (!rev) other).map Graph.Candidate.key).map V =
      (physicalCandidates cell mem vs S lay (!rev) (Graph.readField Graph.Candidate.otherBase key localList)).map Graph.Candidate.key := by
    rw [map_keys,candidate_values,getOther]
  have selected (yes no : F) : V (.select .lt port (.lit S.liveDegree) yes no)=V yes := by
    have active : V port < (S.liveDegree : Word w) := slot.trans_lt live
    simp [Formula.value,Comparison.test,active,Fin.ofNat_eq_cast]
  cases j with
  | neighbor =>
    exact (selected (get Graph.Candidate.otherBase) (.op .bitXor x (.lit 1))).trans getOther
  | matePort =>
    let reverseKeys := (candidates S lay (!rev) other).map Graph.Candidate.key
    have rank := rank_value cell pub mem vs one id reverseKeys
    dsimp only [reverseKeys] at rank
    rw [idEq, toList] at rank
    exact (selected (below id reverseKeys) port).trans rank
  | delta => exact (selected (get Graph.Candidate.shift) (.lit 0)).trans getShift
  | identifier => exact (selected id (.lit 0)).trans idEq


end ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkStage.Template

end OAI
