import OAI.Hierarchy.DescentProgramArgumentKeys
import OAI.Hierarchy.DescentLanePortMap

namespace OAI
namespace Hierarchy.DescentLaneGates.PortMap
open DescentBundleHistory DescentLaneGates DescentKernelHistory
noncomputable section
set_option quotPrecheck false
variable {A B : Type} {w : A→ℕ} {v : B→ℕ} {p Y : ℕ} (f : PortMap w v)

def wordBlock (r : BlockRef p w) : BlockRef p v :=
  ⟨f.slot r.port,r.block,(f.sameWidth r.port) ▸ r.fits⟩

theorem lane_count (l : Lane p w) :
    (l.transport f).count (fun i=>v i/p)=l.count (fun i=>w i/p) :=by
  simp only [Lane.count,Lane.bundleStart,Lane.transport,f.sameWidth]

variable (source : ∀i,w i=w i/p*p) (target : ∀i,v i=v i/p*p) (hp : 0<p) (P : Program Y p w)
local notation "oldWords" => fun i=>w i/p
local notation "newWords" => fun i=>v i/p
local notation "oldNames" => laneProgramNames oldWords source hp P
local notation "newNames" => laneProgramNames newWords target hp (P.transport f)

theorem lane_names (l : Lane p w) :
    newNames (l.transport f)=(oldNames l).map (Sum.map f.wordBlock id) :=by
  apply List.ext_getElem?
  intro j
  change (List.ofFn (fun i : Fin ((l.transport f).count newWords)=>
    (Sum.inl (laneBlock newWords target hp (l.transport f) i) : BlockRef p v ⊕ BlockRef p (Empty.elim : Empty→ℕ))))[j]?=
    ((List.ofFn (fun i : Fin (l.count oldWords)=>(Sum.inl (laneBlock oldWords source hp l i) :
      BlockRef p w ⊕ BlockRef p (Empty.elim : Empty→ℕ)))).map (Sum.map f.wordBlock id))[j]?
  rw [List.getElem?_map]
  by_cases inside : j<l.count oldWords
  · have fits : j<(l.transport f).count newWords:=(f.lane_count l).symm ▸ inside
    simp only [List.getElem?_ofFn,dite_eq_left inside,dite_eq_left fits,Option.map_some,Sum.map_inl]
    rfl
  · have past : ¬j<(l.transport f).count newWords:=(f.lane_count l).symm ▸ inside
    simp [past,inside]

theorem transported_keys (u : P.Node) :
    ((ofProgram newWords target hp (P.transport f)).keys u)=
    ((ofProgram oldWords source hp P).keys u).map (Sum.map f.wordBlock id) :=by
  have arms : List.ofFn (((P.transport f).op u).arg)=(List.ofFn ((P.op u).arg)).map (fun l=>l.transport f):=by
    rw [List.map_ofFn]
    rfl
  have start:=program_keys newWords target hp (P.transport f) u
  have stop:=congrArg (List.map (Sum.map f.wordBlock (id : BlockRef p (Empty.elim : Empty→ℕ)→_)))
    (program_keys oldWords source hp P u).symm
  refine start.trans (Eq.trans ?_ stop)
  rw (config := {transparency := .all}) [arms,List.flatMap_map,List.map_flatMap]
  apply congrArg (fun g=>(List.ofFn ((P.op u).arg)).flatMap g)
  funext l
  exact f.lane_names source target hp P l

theorem transported_key (u : P.Node) (j : ℕ) (r : BlockRef p w)
    (read : ((ofProgram oldWords source hp P).keys u)[j]?=some (.inl r)) :
    ((ofProgram newWords target hp (P.transport f)).keys u)[j]?=some (.inl (f.wordBlock r)) :=by
  have original:=f.transported_keys source target hp P u
  have atSlot:=congrArg (fun xs : List (BlockRef p v ⊕ BlockRef p P.recipe.hiddenWidth)=>xs[j]?) original
  refine atSlot.trans ?_
  calc
    _ = (Sum.map f.wordBlock id) <$> (((ofProgram oldWords source hp P).keys u)[j]?) := List.getElem?_map
    _ = _ := by rw [read];rfl

end
end Hierarchy.DescentLaneGates.PortMap

end OAI
