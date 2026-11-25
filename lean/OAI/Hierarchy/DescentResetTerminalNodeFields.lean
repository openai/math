import OAI.Hierarchy.DescentResetNodePanels
import OAI.Hierarchy.DescentResetDonorSlotSources
import OAI.Hierarchy.DescentInstalledLaneIssue

namespace OAI
/-! # Terminal block tags, arities and operand fields of installed reset nodes -/
namespace Hierarchy.DescentBundleHistory
open DescentKernelHistory DescentNamedContact DescentRouterBank DescentResetTrunks Computability.BorderVNP.Crossing
open scoped Classical BigOperators
noncomputable section
variable {n d L p : ℕ} {P H Q X Y : Type} [Fintype H] [Fintype Q] {bits : P→ℕ}
variable (N : Network n P bits) (home : N.Site→H) (group : Bool→N.Edge→Q)
variable (R : Network d (Bool×Q) (publicWidth group N.width)) (key : N.Edge↪Fin L)
variable (whole : ∀e,p∣N.width e) (hp : 0<p)
variable (old : SiteBits (U:=X) N) (bank : SiteBits (U:=Y) R) (src : ∀v,Shape p (old v)) (dev : ∀v,Shape p (bank v))
local notation "shape" => trunkShape N home group R key whole hp old bank src dev
local notation "tr" => trunkBits N home group R key old bank
local notation "G" => network N home group R

omit [Fintype Q] in
/-- All slice parameters stay attached to the same retained scalar call. -/
theorem retained_terminal_tag (v : N.Site) (u : (old v).Node) :
    ((shape (.inl (false,home v))).recipe hp).tag ⟨⟨v,rfl⟩,u⟩ =
      ((Sum.inl (((src v).recipe hp).tag u).1 : X⊕(Unit⊕Y)),(((src v).recipe hp).tag u).2) := by
  refine Prod.ext ?_ ?_
  · rfl
  simp [Shape.recipe,Shape.rows,trunkShape,inShape,combined,oldGatherShape,oldGather,
    Slice.code,Slice.map,Shape.reroute,Shape.retag,List.map_ofFn,Function.comp_def]
  apply congrArg List.ofFn
  funext j
  exact List.map_ofFn

omit [Fintype Q] in
theorem retained_terminal_arity (v : N.Site) (u : (old v).Node) :
    ((shape (.inl (false,home v))).recipe hp).arity ⟨⟨v,rfl⟩,u⟩ = ((src v).recipe hp).arity u := by
  exact retained_argument_count hp N home group R key whole old src (home v) ⟨v,rfl⟩ u

omit [Fintype Q] in
/-- At its old local operand ordinal, a public input reads the new true cable and complete block. -/
theorem retained_public (v : N.Site) (u : (old v).Node) (j : Fin (((src v).recipe hp).arity u))
    (b : BlockRef p (boundaryWidth N v)) (was : ((src v).recipe hp).operand u j=.inl b) :
    let after:=(shape (.inl (false,home v))).recipe hp
    after.operand ⟨⟨v,rfl⟩,u⟩ (Fin.cast (retained_terminal_arity N home group R key whole hp old bank src dev v u).symm j)=
      .inl ((oldBlockMap N home group R key whole v).map b) := by
  let i : Fibre home (home v):=⟨v,rfl⟩
  let recs:=oldGather N home group R key old (home v)
  let shapes:=oldGatherShape N home group R key whole old src (home v)
  let width:=boundaryWidth G (.inl (false,home v))
  let mapBits:=fun (_ : Fibre home (home v)) (x : BitRef width)=>(Sum.inl x : BitRef width⊕BitRef (Empty.elim : Empty→ℕ))
  let maps:=fun _ : Fibre home (home v)=>({map:=id,read:=fun _ _=>rfl} : BlockMap p width width id).publicOnly
  let f:=oldBlockMap N home group R key whole v
  let srcSlot:=Fin.cast (rerouteLen hp (src v) f u).symm j
  have moved:=reroute_operand hp (src v) f u j
  rw [was] at moved
  have here : ((shapes i).recipe hp).operand u srcSlot=.inl (f.map b):=moved
  have carried:=wordTransfer_read hp recs (Empty.elim : Empty→ℕ) mapBits shapes (fun z => nomatch z) maps i u srcSlot
  dsimp only at carried
  rw [here] at carried
  exact carried

omit [Fintype Q] in
/-- The two previous word occurrences at this node each contribute one reference per real grain. -/
theorem relay_terminal_arity (h : H) (e : Fibre (moved N home) h) :
    ((shape (.inl (true,h))).recipe hp).arity e=2*(N.width e.val/p) := by
  refine (Shape.recipe_refs hp (shape (.inl (true,h))) e).trans ?_
  change (∑ _j : Fin 2, ∑ _g : Fin (N.width e.val / p), (1 : ℕ)) = _
  simp

omit [Fintype Q] in
theorem bank_terminal_tag (v : R.Site) (z : (bank v).Node) :
    ((shape (.inr v)).recipe hp).tag z=
      ((Sum.inr (Sum.inr (((dev v).recipe hp).tag z).1) : X⊕(Unit⊕Y)),(((dev v).recipe hp).tag z).2) := by
  refine Prod.ext ?_ ?_
  · rfl
  simp [Shape.recipe,Shape.rows,trunkShape,bankPullbackShape,Shape.reroute,Shape.retag,
    Slice.code,Slice.map,List.map_ofFn,Function.comp_def]
  apply congrArg List.ofFn
  funext j
  exact List.map_ofFn

omit [Fintype Q] in
theorem bank_terminal_arity (v : R.Site) (z : (bank v).Node) :
    ((shape (.inr v)).recipe hp).arity z=((dev v).recipe hp).arity z := by
  exact rerouteLen hp (dev v) (bankBlockMap N home group R key whole hp v) z

omit [Fintype Q] in
theorem bank_terminal_operand (v : R.Site) (z : (bank v).Node) (j : Fin (((dev v).recipe hp).arity z))
    (b : BlockRef p (boundaryWidth R v)) (was : ((dev v).recipe hp).operand z j=.inl b) :
    ((shape (.inr v)).recipe hp).operand z
        (Fin.cast (bank_terminal_arity N home group R key whole hp old bank src dev v z).symm j)=
      .inl ((bankBlockMap N home group R key whole hp v).map b) := by
  have exactRead:=reroute_operand hp (dev v) (bankBlockMap N home group R key whole hp v) z j
  rw [was] at exactRead
  exact exactRead

open DescentLaneGates
variable {A : Type} {bw : A→ℕ} {alphabet : ℕ} (units : A→ℕ) (multiple : ∀a,bw a=units a*p)
variable (prg : Program alphabet p bw)

theorem lane_terminal_arity (z : prg.Node) :
    ((ofProgram units multiple hp prg).recipe hp).arity z=∑j,((prg.op z).arg j).count units := by
  refine (Shape.recipe_refs hp (ofProgram units multiple hp prg) z).trans ?_
  change (∑ j : Fin (prg.op z).arity, ∑ _g : Fin 1, ((prg.op z).arg j).count units) = _
  simp

theorem lane_terminal_tag (z : prg.Node) :
    ((ofProgram units multiple hp prg).recipe hp).tag z=
      ((prg.op z).tag,List.ofFn (fun j : Fin (prg.op z).arity=>
        [⟨((prg.op z).arg j).residue,((prg.op z).arg j).stride,((prg.op z).arg j).count units⟩])) := by
  simp [Shape.recipe,Shape.rows,ofProgram,laneSlice,Slice.code,List.map_ofFn,Function.comp_def]
  exact ⟨rfl,rfl⟩

end
end Hierarchy.DescentBundleHistory

end OAI
