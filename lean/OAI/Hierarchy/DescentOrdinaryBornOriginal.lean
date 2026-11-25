import OAI.Hierarchy.DescentOrdinaryBornDigits
import OAI.Hierarchy.DescentBundlePrivateRelabel
import OAI.Hierarchy.DescentPrivateOldDonors
import Mathlib.Data.List.FinRange

namespace OAI
/-! # Original and contracted operand ordinals for a newborn party -/

namespace Hierarchy.DescentOrdinaryBorn
open DescentKernelHistory DescentSixParty GadgetNetwork DescentBundleHistory DescentOperandPhysicalInput Computability.BorderVNP.Crossing
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false

private theorem val_range (n : ℕ) : (List.finRange n).map Fin.val=List.range n := by
  apply List.ext_getElem (by simp)
  simp

variable {F P I : Type} [Field F] [Fintype I] {d p Z : ℕ} {bits : P→ℕ}
variable (W : MarkedWorld F d P bits) (G : PoweredGadget F) (pick : I×Fin 2↪W.graph.Edge)
    (z : I→ℕ) (pr : I→Profile G.C)
local notation "net" => physical W.graph pick (branchWidth G z pr)
local notation "bw" => fun (i : I) (j : Fin 6) => boundaryWidth (net) (.inr (i,j))
local notation "port" => fun (i : I) (j : Fin 6) (a : Fin (Fintype.card (RolePort j))) => nativeRole W.graph pick (branchWidth G z pr) i j ((roleIndex j).symm a)
local notation "code" => fun (i : I) => (DescentPacking.PackedMatch.LayoutSum.profileCode G.C (pr i)).val

/-- Each entry records the original argument and its original aligned word ordinal. -/
abbrev Occurrence (p : ℕ) (i : I) (j : Fin 6) :=
  Σ a : Fin (Fintype.card (RolePort j)), Fin ((bw i j) (port i j a)/p)

def occurrences (p : ℕ) (i : I) (j : Fin 6) : List (Occurrence W G pick z pr p i j) :=
  (List.finRange (Fintype.card (RolePort j))).flatMap (fun a=>
    (List.finRange ((bw i j) (port i j a)/p)).map (fun g=>⟨a,g⟩))

def occurrenceMouth {i : I} {j : Fin 6} (x : Occurrence W G pick z pr p i j) : Mouth :=
  let socket:=(roleIndex j).symm x.1
  ⟨role socket,side socket,x.2.val⟩

def occurrenceBlock (hp : 0<p) {i : I} {j : Fin 6} (x : Occurrence W G pick z pr p i j) :
    BlockRef p (bw i j) :=
  ⟨port i j x.1,x.2.val,(Nat.le_div_iff_mul_le hp).mp x.2.isLt⟩


/-- The normalized first-source ticket/arm/supply selector and its sign identify
the very incidence used by the original argument, before either contraction. -/
theorem occurrence_incidence (hp : 0<p) {i : I} {j : Fin 6}
    (x : Occurrence W G pick z pr p i j)
    (edge : W.graph.Edge≃Fin (Fintype.card W.graph.Edge)) (pair : I≃Fin (Fintype.card I)) :
    let m:=occurrenceMouth W G pick z pr x
    let b:=occurrenceBlock W G pick z pr hp x
    b.block=m.chunk ∧ ∃e, b.port=Sum.inl e ∧
      MarkedWorld.edgeNumber W edge pair e.val=bornName W pick edge pair i m.origin ∧
      (if m.target then (net).dst e.val else (net).src e.val)=.inr (i,j) := by
  intro m b
  constructor
  · rfl
  · change ∃e, nativeRole W.graph pick (branchWidth G z pr) i j ((roleIndex j).symm x.1)=Sum.inl e ∧
      MarkedWorld.edgeNumber W edge pair e.val=bornName W pick edge pair i (role ((roleIndex j).symm x.1)) ∧
      (if side ((roleIndex j).symm x.1) then (net).dst e.val else (net).src e.val)=.inr (i,j)
    generalize (roleIndex j).symm x.1=socket
    rcases socket with (⟨t,ht⟩|⟨t,ht⟩)|(⟨t,ht⟩|⟨t,ht⟩) <;> refine ⟨_,rfl,rfl,?_⟩ <;>
      simp [side,physical,source,target,ht]

omit [Field F] in
/-- The two printed coordinates recover the earlier picked edge or the
specific new arm or supply edge in the original marked edge enumeration. -/
theorem label_of_mouth (m : Mouth) (i : I) (edge : W.graph.Edge≃Fin (Fintype.card W.graph.Edge))
    (pair : I≃Fin (Fintype.card I)) :
    bornName W pick edge pair i m.origin =
      (if m.rawRole=0 then (edge (pick (i,m.anchor))).val
       else Fintype.card W.graph.Edge+10*(pair i).val+(m.rawRole-1)) :=by
  cases m with
  | mk r target chunk =>
    cases r with
    | original s=>rfl
    | arm s=>
      split <;> simp only [Mouth.rawRole,bornName] at * <;> omega
    | supply s=>
      split <;> simp only [Mouth.rawRole,bornName] at * <;> omega

theorem original_inventory (fit : ∀i s,W.graph.width (pick (i,s))=z i*G.b) (i : I) (j : Fin 6) :
    inventory (actual G p) (z i) (code i) j=
      (occurrences W G pick z pr p i j).map (occurrenceMouth W G pick z pr) := by
  unfold inventory occurrences
  rw [List.map_flatMap]
  congr 1
  funext a
  unfold group
  dsimp only
  erw [actual_units W G pick z pr p fit i j ((roleIndex j).symm a),← val_range]
  simp only [List.map_map,Function.comp_def,occurrenceMouth]

variable (room : ∀i,z i≤Z) (hp : 0<p)
local notation "R" => fun (i : I) (j : Fin 6) => roleRecipe G W.graph pick z room pr i j
local notation "xs" => fun (i : I) (j : Fin 6) => occurrences W G pick z pr p i j

/-- Word occurrences in the original recipe, in argument, group and slice order. -/
theorem exposed_original (i : I) (j : Fin 6) (multiple : ∀e,p∣(bw i j) e) :
    (exposed (R i j) (bw i j) hp multiple (fun h => nomatch h)).keys ()=
      (xs i j).map (fun x=>Sum.inl (occurrenceBlock W G pick z pr hp x)) := by
  change (List.ofFn (fun a : Fin (Fintype.card (RolePort j))=>
    List.ofFn (fun g : Fin ((bw i j) (port i j a)/p)=>
      Slice.whole hp (Sum.inl (occurrenceBlock W G pick z pr hp ⟨a,g⟩) :
        BlockRef p (bw i j) ⊕ BlockRef p (R i j).width)))).flatMap (List.flatMap Slice.names)=_
  have whole {α : Type} (x : α) : (Slice.whole hp x).names=[x] := by
    change List.ofFn (fun _ : Fin 1=>x)=[x]
    simp [List.ofFn_succ]
  simp only [whole,occurrences,List.ofFn_eq_map,List.map_flatMap,List.flatMap_map,List.map_map,
    Function.comp_def, ← List.map_eq_flatMap]
  rfl

variable (B : BitDescription W) (old : ∀v,Shape p (B.recipe v))
    (edge : ∀e,p∣W.graph.width e) (pins : ∀a,p∣bits a) (unit : ∀i,p∣z i)

theorem physical_original (i : I) (j : Fin 6) :
    (physicalShape W B G pick z room pr hp old edge pins unit (.inr (i,j))).keys ()=
      (xs i j).map (fun x=>Sum.inl (occurrenceBlock W G pick z pr hp x)) :=
  exposed_original W G pick z pr room hp i j (fun b=>by
    rcases b with e|a
    · exact physical_multiple W G pick z pr edge unit e.val
    · exact pins a.val)

/-- Reindexing at a selected quotient takes the actual surviving/captured branch
of the quotient for each word, while retaining its operand ordinal. -/
theorem selected_original {C : Type} (pack : W.graph.Site→C)
    (hz : ∀i,0<z i) (fit : ∀i s,W.graph.width (pick (i,s))=z i*G.b)
    (i : I) (j : Fin 6) (v) (birth : (newSite W.graph pick (bestLayout (branchWidth G z pr)) pack (.inr (i,j)))=v) :
    let loc:=newSite W.graph pick (bestLayout (branchWidth G z pr)) pack
    let pos:=fun _ : Merged W.graph pick (bestLayout (branchWidth G z pr)) pack=>(0:EuclideanSpace ℝ (Fin d))
    let ball:=fun c=> (by simp [pos] : ‖pos c‖≤1)
    let u := (⟨.inr (i,j),birth⟩ : {x // loc x=v})
    (Shape.selected W B G pick z hz fit room pack pr hp old edge pins unit v).keys ⟨u,()⟩=
      (xs i j).map (fun x=>
        destination (fun t : {x // loc x=v}=>physicalBits G W.toWorld pick z room pr B.recipe t.val)
          (fun e : DescentNetworkPartition.PrivateEdge (net) loc v=>(net).width e.val)
          (quotientBit (net) loc pos ball v) (quotientMap (net) loc pos ball v) u (.inl (occurrenceBlock W G pick z pr hp x))) := by
  dsimp only
  unfold Shape.selected quotientShape
  erw [combined_keys,physical_original,List.map_map]
  rfl

theorem synchronized (fit : ∀i s,W.graph.width (pick (i,s))=z i*G.b)
    (i : I) (j : Fin 6) (n : ℕ) :
    mouth (actual G p) (z i) (code i) j n=((xs i j)[n]?).map (occurrenceMouth W G pick z pr) ∧
    ((physicalShape W B G pick z room pr hp old edge pins unit (.inr (i,j))).keys ())[n]?=
      ((xs i j)[n]?).map (fun x=>Sum.inl (occurrenceBlock W G pick z pr hp x)) := by
  constructor
  · rw [mouth,original_inventory W G pick z pr fit,List.getElem?_map]
  · rw [physical_original,List.getElem?_map]


/-- Pointwise transfer of the synchronized operand ordinal through each real grain
or physical-rename block map. The hidden branch retains its original owner. -/
theorem rerouted_original {U A A' T : Type} {w : A→ℕ} {w' : A'→ℕ}
    {r : BitRecipe U A w} (s : Shape p r) {route : BitRef w→BitRef w'}
    (map : BlockMap p w w' route) (u : r.Node) (tape : List T)
    (label : T→BlockRef p w ⊕ BlockRef p r.hiddenWidth) (prior : s.keys u=tape.map label) (n : ℕ) :
    ((s.reroute map).keys u)[n]?=tape[n]?.map (fun x=>(label x).map map.map id) := by
  rw [DescentBundleHistory.reroute_keys,prior,List.map_map]
  exact List.getElem?_map

theorem component_original (i : I) (j : Fin 6) (n width : ℕ) (f : Fin 7)
    (fit : ∀i s,W.graph.width (pick (i,s))=z i*G.b) :
    field (actual G p) width f n (z i) (code i) j=
      (((xs i j)[n]?).elim 0 (fun x=>
        (DescentOperandStateBanks.Pointer.cable 0 0 x.2.val).fields ⟨0,1,1⟩ f) : ℕ) := by
  unfold field mouth
  rw [original_inventory W G pick z pr fit,List.getElem?_map]
  cases h : (xs i j)[n]? <;> rfl

end
end Hierarchy.DescentOrdinaryBorn

end OAI
