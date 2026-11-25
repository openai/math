import OAI.Hierarchy.DescentDonorPublicCounts
import OAI.Hierarchy.DescentRawCablePanel
import OAI.Hierarchy.DescentSharedCableNames
import OAI.Hierarchy.DescentCableDonorNames
import OAI.Hierarchy.DescentRecordedBranch
import OAI.Hierarchy.DescentGadgetNetwork

namespace OAI
/-! # Source-block panel for the entire ordinary raw-cable census -/

namespace Hierarchy.DescentRawCablePanel
open DescentSIMDLookup DescentSharedCableNames DescentSixParty DescentCompiler DescentCableDonorNames
open scoped BigOperators Classical
noncomputable section
variable {I F P J V : Type} [Fintype I] [DecidableEq I] [Field F] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
variable {d k H R i : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F}
    {price ε : ℝ} (A : GroupStage W G price ε J V k) (S : AtomSchedule) (ready : A.StateBounds S i)
    (old : W.graph.Edge↪ℕ) (vertex : V↪Fin H) (group : J≃Fin R) (pick : I×Fin 2↪W.graph.Edge)
abbrev Live := {e : Raw W.graph.Edge I // 0<A.grainCount (anchor pick e)}
def span (R k cap : ℕ) := R*2^k*cap*11

/-- The raw edge's original first-grain donor and role fix its position before
any endpoint is evaluated. This includes all ten arms/supplies of every pair. -/
def slot : Live A pick ↪ (Fin H×Fin (span R k A.cap)) where
  toFun q :=
    let e : Stage.Positive A:=⟨anchor pick q.val,q.property⟩
    let u:=W.graph.src e.val
    (vertex (A.pos u).2,finProdFinEquiv (finProdFinEquiv
      (finProdFinEquiv (group (A.pos u).1,A.block u),Stage.outgoing A old S ready e),role q.val))
  inj' := by
    intro e f packed
    let oldE : Stage.Positive A:=⟨anchor pick e.val,e.property⟩
    let oldF : Stage.Positive A:=⟨anchor pick f.val,f.property⟩
    have hv:=vertex.injective (congrArg Prod.fst packed)
    have outer:=finProdFinEquiv.injective (congrArg Prod.snd packed)
    have middle:=finProdFinEquiv.injective (congrArg Prod.fst outer)
    have inner:=finProdFinEquiv.injective (congrArg Prod.fst middle)
    have pos : A.pos (W.graph.src oldE.val)=A.pos (W.graph.src oldF.val) :=
      Prod.ext (group.injective (congrArg Prod.fst inner)) hv
    have blockEq : A.block (W.graph.src oldE.val)=A.block (W.graph.src oldF.val) :=
      congrArg (fun x : Fin R × _ => x.2) inner
    have loc : W.graph.src oldE.val=W.graph.src oldF.val :=
      ready.coordinates (Prod.ext pos blockEq)
    have oe := Stage.outgoing_identify A old S ready oldE oldF loc (congrArg Prod.snd middle)
    exact Subtype.ext (identify pick (congrArg Subtype.val oe) (congrArg Prod.snd outer))

variable (profile : I→Profile G.C)
local notation "M" => GadgetNetwork.physical W.graph pick (branchWidth G (fun _=>A.z) profile)

/-- All previous cables use A.grainCount, including unmarked tethers. -/
def normalized : Raw W.graph.Edge I→ℕ
  | .inl e=>A.grainCount e*G.b
  | .inr (.inl _)=>G.b
  | .inr (.inr (j,t))=>((profile j).1 t).val+G.k

include ready in
theorem local_grains (e : W.graph.Edge) : A.grainCount e≤A.cap := by
  let u:=W.graph.src e
  let sourceOrder : Fin (A.grainCount e) ↪ A.CellPorts (A.pos u).1 (A.pos u).2 (A.block u) :=
    ⟨fun j=>Sum.inl ⟨⟨e,rfl,rfl⟩,j⟩,by
      intro i j eqn
      have h:=congrArg (fun p=> (Stage.recover A (Stage.home A u) p).2.val) eqn
      exact Fin.ext h⟩
  exact (show A.grainCount e≤Fintype.card _ by simpa using Fintype.card_le_of_embedding sourceOrder).trans
    (A.local_port_count S ready (A.pos u).1 (A.pos u).2 (A.block u))


include ready in
omit [Fintype I] [DecidableEq I] in
theorem normalized_bound (e : Raw W.graph.Edge I) :
    normalized A profile e≤ max (A.cap*G.b) (G.C+1+G.k) :=by
  rcases e with e|⟨i,t⟩|⟨i,t⟩
  · exact (Nat.mul_le_mul_right _ (local_grains A S ready e)).trans (Nat.le_max_left _ _)
  · change G.b≤_
    exact (show G.b≤A.cap*G.b by simpa using Nat.mul_le_mul_right G.b A.capPos).trans (Nat.le_max_left _ _)
  · exact (Nat.add_le_add_right (by have:=((profile i).1 t).isLt;omega) G.k).trans (Nat.le_max_right _ _)

include ready in
omit [Fintype I] [DecidableEq I] in
theorem normalized_fits (e : Raw W.graph.Edge I) :
    normalized A profile e<2^(normBits A.cap G.b G.C G.k) := by
  have lim:=normalized_bound A S ready profile e
  exact (Nat.lt_succ_of_le lim).trans_le (Nat.le_pow_clog (by decide : 1<2) _)

include ready in
omit [DecidableEq I] in
theorem normalized_width (fit : ∀t,W.graph.width (pick t)=A.z*G.b) (e : Raw W.graph.Edge I) :
    normalized A profile e*A.z=(M).width e := by
  rcases e with e|⟨j,s⟩|⟨j,s⟩
  · change A.grainCount e*G.b*A.z=W.graph.width e
    rw [A.grainCount_fit S ready e];ring
  · change G.b*A.z=W.graph.width (pick (j,s))
    rw [fit];ring
  · change (((profile j).1 s).val+G.k)*A.z=A.z*(((profile j).1 s).val+G.k)
    ring

include ready in
omit [DecidableEq I] in
theorem omitted_width (fit : ∀t,W.graph.width (pick t)=A.z*G.b) (e : Raw W.graph.Edge I)
    (miss : ¬0<A.grainCount (anchor pick e)) : (M).width e=0 := by
  have selected (j : I) : 0<A.grainCount (pick (j,0)) := by
    have positive:=Nat.mul_pos A.unitPos G.base_pos
    have equal:=A.grainCount_fit S ready (pick (j,0))
    rw [fit] at equal
    by_contra! zero
    rw [Nat.eq_zero_of_le_zero zero,Nat.zero_mul] at equal
    omega
  rcases e with e|⟨j,s⟩|⟨j,s⟩
  · have eq : A.grainCount e=0:=by simpa [anchor] using Nat.eq_zero_of_not_pos miss
    change W.graph.width e=0
    rw [A.grainCount_fit S ready e,eq,Nat.zero_mul]
  · exact False.elim (miss (selected j))
  · exact False.elim (miss (selected j))

def place {T X : Type} [Zero X] (name : T↪Fin H×Fin R) (v : T→X) (h : Fin H) (j : Fin R) : X :=
  if found : ∃t,name t=(h,j) then v found.choose else 0

theorem padded_sum {T : Type} [Fintype T] {a : ℕ} (name : T↪Fin H×Fin R) (v : T→Cell a)
    (s : Cell a→ℕ) (zero : s 0=0) :
    (∑h,∑j,s (place name v h j))=∑t,s (v t) := by
  let amount (p : Fin H×Fin R):=s (place name v p.1 p.2)
  have filled (t : T) : amount (name t)=s (v t) := by
    have good : ∃t',name t'=((name t).1,(name t).2):=⟨t,rfl⟩
    simp only [amount,place,dite_eq_left good]
    rw [name.injective good.choose_spec]
  change (∑h,∑j,amount (h,j))=_
  rw [←Fintype.sum_prod_type]
  calc
    _ = ∑p∈(Finset.univ.map name),amount p := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro p _ outside
      have nope : ¬∃t,name t=p := by simpa using outside
      simp [amount,place,nope,zero]
    _ = _ := by simp only [Finset.sum_map,filled]

omit [DecidableEq I] in
/-- A single bounded rectangular raw panel accounts for exactly the
same amount as all physical old cables, two additional arms and eight
supplies. Missing donors have zero physical width. -/
theorem stage_fee {c : ℕ} (fit : ∀t,W.graph.width (pick t)=A.z*G.b)
    (pre post : (M).Site→ℕ) (room : ∀e : Live A pick,normalized A profile e.val<2^c) :
    let sample (q : Live A pick):=cell
      (decide (pre ((M).src q.val)=pre ((M).dst q.val)))
      (decide (post ((M).src q.val)=post ((M).dst q.val)))
      (⟨normalized A profile q.val,room q⟩ : Cell c)
    (∑h,∑j,score (place (slot A S ready old vertex group pick) sample h j))*A.z=
      ∑e : (M).Edge,if post ((M).src e)=post ((M).dst e) then (M).width e else 0 := by
  dsimp only
  rw [padded_sum _ _ _ (score_zero c),Finset.sum_mul]
  let keep (e : (M).Edge) := 0<A.grainCount (anchor pick e)
  let cost (e : (M).Edge) := if post ((M).src e)=post ((M).dst e) then (M).width e else 0
  change _=∑e,cost e
  rw [←Fintype.sum_subtype_add_sum_subtype keep cost]
  have empty : ∑e : {e // ¬keep e},cost e.val=0 := by
    apply Finset.sum_eq_zero
    intro e _
    simp [cost,omitted_width A S ready pick profile fit e.val e.property]
  rw [empty,Nat.add_zero]
  apply Finset.sum_congr rfl
  intro e _
  by_cases paid : post ((M).src e.val)=post ((M).dst e.val)
  · simp [score,cost,paid,normalized_width A S ready pick profile fit]
  · simp [score,cost,paid]

end
end Hierarchy.DescentRawCablePanel

end OAI
