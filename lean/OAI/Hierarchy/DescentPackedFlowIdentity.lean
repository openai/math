import OAI.Hierarchy.DescentPackedMatchRoster
import OAI.Hierarchy.DescentFlattenGroups
import OAI.Hierarchy.DescentGrainMeasurements
import OAI.Hierarchy.DescentSharedCableSiblings

namespace OAI
/-! # Old signed neighbor slots count the actual two-sided reset core mass -/
namespace Hierarchy.DescentSixParty.PackedFlow
open DescentColonies DescentSIMDLookup DescentSharedCableNames
open DescentPacking.PackedMatch.Local
open scoped Classical BigOperators Fin.CommRing
noncomputable section
variable {F P J V : Type} [Field F] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
  {d k i m : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F} {q ε : ℝ}
  (A : GroupStage W G q ε J V k) (native : W.graph.Edge↪ℕ) (S : DescentCompiler.AtomSchedule) (ready : A.StateBounds S i)
  (rank : J×V↪ℕ)
local notation "Nm" => DescentPacking.PackedMatch.Local.Stage.cableNames k rank
local notation "rot" => DescentPacking.PackedMatch.Local.Stage.rotor A rank
local notation "Dest" => DescentPacking.PackedMatch.Local.Stage.target A native S ready Nm
local notation "Loc" => DescentPacking.PackedMatch.Local.Stage.address A native S ready
local notation "Q" => A.wire*(A.z*G.b)

theorem rotor_unique (h z : J×V) (p r : Fin A.degree) (one : rot h p=some z) (two : rot h r=some z) : p=r := by
  unfold DescentPacking.PackedMatch.Local.Stage.rotor at one two
  split at one <;> try contradiction
  rename_i found
  split at two <;> try contradiction
  rename_i found'
  have same : found.choose=found'.choose:=Subtype.ext ((Option.some.inj one).trans (Option.some.inj two).symm)
  exact found.choose_spec.symm.trans ((congrArg _ same).trans found'.choose_spec)

/-- One active physical slot exactly identifies one original paid edge. -/
theorem directed_card (short : ℕ) (good : A.degree<2^short) (h z : J×V) (x : Block k)
    (t : Fin A.degree) (route : rot h t=some z) :
    let panel:=DescentPacking.PackedMatch.Local.Stage.terrain (short:=short) A native S ready Nm
      (fun _ _=>(0:Cell 1)) rot h
    Fintype.card {s : Fin (2*A.cap) // peer panel x s=some t} =
      Fintype.card {e : W.graph.Edge // (A.pos (W.graph.src e)=h ∧ A.block (W.graph.src e)=x) ∧
        e∈W.core ∧ A.pos (W.graph.dst e)=z} := by
  intro panel
  let Old:= {e : W.graph.Edge // (A.pos (W.graph.src e)=h ∧ A.block (W.graph.src e)=x) ∧
    e∈W.core ∧ A.pos (W.graph.dst e)=z}
  let slot (e : Old) : Fin (2*A.cap) := Loc (h,x) ⟨e.val,e.property.1,e.property.2.1⟩
  have oldTarget (e : PackedCensus.Out W A.pos A.block h x) :
      Dest (h,x) e=t ↔ A.pos (W.graph.dst e.val)=z := by
    have found:=DescentPacking.PackedMatch.Local.Stage.rotor_routes A native S ready rank h x e
    constructor
    · intro eqn;rw [eqn,route] at found;exact (Option.some.inj found).symm
    · intro eqn;rw [eqn] at found;exact rotor_unique A rank h z _ _ found route
  have iffSlot (s : Fin (2*A.cap)) : peer panel x s=some t ↔ ∃e : Old,slot e=s := by
    rw [DescentPacking.PackedMatch.Local.Stage.all_ports A native S ready Nm (fun _ _=>(0:Cell 1)) rot (h,x) s t good]
    constructor
    · rintro ⟨e,eqn,dest⟩;exact ⟨⟨e.val,e.property.1,e.property.2,(oldTarget e).1 dest⟩,eqn⟩
    · rintro ⟨e,eqn⟩
      let a : PackedCensus.Out W A.pos A.block h x:=⟨e.val,e.property.1,e.property.2.1⟩
      exact ⟨a,eqn,(oldTarget a).2 e.property.2.2⟩
  let put (e : Old) : {s : Fin (2*A.cap) // peer panel x s=some t}:=⟨slot e,(iffSlot _).2 ⟨e,rfl⟩⟩
  have inj : Function.Injective put := by
    intro a b same
    have eqn:=((Loc (h,x)).injective (congrArg Subtype.val same))
    have edgeEq := congrArg (fun e : PackedCensus.Out W A.pos A.block h x=>e.val) eqn
    exact Subtype.ext edgeEq
  have surj : Function.Surjective put := by
    intro p;obtain ⟨e,yes⟩:=(iffSlot _).1 p.property;exact ⟨e,Subtype.ext yes⟩
  exact (Fintype.card_congr (Equiv.ofBijective put ⟨inj,surj⟩)).symm

def outgoing (v z : J×V) (x : Block k) :=
  Fintype.card {e : W.graph.Edge // (A.pos (W.graph.src e)=v ∧ A.block (W.graph.src e)=x) ∧
    e∈W.core ∧ A.pos (W.graph.dst e)=z}

private theorem group_preserved (e : W.graph.Edge) : (A.pos (W.graph.src e)).1=(A.pos (W.graph.dst e)).1 := by
  obtain ⟨v,_,same⟩:=Finset.mem_map.mp (A.peers e).1
  have groups := congrArg (fun pair : J×V=>pair.1) same
  exact groups

/-- The real reset and old-group directed coordinates select the same edge set. -/
theorem directed_issued (digits : Block m≃J×Block k) (v z : V) (x : Block m) :
    directedLoad (W.countWorld A.grainCount).core W.graph.src W.graph.dst
      (fun u=>(A.pos u).2) (StarKeys.filled W.graph A.pos A.block digits)
      (fun e=>Q*A.grainCount e) v z x = Q*outgoing A ((digits x).1,v) ((digits x).1,z) (digits x).2 := by
  let selected (e : W.graph.Edge) := (A.pos (W.graph.src e)=((digits x).1,v) ∧ A.block (W.graph.src e)=(digits x).2) ∧
      e∈W.core ∧ A.pos (W.graph.dst e)=((digits x).1,z)
  have iffAt (e : W.graph.Edge) (core : e∈W.core) :
      (A.pos (W.graph.src e)).2=v ∧ (A.pos (W.graph.dst e)).2=z ∧
        StarKeys.filled W.graph A.pos A.block digits (W.graph.src e)=x ↔ selected e := by
    constructor
    · rintro ⟨src,dst,both⟩
      have parts : ((A.pos (W.graph.src e)).1,A.block (W.graph.src e))=digits x := by
        simpa only [StarKeys.filled,Equiv.apply_symm_apply] using congrArg digits both
      have groupAt := congrArg (fun pair : J×Block k=>pair.1) parts
      have blockAt := congrArg (fun pair : J×Block k=>pair.2) parts
      exact ⟨⟨Prod.ext groupAt src,blockAt⟩,core,
        Prod.ext ((group_preserved A e).symm.trans groupAt) dst⟩
    · rintro ⟨⟨src,blk⟩,_,dst⟩
      refine ⟨congrArg Prod.snd src,congrArg Prod.snd dst,digits.injective ?_⟩
      simp only [StarKeys.filled,Equiv.apply_symm_apply,src,blk]
  change (∑e∈W.core, if (A.pos (W.graph.src e)).2=v ∧ (A.pos (W.graph.dst e)).2=z ∧
    StarKeys.filled W.graph A.pos A.block digits (W.graph.src e)=x then Q*A.grainCount e else 0)=
    Q*Fintype.card {e // selected e}
  calc
    _ = ∑e∈W.core,if selected e then Q else 0 := by
      apply Finset.sum_congr rfl
      intro e member
      have one := Siblings.paid_one A e member
      simp only [iffAt e member,one,Nat.mul_one]
    _ = ∑e∈Finset.univ.filter selected,Q := by
      rw [←Finset.sum_filter]
      congr 1
      ext e
      simp only [Finset.mem_filter,Finset.mem_univ,true_and]
      exact and_iff_right_of_imp (fun h : selected e=>h.2.1)
    _ = _ := by rw [Finset.sum_const,Fintype.card_subtype,smul_eq_mul,Nat.mul_comm]

/-- Summing the actual directed amounts at the two reciprocal sockets
counts a loop twice, as required by the original symmetric load. -/
theorem pair_issued (digits : Block m≃J×Block k) (v z : V) (x : Block m) :
    pairLoad (W.countWorld A.grainCount) (fun u=>(A.pos u).2) (StarKeys.filled W.graph A.pos A.block digits)
      Q v z x =
    Q*outgoing A ((digits x).1,v) ((digits x).1,z) (digits x).2+
    Q*outgoing A ((digits x).1,z) ((digits x).1,v) (digits x).2 := by
  unfold pairLoad
  rw [←directed_issued A digits v z x,←directed_issued A digits z v x]
  apply congrArg₂ (·+·) rfl
  apply Finset.sum_congr rfl
  intro e _
  have same : StarKeys.filled W.graph A.pos A.block digits (W.graph.src e)=
      StarKeys.filled W.graph A.pos A.block digits (W.graph.dst e) :=
    congrArg digits.symm (Prod.ext (group_preserved A e) (A.same e))
  simp only [MarkedWorld.countWorld]
  rw [same]
  simp only [and_assoc,and_comm,and_left_comm]

end
end Hierarchy.DescentSixParty.PackedFlow

end OAI
