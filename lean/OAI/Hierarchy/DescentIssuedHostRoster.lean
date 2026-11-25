import OAI.Hierarchy.DescentGroupPeerOrder
import OAI.Hierarchy.DescentMountedSortedRoster
import OAI.Hierarchy.DescentPackedMatchTerrain
import OAI.Hierarchy.DescentColonyDynamicSplit

namespace OAI
/-! # Physical reads of the matching neighbor aperture at every previous host -/
namespace Hierarchy.DescentGroupPeerOrder
open DescentSixParty DescentSortedRoster DescentColonies.DynamicSplit DescentPackedColony DescentSIMDLookup
open DescentPacking.PackedMatch.Local.Stage
open ThreeFlat.RAM Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {F P J V : Type} [Field F] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
    {d k H G M w : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {g : PoweredGadget F} {q ε : ℝ}
variable (A : GroupStage W g q ε J V k) (e : V↪Fin H) (rs : Fin H→Fin A.degree→Option (Fin H))
local notation "vertex" => e.trans Fin.valEmbedding
local notation "neighbors" => hostRotor e (hostRoster A vertex)
variable (mem : ∀i j,j∈(List.ofFn (rs i)).filterMap id ↔ ∃v u:V,i=e v ∧ j=e u ∧ v∈A.near u)

include mem

private theorem available (x z : Fin H) : z∈present rs x ↔ ∃v u:V,x=e v ∧ z=e u ∧ u∈A.near v := by
  have row : z∈present rs x ↔ z∈(List.ofFn (rs x)).filterMap id := by
    simp only [present,Finset.mem_filter,Finset.mem_univ,true_and,List.mem_filterMap,List.mem_ofFn,id_eq]
    constructor
    · rintro ⟨j,hj⟩
      exact ⟨some z,⟨j,hj⟩,rfl⟩
    · rintro ⟨a,⟨j,hj⟩,ha⟩
      exact ⟨j,hj.trans ha⟩
  rw [row,mem]
  constructor
  · rintro ⟨v,u,ha,hb,h⟩
    exact ⟨v,u,ha,hb,(A.symmetric u v).mp h⟩
  · rintro ⟨v,u,ha,hb,h⟩
    exact ⟨v,u,ha,hb,(A.symmetric v u).mp h⟩

private theorem whole (v : V) : present rs (e v)=(A.near v).map e := by
  ext z
  rw [available A e rs mem,Finset.mem_map]
  constructor
  · rintro ⟨v',u,vv,zu,hu⟩
    have eqn:=e.injective vv
    subst v'
    exact ⟨u,hu,zu.symm⟩
  · rintro ⟨u,hu,rfl⟩
    exact ⟨v,u,rfl,rfl,hu⟩

theorem issued_roster : indexed rs=neighbors := by
  funext h j
  by_cases real : ∃v,e v=h
  · obtain ⟨v,rfl⟩:=real
    have exv : ∃z,e z=e v:=⟨v,rfl⟩
    rw [hostRotor,dite_eq_left exv,e.injective exv.choose_spec]
    have score (z : ↥(A.near v)) : before rs (e v) (e z.val)=(hostSlot A vertex v z).val := by
      simp only [before,whole A e rs mem v,hostSlot_val,Finset.filter_map,Finset.card_map]
      rfl
    by_cases exists' : ∃z,hostSlot A vertex v z=j
    · obtain ⟨z,rfl⟩:=exists'
      rw [at_host,Option.map_some]
      apply (indexed_iff rs _ _ _).2
      refine ⟨?_,score z⟩
      rw [whole A e rs mem v]
      exact Finset.mem_map.mpr ⟨z.val,z.property,rfl⟩
    · simp only [hostRoster,dite_eq_right exists',Option.map_none]
      cases eqn:indexed rs (e v) j with
      | none=>rfl
      | some z=>
        obtain ⟨hz,count⟩:=(indexed_iff rs _ _ _).1 eqn
        rw [whole A e rs mem] at hz
        obtain ⟨u,hu,rfl⟩:=Finset.mem_map.mp hz
        exact (exists' ⟨⟨u,hu⟩,Fin.ext ((score ⟨u,hu⟩).symm.trans count)⟩).elim
  · rw [hostRotor,dite_eq_right real]
    cases eqn:indexed rs h j with
    | none=>rfl
    | some z=>
      obtain ⟨v,u,hv,_⟩:=(available A e rs mem _ _).1 ((indexed_iff rs _ _ _).1 eqn).1
      exact (real ⟨v,hv.symm⟩).elim

theorem rotor_mounted (C : Chart) (m : Memory w) (P : Ports A.degree) (out : Bank)
    (fit : Room C A.degree H w out.base) (raw : Raw C rs m) (old : Mounted P rs m G M)
    (left : ∀j,(P.ids j).base+H*chunks G M≤out.base) (off : P.offsets.base+H≤out.base)
    (ch : P.chunks.base+H*chunks G M≤out.base) :
    let reached:=image out.base (H*A.degree) (DescentSortedRoster.code C A.degree H) m
    (scan w out.base (H*A.degree) (DescentSortedRoster.code C A.degree H)).Exec m reached
      (4+(H*A.degree)*(2*(DescentSortedRoster.code C A.degree H).work+4)) ∧
    Mounted {P with roster:=out} neighbors reached G M := by
  exact ⟨(issued C rs m _ fit raw).1,issued_roster A e rs mem ▸ ports C rs m P out fit raw old left off ch⟩

end
end Hierarchy.DescentGroupPeerOrder

end OAI
