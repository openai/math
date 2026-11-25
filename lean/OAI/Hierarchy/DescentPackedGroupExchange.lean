import OAI.Hierarchy.DescentPackedExchange
import OAI.Hierarchy.DescentGroupStage

namespace OAI
/-! # The packed common-neighbor pass on both actual endpoints of a descent stage -/
namespace Hierarchy.DescentPackedExchange
open DescentSixParty DescentHostDirectory
open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.RAMSerialization
open ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open scoped BigOperators Classical
noncomputable section

variable {F P J V : Type} [Field F] [Fintype P] [Fintype J] [DecidableEq J]
    [Fintype V] [DecidableEq V] {d k w b : ℕ} {bits : P→ℕ}
    {W : MarkedWorld F d P bits} {G : PoweredGadget F} {price ε : ℝ}
    (A : GroupStage W G price ε J V k)
local notation "H" => Fintype.card V

omit [Fintype P] in
private theorem actual_peer {v u : J×V} (h : u∈groupedNear A.near v) : u.2∈A.near v.2 := by
  obtain ⟨t,mem,eq⟩:=Finset.mem_map.mp h
  have same : t=u.2 := congrArg Prod.snd eq
  exact same ▸ mem

abbrev Ports := Port H A.degree

private theorem reciprocal_membership {T : Type} (near : T → Finset T) (v u : T) :
    u ∈ reciprocal near v ↔ u ∈ near v ∧ v ∈ near u := by
  classical
  simp only [reciprocal, Finset.mem_filter]

def stageNext : Ports A→Option (Fin H) := neighborSlot (Fintype.equivFin V) (reciprocal A.near)

omit [Fintype P] in
/-- For a reached host the shared physical adjacency is exactly its full
incoming roster, including template neighbors unused by any current cable. -/
theorem stageNext_iff (v u : V) :
    (∃d : Fin A.degree,stageNext A ((Fintype.equivFin V) v,d)=some ((Fintype.equivFin V) u)) ↔ v∈A.near u := by
  let e := Fintype.equivFin V
  constructor
  · rintro ⟨d,hit⟩
    obtain ⟨inBoth,_⟩:=neighbor_info e (reciprocal A.near) (e v,d) u hit
    have both : u∈reciprocal A.near v := by simpa only [Equiv.symm_apply_apply] using inBoth
    exact ((reciprocal_membership A.near v u).mp both).2
  · intro present
    exact neighbor_at e (reciprocal A.near) (reciprocal_cap A.near A.degreeBound)
      ((reciprocal_membership A.near v u).mpr ⟨(A.symmetric v u).mpr present,present⟩)

omit [Fintype P] in
theorem copies_per_word (u : V) :
    Fintype.card {a : Ports A // stageNext A a=some ((Fintype.equivFin V) u)}≤A.degree :=
  bounded_reads (Fintype.equivFin V) (reciprocal A.near) (reciprocal_cap A.near A.degreeBound)
    (fun v t h=>(reciprocal_symm A.near v t).mp h) u

/-- The desired block-indexed aggregate is packed into one shared vector per
position. Distinct edges of a multigraph can refer to the same port without
causing additional paid vectors or neighbor addresses. -/
def EndReads (x : Fin H→Fin b→Bool) (out : ℕ) (mem : Memory w) (v u : W.graph.Site) : Prop :=
  ∃ j : Fin A.degree, ∀ c : Fin (batch w b), ∀ t : Fin w,
    wordBits w (mem (out+(id H A.degree w b (c,(Fintype.equivFin V) (A.pos v).2,j)).val)) t =
      if h : c.val*w+t.val<b then x ((Fintype.equivFin V) (A.pos u).2) ⟨c.val*w+t.val,h⟩ else false

omit [Fintype P] in
theorem stage_spec (g : Banks) (out : ℕ) (fit : Fits g out H A.degree w b)
    (x : Fin H→Fin b→Bool) :
    (program out H A.degree w b g).Spec (Reads g (stageNext A) x)
      (fun src result=>result=image out (rows H A.degree w b) (gather g) src ∧
        ∀e,EndReads A x out result (W.graph.src e) (W.graph.dst e) ∧
           EndReads A x out result (W.graph.dst e) (W.graph.src e))
      (4+rows H A.degree w b*(2*work g+4)) ∧ CheapCode (program out H A.degree w b g) := by
  obtain ⟨real,cheap⟩:=spec g out fit (stageNext A) x
  refine ⟨real.mono (fun _ h=>h) ?_ (le_refl _),cheap⟩
  rintro m after ⟨written,word⟩
  refine ⟨written,fun e=>?_⟩
  have src:=actual_peer A (A.peers e).1
  have dst:=actual_peer A (A.peers e).2
  refine ⟨neighbor_read (Fintype.equivFin V) (reciprocal A.near) (reciprocal_cap A.near A.degreeBound)
    ((reciprocal_membership A.near _ _).mpr ⟨src,dst⟩) x after out word,?_⟩
  exact neighbor_read (Fintype.equivFin V) (reciprocal A.near) (reciprocal_cap A.near A.degreeBound)
    ((reciprocal_membership A.near _ _).mpr ⟨dst,src⟩) x after out word

omit [Fintype P] in
theorem stage_volume (N w b : ℕ) [Nonempty V] :
    tapeWords N H A.degree w b*w ≤ (4*A.degree+4)*((N+H)*w+H*b) :=
  volume _ _ _ _ _ Fintype.card_pos


end
end Hierarchy.DescentPackedExchange

end OAI
