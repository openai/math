import OAI.Hierarchy.DescentPaddedFlowChips
import OAI.Hierarchy.DescentIssuedHostRoster

namespace OAI
/-! # Sorting the live neighbors on the full public degree rectangle -/
namespace Hierarchy.DescentSixParty.PackedFlow.Padded
open DescentColonies DescentSortedRoster DescentPackedColony DescentSIMDLookup DescentPackedFlowPair.Padded
open ThreeFlat.RAM Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open scoped Classical BigOperators Fin.CommRing
noncomputable section
variable {F P J V : Type} [Field F] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
    {d k H N D G M w : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {Gad : PoweredGadget F} {q ε : ℝ}
    (A : GroupStage W Gad q ε J V k) (hosts : V≃Fin H) (ph : H≤N) (pd : A.degree≤D)
    (rs : Fin N→Fin D→Option (Fin N))
local notation "rank" => hosts.toEmbedding.trans (Fin.castLEEmb ph)
variable (shape : ∀x y,y∈(List.ofFn (rs x)).filterMap id ↔
  ∃v u:V,x=(hosts.toEmbedding.trans (Fin.castLEEmb ph)) v ∧
    y=(hosts.toEmbedding.trans (Fin.castLEEmb ph)) u ∧ v∈A.near u)

include shape in
private theorem real_peers (x z : Fin N) :
    z∈present rs x ↔ ∃v u:V,x=rank v ∧ z=rank u ∧ u∈A.near v := by
  have row : z∈present rs x ↔ z∈(List.ofFn (rs x)).filterMap id := by
    simp only [present,Finset.mem_filter,Finset.mem_univ,true_and,List.mem_filterMap,List.mem_ofFn,id_eq]
    constructor
    · rintro ⟨j,hj⟩
      exact ⟨some z,⟨j,hj⟩,rfl⟩
    · rintro ⟨a,⟨j,hj⟩,ha⟩
      exact ⟨j,hj.trans ha⟩
  rw [row,shape]
  constructor <;> rintro ⟨v,u,a,b,mem⟩
  · exact ⟨v,u,a,b,(A.symmetric u v).mp mem⟩
  · exact ⟨v,u,a,b,(A.symmetric v u).mp mem⟩

include shape in
private theorem real_row (v : V) : present rs (rank v)=(A.near v).map rank := by
  ext w
  rw [real_peers A hosts ph rs shape,Finset.mem_map]
  constructor
  · rintro ⟨t,u,eq,hit,adj⟩
    have same:=(hosts.toEmbedding.trans (Fin.castLEEmb ph)).injective eq
    subst t;exact ⟨u,adj,hit.symm⟩
  · rintro ⟨u,adj,rfl⟩;exact ⟨v,u,rfl,rfl,adj⟩

include shape in
private theorem ordered (v : V) (u : ↥(A.near v)) :
    before rs (rank v) (rank u.val)=(socket A (hosts.toEmbedding.trans Fin.valEmbedding) v u).val := by
  unfold before
  rw [real_row A hosts ph rs shape]
  change ((Finset.map rank (A.near v)).filter (·<rank u.val)).card=
    (DescentGroupPeerOrder.hostSlot A (hosts.toEmbedding.trans Fin.valEmbedding) v u).val
  rw [DescentGroupPeerOrder.hostSlot_val,Finset.filter_map,Finset.card_map]
  rfl

theorem canonical (v : V) (u : ↥(A.near v)) :
    roster A hosts ph (rank v) ((socket A (hosts.toEmbedding.trans Fin.valEmbedding) v u).castLE pd)=some (rank u.val) := by
  simp [roster,DescentPackedFlowPair.Padded.next,Function.Embedding.trans_apply,Equiv.toEmbedding_apply,
    Fin.castLEEmb_apply,project_cast,PackedFlow.next_at]

include pd shape in
theorem sorted_eq : indexed rs=roster A hosts ph := by
  funext x i
  cases old : indexed rs x i with
  | some z=>
    obtain ⟨mem,val⟩:=(indexed_iff rs x i z).1 old
    obtain ⟨v,u,rfl,rfl,adj⟩:=(real_peers A hosts ph rs shape _ _).1 mem
    have nu : ((socket A (hosts.toEmbedding.trans Fin.valEmbedding) v ⟨u,adj⟩).castLE pd)=i := by
      apply Fin.ext
      exact (ordered A hosts ph rs shape v ⟨u,adj⟩).symm.trans val
    exact nu ▸ (canonical A hosts ph pd v ⟨u,adj⟩).symm
  | none=>
    cases can : roster A hosts ph x i with
    | none=>rfl
    | some z=>
      exfalso
      unfold roster DescentPackedFlowPair.Padded.next at can
      cases hx:project H x with
      | none=>simp [hx] at can
      | some t=>
        cases hj:project A.degree i with
        | none=>simp [hx,hj] at can
        | some j=>
          let v:=hosts.symm t
          have sameX : x=rank v := by simpa [v] using project_some hx ph
          have sameI:=project_some hj pd
          by_cases hit : ∃b : ↥(A.near v),socket A (hosts.toEmbedding.trans Fin.valEmbedding) v b=j
          · obtain ⟨b,hb⟩:=hit
            have good : indexed rs (rank v) (j.castLE pd)=some (rank b.val) :=
              (indexed_iff rs _ _ _).2 ⟨(real_peers A hosts ph rs shape _ _).2
                ⟨v,b.val,rfl,rfl,b.property⟩,(ordered A hosts ph rs shape v b).trans (congrArg Fin.val hb)⟩
            rw [←sameX,←sameI,old] at good
            contradiction
          · have empty : PackedFlow.next A hosts t j=none := by
              unfold PackedFlow.next
              dsimp only
              split
              · rename_i found
                exact False.elim (hit found)
              · rfl
            simp [hx,hj,empty] at can

include pd shape in
theorem mounted_roster (C : Chart) (mem : Memory w) (P : Ports D) (out : Bank)
    (fit : Room C D N w out.base) (raw : Raw C rs mem) (previous : Mounted P rs mem G M)
    (ids : ∀j,(P.ids j).base+N*chunks G M≤out.base) (offsets : P.offsets.base+N≤out.base)
    (chunksBelow : P.chunks.base+N*chunks G M≤out.base) :
    let reached:=image out.base (N*D) (DescentSortedRoster.code C D N) mem
    (scan w out.base (N*D) (DescentSortedRoster.code C D N)).Exec mem reached
      (4+(N*D)*(2*(DescentSortedRoster.code C D N).work+4)) ∧
    Mounted {P with roster:=out} (roster A hosts ph) reached G M := by
  exact ⟨(issued C rs mem _ fit raw).1,sorted_eq A hosts ph pd rs shape ▸
    ports C rs mem P out fit raw previous ids offsets chunksBelow⟩

end
end Hierarchy.DescentSixParty.PackedFlow.Padded

end OAI
