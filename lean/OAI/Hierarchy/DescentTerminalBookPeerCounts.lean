import OAI.Hierarchy.DescentTerminalBookBoard
import OAI.Hierarchy.DescentTerminalPeerDirectory
import OAI.Hierarchy.DescentTerminalPeerCounterRead

namespace OAI
/-! # Reading the size and order of an entire peer group from bounded physical wings -/
namespace Hierarchy.DescentTerminalLocalPortBook.Board
open DescentSixParty DescentCompiler DescentSharedCableNames DescentChosenRouter DescentColonies
open DescentTerminalCableOrder DescentTerminalPeerChronology DescentTerminalGrainProfiles DescentPacking
open DescentOrderedWords DescentPackedTicketChronology Computability.BorderVNP.Crossing
open DescentPacking.PackedMatch.Local.Stage DescentStageEdgeReceipt
open scoped Classical BigOperators
noncomputable section

variable {D groups blocks cap:ℕ} (board:Board D groups blocks cap)

theorem native_keys (lane:Fin D) (h j:ℕ) (side:board.side lane=compare h j) :
    board.keys lane=peerKeys h j lane board.ports := by
  unfold keys
  rw [side]
  unfold peerKeys
  congr 1
  funext g
  congr 1
  funext b
  ext x
  simp only [mem_keys,short_key]

variable {F P V : Type} [Field F] [Fintype V] [DecidableEq V] {d k i H : ℕ}
    {bits:P→ℕ} {W:MarkedWorld F d P bits} {G:PoweredGadget F} {price ε:ℝ}
    (A:GroupStage W G price ε (Fin groups) V k) (hosts:V↪Fin H) (S:AtomSchedule) (ready:A.StateBounds S i)
    (native:W.graph.Edge↪Fin (Fintype.card W.graph.Edge))
    (raw:Fin H→Fin A.degree→Option (Fin H)) (roster:∀v,DescentSortedRoster.present raw (hosts v)=(A.near v).map hosts)
local notation "atH" => fun v:W.graph.Site=>hosts (Prod.snd (A.pos v))
local notation "ord" => native.trans Fin.valEmbedding
local notation "names" => cableNames k (groupRank (Fin.valEmbedding (n:=groups)) (hosts.trans Fin.valEmbedding))
local notation "serial" => DescentOrderedReset.grains W A.grainCount native

include roster in
theorem reached_keys (o:V) (board:Board A.degree groups (2^k) A.cap) (lane:Fin A.degree)
    (z:Fin H) (hit:DescentSortedRoster.indexed raw (hosts o) lane=some z)
    (side:board.side lane=compare (hosts o).val z.val)
    (read:∀g b,board.ports g b=Stage.signedPanel A ord S ready names ((g,o),b)) :
    board.keys lane=keySet A hosts S ready native (hosts o) z := by
  obtain ⟨u,rfl,slot⟩:=Counter.reached_socket A hosts raw roster o lane hit
  rw [native_keys board lane _ _ side]
  let make (g:Fin groups) (b:Block k):↥(Stage.near A ((g,o),b)):=
    ⟨((g,u.val),b),Finset.mem_map.mpr ⟨(g,u.val),Finset.mem_map.mpr ⟨u.val,u.property,rfl⟩,rfl⟩⟩
  have slots (g:Fin groups) (b:Block k) :
      Ends.neighborOrder (Stage.near A) names (Stage.near_room A) ((g,o),b) (make g b)=lane := by
    have adj:(g,u.val)∈neighbors A (g,o):=Finset.mem_map.mpr ⟨u.val,u.property,rfl⟩
    have stage:=paired A (groupRank (Fin.valEmbedding (n:=groups)) (hosts.trans Fin.valEmbedding)) (g,o) b ⟨_,adj⟩
    rw [PackedFlow.socket_grouped A Fin.valEmbedding (hosts.trans Fin.valEmbedding) g o u] at stage
    exact stage.trans slot
  have all_:=union_keys A hosts S ready native names o u.val u.property
  refine Eq.trans ?_ all_
  apply Finset.biUnion_congr rfl
  intro g _
  apply Finset.biUnion_congr rfl
  intro b _
  rw [read g b]
  exact congrArg (localKeys (hosts o).val (hosts u.val).val g.val b.val (2^k)
    (Stage.signedPanel A ord S ready names ((g,o),b))) (slots g b).symm

include roster in
theorem missing_keys (o:V) (board:Board A.degree groups (2^k) A.cap) (lane:Fin A.degree)
    (off:DescentSortedRoster.indexed raw (hosts o) lane=none)
    (read:∀g b,board.ports g b=Stage.signedPanel A ord S ready names ((g,o),b)) :
    board.keys lane=∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro z hz
  obtain ⟨g,_,h⟩:=Finset.mem_biUnion.mp hz
  obtain ⟨b,_,h⟩:=Finset.mem_biUnion.mp h
  obtain ⟨j,u,hit,side,_⟩:=(mem_keys ..).mp h
  rw [read] at hit
  let h:Stage.Host (Fin groups) V k:=((g,o),b)
  have yes:∃a,Stage.signed A ord S ready h.1 h.2 a=j:=by
    by_contra no
    rw [Stage.signed_empty A ord S ready names h j (not_exists.mp no)] at hit
    contradiction
  obtain ⟨a,rfl⟩:=yes
  rw [Stage.signed_read] at hit
  obtain rfl:=Option.some.inj hit
  let src:=Stage.source A ord
  let q:=Stage.ofPort A ord h a
  let peer:=src.peer h q.val
  have near:=src.peer_mem (Stage.near A) (Stage.connected A ord) h q
  obtain ⟨t,ht,eqn⟩:=Finset.mem_map.mp near
  obtain ⟨v,hv,eqv⟩:=Finset.mem_map.mp ht
  change (((t.1,t.2),b):Stage.Host (Fin groups) V k)=peer at eqn
  have source:peer=((g,v),b):=by rw [←eqn,←eqv];rfl
  let kx:=PackedFlow.socket A (hosts.trans Fin.valEmbedding) o ⟨v,hv⟩
  have pos:DescentSortedRoster.indexed raw (hosts o) kx=some (hosts v):=by
    apply (DescentSortedRoster.indexed_iff ..).2
    constructor
    · rw [roster];exact Finset.mem_map.mpr ⟨_,hv,rfl⟩
    · dsimp only [kx]
      rw [DescentSortedRoster.before,roster,PackedFlow.socket,nb_val,Finset.filter_map,Finset.card_map]
      rfl
  have adj:(g,v)∈neighbors A (g,o):=Finset.mem_map.mpr ⟨v,hv,rfl⟩
  have slot:=paired A (groupRank (Fin.valEmbedding (n:=groups)) (hosts.trans Fin.valEmbedding)) (g,o) b ⟨_,adj⟩
  rw [PackedFlow.socket_grouped A Fin.valEmbedding (hosts.trans Fin.valEmbedding) g o ⟨v,hv⟩] at slot
  have equal:kx=lane:=slot.symm.trans (((peer_slot A ord S ready names h _ a).2 source).symm.trans side)
  rw [equal,off] at pos
  contradiction

variable (named:SiteOrder A hosts) (ordered:SourceSorted W native)

include named ordered in
theorem key_count (i j:Fin H) :
    (keySet A hosts S ready native i j).card=
      ∑e∈Finset.univ.filter (fun e=>pairIndex W.graph atH e=pair i j),A.grainCount e := by
  classical
  let keep (e:W.graph.Edge):=pairIndex W.graph atH e=pair i j
  let code:=grainKey A hosts S ready native (min i.val j.val)
  have endAt (y:Stage.Grain A) (hy:keep y.1) :
      (atH (W.graph.src y.1)).val=min i.val j.val ∨ (atH (W.graph.src y.1)).val=max i.val j.val := by
    obtain ⟨l,_⟩|⟨l,_⟩:=(pair_iff ..).1 hy
    all_goals rw [l];omega
  unfold keySet
  rw [Finset.card_image_of_injOn]
  · rw [Finset.card_filter,Fintype.sum_sigma,Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro e _
    by_cases he:keep e <;> simp [keep] at he ⊢ <;> simp [he]
  · intro x hx y hy eqn
    have xAt:=endAt x (Finset.mem_filter.mp hx).2
    have yAt:=endAt y (Finset.mem_filter.mp hy).2
    have unique (x y:Stage.Grain A) (a:_∨_) (b:_∨_) := grain_order A hosts S ready native named ordered (min_le_max : min i.val j.val ≤ max i.val j.val) x y a b
    apply (serial).injective
    apply le_antisymm
    · by_contra! gt
      exact ((unique y x yAt xAt).mp ((earlier_grain ..).mp gt)).ne eqn.symm
    · by_contra! gt
      exact ((unique x y xAt yAt).mp ((earlier_grain ..).mp gt)).ne eqn

include named ordered in
theorem entire_pair {scale p:ℕ} (hp:0<p) (whole:A.z*G.b=scale*p) (i j:Fin H) :
    (keySet A hosts S ready native i j).card*scale=pairMass W.graph atH (pair i j)/p := by
  rw [key_count A hosts S ready native named ordered,pairMass]
  have each (e:W.graph.Edge):W.graph.width e=A.grainCount e*scale*p:=by
    rw [A.grainCount_fit S ready e,whole,Nat.mul_assoc]
  simp only [each,←Finset.sum_mul]
  exact (Nat.mul_div_cancel _ hp).symm

end
end Hierarchy.DescentTerminalLocalPortBook.Board

end OAI
