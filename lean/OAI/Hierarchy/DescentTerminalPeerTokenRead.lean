import OAI.Hierarchy.DescentTerminalPeerChronology
import OAI.Hierarchy.DescentTerminalNeighborVolume

namespace OAI
/-! # Recover the source-order key at either printed wing, including self loops -/
namespace Hierarchy.DescentTerminalPeerChronology
open DescentSixParty DescentCompiler DescentSharedCableNames DescentOrderedWords DescentChosenRouter
open DescentColonies DescentPackedTicketChronology Computability.BorderVNP.Crossing
open scoped Classical
noncomputable section

variable {F P V : Type} [Field F] [Fintype V] [DecidableEq V] {groups d k i Hn : ℕ}
    {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F} {price ε:ℝ}
    (A : GroupStage W G price ε (Fin groups) V k)
    (hosts : V↪Fin Hn) (S : AtomSchedule) (ready : A.StateBounds S i)
    (native : W.graph.Edge↪Fin (Fintype.card W.graph.Edge))
    (names : Stage.Host (Fin groups) V k↪ℕ)
local notation "ord" => native.trans Fin.valEmbedding
local notation "B" => Stage.source A ord
local notation "wing" => Stage.live A ord S ready names

/-- Evaluated by the short geometry lookup. Only the comparison of the two
hosts is needed to select the sender digit. -/
def wingKey {D cap : ℕ} (here peer group block blocks:ℕ) (r:Stage.Live D cap) :=
  key (cell group (min here peer) (if r.target then peer else here) block blocks) cap r.sourceWire.val r.within.val

theorem recover_stream (h:Stage.Host (Fin groups) V k) (u:A.CellPorts h.1.1 h.1.2 h.2) :
    (Stage.ofPort A ord h u).val=Stage.stream A ord (Stage.recover A h u) := by cases u <;> rfl

theorem source_wing (h:Stage.Host (Fin groups) V k) (u:A.CellPorts h.1.1 h.1.2 h.2) :
    Stage.home A (W.graph.src (Stage.recover A h u).1)=
      if (wing h u).target then (B).peer h (Stage.ofPort A ord h u).val else h := by
  rcases h with ⟨⟨g,v⟩,b⟩
  rcases u with ⟨e,j⟩|⟨e,j⟩
  · simpa [Stage.live,Stage.signedBit,Stage.recover,Stage.home] using
      (Prod.ext e.property.1 e.property.2 : (A.pos (W.graph.src e.val),A.block (W.graph.src e.val))=((g,v),b))
  · have dst:Stage.home A (W.graph.dst e.val)=((g,v),b):=Prod.ext e.property.1 e.property.2
    simp only [Stage.live,Stage.signedBit,Sum.elim_inr,Fin.val_one,decide_true,ite_true,
      Stage.recover,Ends.peer,recover_stream,Stage.source,Equiv.symm_apply_apply]
    split
    · rename_i eqn
      exact eqn.trans dst.symm
    · rfl

theorem peer_home (h:Stage.Host (Fin groups) V k) (u:A.CellPorts h.1.1 h.1.2 h.2) :
    ((B).peer h (Stage.ofPort A ord h u).val).1.1=h.1.1 ∧
    ((B).peer h (Stage.ofPort A ord h u).val).2=h.2 := by
  let e:=Stage.ofPort A ord h u
  have friend:=(B).peer_mem (Stage.near A) (Stage.connected A ord) h e
  obtain ⟨z,zmem,eqn⟩:=Finset.mem_map.mp friend
  obtain ⟨u,_,rfl⟩:=Finset.mem_map.mp zmem
  exact ⟨(congrArg (fun t:Stage.Host (Fin groups) V k=>t.1.1) eqn).symm,
    (congrArg (fun t:Stage.Host (Fin groups) V k=>t.2) eqn).symm⟩

theorem wing_key (h:Stage.Host (Fin groups) V k) (u:A.CellPorts h.1.1 h.1.2 h.2) :
    let peer:=(B).peer h (Stage.ofPort A ord h u).val
    wingKey (hosts h.1.2).val (hosts peer.1.2).val h.1.1.val h.2.val (2^k) (wing h u)=
      grainKey A hosts S ready native (min (hosts h.1.2).val (hosts peer.1.2).val) (Stage.recover A h u) := by
  intro peer
  let tgt:=(wing h u).target
  let src:=W.graph.src (Stage.recover A h u).1
  have addr:Stage.home A src=(if tgt then peer else h):=source_wing A S ready native names h u
  have both:=peer_home A native h u
  change key _ A.cap _ _=key _ A.cap _ _
  congr 1
  change cell _ _ _ _ _=cell (Stage.home A src).1.1.val _ (hosts (Stage.home A src).1.2).val
    (Stage.home A src).2.val (2^k)
  cases hx:tgt <;> simp [tgt] at hx <;> simp [addr,tgt,hx,peer]; simp_all [peer]

end
end Hierarchy.DescentTerminalPeerChronology

end OAI
