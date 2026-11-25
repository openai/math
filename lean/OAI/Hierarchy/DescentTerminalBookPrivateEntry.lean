import OAI.Hierarchy.DescentTerminalBookPrivatePeer

namespace OAI
/-! # Repeated cable operands read the same truthful catalog entry at either endpoint -/
namespace Hierarchy.DescentTerminalLocalPortBook.Board
open DescentSixParty DescentCompiler DescentSharedCableNames DescentColonies DescentChosenRouter DescentPackedTicketChronology
open DescentTerminalPeerChronology DescentTerminalPointerDigits DescentTerminalGrainProfiles DescentTerminalPaidHeaderEvents
open DescentTerminalGraphPositions DescentTerminalCableOrder DescentPacking DescentSortedRoster
open DescentPacking.PackedMatch.Local.Stage DescentKernelHistory DescentTerminalGraphRows Computability.BorderVNP.Crossing DescentStageEdgeReceipt
open ThreeFlat.Routing
open scoped Classical BigOperators
noncomputable section

variable {F P V:Type} [Field F] [Fintype P] [Fintype V] [DecidableEq V] {groups d k i H p scale:ℕ}
    {bits:P→ℕ} {W:MarkedWorld F d P bits} {G:PoweredGadget F} {price ε:ℝ}
    (A:GroupStage W G price ε (Fin groups) V k) (hosts:V↪Fin H) (S:AtomSchedule) (ready:A.StateBounds S i)
    (native:W.graph.Edge↪Fin (Fintype.card W.graph.Edge)) (raw:Fin H→Fin A.degree→Option (Fin H))
    (roster:∀o,present raw (hosts o)=(A.near o).map hosts)
    (ordered:Sorted (indexed raw)) (birth:SiteOrder A hosts) (sorted:SourceSorted W native)
    (coords:Function.Injective (fun s=>(A.pos s,A.block s)))
    (ext:P↪ℕ) (nodes:W.graph.Site↪ℕ) (pins:∀v,Attached W.graph v↪ℕ)
    (hp:0<p) (whole:A.z*G.b=scale*p)
local notation "ord" => native.trans Fin.valEmbedding
local notation "names" => cableNames k (groupRank (Fin.valEmbedding (n:=groups)) (hosts.trans Fin.valEmbedding))
local notation "ops" => fun v=>DescentTerminalPortChart.rank A ord S ready names v (pins v)
local notation "atH" => fun v:W.graph.Site=>hosts (Prod.snd (A.pos v))
local notation "graph" => order W.graph atH native p ext nodes ops

include roster ordered birth sorted coords hp whole in
/-- The search is on a single bounded node panel. Its two possible hits for
a loop have the same catalog row and the same payload coordinate. -/
theorem cable_entry (v:W.graph.Site) (edge:Incident W.graph v) (j:Fin (poolBatchCount (W.graph.width edge.val) p))
    (g:Order.Group graph (atH v)) (nm:Order.At graph (atH v) g) (name:nm.val=.inl ⟨edge.val,j⟩)
    (socket:Fin (A.degree+1)) (socketTag:label (indexed raw) (atH v) socket=some g.val)
    (board:Board A.degree groups (2^k) A.cap)
    (sides:∀l o,indexed raw (atH v) l=some o→board.side l=compare (atH v).val o.val)
    (panel:∀g b,board.ports g b=Stage.signedPanel A ord S ready names ((g,(A.pos v).2),b))
    (arity pinWords calendar:ℕ) (active:Fin groups→Block k→ℕ)
    (jRoom:(number W.graph p v (ops v) ⟨.inl edge,j⟩).val<arity) :
    (board.directory arity scale pinWords calendar active).address
      (finProdFinEquiv ((A.pos v).1,A.block v)) ⟨_,jRoom⟩=some (socket,(Order.inGroup graph _ g nm).val) := by
  let h:=Stage.home A v
  let addr:=number W.graph p v (ops v)
  let lookup:=Stage.signedPanel A ord S ready names h
  let here:=atH v
  let pos:=(addr ⟨.inl edge,j⟩).val
  let info:=Stage.live A ord S ready names h
  have actual:board.ports (A.pos v).1 (A.block v)=lookup:=panel _ _
  have inside_ : pos<board.internal scale (A.pos v).1 (A.block v):=by
    rw [internal,actual];exact inside A S ready native names coords v (pins v) hp whole edge j
  simp only [directory,Equiv.symm_apply_apply]
  rw [ite_eq_left inside_]
  apply lookup_read
  · rw [actual]
    exact choose_live A S ready native names coords v (pins v) hp whole edge j
  · intro t z l measured matched
    rw [actual] at measured matched
    obtain ⟨u,e,m,head,rec,whereAt⟩:=candidate_word A S ready native names coords v (pins v) hp whole t z l measured
    subst z
    let piece:Fin (poolBatchCount (W.graph.width e.val) p):=⟨m.val*scale+l.val,fine_word A S ready v hp whole e m l⟩
    have same:((⟨.inl e,piece⟩:Part W.graph p v))=⟨.inl edge,j⟩:=addr.injective (Fin.ext (whereAt.symm.trans matched))
    have valid:nm.val=.inl ⟨e.val,piece⟩:=name.trans (congrArg (DescentTerminalGraphPositions.name W.graph) same.symm)
    let y:=Stage.recover A h u
    let grainWord:Fin (poolBatchCount (W.graph.width y.1) p):=⟨y.2.val*scale+l.val,by
      change (Stage.recover A (Stage.home A v) u).2.val*scale+l.val<poolBatchCount (W.graph.width (Stage.recover A (Stage.home A v) u).1) p
      rw [rec]
      exact piece.isLt⟩
    have original:nm.val=.inl ⟨y.1,grainWord⟩:=by
      have edgeId:e.val=y.1:=congrArg Sigma.fst rec.symm
      apply valid.trans
      apply congrArg Sum.inl
      apply Sigma.ext edgeId
      apply (Fin.heq_ext_iff (congrArg (fun a=>poolBatchCount (W.graph.width a) p) edgeId)).mpr
      exact congrArg (fun a=>(a.2:Fin (A.grainCount a.1)).val*scale+l.val) rec.symm
    let peer:=hosts ((Stage.source A ord).peer h (Stage.ofPort A ord h u).val).1.2
    let lane:=(info u).neighbor
    have physical:indexed raw here lane=some peer:=wing_socket A hosts S ready native raw roster h u
    have side:=sides lane peer physical
    have opposite:g.val=some peer:=actual_neighbor A hosts native ext nodes ops v u g nm grainWord original
    have laneTag:label (indexed raw) here lane.succ=some g.val:=by simp [DescentTerminalPaidHeaderEvents.label,physical,opposite]
    have row := same_socket (indexed raw) ordered here lane.succ socket g.val laneTag socketTag
    have entryOffset:=group_read A hosts S ready native names birth sorted v hp whole ext nodes ops u peer rfl g opposite nm l grainWord rfl original
    have output := reached_keys A hosts S ready native raw roster (A.pos v).2 board lane peer physical side panel
    apply Prod.ext row
    change portOffset (board.keys lane) (Board.here (board.side lane)) (Board.other (board.side lane)) _ _ _ scale l.val (info u)=_
    rw [output,side,portOffset,short_key]
    exact entryOffset

end
end Hierarchy.DescentTerminalLocalPortBook.Board

end OAI
