import OAI.Hierarchy.DescentDatedTicketNativeKeys
import OAI.Hierarchy.DescentDatedSourcePathHeaders
import OAI.Hierarchy.DescentOrdinaryOriginPorts
import OAI.Hierarchy.DescentOperandStateCodec

namespace OAI
/-! The native socket key at a retained or newborn W stamp. -/
namespace Hierarchy.DescentDatedOperandReadPipeline
open DescentSIMDLookup DescentDatedOperandCoordinates DescentPacking.PackedMatch.Local.Stage
open DescentOrdinaryOriginMask DescentOrdinaryOriginPorts
open scoped Classical
noncomputable section

/-- The original W register is a bank of one-based compacted ordinals. -/
theorem origin_from_stamp (R : Return) {d : ℕ} (node : Fin R.newNodes)
    (word : Cell (R.ordinalBits*R.newNodes)) (i : Fin (extent R)) (f : Fin 6)
    (stamp : ((encode R.ordinalBits R.newNodes).symm word node).val=i.val+1)
    (fits : tuple R i f<2^d) :
    (readLaw R d node f word).val=tuple R i f := by
  rw [at_stamp R d node f word i stamp]
  exact Nat.mod_eq_of_lt fits

variable (g : Geometry) (v : Data g) (j : Fin g.jobs) (h : Fin g.hosts) (k : Fin g.groups)

theorem origin_at_old (R : Return) (p : Fin (DescentHaloWalkRAM.breadth R.degree))
    (x : Fin (2^R.depth)) (n : Fin R.oldNodes) (node : Fin R.newNodes)
    (word : Cell (R.ordinalBits*R.newNodes))
    (stamp : ((encode R.ordinalBits R.newNodes).symm word node).val=(candidate R p x (.inl n)).val+1)
    (read : ∀f,v.origin j f h k=readLaw R g.digitBits node f word)
    (f : Fin 6) (fits : (![1,p.val,x.val,n.val,0,0] f)<2^g.digitBits) :
    (v.origin j f h k).val=![1,p.val,x.val,n.val,0,0] f := by
  rw [read,← tuple_old R p x n]
  apply origin_from_stamp R node word _ f stamp
  rwa [tuple_old]

theorem origin_at_birth (R : Return) (p : Fin (DescentHaloWalkRAM.breadth R.degree))
    (x : Fin (2^R.depth)) (t : Fin R.capacity) (party : Fin 6) (node : Fin R.newNodes)
    (word : Cell (R.ordinalBits*R.newNodes))
    (stamp : ((encode R.ordinalBits R.newNodes).symm word node).val=(candidate R p x (.inr (t,party))).val+1)
    (read : ∀f,v.origin j f h k=readLaw R g.digitBits node f word)
    (f : Fin 6) (fits : (![2,p.val,x.val,0,t.val,party.val] f)<2^g.digitBits) :
    (v.origin j f h k).val=![2,p.val,x.val,0,t.val,party.val] f := by
  rw [read,← tuple_born R p x t party]
  apply origin_from_stamp R node word _ f stamp
  rwa [tuple_born]

/-- A retained wire addresses its ordinary stay/neighbor column with its signed polarity. -/
theorem path_choice_previous (p : Fin g.paths) (e : Fin g.degree) (target : Bool)
    (cause : (v.origin j 0 h k).val=1) (walk : (v.origin j 1 h k).val=p.val)
    (slot : (oldV g v j 3 h k).val≠0)
    (neighbor : target=true → (oldV g v j 1 h k).val=e.val+1)
    (side : (oldV g v j 2 h k).val=target.toNat) :
    (pathChoice g v j h k).val=(finProdFinEquiv (p,if target then e.castSucc else Fin.last g.degree)).val+1 := by
  let index:=finProdFinEquiv (p,if target then e.castSucc else Fin.last g.degree)
  change (DescentDatedOperandCoordinates.digit _ (previousPath g.paths g.degree (v.origin j 0 h k).val (v.origin j 1 h k).val
    (oldV g v j 3 h k).val (oldV g v j 1 h k).val (oldV g v j 2 h k).val)).val=index.val+1
  rw [cause,walk,side]
  have key : previousPath g.paths g.degree 1 p.val (oldV g v j 3 h k).val
      (oldV g v j 1 h k).val target.toNat=index.val+1 := by
    cases target
    · exact stay_at p _ _ slot
    · rw [neighbor rfl]
      exact peer_at p _ e slot
  rw [key]
  exact digit_at index.isLt

/-- Address the actual one-based slice printed by the matcher for a retained cable. -/
theorem anchor_choice_old (p : Fin g.paths) (x : Fin g.blocks) (t : Fin g.cap) (target : Bool)
    (cause : (v.origin j 0 h k).val=1) (kind : (v.prior j 0 h k).val=1)
    (path : (pathV g v j 0 h k).val=p.val+1) (block : (v.origin j 2 h k).val=x.val)
    (slot : (oldV g v j 3 h k).val=t.val+1) (side : (oldV g v j 2 h k).val=target.toNat) :
    (anchorChoice g v j h k).val=(finProdFinEquiv (p,finProdFinEquiv (x,
      finProdFinEquiv (t,(if target then 1 else 0:Fin 3))))).val+1 := by
  let a:=finProdFinEquiv (p,finProdFinEquiv (x,finProdFinEquiv (t,(if target then 1 else 0:Fin 3))))
  change (DescentDatedOperandCoordinates.digit _ (anchorKey _ _ _ (v.origin j 0 h k).val (v.prior j 0 h k).val
    (sourcePath (v.origin j 0 h k).val (v.origin j 1 h k).val (pathV g v j 0 h k).val)
    (v.origin j 2 h k).val (oldV g v j 3 h k).val (oldV g v j 2 h k).val
    (v.origin j 4 h k).val (v.mouth j 0 h k).val)).val=a.val+1
  rw [cause,kind,block,slot,side]
  change (DescentDatedOperandCoordinates.digit _ (anchorKey _ _ _ 1 1 (pathV g v j 0 h k).val x.val (t.val+1) target.toNat _ _)).val = a.val+1
  rw [path]
  rw [carried_at p x t target]
  exact digit_at a.isLt

theorem anchor_choice_birth (p : Fin g.paths) (x : Fin g.blocks) (t : Fin g.cap) (second : Bool)
    (cause : (v.origin j 0 h k).val=2) (kind : (v.prior j 0 h k).val=1)
    (path : (v.origin j 1 h k).val=p.val) (block : (v.origin j 2 h k).val=x.val)
    (slot : (v.origin j 4 h k).val=t.val) (side : (v.mouth j 0 h k).val=second.toNat) :
    (anchorChoice g v j h k).val=(finProdFinEquiv (p,finProdFinEquiv (x,
      finProdFinEquiv (t,(if second then 2 else 0:Fin 3))))).val+1 := by
  let a:=finProdFinEquiv (p,finProdFinEquiv (x,finProdFinEquiv (t,(if second then 2 else 0:Fin 3))))
  change (DescentDatedOperandCoordinates.digit _ (anchorKey _ _ _ (v.origin j 0 h k).val (v.prior j 0 h k).val
    (sourcePath (v.origin j 0 h k).val (v.origin j 1 h k).val (pathV g v j 0 h k).val)
    (v.origin j 2 h k).val (oldV g v j 3 h k).val (oldV g v j 2 h k).val
    (v.origin j 4 h k).val (v.mouth j 0 h k).val)).val=a.val+1
  rw [cause,kind,path,block,slot,side]
  change (DescentDatedOperandCoordinates.digit _ (anchorKey _ _ _ 2 1 (p.val+1) x.val _ _ t.val second.toNat)).val = a.val+1
  rw [born_at p x t second]
  exact digit_at a.isLt

/-- Numerical readback of every true physical anchor, including the redirected target. -/
theorem selected_anchor {B C : ℕ} (shape : DescentPacking.PackedMatch.Shape)
    (packet : Cell shape.outputBits) (a : Fin (g.paths*(g.blocks*(g.cap*3))))
    (selected : (anchorChoice g v j h k).val=a.val+1)
    (target : Bool) (key : ℕ) (small : key<2^shape.digit) (z : Ticket.SocketSeat B C) (born : Bool)
    (chosen : retarget (topologyRecord shape packet) target key =
      (z.1.val*(2*C)+z.2.1.val,if born then 0 else z.2.2.val))
    (f : Fin 5) (fits : Ticket.anchor born z f<2^(shape.digit+4))
    (issued : (v.anchor j f a h k).val =
      (anchorField shape C f packet (anchorQuery shape.digit key target)).val) :
    (anchorV g v j f h k).val=Ticket.anchor born z f := by
  rw [anchorV_at g v j h k a selected f,issued,Ticket.matcher_at shape packet target key small z born chosen f]
  exact Nat.mod_eq_of_lt fits

/-- Exact old four-column index before looking up a signed slot. -/
theorem oldV_from_header (p : Fin g.paths) (x : Fin g.blocks) (peer : Fin g.degree) (serial : Fin g.cap)
    (cause : (v.origin j 0 h k).val=1) (kind : (v.prior j 0 h k).val=1)
    (walk : (v.origin j 1 h k).val=p.val) (block : (v.origin j 2 h k).val=x.val)
    (priorPeer : (v.prior j 1 h k).val=peer.val) (priorSerial : (v.prior j 2 h k).val=serial.val)
    (f : Fin 4) : oldV g v j f h k =
      v.old j f (finProdFinEquiv (p,finProdFinEquiv (x,finProdFinEquiv (peer,serial)))) h k := by
  let i:=finProdFinEquiv (p,finProdFinEquiv (x,finProdFinEquiv (peer,serial)))
  apply DescentResetStemMux.pick_actor _ (fun t=>v.old j f t h k) i
  change (DescentDatedOperandCoordinates.digit _ (oldName _ _ _ _ (v.origin j 0 h k).val (v.prior j 0 h k).val
    (v.origin j 1 h k).val (v.origin j 2 h k).val (v.prior j 1 h k).val (v.prior j 2 h k).val)).val=i.val+1
  rw [cause,kind,walk,block,priorPeer,priorSerial,old_name_at p x peer serial]
  exact digit_at i.isLt

/-- The measured source-path cell in native field two supplies the same one-based
donor as the signed walk. The two physical addresses are fixed by the prior polarity. -/
theorem prior_path_read (p q : Fin g.paths) (e : Fin g.degree) (target : Bool)
    (cause : (v.origin j 0 h k).val=1) (walk : (v.origin j 1 h k).val=p.val)
    (slot : (oldV g v j 3 h k).val≠0) (neighbor : target=true → (oldV g v j 1 h k).val=e.val+1)
    (side : (oldV g v j 2 h k).val=target.toNat)
    (reach : Fin g.hosts→Fin g.paths→Option (Fin g.hosts)) (short : Fin (g.degree+1)→Fin g.paths)
    (table : (v.path (finProdFinEquiv (p,if target then e.castSucc else Fin.last g.degree)) h k).val =
      DescentDatedSourcePathDirectory.value reach h p (short (if target then e.castSucc else Fin.last g.degree)))
    (original : DescentDatedSourcePathDirectory.value reach h p (short (if target then e.castSucc else Fin.last g.degree))=q.val+1) :
    (pathV g v j 0 h k).val=q.val+1 := by
  rw [pathV_at g v j h k _ (path_choice_previous g v j h k p e target cause walk slot neighbor side)]
  exact table.trans original

/-- The retained socket starts from the literal old W stamp, the saved cable header
and the signed row. The path and matcher tables are both addressed by their measured fields. -/
theorem prior_origin_rows (R : Return) (walk : Fin (DescentHaloWalkRAM.breadth R.degree))
    (block : Fin (2^R.depth)) (n : Fin R.oldNodes) (node : Fin R.newNodes)
    (word : Cell (R.ordinalBits*R.newNodes))
    (stamp : ((encode R.ordinalBits R.newNodes).symm word node).val=(candidate R walk block (.inl n)).val+1)
    (origin : ∀f,v.origin j f h k=readLaw R g.digitBits node f word)
    (o p : Fin g.paths) (x : Fin g.blocks) (peer neighbor : Fin g.degree) (serial old : Fin g.cap)
    (rootId : walk.val=o.val) (blockId : block.val=x.val)
    (wide : max 1 (max walk.val block.val)<2^g.digitBits)
    (chunk : ℕ) (prior : ∀f,(v.prior j f h k).val =
      (DescentOperandStateBanks.Pointer.cable peer.val serial.val chunk).header f)
    (target : Bool)
    (saved : let i:=finProdFinEquiv (o,finProdFinEquiv (x,finProdFinEquiv (peer,serial)))
      (v.old j 3 i h k).val=old.val+1 ∧ (v.old j 2 i h k).val=target.toNat ∧
        (target=true → (v.old j 1 i h k).val=neighbor.val+1))
    (reach : Fin g.hosts→Fin g.paths→Option (Fin g.hosts)) (short : Fin (g.degree+1)→Fin g.paths)
    (table : (v.path (finProdFinEquiv (o,if target then neighbor.castSucc else Fin.last g.degree)) h k).val =
      DescentDatedSourcePathDirectory.value reach h o (short (if target then neighbor.castSucc else Fin.last g.degree)))
    (original : DescentDatedSourcePathDirectory.value reach h o (short (if target then neighbor.castSucc else Fin.last g.degree))=p.val+1)
    (z : Ticket.SocketSeat g.blocks g.cap)
    (issued : let a:=finProdFinEquiv (p,finProdFinEquiv (x,finProdFinEquiv (old,(if target then 1 else 0:Fin 3))))
      (v.anchor j 4 a h k).val=Ticket.anchor false z 4) :
    (rawKey g v j h k).val=Ticket.socket p false z ∧ (v.origin j 0 h k).val=1 ∧ (v.prior j 0 h k).val=1 ∧
      (anchorChoice g v j h k).val=(finProdFinEquiv (p,finProdFinEquiv (x,
        finProdFinEquiv (old,(if target then 1 else 0:Fin 3))))).val+1 ∧
      (pathV g v j 0 h k).val=p.val+1 := by
  have origin_:=origin_at_old g v j h k R walk block n node word stamp origin
  have cause : (v.origin j 0 h k).val=1:=origin_ 0 (by change 1<2^g.digitBits; omega)
  have root_ : (v.origin j 1 h k).val=o.val:=(origin_ 1 (by change walk.val<2^g.digitBits; omega)).trans rootId
  have block_ : (v.origin j 2 h k).val=x.val:=(origin_ 2 (by change block.val<2^g.digitBits; omega)).trans blockId
  have kind : (v.prior j 0 h k).val=1:=prior 0
  have old_:=oldV_from_header g v j h k o x peer serial cause kind root_ block_ (prior 1) (prior 2)
  have slot : (oldV g v j 3 h k).val=old.val+1:=(congrArg Fin.val (old_ 3)).trans saved.1
  have side : (oldV g v j 2 h k).val=target.toNat:=(congrArg Fin.val (old_ 2)).trans saved.2.1
  have path:=prior_path_read g v j h k o p neighbor target cause root_ (by omega)
    (fun yes=>(congrArg Fin.val (old_ 1)).trans (saved.2.2 yes)) side reach short table original
  have row:=anchor_choice_old g v j h k p x old target cause kind path block_ slot side
  have head: (anchorV g v j 4 h k).val=Ticket.anchor false z 4 :=
    (congrArg Fin.val (anchorV_at g v j h k _ row 4)).trans issued
  exact ⟨rawKey_at_socket g v j h k rfl rfl p false z cause path head (by simp),cause,kind,row,path⟩

theorem prior_origin_socket (R : Return) (walk : Fin (DescentHaloWalkRAM.breadth R.degree))
    (block : Fin (2^R.depth)) (n : Fin R.oldNodes) (node : Fin R.newNodes)
    (word : Cell (R.ordinalBits*R.newNodes))
    (stamp : ((encode R.ordinalBits R.newNodes).symm word node).val=(candidate R walk block (.inl n)).val+1)
    (origin : ∀f,v.origin j f h k=readLaw R g.digitBits node f word)
    (o p : Fin g.paths) (x : Fin g.blocks) (peer neighbor : Fin g.degree) (serial old : Fin g.cap)
    (rootId : walk.val=o.val) (blockId : block.val=x.val)
    (wide : max 1 (max walk.val block.val)<2^g.digitBits)
    (chunk : ℕ) (prior : ∀f,(v.prior j f h k).val =
      (DescentOperandStateBanks.Pointer.cable peer.val serial.val chunk).header f)
    (target : Bool)
    (saved : let i:=finProdFinEquiv (o,finProdFinEquiv (x,finProdFinEquiv (peer,serial)))
      (v.old j 3 i h k).val=old.val+1 ∧ (v.old j 2 i h k).val=target.toNat ∧
        (target=true → (v.old j 1 i h k).val=neighbor.val+1))
    (reach : Fin g.hosts→Fin g.paths→Option (Fin g.hosts)) (short : Fin (g.degree+1)→Fin g.paths)
    (table : (v.path (finProdFinEquiv (o,if target then neighbor.castSucc else Fin.last g.degree)) h k).val =
      DescentDatedSourcePathDirectory.value reach h o (short (if target then neighbor.castSucc else Fin.last g.degree)))
    (original : DescentDatedSourcePathDirectory.value reach h o (short (if target then neighbor.castSucc else Fin.last g.degree))=p.val+1)
    (z : Ticket.SocketSeat g.blocks g.cap)
    (issued : let a:=finProdFinEquiv (p,finProdFinEquiv (x,finProdFinEquiv (old,(if target then 1 else 0:Fin 3))))
      (v.anchor j 4 a h k).val=Ticket.anchor false z 4) :
    (rawKey g v j h k).val=Ticket.socket p false z ∧ (v.origin j 0 h k).val=1 ∧ (v.prior j 0 h k).val=1 := by
  obtain ⟨word_,cause,kind,_,_⟩:=prior_origin_rows g v j h k R walk block n node word stamp origin o p x peer
    neighbor serial old rootId blockId wide chunk prior target saved reach short table original z issued
  exact ⟨word_,cause,kind⟩


end
end Hierarchy.DescentDatedOperandReadPipeline

end OAI
