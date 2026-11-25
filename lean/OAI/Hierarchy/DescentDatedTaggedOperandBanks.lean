import OAI.Hierarchy.DescentPackedPorts
import OAI.Hierarchy.DescentDatedOperandBankSlots
import OAI.Hierarchy.DescentDatedOperandRecordedSide
import OAI.Hierarchy.DescentDatedOperandTagRead

namespace OAI
/-! Registering the exact packed source rows and public routes used by a tagged resolver job. -/
namespace Hierarchy.DescentDatedPriorOperand
open DescentSIMDLookup DescentPackedColony DescentOperandStateBanks DescentPackedOperand
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {l : Layout} {floor w : ℕ} (t : Banks l) (b : Books l)
    (s : Fin l.jobs→Fin l.hosts→Fin l.groups→DescentPriorOperandColumns.Side l.size)
    (r : Fin l.jobs→Fin 3→Fin l.hosts→Fin l.groups→Cell (l.size+2))
    (room : ∀(j:Fin l.jobs) (h:Fin l.hosts) (g:Fin l.groups),11*(r j 1 h g).val+(r j 2 h g).val<2^(l.size+2))

structure Banks.Tagged (m : Memory w) : Prop where
  tags : BookTags b
  previous : ∀j p,Reads (t.book j p) ((decodedBooks b s r room j).books p) l.lanes m
  side : ∀j i,Reads (t.side j i) (fun h g=>sourceFields ((decodedBooks b s r room j).fragment h g)
    (DescentPriorOperandColumns.sideIndex i)) l.lanes m
  route : ∀j i,Reads (t.route j i) (r j i) l.lanes m

/-- Only the actual tag, the original bank reads and the unchanged current side and route
fields are necessary. The private pointer may retain its previous peer and chunk. -/
theorem registered_books_tagged (tags : BookTags b) (m : Memory w)
    (previous : ∀x p,Reads (t.previous x p) (b x p) l.lanes m)
    (side : ∀j i,Reads (t.side j i) (fun h g=>sourceFields ((decodedBooks b s r room j).fragment h g)
      (DescentPriorOperandColumns.sideIndex i)) l.lanes m)
    (roles : ∀j i,Reads (t.route j i) (r j i) l.lanes m) :
    t.Tagged b s r room m :=
  ⟨tags,fun j p=>previous (l.index.symm j).1 p,side,roles⟩

theorem registered_digits_tagged (tags : BookTags b) (m : Memory w)
    (previous : ∀x p,Reads (t.previous x p) (b x p) l.lanes m)
    (fields : ∀j i,Reads (t.side j i) (fun h g=>(s j h g).digits i) l.lanes m)
    (roles : ∀j i,Reads (t.route j i) (r j i) l.lanes m) :
    t.Tagged b s r room m :=by
  apply registered_books_tagged t b s r room tags m previous _ roles
  intro j i
  simpa only [Source.fragment,DescentPriorOperandColumns.Side.side_value,decodedBooks] using fields j i


namespace Banks

/-- Registers held before the current allocation retain every measured previous,
side and route row when the step writes only within its own bank suffix. -/
theorem tagged_keep (early : t.Early floor w) {m o : Memory w} (prior : t.Tagged b s r room m)
    (keep : ∀a,a<floor→ o a=m a) : t.Tagged b s r room o :=by
  have transfer {width} (B : Bank) (fit : B.Fits w floor ∧ l.rows≤B.size)
      (x : Fin l.hosts→Fin l.groups→Cell width) (read : Reads B x l.lanes m) : Reads B x l.lanes o :=by
    intro q
    exact (keep _ ((Nat.add_lt_add_left ((row _ _ _ q).isLt.trans_le fit.2) _).trans_le fit.1.2.2)).trans (read q)
  exact ⟨prior.tags,fun j p=>transfer _ (early.previous j p) _ (prior.previous j p),
    fun j i=>transfer _ (early.side j i) _ (prior.side j i),fun j i=>transfer _ (early.route j i) _ (prior.route j i)⟩

end Banks

end
end Hierarchy.DescentDatedPriorOperand

end OAI
