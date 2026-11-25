import OAI.Hierarchy.DescentDatedTicketRank
import OAI.Hierarchy.DescentDatedTicketNativeKeys
import OAI.Hierarchy.DescentDatedTicketSockets

namespace OAI
/-! # The active native ticket at its selected matcher and material rows -/
namespace Hierarchy.DescentDatedOperandReadPipeline
open DescentDatedOperandCoordinates DescentSIMDLookup DescentRawCablePanel DescentRawCablePanel.DepotRAM
open DescentRawCablePanel.DepotRAM.Material Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section

variable (g : Geometry) (v : Data g) (j : Fin g.jobs) (h : Fin g.hosts) (k : Fin g.groups)

variable {s : DepotRAM.Shape} (blocks : g.blocks=s.blocks) (cap : g.cap=s.cap)
  (p : Fin g.paths) (born : Bool) (z : Seat s)

variable (u : Setup) (state : Fin g.paths→Parts s) (rev : Fin g.paths→Cell (chartBits s))
local notation "atRaw" => rawCandidate g blocks cap p z
local notation "q" => rawKey g v j h k

/-- Only the visible columns of the two selected rows are used. Columns six and seven
come from the same eight-column raw bank as the capture fields. -/
theorem ticketAt_selected (a : Fin (g.paths*(g.blocks*(g.cap*3))))
    (chosen : (anchorChoice g v j h k).val=a.val+1)
    (present : (q).val=Ticket.socket p born z)
    (cause : (v.origin j 0 h k).val=if born then 2 else 1) (kind : (v.prior j 0 h k).val=1)
    (mouth : born=true→(v.mouth j 1 h k).val=z.2.2.val)
    (matcher : ∀f : Fin 5,f.val≤2→(v.anchor j f a h k).val=Ticket.anchor born z f)
    (material : ∀f : Fin 6,2≤f.val→
      (v.raw j (f.castLE (by decide : 6≤8)) atRaw h k).val=(rawObserved s u (state p) (rev p) z f).val) :
    ticketAt g v j h k=Ticket.current u state rev born z q (rankV g v j 0 h k).val
      (v.origin j 2 h k).val (v.raw j 6 atRaw h k).val (v.raw j 7 atRaw h k).val := by
  unfold Ticket.current
  apply ticketAt_active_fields g v j h k blocks cap p born z a chosen present cause kind mouth matcher
  intro f cut
  exact (material f cut).trans (congrArg Fin.val (Ticket.selected_raw p born z q u state rev present f)).symm

/-- The eight outputs after the original capture/survival test at the selected occurrence. -/
theorem ticketAt_at_socket (a : Fin (g.paths*(g.blocks*(g.cap*3))))
    (chosen : (anchorChoice g v j h k).val=a.val+1)
    (present : (q).val=Ticket.socket p born z)
    (cause : (v.origin j 0 h k).val=if born then 2 else 1) (kind : (v.prior j 0 h k).val=1)
    (mouth : born=true→(v.mouth j 1 h k).val=z.2.2.val)
    (matcher : ∀f : Fin 5,f.val≤2→(v.anchor j f a h k).val=Ticket.anchor born z f)
    (material : ∀f : Fin 6,2≤f.val→
      (v.raw j (f.castLE (by decide : 6≤8)) atRaw h k).val=(rawObserved s u (state p) (rev p) z f).val) :
    let raw:=rawObserved s u (state p) (rev p) z
    let got:=(raw 2).val≠0 ∨ (raw 3).val≠0
    ticketAt g v j h k= ![if got then (raw 4).val*s.blocks+z.1.val else 0,(raw 2).val,
      (raw 3).val,if z.2.2.val=0 then (raw 5).val else 1,
      if got then 0 else (v.raw j 6 atRaw h k).val,if got then 0 else (v.raw j 7 atRaw h k).val,
      z.2.1.val,z.2.2.val] :=
  (ticketAt_selected g v j h k blocks cap p born z u state rev a chosen present cause kind mouth
    matcher material).trans (Ticket.at_socket p born z q u state rev _ _ _ _ present)

/-- The word equality also follows directly from the route and the actual chosen matcher row. -/
theorem ticketAt_routed (a : Fin (g.paths*(g.blocks*(g.cap*3))))
    (chosen : (anchorChoice g v j h k).val=a.val+1)
    (cause : (v.origin j 0 h k).val=if born then 2 else 1) (kind : (v.prior j 0 h k).val=1)
    (path : (if born then (v.origin j 1 h k).val+1 else (pathV g v j 0 h k).val)=p.val+1)
    (mouth : born=true→(v.mouth j 1 h k).val=z.2.2.val)
    (matcher : ∀f : Fin 5,f.val≤2 ∨ f.val=4→(v.anchor j f a h k).val=Ticket.anchor born z f)
    (material : ∀f : Fin 6,2≤f.val→
      (v.raw j (f.castLE (by decide : 6≤8)) atRaw h k).val=(rawObserved s u (state p) (rev p) z f).val) :
    ticketAt g v j h k=Ticket.current u state rev born z q (rankV g v j 0 h k).val
      (v.origin j 2 h k).val (v.raw j 6 atRaw h k).val (v.raw j 7 atRaw h k).val := by
  have anchor : (anchorV g v j 4 h k).val=Ticket.anchor born z 4 :=
    (congrArg Fin.val (anchorV_at g v j h k a chosen 4)).trans (matcher 4 (Or.inr rfl))
  exact ticketAt_selected g v j h k blocks cap p born z u state rev a chosen
    (rawKey_at_socket g v j h k blocks cap p born z cause path anchor mouth) cause kind mouth
    (fun f cut=>matcher f (Or.inl cut)) material

open DescentHaloWalkRAM DescentHaloPackedRebase DescentHaloDonorChart DescentSharedCableNames
open DescentDatedAddressBook DescentHostDirectory ProtocolRAM

/-- The selected fourth raw field observes the previous header's reverse-rank word at
the donor and forward path, including captures whose receiver is another host. -/
theorem selected_rank_word {H G M w : ℕ} (R : Fin H → Fin s.degree → Option (Fin H))
    (back : ∀v v' i, R v i = some v' → ∃o, R v' o = some v)
    (base : ℕ) (adj : Bank) (ok : PriorHeader.Room adj H G M s.degree base w) (m : Memory w)
    (old : ∀(v : Fin H) (i : Fin s.degree),m (adj.base+v.val*s.degree+i.val) = (number (R v i) : Word w))
    (sender receiver : Fin H) (forward : Fin (breadth s.degree))
    (same : rev p = digest (reverseEntries s R sender))
    (held : rawAtSeat s u.profile u.motifWidth u.slots false (state p) z.1 z.2.1 z.2.2 =
      DescentSharedCableNames.Packed.token (some forward))
    (hit : walk R sender (DescentHaloWalkRAM.path forward) 4 = some receiver) (fit : breadth s.degree ≤ 2^u.fieldBits)
    (material : ∀f : Fin 6, 2≤f.val →
      (v.raw j (f.castLE (by decide : 6≤8)) atRaw h k).val = (rawObserved s u (state p) (rev p) z f).val) :
    (v.raw j 4 atRaw h k).val =
      (PriorHeader.image H G M s.degree base adj m
        ((PriorHeader.rankBanks H G M s.degree base).reverseRank.base+(Ranks.id sender forward).val)).val := by
  have observed := material 4 (by decide)
  rw [same] at observed
  exact observed.trans (Ticket.capture_rank_word (s:=s) (u:=u) (R:=R) («mutual»:=back)
    base adj ok m old sender receiver (state p) z forward held hit fit)

end
end Hierarchy.DescentDatedOperandReadPipeline

end OAI
