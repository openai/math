import OAI.Hierarchy.DescentDatedTicketOriginRows
import OAI.Hierarchy.DescentDatedSortedOperandAdapter
import OAI.Hierarchy.DescentDatedSortedPathSocket
import OAI.Hierarchy.DescentDatedOperandPages

namespace OAI
/-! # The retained socket selected by a sampled signed header, path and anchor -/
namespace Hierarchy.DescentDatedOperandPages
open DescentRawCablePanel.DepotRAM DescentOperandPriorIncidence
open scoped Fin.CommRing
noncomputable section

/-- The old header depends only on the signed cable word in the selected donor packet. -/
theorem header_at_cables (s : Shape) (profile width : ℕ) (x : Fin s.blocks)
    (peer : Fin s.degree) (first : Fin s.cap) (f : Fin 4) (a b : Parts s)
    (same : a.cables=b.cables) :
    law s profile width (header s x peer first f).val (combine s a)=
      law s profile width (header s x peer first f).val (combine s b) :=by
  have cable : Origin.signedWord s x a=Origin.signedWord s x b:=by
    funext port
    simp only [Origin.signedWord,same]
  simp only [header_value,Origin.readOrigin,separate_combine,cable]

end
end Hierarchy.DescentDatedOperandPages

namespace Hierarchy.DescentDatedOperandReadPipeline
open DescentDatedOperandCoordinates DescentDatedSourcePathDirectory DescentHaloWalkRAM
open DescentSIMDLookup
open scoped Classical
noncomputable section
variable (g : Geometry) (v : Data g) (j : Fin g.jobs) (h : Fin g.hosts) (y : Fin g.groups)
    (root p : Fin g.paths) (x : Fin g.blocks) (peer neighbor : Fin g.degree)
    (first old : Fin g.cap) (target : Bool) (z : Ticket.SocketSeat g.blocks g.cap)

/-- The three sampled table entries are addressed by the earlier cable, its signed
stay/neighbor choice, and its matched donor respectively. -/
structure OldSocketRows : Prop where
  signed : let i:=finProdFinEquiv (root,finProdFinEquiv (x,finProdFinEquiv (peer,first)))
    (v.old j 3 i h y).val=old.val+1 ∧ (v.old j 2 i h y).val=target.toNat ∧
    (target=true → (v.old j 1 i h y).val=neighbor.val+1)
  path : (v.path (finProdFinEquiv (root,if target then neighbor.castSucc else Fin.last g.degree)) h y).val=p.val+1
  anchor : let a:=finProdFinEquiv (p,finProdFinEquiv (x,finProdFinEquiv (old,(if target then 1 else 0 : Fin 3))))
    (v.anchor j 4 a h y).val=Ticket.anchor false z 4

/-- The native output includes all eight raw cable fields of the selected socket. -/
def SampledOldSocket (p : Fin g.paths) (x : Fin g.blocks) (old : Fin g.cap) (target : Bool)
    (z : Ticket.SocketSeat g.blocks g.cap) : Prop :=
  let a:=finProdFinEquiv (p,finProdFinEquiv (x,finProdFinEquiv (old,(if target then 1 else 0 : Fin 3))))
  let raw:=finProdFinEquiv (p,Ticket.seatNo z)
  (rawKey g v j h y).val=Ticket.socket p false z ∧
    (v.origin j 0 h y).val=1 ∧ (v.prior j 0 h y).val=1 ∧
    (anchorChoice g v j h y).val=a.val+1 ∧ (pathV g v j 0 h y).val=p.val+1 ∧
    ∀f,rawV g v j f h y=v.raw j f raw h y

theorem sampled_old_rows_socket (chunk : ℕ)
    (cause : (v.origin j 0 h y).val=1) (walk : (v.origin j 1 h y).val=root.val)
    (block : (v.origin j 2 h y).val=x.val)
    (header : ∀f,(v.prior j f h y).val=(DescentOperandStateBanks.Pointer.cable peer.val first.val chunk).header f)
    (rows : OldSocketRows g v j h y root p x peer neighbor first old target z) :
    SampledOldSocket g v j h y p x old target z :=by
  have kind : (v.prior j 0 h y).val=1:=header 0
  have read:=oldV_from_header g v j h y root x peer first cause kind walk block (header 1) (header 2)
  obtain ⟨s,polarity,next⟩:=rows.signed
  have slot : (oldV g v j 3 h y).val=old.val+1:=(congrArg Fin.val (read 3)).trans s
  have side : (oldV g v j 2 h y).val=target.toNat:=(congrArg Fin.val (read 2)).trans polarity
  have choice:=path_choice_previous g v j h y root neighbor target cause walk (by omega)
    (fun ht=>(congrArg Fin.val (read 1)).trans (next ht)) side
  have path := (congrArg Fin.val (pathV_at g v j h y _ choice)).trans rows.path
  have chosen:=anchor_choice_old g v j h y p x old target cause kind path block slot side
  have head:=(congrArg Fin.val (anchorV_at g v j h y _ chosen 4)).trans rows.anchor
  have address:=rawKey_at_socket g v j h y rfl rfl p false z cause path head (by simp)
  exact ⟨address,cause,kind,chosen,path,fun f=>rawV_at g v j h y _
    (address.trans (Ticket.socket_at p false z)) f⟩

/-- A dense W ordinal selects the unique first raw path to its donor in the
physical inverse table, including when several walks reach the same donor. -/
theorem sampled_old_sorted_rows_socket {H : ℕ} (reach : Fin H→Fin g.paths→Option (Fin H))
    (recv actor : Fin H) (ordinal : Fin g.paths) (table : Fin g.paths→Values g g.digitBits)
    (chunk : ℕ) (cause : (v.origin j 0 h y).val=1) (stamped : (v.origin j 1 h y).val=ordinal.val)
    (sorted : DescentSortedRoster.indexed reach recv ordinal=some actor)
    (visited : Gather.select reach recv root=some actor)
    (inverse : (table ordinal h y).val=Sorted.rawAtOrdinal reach recv ordinal)
    (block : (v.origin j 2 h y).val=x.val)
    (header : ∀f,(v.prior j f h y).val=(DescentOperandStateBanks.Pointer.cable peer.val first.val chunk).header f)
    (rows : OldSocketRows g v j h y root p x peer neighbor first old target z) :
    SampledOldSocket g (SortedInput.values g v table) j h y p x old target z :=by
  let normalized:=SortedInput.values g v table
  have selected:=SortedInput.selected_at g v table j h y ordinal (Or.inl cause) stamped
  have path : (normalized.origin j 1 h y).val=root.val:=(congrArg Fin.val selected).trans
    (inverse.trans (Sorted.raw_eq reach recv actor ordinal root sorted visited))
  exact sampled_old_rows_socket g normalized j h y root p x peer neighbor first old target z chunk cause path block
    header ⟨rows.signed,rows.path,rows.anchor⟩

end
end Hierarchy.DescentDatedOperandReadPipeline

end OAI
