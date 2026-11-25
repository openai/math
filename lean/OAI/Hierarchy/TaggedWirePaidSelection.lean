import OAI.Hierarchy.TaggedWirePaidRead
import OAI.Hierarchy.ProtocolRAMCatalogueAlignment

namespace OAI
/-! # The actual native role on a positive final edge, by original chronological identity -/

noncomputable section
namespace Hierarchy.ProbeStage.CoreBoard.HistoryRoles.RoleProgram
open AdaptiveProbe ReportSockets WireTelescope ProtocolRAM Calendar ProtocolRAMEmit
open Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
variable {h W k attempts w depth M : ℕ} (S : PurchaseSampler) (L : Chart)
    (b : CatalogueRows.Board) (π : Equiv.Perm (Fin (2^h))) (marks : Marks h W k attempts) (unique : Exclusive marks)
    (order : Fin b.coreRows≃Edges S h (2^W) k) (acquired : Bought S π depth marks→Fin b.boughtRows)
    {rows : Fin b.rows→Row} {width : Fin b.rows→ℕ}
    (A : CatalogueRows.Alignment b S π depth marks M rows width (b.original S π depth marks order acquired))

def livePort (i : Fin b.rows) (hi : 0<width i) (right : Bool) : PaidPorts S h W k attempts :=
  paid S π depth marks unique (A.ident ⟨i,hi⟩,right)

theorem paid_selection (m : Memory w) (core bought : Bool→Socket) (room : b.rows<2^w)
    (coreAt : ∀i s,Resolved S L (core s) m (i.val:Word w) (.inl (paid S π depth marks unique (.inl (order i),s))))
    (boughtAt : ∀i s,Resolved S L (bought s) m ((acquired i).val:Word w) (.inl (paid S π depth marks unique (.inr i,s))))
    (i : Fin b.rows) (hi : 0<width i) (side : Bool) :
    Resolved S L (paidInputs b core bought side) m (i.val:Word w)
      (.inl (livePort S b π marks unique order acquired A i hi side)) := by
  let live : {j//0<width j}:=⟨i,hi⟩
  have addr:=A.original live
  change Resolved S L _ m _ (.inl (paid S π depth marks unique (A.ident live,side)))
  cases tag:A.ident live with
  | inl e=>
    have same : b.coreIndex (order.symm e)=i:=by simpa only [tag,CatalogueRows.Board.original,Sum.elim_inl] using addr
    rw [←same]
    apply paid_core S L b m core bought (order.symm e) side _ room
    simpa only [Equiv.apply_symm_apply] using coreAt (order.symm e) side
  | inr e=>
    have same : b.boughtIndex (acquired e)=i:=by simpa only [tag,CatalogueRows.Board.original,Sum.elim_inr] using addr
    rw [←same]
    exact paid_bought S L b m core bought (acquired e) side _ room (boughtAt e side)

end Hierarchy.ProbeStage.CoreBoard.HistoryRoles.RoleProgram

end
end OAI
