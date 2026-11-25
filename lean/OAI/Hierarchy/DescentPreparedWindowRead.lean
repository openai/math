import OAI.Hierarchy.DescentResetReceiverRead
import OAI.Hierarchy.DescentPreparedPrivateRoots

namespace OAI
/-! # Physical window and private-root reads in the unique output of the public reset CPU -/
namespace Hierarchy.DescentFallbackPeriod.Projected
open DescentGLPacked DescentGLPacked.BankImage DescentGLPacked.BankImage.SignedFields
open DescentSIMDLookup DescentPackedZip DescentGL DescentGLNielsen DescentColonies DescentIssuedFallbackPanel
open DescentPackedColony DescentPacking.PackedMatch.Local DescentSixParty DescentSharedCableNames.Stage
open DescentSixParty.Chronology DescentSixParty.Chronology.Shelf
open DescentGroupPeerOrder DescentStageEdgeReceipt ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {F P J V : Type} [Field F] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
    {d k i w n h l c H G K R M Ht t field : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
    {gate : PoweredGadget F} {q ε : ℝ} (A : GroupStage W gate q ε J V k)
    (native : W.graph.Edge↪ℕ) (S : DescentCompiler.AtomSchedule) (ready : A.StateBounds S i)
    (groups : J≃Fin G) (host : V↪Fin H)
local notation "L" => 2^(h+l-c)
local notation "D" => 2*A.cap
local notation "degree" => A.degree
local notation "b" => DescentSignedCableCodec.width A.degree A.cap
local notation "N" => 2^k
variable (a : Receiver A.degree A.cap (2^k) n (h+l-c) c H G K R M h l t field Ht w)
local notation "outputs" => bankAt a.stencil a.tapped t degree a.signedEnd H (2^c) M

theorem prepared_window_read (book : RootBook n (h+l-c) degree L A.cap field) (space : a.PreparedFits book)
    (μ : DescentGL.Layout (h+l)) (size : 2^(h+l)=G*N) (width : 2^l=M*N)
    (small : c≤h+l) (repack : M*L=2^l) (mem : Memory w)
    (sources : ∀j x,Reads (a.old j x) (fun v g=>DescentSignedCableCodec.encode
      (Stage.Prepare.signed A native S ready groups.toEmbedding host x j v g)) (R*M) mem)
    (saved : mem a.saved.base=((DescentExterior.matrixCode μ).val:Word w))
    (beforeKey : a.saved.Fits w a.origin) (shape : a.stencil.Fits w a.origin)
    (sizeOfShape : H*chunks (2^c) M≤a.stencil.size)
    (code : V→Block c→Fin L→Cell t)
    (stencil : PackedFlow.Padded.Published (h:=h) (l:=l) M t a.stencil.base host code mem) :
    ∃(values : Fin H→Block c→Fin L→Cell t) (ports : Fin H→Block c→Fin L→Fin D→Option (Live degree A.cap)),
      (∀x,Reads (outputs (.inl (0,x))) (fun v hi=>((values v hi x).val:Cell field)) M (a.preparedImage book space mem)) ∧
      (∀x,Reads (outputs (.inl (1,x))) (fun v hi=>((values v hi x).val+1:Cell field)) M (a.preparedImage book space mem)) ∧
      (∀j x,Reads (outputs (.inr (j,x))) (fun v hi=>((DescentSignedCableCodec.encode (ports v hi x j)).val:Cell field)) M (a.preparedImage book space mem)) ∧
      (∀v hi x,values (host v) hi x=code v hi x) ∧
      ∀v hi x j,ports (host v) hi x j=signedPanel A native S ready
        (DescentPacking.PackedMatch.Local.Stage.cableNames k (groupRank (groups.toEmbedding.trans Fin.valEmbedding) (host.trans Fin.valEmbedding)))
        (donor (PackedFlow.digits groups size) μ small v hi x) j := by
  exact window_frame A native S ready groups host a space.toPrefixFits μ size width small repack mem _
    (a.prepared_window book space mem) sources saved beforeKey shape sizeOfShape code stencil

theorem prepared_mid_window_read_rows (book : RootBook n (h+l-c) degree L A.cap field) (space : a.PreparedFits book)
    (μ : DescentGL.Layout (h+l)) (size : 2^(h+l)=G*N) (width : 2^l=M*N)
    (small : c≤h+l) (repack : M*L=2^l) (mem : Memory w)
    (sources : ∀j x,Reads (a.old j x) (fun v g=>DescentSignedCableCodec.encode
      (Stage.Prepare.signed A native S ready groups.toEmbedding host x j v g)) (R*M) mem)
    (saved : mem a.saved.base=((DescentExterior.matrixCode μ).val:Word w))
    (beforeKey : a.saved.Fits w a.origin) (shape : a.stencil.base+H*chunks (2^c) M≤a.origin)
    (sizeOfShape : H*chunks (2^c) M≤a.stencil.size)
    (code : V→Block c→Fin L→Cell t)
    (stencil : PackedFlow.Padded.Published (h:=h) (l:=l) M t a.stencil.base host code mem) :
    ∃(values : Fin H→Block c→Fin L→Cell t) (ports : Fin H→Block c→Fin L→Fin D→Option (Live degree A.cap)),
      (∀x,Reads (outputs (.inl (0,x))) (fun v hi=>((values v hi x).val:Cell field)) M (a.preparedMid book space mem)) ∧
      (∀x,Reads (outputs (.inl (1,x))) (fun v hi=>((values v hi x).val+1:Cell field)) M (a.preparedMid book space mem)) ∧
      (∀j x,Reads (outputs (.inr (j,x))) (fun v hi=>((DescentSignedCableCodec.encode (ports v hi x j)).val:Cell field)) M (a.preparedMid book space mem)) ∧
      (∀v hi x,values (host v) hi x=code v hi x) ∧
      ∀v hi x j,ports (host v) hi x j=signedPanel A native S ready
        (DescentPacking.PackedMatch.Local.Stage.cableNames k (groupRank (groups.toEmbedding.trans Fin.valEmbedding) (host.trans Fin.valEmbedding)))
        (donor (PackedFlow.digits groups size) μ small v hi x) j := by
  exact window_frame_rows A native S ready groups host a space.toPrefixFits μ size width small repack mem _
    (a.prepared_mid_window book space mem) sources saved beforeKey shape sizeOfShape code stencil

theorem prepared_mid_window_read (book : RootBook n (h+l-c) degree L A.cap field) (space : a.PreparedFits book)
    (μ : DescentGL.Layout (h+l)) (size : 2^(h+l)=G*N) (width : 2^l=M*N)
    (small : c≤h+l) (repack : M*L=2^l) (mem : Memory w)
    (sources : ∀j x,Reads (a.old j x) (fun v g=>DescentSignedCableCodec.encode
      (Stage.Prepare.signed A native S ready groups.toEmbedding host x j v g)) (R*M) mem)
    (saved : mem a.saved.base=((DescentExterior.matrixCode μ).val:Word w))
    (beforeKey : a.saved.Fits w a.origin) (shape : a.stencil.Fits w a.origin)
    (sizeOfShape : H*chunks (2^c) M≤a.stencil.size)
    (code : V→Block c→Fin L→Cell t)
    (stencil : PackedFlow.Padded.Published (h:=h) (l:=l) M t a.stencil.base host code mem) :
    ∃(values : Fin H→Block c→Fin L→Cell t) (ports : Fin H→Block c→Fin L→Fin D→Option (Live degree A.cap)),
      (∀x,Reads (outputs (.inl (0,x))) (fun v hi=>((values v hi x).val:Cell field)) M (a.preparedMid book space mem)) ∧
      (∀x,Reads (outputs (.inl (1,x))) (fun v hi=>((values v hi x).val+1:Cell field)) M (a.preparedMid book space mem)) ∧
      (∀j x,Reads (outputs (.inr (j,x))) (fun v hi=>((DescentSignedCableCodec.encode (ports v hi x j)).val:Cell field)) M (a.preparedMid book space mem)) ∧
      (∀v hi x,values (host v) hi x=code v hi x) ∧
      ∀v hi x j,ports (host v) hi x j=signedPanel A native S ready
        (DescentPacking.PackedMatch.Local.Stage.cableNames k (groupRank (groups.toEmbedding.trans Fin.valEmbedding) (host.trans Fin.valEmbedding)))
        (donor (PackedFlow.digits groups size) μ small v hi x) j := by
  exact prepared_mid_window_read_rows A native S ready groups host a book space μ size width small repack mem sources saved beforeKey
    ((Nat.add_le_add_left sizeOfShape _).trans shape.2.2) sizeOfShape code stencil

end
end Hierarchy.DescentFallbackPeriod.Projected

end OAI
