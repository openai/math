import OAI.Hierarchy.DescentResetReceiverCPU
import OAI.Hierarchy.DescentTerminalExecUnique

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
    {templates : RootTemplates n (h+l-c) A.degree (2^(h+l-c)) A.cap} (room : a.Fits templates)
local notation "outputs" => bankAt a.stencil a.tapped t degree a.signedEnd H (2^c) M

theorem window_frame_rows (space : a.PrefixFits) (μ : DescentGL.Layout (h+l)) (size : 2^(h+l)=G*N) (width : 2^l=M*N)
    (small : c≤h+l) (repack : M*L=2^l) (mem out : Memory w)
    (stable : ∀z,z<a.projectionEnd → out z=a.prefixImage space mem z)
    (sources : ∀j x,Reads (a.old j x) (fun v g=>DescentSignedCableCodec.encode
      (Stage.Prepare.signed A native S ready groups.toEmbedding host x j v g)) (R*M) mem)
    (saved : mem a.saved.base=((DescentExterior.matrixCode μ).val:Word w))
    (beforeKey : a.saved.Fits w a.origin) (shape : a.stencil.base+H*chunks (2^c) M≤a.origin)
    (sizeOfShape : H*chunks (2^c) M≤a.stencil.size)
    (code : V→Block c→Fin L→Cell t)
    (stencil : PackedFlow.Padded.Published (h:=h) (l:=l) M t a.stencil.base host code mem) :
    ∃(values : Fin H→Block c→Fin L→Cell t) (ports : Fin H→Block c→Fin L→Fin D→Option (Live degree A.cap)),
      (∀x,Reads (outputs (.inl (0,x))) (fun v hi=>((values v hi x).val:Cell field)) M out) ∧
      (∀x,Reads (outputs (.inl (1,x))) (fun v hi=>((values v hi x).val+1:Cell field)) M out) ∧
      (∀j x,Reads (outputs (.inr (j,x))) (fun v hi=>((DescentSignedCableCodec.encode (ports v hi x j)).val:Cell field)) M out) ∧
      (∀v hi x,values (host v) hi x=code v hi x) ∧
      ∀v hi x j,ports (host v) hi x j=signedPanel A native S ready
        (DescentPacking.PackedMatch.Local.Stage.cableNames k (groupRank (groups.toEmbedding.trans Fin.valEmbedding) (host.trans Fin.valEmbedding)))
        (donor (PackedFlow.digits groups size) μ small v hi x) j := by
  have safe (s : Column L A.cap) : (spec a.stencil a.tapped t degree s).Room
      (start a.signedEnd (maxBits t degree A.cap L) H (2^c) M ((column L A.cap) s).val) H (2^c) M field w := by
    simpa [Receiver.lookup,Receiver.atQuery] using space.projected ((column L A.cap) s)
  obtain ⟨dst,vals,ports,ran,_,own,tag,sign,chart,actual,_⟩:=after_retile_rows A native S ready groups host a.origin
    a.saved a.stencil a.old a.slots a.ratio μ size width a.positive small repack a.positive mem space.inputs
    space.inputSize sources beforeKey saved space.retileRoom space.signedRoom shape sizeOfShape code stencil safe
  have eqn : a.prefixImage space mem=dst:=
    exec_unique (a.prefix space) mem _ _ (a.prefix_run space mem) ran
  have accessible (s : Column L A.cap) (p : Row H (2^c) M) :
      (outputs s).base+(row H (2^c) M p).val<a.projectionEnd := by
    let j:=(column L A.cap) s
    let z:=start a.signedEnd (maxBits t degree A.cap L) H (2^c) M j.val
    have upto:=extent (H:=H) (G:=2^c) (M:=M) (spec a.stencil a.tapped t degree s) a.signedEnd (maxBits t degree A.cap L) j
      (word_bound a.stencil a.tapped s)
    have slots:=Nat.mul_le_mul_left (stride (maxBits t degree A.cap L) H (2^c) M) j.isLt
    change stride (maxBits t degree A.cap L) H (2^c) M * (j.val+1) ≤ _ at slots
    have rowCap:= (row H (2^c) M p).isLt
    change (spec a.stencil a.tapped t degree s).out z H (2^c) M+(row H (2^c) M p).val <
      a.signedEnd+stride (maxBits t degree A.cap L) H (2^c) M*count L A.cap
    change (spec a.stencil a.tapped t degree s).out z H (2^c) M+H*chunks (2^c) M≤_ at upto
    omega
  have unchanged (s : Column L A.cap) (p : Row H (2^c) M) :=
    (stable _ (accessible s p)).trans
      (congrFun eqn ((outputs s).base+(row H (2^c) M p).val))
  exact ⟨vals,ports,fun x p=>(unchanged _ p).trans (own x p),fun x p=>(unchanged _ p).trans (tag x p),
    fun j x p=>(unchanged _ p).trans (sign j x p),chart,actual⟩

theorem window_frame (space : a.PrefixFits) (μ : DescentGL.Layout (h+l)) (size : 2^(h+l)=G*N) (width : 2^l=M*N)
    (small : c≤h+l) (repack : M*L=2^l) (mem out : Memory w)
    (stable : ∀z,z<a.projectionEnd → out z=a.prefixImage space mem z)
    (sources : ∀j x,Reads (a.old j x) (fun v g=>DescentSignedCableCodec.encode
      (Stage.Prepare.signed A native S ready groups.toEmbedding host x j v g)) (R*M) mem)
    (saved : mem a.saved.base=((DescentExterior.matrixCode μ).val:Word w))
    (beforeKey : a.saved.Fits w a.origin) (shape : a.stencil.Fits w a.origin)
    (sizeOfShape : H*chunks (2^c) M≤a.stencil.size)
    (code : V→Block c→Fin L→Cell t)
    (stencil : PackedFlow.Padded.Published (h:=h) (l:=l) M t a.stencil.base host code mem) :
    ∃(values : Fin H→Block c→Fin L→Cell t) (ports : Fin H→Block c→Fin L→Fin D→Option (Live degree A.cap)),
      (∀x,Reads (outputs (.inl (0,x))) (fun v hi=>((values v hi x).val:Cell field)) M out) ∧
      (∀x,Reads (outputs (.inl (1,x))) (fun v hi=>((values v hi x).val+1:Cell field)) M out) ∧
      (∀j x,Reads (outputs (.inr (j,x))) (fun v hi=>((DescentSignedCableCodec.encode (ports v hi x j)).val:Cell field)) M out) ∧
      (∀v hi x,values (host v) hi x=code v hi x) ∧
      ∀v hi x j,ports (host v) hi x j=signedPanel A native S ready
        (DescentPacking.PackedMatch.Local.Stage.cableNames k (groupRank (groups.toEmbedding.trans Fin.valEmbedding) (host.trans Fin.valEmbedding)))
        (donor (PackedFlow.digits groups size) μ small v hi x) j := by
  exact window_frame_rows A native S ready groups host a space μ size width small repack mem out stable sources saved beforeKey
    ((Nat.add_le_add_left sizeOfShape _).trans shape.2.2) sizeOfShape code stencil

theorem window_read (μ : DescentGL.Layout (h+l)) (size : 2^(h+l)=G*N) (width : 2^l=M*N)
    (small : c≤h+l) (repack : M*L=2^l) (mem : Memory w)
    (sources : ∀j x,Reads (a.old j x) (fun v g=>DescentSignedCableCodec.encode
      (Stage.Prepare.signed A native S ready groups.toEmbedding host x j v g)) (R*M) mem)
    (saved : mem a.saved.base=((DescentExterior.matrixCode μ).val:Word w))
    (beforeKey : a.saved.Fits w a.origin) (shape : a.stencil.Fits w a.origin)
    (sizeOfShape : H*chunks (2^c) M≤a.stencil.size)
    (code : V→Block c→Fin L→Cell t)
    (stencil : PackedFlow.Padded.Published (h:=h) (l:=l) M t a.stencil.base host code mem) :
    ∃(values : Fin H→Block c→Fin L→Cell t) (ports : Fin H→Block c→Fin L→Fin D→Option (Live degree A.cap)),
      (∀x,Reads (outputs (.inl (0,x))) (fun v hi=>((values v hi x).val:Cell field)) M (a.image room mem)) ∧
      (∀x,Reads (outputs (.inl (1,x))) (fun v hi=>((values v hi x).val+1:Cell field)) M (a.image room mem)) ∧
      (∀j x,Reads (outputs (.inr (j,x))) (fun v hi=>((DescentSignedCableCodec.encode (ports v hi x j)).val:Cell field)) M (a.image room mem)) ∧
      (∀v hi x,values (host v) hi x=code v hi x) ∧
      ∀v hi x j,ports (host v) hi x j=signedPanel A native S ready
        (DescentPacking.PackedMatch.Local.Stage.cableNames k (groupRank (groups.toEmbedding.trans Fin.valEmbedding) (host.trans Fin.valEmbedding)))
        (donor (PackedFlow.digits groups size) μ small v hi x) j := by
  exact window_frame A native S ready groups host a room.toPrefixFits μ size width small repack mem _
    (a.kept_prefix room mem) sources saved beforeKey shape sizeOfShape code stencil

end
end Hierarchy.DescentFallbackPeriod.Projected

end OAI
