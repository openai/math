import OAI.Hierarchy.DescentResetReceiverRead
import OAI.Hierarchy.DescentResetPrefixRoom

namespace OAI
/-! # The original packed signed-arrival sheet seen by the paid reset census -/
namespace Hierarchy.DescentFallbackPeriod.Projected
open DescentGLPacked DescentGLPacked.BankImage DescentGLPacked.BankImage.SignedFields DescentGL
open DescentSIMDLookup DescentPackedZip DescentSixParty DescentGroupPeerOrder DescentStageEdgeReceipt
open DescentSharedCableNames.Stage DescentIssuedFallbackPanel DescentColonies DescentPacking.PackedMatch.Local
open DescentSixParty.Chronology DescentSixParty.Chronology.Shelf ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
set_option hygiene false
variable {F P J V : Type} [Field F] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
    {d k i w n h l c H G K R M Ht t field : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
    {gate : PoweredGadget F} {q ε : ℝ} (A : GroupStage W gate q ε J V k)
    (native : W.graph.Edge↪ℕ) (S : DescentCompiler.AtomSchedule) (ready : A.StateBounds S i)
    (groups : J≃Fin G) (host : V↪Fin H)
local notation "L" => 2^(h+l-c)
local notation "D" => 2*A.cap
local notation "degree" => A.degree
local notation "sigBits" => DescentSignedCableCodec.width A.degree A.cap
local notation "N" => 2^k
variable (a : Receiver A.degree A.cap (2^k) n (h+l-c) c H G K R M h l t field Ht w)
local notation "outputs" => bankAt a.stencil a.tapped t degree a.signedEnd H (2^c) M


/-- Read the real GL output before clipping to individual slots. All incident
port selectors share the same old-grain basis as the mounted reset window. -/
theorem funded_taps (space : a.PrefixFits) (μ : Layout (h+l)) (size : 2^(h+l)=G*N)
    (width : 2^l=M*N) (cut : c≤h+l) (pack : M*L=2^l) (before out : Memory w)
    (stable : ∀i,i<a.projectionEnd→ out i=a.prefixImage space before i)
    (original : ∀j x,DescentPackedColony.Reads (a.old j x) (fun v g=>DescentSignedCableCodec.encode
      (Stage.Prepare.signed A native S ready groups.toEmbedding host x j v g)) (R*M) before)
    (early : a.saved.Fits w a.origin) (key : before a.saved.base=((DescentExterior.matrixCode μ).val:Word w)) :
    ∀j,Source (.lookup (a.tapped j) .row) (fun v hi=>encode sigBits L
      (fun lo=>oldWord A native S ready groups host size j v ((rearrange μ).symm (join cut hi lo)))) M out :=by
  let val (j : Fin D) (x : Fin N) (v : Fin H) (g : Fin G):=DescentSignedCableCodec.encode
    (Stage.Prepare.signed A native S ready groups.toEmbedding host x j v g)
  let flat (j : Fin (D*N)) :=let p:=finProdFinEquiv.symm j;val p.1 p.2
  obtain ⟨mid,ret,_,read,initial⟩:=Retile.issued a.origin a.slots a.ratio a.positive (incoming a.old) flat before
    (fun _=>space.inputs _ _) (fun _=>space.inputSize _ _) (fun _=>original _ _) space.retileRoom
  have literal:=Retile.runs (a:=sigBits) a.origin a.slots a.ratio a.positive (incoming a.old)
    (fun _=>space.inputs _ _) (fun _=>space.inputSize _ _) space.retileRoom before
  have eqn : a.retileImage before=mid:=exec_unique _ before _ _ literal.1 ret
  have srcFit (j : Fin D) (x : Fin N) : (.lookup (a.tiles j x) .row:Expr).Fits w a.retileEnd :=
    ⟨(Retile.fits_output a.origin (finProdFinEquiv (j,x)) space.retileRoom).1,trivial⟩
  have srcRead (j : Fin D) (x : Fin N) : Source (.lookup (a.tiles j x) .row) (val j x) M mid :=by
    have fits:=Retile.fits_output a.origin (finProdFinEquiv (j,x)) space.retileRoom
    apply source_column (a.tiles j x) a.retileEnd fits.1 mid _ fits.2
    simpa only [flat,Receiver.tiles,Equiv.symm_apply_apply] using read (finProdFinEquiv (j,x))
  have oldLow : a.saved.base<a.origin:=by
    have posKey:=space.key.1
    exact (Nat.lt_add_of_pos_right posKey).trans_le early.2.2
  have beforeKey:= (initial _ (.inl oldLow)).trans key
  obtain ⟨end_,run,_,dense,_⟩:=SignedFields.from_slots a.retileEnd a.saved (fun j x=>.lookup (a.tiles j x) .row)
    μ size width a.positive (Nat.two_pow_pos _) (fun j v g x=>val j x v g) mid srcFit srcRead space.key beforeKey space.signedRoom
  have exec:=SignedFields.from_slots_any (b:=sigBits) (M:=M) (h:=h) (l:=l) (H:=H) a.retileEnd
    a.saved (fun j x=>Expr.lookup (a.tiles j x) .row) mid srcFit space.key space.signedRoom
  have hardware : a.chipImage mid=end_:=exec_unique _ mid _ _ exec.1 run
  have shield:=(issued_catalog (a.jobs space) a.signedEnd (stride (maxBits t degree A.cap L) H (2^c) M)
    (a.proj_layout space) (a.chipImage (a.retileImage before))).2.2.2
  have sz : 2^c*L=2^(h+l):=by rw [←pow_add,Nat.add_sub_of_le cut]
  have groups':=DescentSIMDLookup.chunks_group (2^c) M L a.positive (Nat.two_pow_pos _)
  rw [sz,pack,DescentGLPacked.chunk_count] at groups'
  intro j
  have room:=a.tapped_fits j space.signedRoom
  have span:H*chunks (2^c) M≤(a.tapped j).size:=by rw [←groups'];exact Nat.le_pow_clog (by decide) _
  apply source_column (a.tapped j) a.signedEnd room out _ span
  intro pos
  let addr:=(a.tapped j).base+(row H (2^c) M pos).val
  have bound:addr<a.signedEnd:=(Nat.add_lt_add_left ((row _ _ _ pos).isLt.trans_le span) _).trans_le room.2.2
  have beforeProj:a.signedEnd≤a.projectionEnd:=Nat.le_add_right ..
  have protected_:out addr=a.chipImage (a.retileImage before) addr:=
    (stable _ (bound.trans_le beforeProj)).trans (shield _ (.inl bound))
  change out addr=_
  rw [protected_,eqn,hardware]
  exact DescentPlainTerminal.Suffix.grouped_remix cut pack a.positive (a.tapped j).base
    (oldWord A native S ready groups host size j) μ end_ (dense j) pos

omit [Fintype V] [DecidableEq V] in
/-- The selected original stencil is already a whole array on all old hosts.
A preserved bound below the original receiver proves that the same paged
expression supplies the complete funded census panel at the later point. -/
theorem funded_panel {a₀ : ℕ} (base limit : ℕ) (slot : Bank) (earlier later : Memory w)
    (safe : slot.Fits w limit) (extent : H*chunks (2^c) M≤ slot.size) (sameBase : slot.base=base)
    (saved : ∀i,i<limit→later i=earlier i)
    (cells : V→Block c→Fin (2^a₀)→Cell t)
    (stored : ∃u : Fin H→Block c→Fin (2^a₀)→Cell t,
      (∀pos : Row H (2^c) M,earlier (base+(row _ _ _ pos).val)=((data (fun v hi=>encode t _ (u v hi)) pos).val:Word w)) ∧
      ∀v hi l,u (host v) hi l=cells v hi l) :
    ∃panel : Fin H→Block c→Cell (t*2^a₀),Source (.lookup slot .row) panel M later ∧
      ∀v hi,panel (host v) hi=encode t _ (cells v hi) :=by
  obtain ⟨u,at_,origin⟩:=stored
  refine ⟨fun v hi=>encode t _ (u v hi),source_column slot limit safe later _ extent ?_,?_⟩
  · intro pos
    have index:=(row H (2^c) M pos).isLt.trans_le extent
    apply (saved _ ((Nat.add_lt_add_left index _).trans_le safe.2.2)).trans
    rw [sameBase]
    exact at_ pos
  · intro v hi
    exact congrArg (encode t _) (funext (origin v hi))

end
end Hierarchy.DescentFallbackPeriod.Projected

end OAI
