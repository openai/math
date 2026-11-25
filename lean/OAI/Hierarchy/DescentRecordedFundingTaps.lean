import OAI.Hierarchy.DescentPhysicalFundedProjection
import OAI.Hierarchy.DescentDatedStageVenue
import OAI.Hierarchy.DescentFundedPreviousBank
import OAI.Hierarchy.DescentResetDigits
import OAI.Hierarchy.DescentClosedReset

namespace OAI
/-! # Original remixed signed ports in the actual paid reset census -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentCompiler DescentColonies DescentGL DescentGLPacked.BankImage.SignedFields DescentFallbackPeriod.Projected
open DescentGroupPeerOrder DescentStageEdgeReceipt DescentSharedCableNames DescentPacking.PackedMatch.Local
open DescentIssuedFallbackPanel DescentSixParty.Chronology DescentSixParty.Chronology.Shelf
open DescentFundedCensus DescentSIMDLookup DescentPackedZip Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open scoped Fin.CommRing Classical
noncomputable section
set_option quotPrecheck false
set_option hygiene false
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F}
    {q ε : ℝ} {S : AtomSchedule} {k age z D n h C f g cut tail wire hist : ℕ}
    {ctl : ResetRates G S k D n h C f g cut tail} {prior : Reached W G q ε S k age z D wire hist}
    (B : ClosedReset prior ctl) {H : ℕ} (pad : Fintype.card prior.V≤H)
local notation "A" => prior.placement
local notation "dim" => S.groupWidth k tail age+k
local notation "cc" => B.terminals.commonDepth
local notation "L" => 2^(dim-cc)
local notation "gg" => S.groupCount age
local notation "host" => prior.vertex.trans (Fin.castLEEmb pad)
local notation "names" => DescentPacking.PackedMatch.Local.Stage.cableNames k (groupRank ((Function.Embedding.refl (Fin gg)).trans Fin.valEmbedding) ((host).trans Fin.valEmbedding))
local notation "native" => prior.order.trans Fin.valEmbedding
local notation "basis" => B.frame.basis
local notation "enough" => B.frame.enough.trans (Nat.sub_le ..)
local notation "digits" => S.resetInputDigits ctl.base ctl.radix age
local notation "index₀" hi:arg lo:arg => digits ((rearrange basis).symm (join enough hi lo))
local notation "sig" => DescentSignedCableCodec.width (A).degree (A).cap

/-- The raw issued signed word before any counted-arrival test. -/
def fundingSign (j : Fin (2*(A).cap)) (v : Fin H) (hi : Block cc) (lo : Fin L) : Cell sig:=
  let x:=index₀ hi lo
  DescentSignedCableCodec.encode (Stage.Prepare.signed A native S prior.valid (Function.Embedding.refl _) host x.2 j v x.1)

theorem funding_sign_at (j : Fin (2*(A).cap)) (v : prior.V) (hi : Block cc) (lo : Fin L) :
    fundingSign B pad j (host v) hi lo=DescentSignedCableCodec.encode
      (Stage.signedPanel A native S prior.valid names (((index₀ hi lo).1,v),(index₀ hi lo).2) j):=by
  have size : 2^dim=gg*2^k:=by rw [pow_add,S.group_power ctl.base ctl.radix]
  exact oldWord_at (h:=S.groupWidth k tail age) (l:=k) A native S prior.valid (Equiv.refl _) host
    size j v ((rearrange basis).symm (join enough hi lo))

private theorem layout_index {a b c groups blocks : ℕ} (time:a=b) (μ : Layout a) (ν : Layout b)
    (physical : HEq μ ν) (first:c≤a) (last:c≤b) (s : 2^a=groups*blocks) (t : 2^b=groups*blocks)
    (hi : Block c) (lo : Fin (2^(a-c))) :
    (finProdFinEquiv.symm (Fin.cast s ((rearrange μ).symm (join first hi lo))) : Fin groups×Fin blocks)=
      finProdFinEquiv.symm (Fin.cast t ((rearrange ν).symm (join last hi (lo.cast (by rw [time]))))):=by
  subst b
  cases eq_of_heq physical
  rfl

/-- A true predecessor bank remains readable through the chosen stencil. The
shared physical row bound also covers the last partly occupied packed word. -/
theorem funding_old_wire {M paid w start : ℕ} (io : Stage.Dated.Operands)
    (peer : Fin H→Fin D→Option (Fin H)) (old now : Memory w)
    (held : stageVenue prior pad io M paid start peer old)
    (wire : ∀(x:Block k)(j:Fin (2*(A).cap)),(io.wire x.val j.val).Fits w start ∧
      H*chunks gg M≤(io.wire x.val j.val).size) (keep : ∀a,a<start→now a=old a) :
    ∀(j:Fin (2*(A).cap))(x:Block k),DescentPackedColony.Reads (io.wire x.val j.val) (fun h g=>DescentSignedCableCodec.encode
      (Stage.Prepare.signed A native S prior.valid (Function.Embedding.refl _) host x j h g)) M now:=by
  intro j x pos
  let cell:=row H gg M pos
  have fit:=wire x j
  have small:cell.val<(io.wire x.val j.val).size:=cell.isLt.trans_le fit.2
  exact (keep _ ((Nat.add_lt_add_left small _).trans_le fit.1.2.2)).trans (held.2.2.2.1 x j pos)

/-- Calibrate the physical GL receiver against the real old stage. Only the
old signed banks and the genuine stored basis are read. -/
theorem funding_tap_rows {degree cap blocks depth cc' H' G' K R M high low t field Ht w n' : ℕ}
    (a : Receiver degree cap blocks n' depth cc' H' G' K R M high low t field Ht w)
    (deg : degree=(A).degree) (cp : cap=(A).cap) (xx : blocks=2^k) (hs : H'=H) (groups : G'=gg)
    (split : cc'=cc) (depthAt : depth=high+low-cc') (time : high+low=dim)
    (space : a.PrefixFits) (μ : Layout (high+low)) (chosen : HEq μ basis)
    (pitch : 2^low=M*2^k) (pack : M*2^(high+low-cc')=2^low)
    (io : Stage.Dated.Operands) (earlier result : Memory w)
    (saved : earlier a.saved.base=((DescentExterior.matrixCode μ).val:Word w)) (keyFits : a.saved.Fits w a.origin)
    (stayed : ∀i,i<a.projectionEnd→ result i=a.prefixImage space earlier i)
    (old : ∀(j : Fin (2*cap)) (x : Fin blocks),a.old j x=io.wire x.val j.val)
    (read : ∀(j:Fin (2*(A).cap))(x:Block k),DescentPackedColony.Reads (io.wire x.val j.val) (fun v group=>DescentSignedCableCodec.encode
      (Stage.Prepare.signed A native S prior.valid (Function.Embedding.refl _) host x j v group)) (R*M) earlier) :
    ∀j:Fin (2*(A).cap),Source (.lookup (a.tapped (j.cast (congrArg (2*·) cp.symm))) .row)
      (fun v hi=>encode sig (2^(high+low-cc)) (fun l=>fundingSign B pad j v hi (l.cast (by rw [time])))) M result:=by
  subst degree;subst cap;subst blocks;subst H';subst G';subst cc';subst depth
  have size : 2^(high+low)=gg*2^k:=by rw [time,pow_add,S.group_power ctl.base ctl.radix]
  have short:cc≤high+low:=by rw [time];exact enough
  have rows:=funded_taps A native S prior.valid (Equiv.refl _) host a space μ size pitch short pack earlier result stayed
    (by intro j x;rw [old];exact read j x) keyFits saved
  have eqn j v hi l : oldWord A native S prior.valid (Equiv.refl _) host size j v ((rearrange μ).symm (join short hi l))=
      fundingSign B pad j v hi (l.cast (by rw [time])):=by
    let get:=fun x:Fin gg×Block k=>DescentSignedCableCodec.encode
      (Stage.Prepare.signed A native S prior.valid (Function.Embedding.refl _) host x.2 j v x.1)
    have origSize:2^dim=gg*2^k:=by rw [pow_add,S.group_power ctl.base ctl.radix]
    exact congrArg get (layout_index time μ basis chosen short enough size origSize hi l)
  intro j
  have got := rows j
  simp only [eqn] at got
  simpa only [Fin.cast_refl,id_eq] using got

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
