import OAI.Hierarchy.DescentResetPeerMeasured
import OAI.Hierarchy.DescentResetPeerOldBanks
import OAI.Hierarchy.DescentContactPreROMRead

namespace OAI
/-! # The actual operand expressions and packed sheets consumed by the reset's peer scanner -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentCompiler DescentColonies DescentDenseHostOrder DescentResetPeerUnionRAM
open DescentPackedColony DescentSIMDLookup ProtocolRAM
open ThreeFlat.RAM PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail wire hist : ℕ}
  {input : Reached W G q ε S k i z D wire hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset input ctl)
set_option quotPrecheck false
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "height" => GroupStage.depthBound D n f g
local notation "r" => (Z).k-(T).commonDepth
local notation "shelf" => (DescentDenseHostOrder.roster (Z).graph r height).card
local notation "J" => 2^(T).commonDepth
local notation "D₀" => input.placement.degree
local notation "K" => 2*DescentFallbackShapeTable.rows r (2^(Z).n)
local notation "capacity" => max (Fintype.card (DescentCommonPalette.rotor (Z).graph).Edge) (2^(height+1))
local notation "Family" => Axes.Fields (stemsCount B) (contactCount B) (privateCount B)

def peerLayout (base H M field keyBits bits : ℕ) : RawTables.Layout :=
  ⟨base,H,shelf,D₀,J,M,capacity,field,keyBits,bits⟩
def peerTemplate (s : Bool) (j : Fin K) := DescentResetStemDecoder.localTemplate (Z).graph r height s j.val

/-- One bank for each already-issued signed key and one original five-field menu for each possible private root. -/
structure PeerInputs where
  keys : Fin (stemsCount B)→Bank
  privatePages : Bool→(Z).RootTicket T→Bank
  actorStarts : Bank
  actorData : Bank
  oldPorts : Bank

variable (base H M field keyBits bits contactBits contactStart : ℕ)
local notation "L" => peerLayout B base H M field keyBits bits
local notation "tpl" => peerTemplate B
local notation "pitch" => H*shelf
local notation "contactDate" => contactLayout B contactStart H M contactBits bits
local notation "boot" => RawTables.image (Z).graph r height L tpl
variable (old : PeerInputs B)

def peerTerms : Family (Fin (chunks J M)→Expr) where
  stem j c:=RawTables.stemOperand L ((stemAxis B).symm j).1 (PrivateEvidence.atOld base H shelf (old.keys j) c.val)
  trunk c:=DescentResetTrunkChip.dataExpr (Z).graph r height (L).trunk H M
    (RawTables.actorOperand old.actorStarts old.actorData c.val)
  contact:=issuedContactExpr B contactStart H M contactBits bits
  privateEdge j c:=
    if live : ∃p,privateProbeId B p=j then
      let p:=live.choose
      PrivateEvidence.operand base H shelf capacity field M (old.privatePages p.1 p.2.1) p.2.2 c.val
    else .lit 0

structure PriorPeerWords where
  keys : Fin (stemsCount B)→Fin H→Fin J→Cell keyBits
  actors : Fin pitch→Fin J→Cell 1
  privatePages : Bool→(Z).RootTicket T→Fin H→Fin J→Cell (field*(capacity*5))

variable (prior : PriorPeerWords B H field keyBits)
def peerWords (contact : Fin (contactCount B)→Fin (stemsCount B)→Fin pitch→Fin J→Cell bits) :
    Family (Fin pitch→Fin J→Cell bits) where
  stem j v g₀:=
    let p : Fin H×Fin shelf:=finProdFinEquiv.symm v
    DescentResetStemPeerChip.bits (tpl ((stemAxis B).symm j).1) D₀ p.2 (prior.keys j p.1 g₀)
  trunk v g₀:=DescentResetTrunkChip.bits (Z).graph r height D₀
    ((finProdFinEquiv.symm v : Fin H×Fin shelf).2) (prior.actors v g₀)
  contact:=contact
  privateEdge j v g₀:=
    if live : ∃p,privateProbeId B p=j then
      let p:=live.choose
      let x : Fin H×Fin shelf:=finProdFinEquiv.symm v
      PrivateEvidence.word D₀ shelf field capacity bits x.2 p.2.2 (prior.privatePages p.1 p.2.1 x.1 g₀)
    else 0

variable {w : ℕ}
structure OldPeerReads (m : Memory w) : Prop where
  keysFit : ∀j,(old.keys j).Fits w base
  keysSize : ∀j,H*chunks J M ≤ (old.keys j).size
  keyWords : ∀j,Reads (old.keys j) (prior.keys j) M m
  privateFit : ∀s t,(old.privatePages s t).Fits w base
  privateSize : ∀s t,H*chunks J M ≤ (old.privatePages s t).size
  privateWords : ∀s t,Reads (old.privatePages s t) (prior.privatePages s t) M m
  actorStarts : old.actorStarts.Fits w base
  actorData : old.actorData.Fits w base
  actorSize : pitch ≤ old.actorStarts.size
  actors : ∃rowAt : Fin pitch→ℕ,
    (∀v,rowAt v+chunks J M ≤ old.actorData.size) ∧ (∀v,m (old.actorStarts.base+v.val)=(rowAt v:Word w)) ∧
    ∀v (c : Fin (chunks J M)),m (old.actorData.base+(rowAt v+c.val))=((data (M:=M) prior.actors (v,c)).val:Word w)

local notation "terms" => peerTerms B base H M field keyBits bits contactBits contactStart old
local notation "values" arm:arg => peerWords B H field keyBits bits prior arm

/-- The second CPU has only added the true contact output and preserved the original tables. -/
theorem measured_operands (m out : Memory w) (read : OldPeerReads B base H M field keyBits old prior m)
    (dated : (L).endAddress ≤ contactStart) (space : (contactDate).endAddress < 2^w)
    (frame : ∀a,a < (L).endAddress → out a=boot m a)
    (contact : Fin (contactCount B)→Fin (stemsCount B)→Fin pitch→Fin J→Cell bits)
    (contactRead : ∀j donor c (v : Fin pitch),((terms).contact j donor c).eval out (v.val:Word w)=
      ((data (M:=M) (contact j donor) (v,c)).val:Word w)) :
    ∀e,(∀c,((terms).all e c).Fits w (contactDate).endAddress) ∧
      RawTables.ReadsAt L ((values contact).all e) ((terms).all e) out := by
  have order:=(contactDate).ordered
  have below : (L).endAddress ≤ (contactDate).endAddress :=
    dated.trans (order.1.trans (order.2.1.trans (order.2.2.1.trans (order.2.2.2.1.trans order.2.2.2.2))))
  have safe:=(below.trans_lt space)
  have preserve (x : Fin (chunks J M)→Expr) (v : Fin pitch→Fin J→Cell bits)
      (pair : (∀c,(x c).Fits w (L).endAddress) ∧ RawTables.ReadsAt L v x (boot m)) :
      (∀c,(x c).Fits w (contactDate).endAddress) ∧ RawTables.ReadsAt L v x out :=
    ⟨fun c=>ProtocolRAMGeneratedWrite.fits_mono _ below (pair.1 c),
      RawTables.reads_before L v x pair.1 frame pair.2⟩
  apply Axes.tabulate (terms) (values contact) (fun x v=>
    (∀c,(x c).Fits w (contactDate).endAddress) ∧ RawTables.ReadsAt L v x out)
  · intro e
    obtain ⟨low,source⟩:=RawTables.original_key L m safe (old.keys e) (prior.keys e) (read.keyWords e)
      (read.keysFit e) (read.keysSize e)
    exact preserve _ _ (RawTables.stem_after_private (Z).graph r height L tpl m safe ((stemAxis B).symm e).1 _ _ source low)
  · obtain ⟨rowAt,rowSize,roots,rows⟩:=read.actors
    obtain ⟨lower,source⟩:=RawTables.actor_read L m base old.actorStarts old.actorData rowAt prior.actors
      read.actorStarts read.actorData read.actorSize rowSize roots rows
    exact preserve _ _ (RawTables.trunk_reads (Z).graph r height L tpl m safe rfl _ prior.actors source lower)
  · intro j donor
    have small : (contactDate).markerBase < 2^w := (order.2.2.2.1.trans order.2.2.2.2).trans_lt space
    let tb:=DescentContactProbePitch.table H shelf J M contactBits (contactDate).pitchBase 4
    have tb₀ : tb.Fits w (contactDate).markerBase := DescentContactProbePitch.table_fits _ _ _ _ _ _ small 4
    have tb' : tb.Fits w (contactDate).endAddress :=
      ⟨tb₀.1,tb₀.2.1,tb₀.2.2.trans (order.2.2.2.1.trans order.2.2.2.2)⟩
    exact ⟨fun c=>DescentContactProbePitch.atChunk_fits _ _ _ tb' (.lookup ((contactDate).output ((contactDate).index j donor).val) .row)
      ⟨(contactDate).output_fits ((contactDate).index j donor) space,trivial⟩ c,
      contactRead j donor⟩
  · intro j
    by_cases live : ∃p,privateProbeId B p=j
    · let p:=live.choose
      have got:=RawTables.private_reads (Z).graph r height L tpl m safe (old.privatePages p.1 p.2.1)
        (prior.privatePages p.1 p.2.1) (read.privateFit p.1 p.2.1) (read.privateSize p.1 p.2.1) (read.privateWords p.1 p.2.1) p.2.2
      simp only [peerTerms,peerWords,dite_eq_left live]
      exact preserve _ _ got
    · refine ⟨fun c=>by simp only [peerTerms,dite_eq_right live,Expr.Fits],?_⟩
      intro c v
      simp only [peerTerms,peerWords,dite_eq_right live,Expr.eval]
      have zero : (data (M:=M) (fun (_ : Fin pitch) (_ : Fin J)=>(0:Cell bits)) (v,c)).val=0 := by
        change (finFunctionFinEquiv (fun j:Fin M=>if _ : c.val*M+j.val < J then (0:Cell bits) else 0)).val=0
        simp
      exact congrArg (fun n : ℕ => (n : Word w)) zero.symm

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
