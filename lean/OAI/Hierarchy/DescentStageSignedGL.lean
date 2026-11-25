import OAI.Hierarchy.DescentSignedGLRun
import OAI.Hierarchy.DescentFallbackGLWindow

namespace OAI
/-! # The reset window reads the old graph's signed cables in the selected coordinates -/
namespace Hierarchy.DescentGLPacked.BankImage.SignedFields
open DescentSIMDLookup DescentPackedZip DescentColonies DescentGL DescentGLNielsen
open DescentPacking.PackedMatch.Local DescentSixParty DescentGroupPeerOrder DescentStageEdgeReceipt
open DescentGLPacked DescentIssuedFallbackPanel DescentSharedCableNames.Stage
open DescentPackedColony ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {F P J V : Type} [Field F] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
  {d k i h l H G c M lanes w : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {gate : PoweredGadget F} {q ε : ℝ} (A : GroupStage W gate q ε J V k)
  (native : W.graph.Edge↪ℕ) (S : DescentCompiler.AtomSchedule) (ready : A.StateBounds S i)
  (groups : J≃Fin G) (host : V↪Fin H)
local notation "rs" => groups.toEmbedding.trans Fin.valEmbedding
local notation "vs" => host.trans Fin.valEmbedding
local notation "sign" => signedPanel A native S ready (Stage.cableNames k (groupRank rs vs))
local notation "N" => 2^k
local notation "D" => 2*A.cap
local notation "b" => DescentSignedCableCodec.width A.degree A.cap

theorem stage_ports (base : ℕ) (saved : Bank) (old : Fin D→Fin N→Bank)
    (μ : DescentGL.Layout (h+l)) (size : 2^(h+l)=G*N) (width : 2^l=M*N)
    (pos : 0<M) (small : c≤h+l) (repack : lanes*2^(h+l-c)=2^l) (many : 0<lanes)
    (mem : Memory w) (safe : ∀j x,(old j x).Fits w base)
    (dataSize : ∀j x,H*chunks G M≤(old j x).size)
    (signed : ∀j x,DescentPackedColony.Reads (old j x) (fun v g=>DescentSignedCableCodec.encode
      (Stage.Prepare.signed A native S ready groups.toEmbedding host x j v g)) M mem)
    (keyFits : saved.Fits w base) (savedWord : mem saved.base=((DescentExterior.matrixCode μ).val:Word w))
    (room : stop (joinStop base b N M) D H h l b<2^w) :
    let first:=joinStop base b N M
    let C:=chart first D H h l b
    let key:=joinOp base b N M D (fun j x=>.lookup (old j x) .row)
    let pre:=Book.install (joinGate b N) (joinWidth b N) M w base
    let X:=oldWord A native S ready groups host size
    let real:=DescentSixParty.PackedFlow.digits groups size
    let n:=(schedule (h+l)).length
    ∃last,(pre.seq (program first C saved key D H h l b w)).Exec mem last
        ((4+10*(N*(2*2^(joinWidth b N*M))))+duration first C saved key D H h l b w) ∧
      CheapCode (pre.seq (program first C saved key D H h l b w)) ∧
      (∀j : Fin D,
        let bank:Bank:=⟨slice (((C.chosen (h+l)).bank n).base) H (2^h) j,Nat.clog 2 (H*2^h)⟩
        let word:=fun v hi lo=>X j v ((rearrange μ).symm (join small hi lo))
        DescentPackedColony.Reads bank (fun v hi=>encode b (2^(h+l-c)) (word v hi)) lanes last ∧
        ∀v hi lo,word (host v) hi lo=DescentSignedCableCodec.encode (sign (DescentIssuedFallbackPanel.donor real μ small v hi lo) j)) ∧
      ∀a,a<base ∨ stop first D H h l b≤a→last a=mem a := by
  let X (j : Fin D) (v : Fin H) (g : Fin G) (x : Fin N) :=
    DescentSignedCableCodec.encode (Stage.Prepare.signed A native S ready groups.toEmbedding host x j v g)
  let term (j : Fin D) (x : Fin N) := Expr.lookup (old j x) .row
  have source (j : Fin D) (x : Fin N) : Source (term j x) (fun v g=>X j v g x) M mem :=
    source_column (old j x) base (safe j x) mem _ (dataSize j x) (signed j x)
  obtain ⟨last,ran,cheap,moved,kept⟩:=from_slots base saved term μ size width pos (Nat.two_pow_pos k) X mem
    (fun j x=>⟨safe j x,trivial⟩) source keyFits savedWord room
  refine ⟨last,ran,cheap,?_,kept⟩
  intro j
  let real:=DescentSixParty.PackedFlow.digits groups size
  apply DescentFallbackPeriod.signed_panel A S ready real native rs host μ small _ j
    (oldWord A native S ready groups host size j) _ repack many last (moved j)
  intro v z
  exact oldWord_at A native S ready groups host size j v z

end
end Hierarchy.DescentGLPacked.BankImage.SignedFields

end OAI
