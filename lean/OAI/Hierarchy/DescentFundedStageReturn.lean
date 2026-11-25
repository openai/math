import OAI.Hierarchy.DescentFundedIssuedValues
import OAI.Hierarchy.DescentFundedRootObservation
import OAI.Hierarchy.DescentFundedMixerReturn

namespace OAI
/-! # The paid output of a real reset occurrence on every stored row -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentCompiler DescentGL DescentColonies DescentPaidResidentCount DescentPaidResidentCount.Reset
open DescentDenseHostOrder DescentSIMDLookup DescentPackedZip DescentFundedCensus
open DescentPacking.PackedMatch.Local.Stage DescentSharedCableNames DescentPlainTerminal.Suffix DescentIssuedFallbackPanel
open DescentCommonPalette DescentCommonHost DescentRelativeContacts DescentPlainTerminal
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open scoped Classical BigOperators Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {F P:Type} [Field F] {d:ℕ} {bits:P→ℕ} {W:MarkedWorld F d P bits} {G:PoweredGadget F}
  {q ε:ℝ} {S:AtomSchedule} {k i z D n h C f g cut tail wire hist : ℕ} {ctl:ResetRates G S k D n h C f g cut tail}
  {cap:Reached W G q ε S k i z D wire hist} (B:ClosedReset cap ctl)
  {p b H M w fBits header field wide : ℕ} (r:B.Recorded p) (oldRoom:Fintype.card cap.V≤H)
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "A" => cap.placement
local notation "host" => cap.vertex.trans (Fin.castLEEmb oldRoom)
local notation "cc" => (T).commonDepth
local notation "dep" => GroupStage.depthBound D n f g
local notation "relative" => ((Z).k-cc)
local notation "dim" => (S.groupWidth k tail i+k)
local notation "small" => (dim-cc)
local notation "pool" => DescentDenseHostOrder.roster (Z).graph relative dep
local notation "L" => 2^small
local notation "digits" => S.resetInputDigits ctl.base ctl.radix i
local notation "fit" => B.frame.enough.trans (Nat.sub_le ..)
local notation "sig" => DescentSignedCableCodec.width (A).degree (A).cap
local notation "vv" => AtlasValues (Z).n relative (pool).card H (2^cc) b (A).degree (A).cap field header
local notation "v₀" t:arg => B.frame.host.symm (((T).code t).1)
local notation "hi₀" t:arg => (Z).rootBlock T (.inr t)
local notation "oldIx" hi:arg l:arg => (rearrange B.frame.basis).symm (join fit hi l)
local notation "lit" => Recorded.realActor (reset:=B) (shapes B) (rack B oldRoom)
local notation "price" => Census.count A (Equiv.refl _) host b
local notation "pKey" => DescentResetHostSize.Code relative×Option (Fin (2^(Z).n))
local notation "rootWidth" => field*DescentFallbackPeriod.inputCount (A).degree (2^relative) (A).cap (Z).n relative
variable (stencil : Fin H→Block B.terminals.commonDepth→Cell (header*2^((S.groupWidth k tail i+k)-B.terminals.commonDepth)))
  (incoming : Fin (2*cap.placement.cap)→Fin H→Block B.terminals.commonDepth→Fin (2^((S.groupWidth k tail i+k)-B.terminals.commonDepth))→Cell (DescentSignedCableCodec.width cap.placement.degree cap.placement.cap))
  (snap : PaddedSnapshot B oldRoom field) (io : DescentFundedCensus.Ports (B.reset.k-B.terminals.commonDepth) B.reset.n) (flag : Fin (DescentDenseHostOrder.roster B.reset.graph (B.reset.k-B.terminals.commonDepth) (GroupStage.depthBound D n f g)).card→Expr)
local notation "mid" =>(fun (_:Bool) (_:pKey)=>savedInput B oldRoom snap)
local notation "s" => (⟨(pool).card,H,2^cc,M,b,wide⟩:Shape)
local notation "dataW" => (A).wire*((A).z*G.b)*(A).cap
local notation "job" => fun j=>compile (Ht:=dep) (Z).graph C (Z).width ((Z).unit/p) b (A).cap f (A).degree (A).cap
  field header io (flag j) (shapes B j)

theorem issued_funded_read (base : ℕ) (m : Memory w) (fits : Room («s»:=s) job w base)
    (order : W.graph.Edge↪ℕ) (names : DescentSharedCableNames.Stage.Host (Fin (S.groupCount i)) cap.V k↪ℕ)
    (panel : ∀v hi,stencil (host v) hi=encode header L (Recorded.realPanel (reset:=B) rfl B.frame.basis fBits header v hi))
    (signed : ∀j v hi lo,incoming j (host v) hi lo=DescentSignedCableCodec.encode (Stage.signedPanel A order S cap.valid names
      (((digits (oldIx hi lo)).1,v),(digits (oldIx hi lo)).2) j))
    (up : small<2^fBits) (one : 1<2^fBits) (enough : L*dataW<2^fBits)
    (legal : 2*DescentFallbackShapeTable.rows small (2^(Z).n)≤2^header)
    (active : 0<dataW) (quotaPos : 0<quota S.rounds) (degreePos : 0<32*Nat.clog 2 (2*(A).degree))
    (paid : dataW<2^b) (arrivals : 2*(A).cap<2^b)
    (readPanel : Source io.stencil stencil M m)
    (readOld : Source io.old (ownOld (b:=b) B oldRoom) M m)
    (readIn : Source io.relay (ownArrivals (b:=b) B incoming) M m)
    (isPresent : ∀j,Source (flag j) (lit j) M m)
    (readRoot : ∀side key,Source (io.bank side key) (savedInput B oldRoom snap) M m)
    (j : Fin (pool).card) (pos : Row H (2^cc) M) :
    memory («s»:=s) job base m ((s).column base j+(row _ _ _ pos).val)=
      (data (fun v hi=>payable (precision:=b) B r oldRoom (finProdFinEquiv (v,j)) hi) pos).val :=by
  let values:=issuedValues (b:=b) B oldRoom stencil incoming mid
  have previous:=funded_measured_values (b:=b) B oldRoom stencil incoming mid order names panel signed
    (saved_observed B oldRoom snap)
  have sources:=original_sources (wide:=wide) B oldRoom stencil incoming mid io flag m
    isPresent readPanel readOld readIn readRoot
  exact funded_read B r oldRoom io flag values previous up one enough legal active quotaPos degreePos
    paid arrivals m fits sources j pos

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
