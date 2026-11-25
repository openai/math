import OAI.Hierarchy.DescentFundedPayeeRun
import OAI.Hierarchy.DescentFundedSetup

namespace OAI
/-! # Building the charged atlas inputs from the previous paid and signed arrays -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentCompiler DescentGL DescentColonies DescentPaidResidentCount DescentPaidResidentCount.Reset
open DescentDenseHostOrder DescentSIMDLookup DescentPackedZip DescentFundedCensus
open DescentPacking.PackedMatch.Local.Stage DescentSharedCableNames DescentPlainTerminal.Suffix DescentIssuedFallbackPanel
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open scoped Classical BigOperators Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {F P:Type} [Field F] {d:ℕ} {bits:P→ℕ} {W:MarkedWorld F d P bits} {G:PoweredGadget F}
  {q ε:ℝ} {S:AtomSchedule} {k i z D n h C f g cut tail wire hist : ℕ} {ctl:ResetRates G S k D n h C f g cut tail}
  {cap:Reached W G q ε S k i z D wire hist} (B:ClosedReset cap ctl)
  {b H M w fBits header field wide : ℕ} (oldRoom:Fintype.card cap.V≤H)
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
local notation "v₀" t => B.frame.host.symm (((T).code t).1)
local notation "hi₀" t => (Z).rootBlock T (.inr t)
local notation "lit" => Recorded.realActor (reset:=B) (shapes B) (rack B oldRoom)
local notation "price" => Census.count A (Equiv.refl _) host b
local notation "pKey" => DescentResetHostSize.Code relative×Option (Fin (2^(Z).n))
local notation "rootWidth" => field*DescentFallbackPeriod.inputCount (A).degree (2^relative) (A).cap (Z).n relative
variable (stencil : Fin H→Block B.terminals.commonDepth→Cell (header*(2^(S.groupWidth k tail i+k-B.terminals.commonDepth))))
  (incoming : Fin (2*cap.placement.cap)→Fin H→Block B.terminals.commonDepth→Fin (2^(S.groupWidth k tail i+k-B.terminals.commonDepth))→Cell (DescentSignedCableCodec.width cap.placement.degree cap.placement.cap))
  (middle : Bool→(DescentResetHostSize.Code (B.reset.k-B.terminals.commonDepth)×Option (Fin (2^B.reset.n)))→Fin H→Block B.terminals.commonDepth→Cell (field*DescentFallbackPeriod.inputCount cap.placement.degree (2^(B.reset.k-B.terminals.commonDepth)) cap.placement.cap B.reset.n (B.reset.k-B.terminals.commonDepth)))

def ownOld (v : Fin H) (hi : Block cc) :
    Cell (b*L) := encode b L (fun lo=>let ix:=digits ((rearrange B.frame.basis).symm (join fit hi lo)); price v ix.1 ix.2)

def ownArrivals (v : Fin H) (hi : Block cc) : Cell (b*L) :=
  encode b L (fun lo=>(Arrivals.count incoming v hi lo:ℕ))

def resize (a : ℕ) (v : Cell (a*L)) : Cell (a*2^relative) :=
  Fin.cast (by rw [B.keyWidth]) v

theorem resize_heq (a : ℕ) (v : Cell (a*L)) : HEq (resize B a v) v :=by
  have transport {i j : ℕ} (h : i=j) (x : Fin i) : HEq (Fin.cast h x) x:=by subst j;rfl
  exact transport _ v

theorem resized_source (e : Expr) (m : Memory w) {a : ℕ} (rows : Fin H→Block cc→Cell (a*L))
    (raw : Source e rows M m) : Source e (fun u hi=>resize B a (rows u hi)) M m :=by
  have eqn : a*L=a*2^relative:=by rw [B.keyWidth]
  have generic {x y : ℕ} (eqw : x=y) (src : Fin H→Block cc→Cell x) (observe : Source e src M m) :
      Source e (fun u hi=>Fin.cast (congrArg (fun k=>2^k) eqw) (src u hi)) M m :=by
    subst y;exact observe
  exact generic eqn rows raw

def issuedValues : vv where
  present:=lit
  old v hi:=resize B b (ownOld B oldRoom v hi)
  relay v hi:=resize B b (ownArrivals B incoming v hi)
  stencil v hi:=resize B header (stencil v hi)
  bank:=middle

local notation "V" => issuedValues (b:=b) B oldRoom stencil incoming middle
local notation "s" => (⟨(pool).card,H,2^cc,M,b,wide⟩:Shape)

theorem funded_measured_values (order : W.graph.Edge↪ℕ) (names : DescentSharedCableNames.Stage.Host (Fin (S.groupCount i)) cap.V k↪ℕ)
    (panel : ∀v hi,stencil (host v) hi=encode header L (Recorded.realPanel (reset:=B) rfl B.frame.basis fBits header v hi))
    (signed : ∀j v hi lo,incoming j (host v) hi lo=DescentSignedCableCodec.encode (Stage.signedPanel A order S cap.valid names
      (((digits ((rearrange B.frame.basis).symm (join fit hi lo))).1,v),(digits ((rearrange B.frame.basis).symm (join fit hi lo))).2) j))
    (saved : ∀side t,Original B t (middle side ((Z).fallLabel T t,((T).code t).2.2) (host (v₀ t)) (hi₀ t))) :
    Observed (fBits:=fBits) B oldRoom V order names :=by
  refine ⟨fun _ _ _=>rfl,?_,fun _=>resize_heq ..,?_,saved⟩
  · intro t
    exact (resize_heq B _ _).trans (heq_of_eq (panel (v₀ t) (hi₀ t)))
  · intro t
    exact ⟨fun j lo=>incoming j (host (v₀ t)) (hi₀ t) lo,fun j lo=>signed j (v₀ t) (hi₀ t) lo,resize_heq ..⟩

theorem original_sources (io : Ports relative (Z).n) (flags : Fin (pool).card→Expr) (m : Memory w)
    (active : ∀j,Source (flags j) (lit j) M m) (readPanel : Source io.stencil stencil M m)
    (readOld : Source io.old (ownOld (b:=b) B oldRoom) M m)
    (readIn : Source io.relay (ownArrivals (b:=b) B incoming) M m)
    (readBank : ∀side key,Source (io.bank side key) (middle side key) M m) : RawSources («s»:=s) io flags V m :=
  ⟨active,resized_source B _ m _ readPanel,resized_source B _ m _ readOld,resized_source B _ m _ readIn,readBank⟩

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
