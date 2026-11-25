import OAI.Hierarchy.DescentFundedStageReturn
import OAI.Hierarchy.DescentFundedByBasis

namespace OAI
/-! # One funded reset execution from the preceding stage venue -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentCompiler DescentGL DescentColonies DescentPaidResidentCount DescentPaidResidentCount.Reset
open DescentDenseHostOrder DescentSIMDLookup DescentPackedZip DescentFundedCensus
open DescentPacking.PackedMatch.Local.Stage DescentSharedCableNames DescentPlainTerminal.Suffix DescentIssuedFallbackPanel
open ThreeFlat.RAM PhysicalProcedure
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
variable (high low oldLanes gatherLanes : ℕ) (base : ℕ)
local notation "s" => (⟨H,S.groupCount i,2^k,oldLanes,gatherLanes,b,high,low,cc,(A).degree,(A).cap,M⟩:Setup)
local notation "book" => (⟨(pool).card,H,2^cc,M,b,wide⟩:Shape)
local notation "budget" => (A).wire*((A).z*G.b)*(A).cap
local notation "fin" => (s).roof base

variable (old : Block k→Bank) (key : Bank) (signal : Fin (2*cap.placement.cap)→Expr)
  (panelOp : Expr) (flag : Fin (DescentDenseHostOrder.roster B.reset.graph (B.reset.k-B.terminals.commonDepth) (GroupStage.depthBound D n f g)).card→Expr) (root : Bool→(DescentResetHostSize.Code (B.reset.k-B.terminals.commonDepth) × Option (Fin (2^B.reset.n)))→Expr)
local notation "io" => (⟨.lookup ((s).primary base) .row,(s).secondary base signal,panelOp,root⟩:DescentFundedCensus.Ports relative (Z).n)
local notation "job" => fun j=>compile (Ht:=dep) (Z).graph C (Z).width ((Z).unit/p) b (A).cap f (A).degree (A).cap
  field header io (flag j) (shapes B j)

theorem funded_channels (m : Memory w) (keys : key.Fits w base) (banks : ∀j,(old j).Fits w base)
    (space : fin<2^w) (μ : DescentGL.Layout (high+low))
    (keyRead : m key.base=((DescentExterior.matrixCode μ).val:Word w))
    (ageDim : high+low=dim) (basis : HEq μ B.frame.basis)
    (axes : 2^(high+low)=S.groupCount i*2^k) (pitch : 2^low=gatherLanes*2^k)
    (short : cc≤high+low) (pack : M*(s).donors=2^low)
    (po : 0<oldLanes) (pg : 0<gatherLanes) (pm : 0<M)
    (oldSize : ∀j,H*chunks (S.groupCount i) oldLanes≤(old j).size)
    (oldRead : ∀j,DescentPackedColony.Reads (old j) (fun v g=>price v g j) oldLanes m)
    (actual : Fin (2*(A).cap)→Fin H→Block cc→Fin L→Cell sig)
    (signalsFit : ∀j,(signal j).Fits w base)
    (signals : ∀j,Source (signal j) (fun v hi=>encode sig (s).donors
      (fun l=>actual j v hi (Fin.cast (by change 2^(high+low-cc)=L;rw [ageDim]) l))) M m)
    (panel : Fin H→Block cc→Cell (header*L)) (snap : PaddedSnapshot B oldRoom field)
    (panelFit : panelOp.Fits w base) (flagFit : ∀j,(flag j).Fits w base) (rootFit : ∀side k,(root side k).Fits w base)
    (panelRead : Source panelOp panel M m) (flags : ∀j,Source (flag j) (lit j) M m)
    (roots : ∀side k,Source (root side k) (savedInput B oldRoom snap) M m)
    (arrivals : 2*(A).cap<2^b) :
    let mid:=(s).memory base old key m
    Source (io).old (ownOld (b:=b) B oldRoom) M mid ∧ Source (io).relay (ownArrivals (b:=b) B actual) M mid ∧
      Source panelOp panel M mid ∧ (∀j,Source (flag j) (lit j) M mid) ∧
      ∀side k,Source (root side k) (savedInput B oldRoom snap) M mid:=by
  intro mid
  let raw:=fun j h hi (l:Fin (s).donors)=>actual j h hi (Fin.cast (by change 2^(high+low-cc)=L;rw [ageDim]) l)
  obtain ⟨lhs,rhs,panelRead',flags',roots'⟩:=(s).returned old key m keys banks space μ keyRead
    axes pitch short pack po pg (Nat.two_pow_pos _) pm (fun j v g=>price v g j)
    oldSize oldRead signal raw signalsFit signals arrivals panelOp flag root panel lit
    (fun _ _=>savedInput B oldRoom snap) panelFit flagFit rootFit panelRead flags roots
  have old':=primary_return (b:=b) B oldRoom high low oldLanes gatherLanes _ mid μ axes short ageDim basis lhs
  have in':=relay_return (b:=b) B _ mid ageDim raw actual (by intros;rfl) rhs
  exact ⟨old',in',panelRead',flags',roots'⟩

/-- The two actual programs use the identical scheduled memory. The only site
data supplied at entry are the previous paid column, signed endpoints, occupied
actors, and retained fallback/stencil panels. -/
theorem funded_phase (m : Memory w) (keys : key.Fits w base) (banks : ∀j,(old j).Fits w base)
    (space : fin<2^w) (μ : DescentGL.Layout (high+low))
    (keyRead : m key.base=((DescentExterior.matrixCode μ).val:Word w))
    (ageDim : high+low=dim) (basis : HEq μ B.frame.basis)
    (axes : 2^(high+low)=S.groupCount i*2^k) (pitch : 2^low=gatherLanes*2^k)
    (short : cc≤high+low) (pack : M*(s).donors=2^low)
    (po : 0<oldLanes) (pg : 0<gatherLanes) (pm : 0<M)
    (oldSize : ∀j,H*chunks (S.groupCount i) oldLanes≤(old j).size)
    (oldRead : ∀j,DescentPackedColony.Reads (old j) (fun v g=>price v g j) oldLanes m)
    (actual : Fin (2*(A).cap)→Fin H→Block cc→Fin L→Cell sig)
    (signalsFit : ∀j,(signal j).Fits w base)
    (signals : ∀j,Source (signal j) (fun v hi=>encode sig (s).donors
      (fun l=>actual j v hi (Fin.cast (by change 2^(high+low-cc)=L;rw [ageDim]) l))) M m)
    (panel : Fin H→Block cc→Cell (header*L)) (snap : PaddedSnapshot B oldRoom field)
    (panelFit : panelOp.Fits w base) (flagFit : ∀j,(flag j).Fits w base) (rootFit : ∀side k,(root side k).Fits w base)
    (panelRead : Source panelOp panel M m) (flags : ∀j,Source (flag j) (lit j) M m)
    (roots : ∀side k,Source (root side k) (savedInput B oldRoom snap) M m)
    (order : W.graph.Edge↪ℕ) (names : DescentSharedCableNames.Stage.Host (Fin (S.groupCount i)) cap.V k↪ℕ)
    (realPanel : ∀v hi,panel (host v) hi=encode header L (Recorded.realPanel (reset:=B) rfl B.frame.basis fBits header v hi))
    (realSigns : ∀j v hi lo,actual j (host v) hi lo=DescentSignedCableCodec.encode (Stage.signedPanel A order S cap.valid names
      (((digits (oldIx hi lo)).1,v),(digits (oldIx hi lo)).2) j))
    (up : small<2^fBits) (one : 1<2^fBits) (enough : L*budget<2^fBits)
    (legal : 2*DescentFallbackShapeTable.rows small (2^(Z).n)≤2^header)
    (active : 0<budget) (quotaPos : 0<quota S.rounds) (degreePos : 0<32*Nat.clog 2 (2*(A).degree))
    (paid : budget<2^b) (arrivals : 2*(A).cap<2^b) (room : Room («s»:=book) job w fin) :
    let done:=memory («s»:=book) job fin ((s).memory base old key m)
    (((s).program w base old key).seq (program («s»:=book) job w fin)).Exec m done
      ((s).ticks w base old key+ticks («s»:=book) job fin) ∧
    (∀j pos,done ((book).column fin j+(row H (2^cc) M pos).val)=
      (data (fun v hi=>payable (precision:=b) B r oldRoom (finProdFinEquiv (v,j)) hi) pos).val) ∧
    (∀a,a<base ∨ (book).roof fin≤a→done a=m a) :=by
  intro out
  let mid:=(s).memory base old key m
  have first:=(s).any base old key m banks keys space
  have second:=DescentFundedCensus.any («s»:=book) job room mid
  obtain ⟨old',in',panelRead',flags',roots'⟩:=funded_channels B oldRoom high low oldLanes gatherLanes base
    old key signal panelOp flag root m keys banks space μ keyRead ageDim basis axes pitch short pack po pg pm
    oldSize oldRead actual signalsFit signals panel snap panelFit flagFit rootFit panelRead flags roots arrivals
  refine ⟨@Procedure.Exec.then w ((s).program w base old key) (program («s»:=book) job w fin)
    m mid out _ _ (@And.left _ _ first) (@And.left _ _ second), ?_, ?_⟩
  · exact issued_funded_read B r oldRoom panel actual snap io flag fin mid room order names realPanel realSigns
      up one enough legal active quotaPos degreePos paid arrivals panelRead' old' in' flags' roots'
  · intro a outside
    have lo:base≤fin:=(s).room base
    have hi:fin≤(book).roof fin:=(book).room fin
    exact (second.2.2 a (by rcases outside with h'|h';exact Or.inl (h'.trans_le lo);exact Or.inr h')).trans
      (first.2.2 a (by rcases outside with h'|h';exact Or.inl h';exact Or.inr (hi.trans h')))

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
