import OAI.Hierarchy.DescentNamedWidePaidHistory
import OAI.Hierarchy.DescentTerminalObservedFlight

namespace OAI
/-! # Flight observations from the actual counted, relocated and contracted paid terminal input -/
namespace Hierarchy.DescentSixParty.SeedNamed
open DescentSixParty DescentCompiler DescentInitialHost DescentMixedRouter DescentResetInvoice
open DescentTerminalEpochChart DescentTerminalEpochDecoder DescentSeedRoot Catalyst Computability.BorderVNP.Crossing
open DescentPackedEpochShelves DescentPackedEpochFold DescentPackedProfileTape DescentPackedProfileInstall
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM ThreeFlat.RAM PhysicalProcedure
open DescentExterior DescentExteriorShelf DescentExteriorMatrixUpdate CorrectionBatch CatalystSubstitution
open DescentTerminalCompiledPrefix
open DescentTerminalVertexFields.MaskAllocation
open ThreeFlat Routing Diagonal
open Computability.VPVNP.RAMMemory (initialMemory)
open scoped Classical
open scoped Fin.CommRing
noncomputable section
variable {F : Type} [Field F] {cp nP : ℕ} (X : Approximation F cp nP) (G : PoweredGadget F) (S : AtomSchedule)
variable {k cut tail n h C f g p : ℕ}
variable (ordinary : OrdinaryRates G S k cut) (reset : ResetRates G S k (atRound S.rounds) n h C f g cut tail)
variable (branch : G.b ≤ 2^S.capGain) (positive : 0 < p) (room : 10*(X.size+1) ≤ S.initialSites)
variable (shorten : reentryRate h C*(1-(2-G.rate)/4)^S.rounds ≤ 1/2)
attribute [local irreducible] Procedure.Exec ProtocolRAM.CheapCode Origin.source Branch.publicLayout Loaded
set_option maxHeartbeats 950000
set_option maxRecDepth 8192
set_option cleanup.letToHave false
set_option quotPrecheck false
local notation "rs" => (normalized_epochs_issued_joint X G S ordinary reset branch positive room shorten).choose
local notation "ow" => inputOrder X G S ordinary reset branch positive room shorten
local notation "q" => S.firstWidth G.b p
variable (w payloadBits : ℕ) (fit : S.firstWidth G.b p < 2^w)
local notation "ch" => normalizedPackedChart X G S ordinary reset branch positive room shorten w fit

variable {blocks ν bound : ℕ} (V : Home.Format) (U : Shape) (I : AddressPlan.Input)
    (R : DescentTerminalVertexFields.MaskAllocation.Channels blocks) (begin_ privateAt : ℕ)
    (short : ν*DescentTerminalVertexFields.span V.publicArity V.roles V.privateWords V.nodes V.addresses V.piece ≤ bound)
    (literal : DescentTerminalEmitter.Compact.Literals I.sources)
local notation "headBits" => U.terminal.plane.headBits
local notation "rest" => U.terminal.plane.restBits
local notation "laneCount" => U.terminal.plane.bitLanes
local notation "B" => S.groupWidth k tail 0+k
local notation "Port₀" => Catalyst.Port ((2^(headBits+(headBits+rest))*laneCount)*nP) (CorrectionFrame.copiesWidth (2^(headBits+(headBits+rest))*laneCount) X.width)
local notation "imageAt" => AddressPlan.afterMeter V U R begin_
local notation "origin" => AddressPlan.takeOff U I imageAt
local notation "sink" => AddressPlan.output V U I R begin_ privateAt short literal
local notation "suffix" => AddressPlan.clock V U I R begin_ privateAt short literal (bw:=w)
local notation "mix" => fun c=>Branch.publicLayout X G S
  (SeedNamed.issued X G S ordinary reset branch positive room shorten c) positive reset.base
variable {K W fieldQ piece rawRows : ℕ} (pub codes : ℕ)
local notation "E" => Fintype.card (Port nP X.width)
local notation "Old" => (ch).Pin ⊕ Hidden E headBits rest laneCount
local notation "All" => DescentTerminalFullPins.Candidate Old K W fieldQ piece rawRows
variable (all : DescentTerminalFullPins.Candidate ((normalizedPackedChart X G S ordinary reset branch positive room shorten w fit).Pin ⊕ Hidden (Fintype.card (Port nP X.width)) U.terminal.plane.headBits U.terminal.plane.restBits U.terminal.plane.bitLanes) K W fieldQ piece rawRows → Bool)
local notation "z" => all ∘ DescentTerminalFullPins.history ∘ Sum.inl
local notation "guesses" => all ∘ DescentTerminalFullPins.history ∘ Sum.inr
local notation "choice_" => (normalizedRoute X G S ordinary reset branch positive room shorten w fit).follow z
local notation "path_" => (SeedNamed.issued X G S ordinary reset branch positive room shorten choice_).path.selections

local notation "seedBase" => DescentWideSeedFlags.endInput X S.copies q payloadBits
local notation "seedRows" => DescentPackedSeed.rows X S.copies q payloadBits
local notation "seedAt" => seedBase+seedRows
local notation "seedCode" => DescentWideSeedFlags.check X S.copies q payloadBits w

local notation "chosen" => SeedNamed.issued X G S ordinary reset branch positive room shorten choice_
variable (width : S.groupWidth k tail 0+k=U.terminal.plane.headBits+(U.terminal.plane.headBits+U.terminal.plane.restBits)) (outer : Catalyst.Port ((2^(U.terminal.plane.headBits+(U.terminal.plane.headBits+U.terminal.plane.restBits))*U.terminal.plane.bitLanes)*nP) (CorrectionFrame.copiesWidth (2^(U.terminal.plane.headBits+(U.terminal.plane.headBits+U.terminal.plane.restBits))*U.terminal.plane.bitLanes) X.width)→Bool)
local notation "x" => DescentExterior.publicRows X outer
local notation "packed" => Sum.elim z guesses
local notation "survives" => (∃c,(ch).read z=some c)
local notation "compact" => fun (lo grain : ℕ)=>end_ (lo+extent grain (ch).layout) G.C grain
local notation "tape" => fun (lo grain : ℕ)=>Root.widePackedImage X S.copies q payloadBits w (ch).seed lo G.C grain (ch).layout (compact lo grain) x packed
local notation "frontSize" => fun (lo grain : ℕ)=>compact lo grain+17*span headBits rest laneCount E
local notation "raw" => fun (lo grain extra : ℕ) (back : Memory w)=>Root.appended (frontSize lo grain) extra (tape lo grain) back
local notation "work" => fun (lo grain extra : ℕ)=>frontSize lo grain+extra
local notation "extra" => DescentTerminalPublicIdentity.total K W fieldQ piece codes rawRows pub
local notation "back" => DescentTerminalPublicIdentity.back (all ∘ DescentTerminalFullPins.chip) w codes pub
local notation "authHeader" => DescentTerminalFullPins.wideHeader X S.copies q payloadBits w (ch).seed
local notation "authPin" => DescentTerminalFullPins.widePins X S.copies q payloadBits w (ch).seed

theorem wide_paid_history_flight (lo grain fence : ℕ) (count : ℕ→ℕ) (plan : Reel)
    (middle : Procedure w) (m : Memory w) (cost : ℕ)
    (arch : payloadBits ≤ w) (payload : fieldQ*(W*piece) ≤ w) (wideSeed : 2*digitsNeeded q ≤ payloadBits) (wide : 0 < w) (fitsSeed : seedBase+(seedRows+1) < 2^w)
    (topSeed : seedBase+(seedRows+1) ≤ lo) (positiveGrain : 0 < grain)
    (below : work lo grain extra ≤ fence)
    (before : finalAt (work lo grain extra) lo grain (ch).layout < origin)
    (low : ∀p∈shelves grain lo 0 (ch).layout,count p.ordinal < lo)
    (words : ∀s∈(ch).layout,slots s.seats grain*grain < 2^w)
    (fits : finalAt (work lo grain extra) lo grain (ch).layout+1 < 2^w)
    (geometry : plan.Room w B S.length fence origin)
    (top : origin+span headBits rest laneCount E+E < 2^w)
    (apart : end_ (lo+extent grain (ch).layout) G.C grain+32*span headBits rest laneCount E ≤ origin)
    (copySpace : origin+17*span headBits rest laneCount E < 2^w)
    (stage : middle.Exec (DescentWideSeedFlags.countedAt X S.copies q payloadBits (ch).seed z (raw lo grain extra back)) m cost)
    (cheap : CheapCode middle)
    (measured : m seedAt=DescentWideSeedFlags.countedAt X S.copies q payloadBits (ch).seed z (raw lo grain extra back) seedAt)
    (archive : ∀a,lo ≤ a→a < end_ (lo+extent grain (ch).layout) G.C grain→
      m a=DescentWideSeedFlags.countedAt X S.copies q payloadBits (ch).seed z (raw lo grain extra back) a)
    (exterior : ∀(col : Fin 17) (u : ℕ),u < span headBits rest laneCount E→
      m ((bank headBits rest laneCount E (compact lo grain) col.val).base+u)=DescentWideSeedFlags.countedAt X S.copies q payloadBits (ch).seed z (raw lo grain extra back) ((bank headBits rest laneCount E (compact lo grain) col.val).base+u))
    (physical : ∀i,i < ((ch).rows z).length→∀v,(path_)[i]?=some v→(m (count i)).val=selectionCount G v)
    (issued : survives→(chosen).path.savedRotations plan fence tail m)
    (edges : U.terminal.plane.exteriors=E) (bits : 2^headBits*laneCount ≤ w)
    (stored : ∀a∈(ch).layout,DescentTerminalEpochBits.width a.C*grain ≤ w)
    (channels : ∀f,(R.bank f).base+(R.bank f).size ≤ begin_) (header_ : privateAt < begin_)
    (old : AddressPlan.Earlier U I imageAt (AddressPlan.meter V R begin_).layout w)
    (space : AddressPlan.last V U I R begin_ < 2^w) (verdict : finalAt (work lo grain extra) lo grain (ch).layout < begin_)
    (decodeCount : (Epochs.finish G _ _ rs).Choice→ℕ)
    (observed : ∀c,proposed (ch).read (fun v=>(mix v) width) x packed=some c→AddressPlan.SeedCount V R begin_ privateAt U.sites m (decodeCount c))
    (privateKept : privateAt<fence ∧ (privateAt<work lo grain extra ∨ finalAt (work lo grain extra) lo grain (ch).layout<privateAt))
    (channelKept : ∀f a,a<(R.bank f).size→let loc:=(R.bank f).base+a
      loc<fence ∧ (loc<work lo grain extra ∨ finalAt (work lo grain extra) lo grain (ch).layout<loc)) :
    let copied:=relocated headBits rest laneCount E (compact lo grain) origin m
    let keep:=plan.result headBits rest laneCount E B S.length origin copied
    let start:=raw lo grain extra back
    let dst:=finalAt (work lo grain extra) lo grain (ch).layout
    let ss:=controlsAt (work lo grain extra) lo G.C grain (ch).layout count (fun _=>seedAt)
    let program:=(((seedCode).seq (middle.seq (relocate headBits rest laneCount E w (compact lo grain) origin))).seq (plan.program headBits rest laneCount E w B S.length origin)).seq (fold w seedAt dst ss)
    let o:=oldStateAt (work lo grain extra) lo G.C grain seedAt (ch).layout count z keep
    let total:=((4+(seedRows+1)*66+(cost+(4+18*(17*span headBits rest laneCount E))))+(10+((4+58*S.length)+(4+16*E))))+bill seedAt dst ss
    let end_:=sink o
    let answer:=flagAt («j»:=headBits) (r:=rest) («t»:=laneCount) (e:=E) origin
    AddressPlan.Flight (program.seq suffix) (work lo grain extra) (total+AddressPlan.time V U I R begin_ privateAt)
      (authPin lo G.C grain (ch).layout pub codes) outer all start end_ dst answer
      (AddressPlan.registers V U R begin_ privateAt).deadBits (proposed (ch).read (fun c=>(mix c) width) x packed) decodeCount := by
  intro copied keep start dst ss program o total end_ answer
  have observedFlight:=wide_paid_history_seed (X:=X) (G:=G) (S:=S) (ordinary:=ordinary) (reset:=reset)
    (branch:=branch) (positive:=positive) (room:=room) (shorten:=shorten) (w:=w) (payloadBits:=payloadBits)
    (fit:=fit) (V:=V) (U:=U) (I:=I) (R:=R) (begin_:=begin_) (privateAt:=privateAt) (short:=short)
    (literal:=literal) (pub:=pub) (codes:=codes) (all:=all) (width:=width) (outer:=outer)
    lo grain fence count plan middle m cost arch payload wideSeed wide fitsSeed topSeed positiveGrain
    below before low words fits geometry top apart copySpace stage cheap measured archive exterior physical issued
    edges bits stored channels header_ old space verdict decodeCount observed privateKept channelKept
  refine ⟨observedFlight.1,?_,observedFlight.2.2.1,observedFlight.2.2.2.1,?_⟩
  · rw [AddressPlan.appended_as_input]
    exact observedFlight.2.1
  · exact fun c hc=>observedFlight.2.2.2.2 c hc ()

end
end Hierarchy.DescentSixParty.SeedNamed

end OAI
