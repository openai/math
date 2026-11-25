import OAI.Hierarchy.DescentNamedBookIssuer
import OAI.Hierarchy.DescentNamedPreflightFormat
import OAI.Hierarchy.DescentTerminalBookPrimitivePages

namespace OAI
/-! One branch-independent six-book decoder reads the selected endpoint, actor, and source fields. -/
namespace Hierarchy.DescentTerminalPreflightSpace.Spec
open ProtocolRAM DescentTerminalLocalPortBook DescentTerminalPrimitiveArena
open ThreeFlat.RAM PhysicalProcedure
noncomputable section
variable (x:Spec) (base:ℕ) (peer:Bank) (wing:Fin x.scalar.blocks → Fin (2*x.cap) → Bank)
private theorem times_fit (w bound d:ℕ) : (timesRow d).Fits w bound := by
  induction d with | zero=>trivial | succ d ih=>exact ⟨ih,trivial⟩

theorem source_before_weights {w:ℕ} (word:x.maskBase base<2^w) (earlier:peer.base+peer.size ≤ x.cohortEnd base)
    (wings:∀b j,(wing b j).base+(wing b j).size ≤ x.cohortEnd base) (i:Fin x.strips) :
    ((x.issuedBook base peer wing).source i).Fits w (x.weights base) := by
  let R:=x.rasters base peer wing
  obtain ⟨a,b,c,d,e,f,g,h,j⟩:=x.layers base
  have early_:x.cohortEnd base ≤ x.weights base:=a.trans b
  have finish_:x.bookBegin base<2^w:=by omega
  have old (bank:Bank) (q:bank.base+bank.size ≤ x.weights base) : bank.Fits w (x.weights base) :=
    ⟨Nat.two_pow_pos _,(Nat.le_add_left ..).trans_lt ((q.trans c).trans_lt finish_),q⟩
  have occ (b:Fin x.scalar.blocks) : (R.geometry.occupied b).Fits w (x.weights base):=
    old _ (x.channel_end base b 1)
  have count (b:Fin x.scalar.blocks) : (R.geometry.primitive b 0).Fits w (x.weights base):=
    old _ (x.channel_end base b 0)
  have seen:R.roster.Fits w (x.weights base):=old peer (earlier.trans (a.trans b))
  have neighbor (j:Fin x.degree) : (R.neighbor j).Fits w (x.weights base):=⟨seen,times_fit ..,trivial⟩
  change (R.sources i).Fits w _
  unfold Rasters.sources
  cases ix:(fieldIndex x.degree x.scalar.blocks x.cap).symm i with
  | inl j=>exact ⟨trivial,neighbor j,trivial,⟨neighbor j,trivial,trivial,trivial⟩⟩
  | inr z=>
    rcases z with ⟨b,j|j⟩
    · refine ⟨?_,trivial⟩
      change (if j=0 then R.geometry.occupied b else R.geometry.primitive b 0).Fits w _
      split <;> first | exact occ b | exact count b
    · exact ⟨old _ ((wings b j).trans early_),trivial⟩

end
end Hierarchy.DescentTerminalPreflightSpace.Spec

namespace Hierarchy.DescentSixParty.SeedNamed.Branch
open DescentCompiler DescentInitialHost DescentMixedRouter DescentResetInvoice Catalyst CatalystSubstitution
open DescentTerminalExteriorPackets DescentKernelHistory CorrectionBatch
open DescentExterior Computability.VPVNP.RAMSerialization DescentTerminalDenseGraphRead DescentTerminalDenseWindow
open scoped Classical BigOperators Fin.CommRing
noncomputable section
set_option quotPrecheck false
attribute [local irreducible] Origin.source Origin.archivePackage Branch.pinSpine Branch.originalPin
variable {F : Type} [Field F] {cp P : ℕ} (X : Approximation F cp P) (G : PoweredGadget F) (S : AtomSchedule)
  {k n h C f g p R : ℕ}
variable {he : 0 ≤ (((S.initialSites * S.copies : ℕ) : ℝ) / S.epochPower)}
  {hu : 0 ≤ (1 / ((S.firstWidth G.b p : ℝ) * (S.epochPower : ℝ) ^ S.priceExponent)) *
    (S.epochPower : ℝ) ^ S.priceExponent} {radix : S.radix = 2^k}
variable {r : Epochs G hu he (h := h) (C := C) (Ht := GroupStage.depthBound (atRound S.rounds) n f g)
  (t := S.rounds) S.height (initial X S.copies (S.firstWidth G.b p) (S.groupCount 0) k (S.initialDigits radix))}
variable {c : (Epochs.finish G hu he r).Choice} (b : Branch X G S (p:=p) (n:=n) (h:=h) (C:=C) (f:=f) (g:=g) radix R r c) (hp : 0 < p)


local notation "s" => S.firstWidth G.b p
local notation "net" => ((Epochs.finish G hu he r).state c).graph
local notation "E" => Fintype.card (Port P X.width)
variable {tail j rest : ℕ} (base : S.baseGroups=2^tail)
variable (width : S.groupWidth k tail 0+k=j+(j+rest))



open DescentTerminalGraphPositions DescentTerminalCableOrder DescentTerminalLocalPortBook DescentSharedCableNames DescentColonies
open ThreeFlat.Routing
local notation "retained" => S.groupWidth k tail S.length+k
local notation "O" => leafOrder X G S b hp base width
local notation "placement" => b.target.placement
local notation "native" => b.target.order.trans Fin.valEmbedding
local notation "names" => DescentPacking.PackedMatch.Local.Stage.cableNames k
  (DescentStageEdgeReceipt.groupRank (Fin.valEmbedding (n:=S.groupCount S.length)) (b.target.vertex.trans Fin.valEmbedding))
local notation "pinRank" v => (densePinEquiv X G S b hp base v).toEmbedding.trans Fin.valEmbedding
local notation "operand" v => leafOperands X G S b hp base v
local notation "calendar" => fun g row => ((S.resetInputDigits base radix S.length).symm (g,row)).val
local notation "scale" => ((placement).z*G.b)/p


open DescentTerminalPaidHeaderEvents DescentTerminalGrainProfiles DescentTerminalPeerChronology DescentTerminalGraphRows
open DescentSortedRoster DescentPhysicalOrder DescentPacking
local notation "H0" => S.hostSize S.length
local notation "hosts" => b.target.vertex.trans (Fin.castLEEmb b.target.valid.host)
local notation "nodeRank" => ((placement).site b.target.vertex b.target.valid.coordinates).trans Fin.valEmbedding
local notation "outs" => leafExternal X G S b hp base width
local notation "ins" => leafOperands X G S b hp base

open DescentSIMDLookup DescentTerminalRecipeRows DescentTerminalPointerDigits ProtocolRAM Calendar Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
local notation "V0" => S.groupCount S.length*2^k
local notation "A0" => NativeBranch.localLimit G S
local notation "M0" => V0*A0


open DescentTerminalPreflightSpace

/-- Transport the reached raster type along the two authenticated geometric dimensions. -/
def presented {d d' k c c' : ℕ} (hd:d=d') (hc:c=c') (rasters:Rasters d' k c') : Rasters d k c := by
  subst d';subst c';exact rasters

/-- The public book key contains just measured shelf lanes and the fixed inverse reset calendar. -/
def decodeBook (S:AtomSchedule) (G:PoweredGadget F) {k tail:ℕ} (hp:S.baseGroups=2^tail)
    (radix:S.radix=2^k) (p q d cap bits:ℕ) (four:d+1≤4)
    (word:Fin (DescentTerminalLocalPortBook.width d (2^k) cap) → Cell bits) :=
  ((Rasters.measure d (2^k) cap (S.groupCount S.length) (Nat.clog 2 (q+1)) word).directory
    (NativeBranch.localLimit G S) G.b (S.firstWidth G.b p/p) (2^(S.groupWidth k tail S.length+k))
    (fun g row=>((S.resetInputDigits hp radix S.length).symm (g,row)).val)).extend four

theorem bookOnDimensions {d cap:ℕ} (eqDegree:(placement).degree=d) (eqCap:(placement).cap=cap)
    (four:d+1≤4) (rack:Rasters d (2^k) cap) (q short first weightsAt:ℕ) {w:ℕ} (m:Memory w)
    (elapsed:0 < S.length) (room:j ≤ retained) (whole:p∣s)
    (raw:Fin H0 → Fin (placement).degree → Option (Fin H0))
    (original:Rasters.Inputs (p:=p) (bw:=short) (argc:=Nat.clog 2 (q+1))
      placement hosts S b.target.valid b.target.order raw (presented eqDegree eqCap rack) m)
    (source:∀l,((rack.controller H0 first short).source l).Fits w weightsAt)
    (mounted:Book.WeightShelf.finish V0 A0 weightsAt ≤ first) (token:2^short<2^w)
    (space:(rack.controller H0 first short).stop<2^w) :
    let dec:=decodeBook S G base radix p q d cap short four
    let cpu:=rack.controller H0 first short
    let action:=(Book.WeightShelf.program V0 A0 weightsAt w).seq (cpu.prefix dec M0 w 6 le_rfl)
    let o:=cpu.memory dec M0 (Book.WeightShelf.memory V0 A0 weightsAt m) 6 le_rfl
    action.Exec m o (4+10*Book.WeightShelf.words V0 A0+cpu.time 6 le_rfl) ∧ CheapCode action ∧
      Book.Issued (cpu.parts (Book.WeightShelf.banks V0 A0 weightsAt)) (fun i=>
        issue ((O).site i) (leaf_local_room X G S b hp base width i) (rowName ((O).site i) (leaf_local_room X G S b hp base width i)) (refName ((O).site i) (leaf_local_room X G S b hp base width i))) o ∧
      ∀a,a < weightsAt → o a=m a := by
  subst d;subst cap
  have grain_ : (placement).z*G.b/p=G.b:=by rw [b.target.grain,Nat.mul_div_cancel_left _ hp]
  have realExec:=book_issued X G S b hp base width rack (Nat.clog 2 (q+1)) short first weightsAt
    elapsed room whole raw m original source mounted token space
  dsimp only
  delta decodeBook
  simp only [bookPrinter,bookMemory,grain_] at realExec
  exact realExec

variable (q drift:ℕ) (op:RotorSpec) (headerRows paidRows:ℕ)
local notation "fmt" => geometryFormat G S k g p tail q drift op headerRows paidRows
local notation "spec" => preflightSpec X G S k g p tail fmt
variable (origin:ℕ) (peer:Bank) (old:Fin (2^k) → Fin (2*((capCalendar G.b S.rounds g S.height).prod*256)) → Bank)
local notation "rack" => (spec).rasters origin peer old
local notation "eqs" => preflight_caps (tail:=tail) X G S b fmt
local notation "measuredRack" => presented (eqs).1 (eqs).2.1 rack
local notation "table₀" => decodeBook S G base radix p q (spec).degree (spec).cap (spec).printBits (by change 3+1≤4; decide)
local notation "cpu₀" => (spec).issuedBook origin peer old

/-- The physical code and its six destination banks are identical on all branches of the named run. -/
theorem fixed_book_issued {w:ℕ} (m:Memory w) (elapsed:0 < S.length) (room:j ≤ retained) (whole:p∣s)
    (raw:Fin H0 → Fin (placement).degree → Option (Fin H0))
    (original:Rasters.Inputs (p:=p) (bw:=(spec).printBits) (argc:=Nat.clog 2 (q+1))
      placement hosts S b.target.valid b.target.order raw measuredRack m)
    (peerEarly:peer.base+peer.size≤(spec).cohortEnd origin)
    (wingsEarly:∀u i,(old u i).base+(old u i).size≤(spec).cohortEnd origin)
    (token:2^(spec).printBits<2^w) (space:(spec).maskBase origin<2^w) :
    let action:=(Book.WeightShelf.program V0 A0 ((spec).weights origin) w).seq ((cpu₀).prefix table₀ M0 w 6 le_rfl)
    let done_:= (cpu₀).memory table₀ M0 (Book.WeightShelf.memory V0 A0 ((spec).weights origin) m) 6 le_rfl
    action.Exec m done_ (4+10*Book.WeightShelf.words V0 A0+(cpu₀).time 6 le_rfl) ∧ CheapCode action ∧
      Book.Issued ((spec).parts origin) (fun i=>issue ((O).site i) (leaf_local_room X G S b hp base width i)
        (rowName ((O).site i) (leaf_local_room X G S b hp base width i)) (refName ((O).site i) (leaf_local_room X G S b hp base width i))) done_ ∧ ∀a,a<(spec).weights origin → done_ a=m a := by
  have bounds:=(spec).layers origin
  have stop_ : (cpu₀).stop<2^w:=by
    rw [(spec).print_stop origin peer old]
    obtain ⟨a,b,c,d,e,f,g,h,j⟩:=bounds
    omega
  exact bookOnDimensions X G S b hp base width (eqs).1 (eqs).2.1 (by change 3+1≤4; decide) rack q
    (spec).printBits ((spec).bookBegin origin) ((spec).weights origin) m elapsed room whole raw original
    ((spec).source_before_weights origin peer old space peerEarly wingsEarly) le_rfl token stop_


open DescentTerminalVertexFields DescentTerminalPointerIssue DescentTerminalSiteShelves
open DescentTerminalSignedGrainWord DescentChosenRouter DescentPackedColony
open Computability.BorderVNP.Crossing

/-- The real public arity f0, occupancy bits, signed wings and original roster give all measured inputs. -/
theorem fixed_book_inputs {tags hidden Nop maxArgs w:ℕ} (m:Memory w) (raw:Fin H0 → Fin (placement).degree → Option (Fin H0))
    (near:∀v,present raw (hosts v)=((placement).near v).map hosts)
    (peers:∀h j z,(DescentSortedRoster.indexed raw) h j=some z→(measuredRack).roster.read m ((h.val*(placement).degree+j.val:ℕ):Computability.VPVNP.BurstRAM.Word w)=(z.val:Computability.VPVNP.BurstRAM.Word w))
    (word:2<2^w) (tiny:2<2^(spec).printBits) (homes:H0≤2^w)
    (maskCap:∀b,H0≤((measuredRack).geometry.occupied b).size) (portCap:∀b,H0≤((measuredRack).geometry.primitive b 0).size)
    (actors:∀h:Fin H0,∀b:Block k,m (((measuredRack).geometry.occupied b).base+h.val)=
      ((encode 1 (S.groupCount S.length) (fun g=>(if ∃v:(net).Site,hosts ((placement).pos v).2=h ∧ ((placement).pos v).1=g ∧ (placement).block v=b then 1 else 0):Fin (S.groupCount S.length) → Cell 1)).val:Computability.VPVNP.BurstRAM.Word w))
    (scalar:∀v:(net).Site,venueField (cellAt
      (measured (q:=q) (t:=tags) (H:=hidden) (N:=Nop) (A:=maxArgs) (w:=p) (groups:=S.groupCount S.length)
        (MaskAllocation.shelf (q:=q) (t:=tags) (H:=hidden) (N:=Nop) (A:=maxArgs) (p:=p) (groups:=S.groupCount S.length) (measuredRack).geometry 0) m (hosts ((placement).pos v).2)) (finProdFinEquiv (((placement).pos v).1,(placement).block v))) publicArity=
      DescentTerminalGraphRows.arity net p v)
    (shelfBits:(S.groupCount S.length)≤(spec).printBits) (bitsRoom:(spec).printBits ≤ w) (argBits:(Nat.clog 2 (q+1))*(S.groupCount S.length)≤(spec).printBits)
    (wingWide:DescentSignedCableCodec.width (placement).degree (placement).cap*(S.groupCount S.length)≤(spec).printBits)
    (pitch:ℕ) (covered:(S.groupCount S.length) ≤ pitch) (wide:DescentSignedCableCodec.width (placement).degree (placement).cap*pitch ≤ w)
    (wings:∀block t,Reads ((measuredRack).wing block t) (fun h g=>DescentSignedCableCodec.encode ((DescentPacking.PackedMatch.Local.Stage.Prepare.signed placement native S b.target.valid (Function.Embedding.refl _) hosts block t h g))) pitch m)
    (wingCap:∀b t,H0≤((measuredRack).wing b t).size) :
    Rasters.Inputs (p:=p) (bw:=(spec).printBits) (argc:=(Nat.clog 2 (q+1))) placement hosts S b.target.valid b.target.order raw measuredRack m := by
  exact Rasters.from_pages (p:=p) (bw:=(spec).printBits) (q:=q) (tags:=tags) (hid:=hidden) (N:=Nop) (M:=maxArgs)
    placement hosts S b.target.valid b.target.order raw measuredRack m near peers word tiny homes
    maskCap portCap actors scalar shelfBits bitsRoom argBits wingWide pitch covered wide wings wingCap

end
end Hierarchy.DescentSixParty.SeedNamed.Branch
end OAI

open OAI.Hierarchy.DescentSixParty.SeedNamed
attribute [local irreducible] Origin.source Origin.archivePackage Branch.pinSpine Branch.originalPin
