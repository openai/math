import OAI.Hierarchy.DescentScheduledDonorCensus
import OAI.Hierarchy.DescentArchiveOriginalSlot
import OAI.Hierarchy.DescentCalendarPrimarySpans

namespace OAI
/-! # Retained donor fields at each true previous host, group and block -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset
open DescentSixParty DescentCompiler DescentPacking.PackedMatch.Local.Stage DescentPackedWalsh
open DescentSixParty.Chronology DescentSIMDLookup DescentWalshPrecision DescentSixParty.PackedFlow.Padded ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
set_option hygiene false
variable {F : Type} [Field F] (G : PoweredGadget F) (S : AtomSchedule) {n d : ℕ}
    (board : NonlinearExpanders.Graph n d) (k tail age p f gain drift degree h : ℕ)
    (ordinary : ℕ→Dated.Ordinary) (op : RotorSpec) (s Z : ℕ)
    (ports : Chronology.DatePorts)
local notation "old" => ports.venue
local notation "io" => ports.io

local notation "a" => scheduledAtPorts G S board k tail age p f gain drift degree h ordinary op s Z ports
variable (floor w : ℕ)
local notation "ap" => (a) floor
local notation "post" => ports.afterPad k floor
local notation "next" => ports.priorStart k floor
local notation "pack" => ports.resetPad k
local notation "L" => (ap).inner.successor.setup.retained
local notation "cap" => ((capCalendar G.b S.rounds gain S.height).take age).prod*256
local notation "support" => ScheduledCodeRoom G S board k tail age p f gain drift degree h ordinary op s Z
  ports.operandLanes ports.roleLanes old io next w (post).archive

local notation "raw" => previousArchiveLayout G S board k tail age p f gain drift degree h ordinary op s Z ports floor

local notation "publisher" => priorArchivePhase G S board k tail age p f gain drift degree h ordinary op s Z ports floor w

open DescentOrdinaryHostPad DescentBundleHistory
variable {V : Type} {dimU : ℕ} {bits : V→ℕ} {U : MarkedWorld F dimU V bits}
    {q ε : ℝ} {z D wire hist : ℕ}
local notation "loaded" => ({raw with hosts:=(old).hosts} : DescentResetRetainedSetup.Layout)


open DescentRetainedRangeDigits DescentDatedPriorOperand DescentLocalArchiveOrder DescentKernelHistory
open DescentGL DescentColonies DescentPackedColony DescentSixParty.PackedFlow.Channels
variable (data : Fin (pack).dataRect.pages→Fin ports.operandHosts→Fin (old).groups→Cell (ports.operandBits*ports.nodes))
    (roles : Fin (2^k)→Fin ports.operandHosts→Fin (old).groups→Cell (ports.tokenBits*ports.nodes))
local notation "X" => padValues G S board k tail age p f gain drift degree h ordinary op s Z ports floor data roles
local notation "l" => loaded
variable (size : 2^((l).high+(l).low)=(l).groups*(l).blocks)
    (cut : (l).cut≤(l).high+(l).low) (matrix : DescentGL.Layout ((l).high+(l).low))
    (carrier : Fin (l).hosts) (hi : Block (l).cut) (d₀ : Fin (l).donors)
local notation "physical" => (l).site (fun j=>blockValues cut ((l).before size (X) j) matrix) carrier hi
local notation "src_" => (rearrange matrix).symm (DescentIssuedFallbackPanel.join cut hi d₀)
local notation "coords" => (finProdFinEquiv.symm (Fin.cast size src_) : Fin (l).groups × Fin (l).blocks)
local notation "prior" => ({(l).previousLayout with hosts:=ports.operandHosts} : DescentDatedPriorOperand.Layout)

variable (r₀ : Reached U G q ε S k age z D wire hist) (B : BitDescription U) (number : Local B)

open DescentPrimitivePalette DescentBundleHistory
variable {bound : ℕ} (room : DatePorts.RangeRoom ports r₀ B)
variable (spec : WorldShape p bound B) (label : NodeOrder.All B→Label G s Z op)
  (pointer : NodeOrder.All B→ℕ→DescentOperandStateBanks.Pointer)
  (flags : Fin (2^(old).k)→Fin ports.nodes→Fin ports.operandHosts→Fin (old).groups→ℕ)
  (mem : Memory w) (archive : DatePorts.ArchiveRead ports r₀ B number room spec op label pointer flags mem)
  (vertex_ : U.graph.Site) (node : (B.recipe vertex_).Node)
local notation "address_" => Reached.NodeCells.coordinate r₀ vertex_
local notation "block_" => (coords).2.cast (congrArg (2^·) room.radix)
local notation "host_" => (⟨(address_).1.val,room.hosts vertex_⟩ : Fin ports.operandHosts)
local notation "index_" => (number vertex_ node).castLE (room.capacity vertex_)
local notation "y_" => (⟨vertex_,node⟩ : NodeOrder.All B)
local notation "arity_" => (occurrences (spec.sites vertex_) node).length
variable (same : carrier.val=(address_).1.val ∧ (coords).1.val=(address_).2.1.val ∧ (coords).2.val=(address_).2.2.val)
variable (width : ports.operandBits*ports.nodes*ports.operandLanes≤w)
local notation "read_" f₀:arg j:arg => Reads (previousBank ports.rangeLayout ports.archive.arguments block_
    (DescentOperandStateBanks.page f₀ j)) (data ((l).sourceID ((l).operandField f₀ j) (coords).2)) ports.operandLanes mem

private theorem found_donor (block : Fin (2^(old).k)) (g₀ : Fin (old).groups)
    (atBlock : block.val=(address_).2.2.val) (atGroup : g₀.val=(address_).2.1.val) :
    DatePorts.slotAt ports r₀ B number room block index_ host_ g₀=some y_ :=by
  have blockEq : block=(address_).2.2.cast (congrArg (2^·) room.radix):=Fin.ext atBlock
  have groupEq : g₀=(address_).2.1.cast room.groups:=Fin.ext atGroup
  rw [blockEq,groupEq]
  exact DatePorts.slotAt_original ports r₀ B number room vertex_ node

include archive same width in
/-- At any true donor the public pointer fields are the previous registered header of
this same argument, including arguments at unpaid vertices. -/
theorem calendar_header_words (j : Fin ports.argumentsPerNode) (f₀ : Fin 4)
    (paid : read_ (f₀.castLE (by decide : 4≤7)) j) (live : j.val<arity_) :
    ((l).entry physical d₀ index_ ((l).operandField (f₀.castLE (by decide : 4≤7)) j)).val=
      (pointer y_ j.val).header f₀ :=by
  have found : DatePorts.slotAt ports r₀ B number room block_ index_ host_ (coords).1=some y_ :=by
    exact found_donor (room:=room) (number:=number) (vertex_:=vertex_) (node:=node)
      (atBlock:=same.2.2) (atGroup:=same.2.1)
  obtain ⟨cells,written,correct⟩:=archive.headers block_ j f₀
  refine (scheduled_original_seven G S board k tail age p f gain drift degree h ordinary op s Z ports floor
    data roles size cut matrix carrier hi d₀ (f₀.castLE (by decide : 4≤7)) j host_ same.1 index_).trans ?_
  rw [paid.determined written room.positive width]
  exact correct host_ (coords).1 index_ y_ found live

include archive same width in
/-- The same chronological previous root emits start, stride or count for each of
its flattened arguments. The count word is also zero throughout the padded tail. -/
theorem calendar_range_words (j : Fin ports.argumentsPerNode) (f₀ : Fin 3)
    (paid : read_ (DescentRetainedRangeDigits.page f₀) j) (live : j.val<arity_ ∨ f₀=2) :
    ((l).entry physical d₀ index_ ((l).operandField (DescentRetainedRangeDigits.page f₀) j)).val=
      atSlot (spec.sites vertex_) node j.val f₀ :=by
  have found : DatePorts.slotAt ports r₀ B number room block_ index_ host_ (coords).1=some y_ :=by
    exact found_donor (room:=room) (number:=number) (vertex_:=vertex_) (node:=node)
      (atBlock:=same.2.2) (atGroup:=same.2.1)
  obtain ⟨cells,written,correct⟩:=archive.spans block_ j f₀
  refine (scheduled_original_seven G S board k tail age p f gain drift degree h ordinary op s Z ports floor
    data roles size cut matrix carrier hi d₀ (DescentRetainedRangeDigits.page f₀) j host_ same.1 index_).trans ?_
  rw [paid.determined written room.positive width]
  exact correct host_ (coords).1 index_ y_ found live

include archive same width in
theorem calendar_arity_words (hp : 0<p)
    (paid : Reads (DatePorts.metadataPage ports 1 block_) (data (ports.arityIndex k (coords).2)) ports.operandLanes mem)
    (fitsArg : arity_<2^ports.operandBits) :
    ((l).entry physical d₀ index_ (l).arityField).val=((spec.sites vertex_).recipe hp).arity node :=by
  have found : DatePorts.slotAt ports r₀ B number room block_ index_ host_ (coords).1=some y_ :=by
    exact found_donor (room:=room) (number:=number) (vertex_:=vertex_) (node:=node)
      (atBlock:=same.2.2) (atGroup:=same.2.1)
  let amount:=fun h' g' n'=>(DatePorts.slotAt ports r₀ B number room block_ n' h' g').elim 0
    (fun y=>(occurrences (spec.sites y.1) y.2).length)
  have measured : amount host_ (coords).1 index_=arity_:=by simp only [amount,found]; rfl
  have arityPage : Reads (DatePorts.metadataPage ports 1 block_) (fun h₀ g₀ => encode ports.operandBits ports.nodes
      (fun j => (amount h₀ g₀ j : Cell ports.operandBits))) ports.operandLanes mem := by
    convert archive.arity block_ using 1
    funext h₀ g₀
    apply congrArg (encode ports.operandBits ports.nodes)
    funext j
    dsimp only [amount]
    cases DatePorts.slotAt ports r₀ B number room block_ j h₀ g₀ <;> rfl
  have issued:=scheduled_original_arity G S board k tail age p f gain drift degree h ordinary op s Z ports floor w
    data roles size cut matrix carrier hi d₀ (DatePorts.metadataPage ports 1 block_) mem room.positive amount
    paid arityPage width host_ same.1 index_ (measured.trans_lt fitsArg)
  exact issued.trans (measured.trans (DescentRetainedRangeDigits.length _ _ hp))


section SourceFamily
variable {I : Type} (site : I→U.graph.Site) (donors : I→Fin (l).donors)
local notation "row_" u => (finProdFinEquiv.symm (Fin.cast size
  ((rearrange matrix).symm (DescentIssuedFallbackPanel.join cut hi (donors u)))) : Fin (l).groups×Fin (l).blocks)
local notation "book_" u => spec.sites (site u)
local notation "addr_" u => Reached.NodeCells.coordinate r₀ (site u)
local notation "node_" u:arg n:arg => (number (site u) n).castLE (room.capacity (site u))
variable (sameRows : ∀u,carrier.val=(addr_ u).1.val ∧ (row_ u).1.val=(addr_ u).2.1.val ∧
  (row_ u).2.val=(addr_ u).2.2.val)
variable (hp : 0<p) (priorArgs : ∀u n,((book_ u).recipe hp).arity n≤ports.argumentsPerNode)
variable (fits : ports.argumentsPerNode<2^ports.operandBits)
local notation "published_" x => DatePorts.metadataPage ports 1 ((x).cast (congrArg (2^·) room.radix))
local notation "word_" u:arg n:arg field₀:arg => (l).entry physical (donors u) (node_ u n) field₀
variable (arities : ∀x : Fin (l).blocks,Reads (published_ x) (data (ports.arityIndex k x)) ports.operandLanes mem)
variable (operands : ∀(f₀:Fin 7)(j:Fin ports.argumentsPerNode)(x:Fin (l).blocks),
  Reads (previousBank ports.rangeLayout ports.archive.arguments (x.cast (congrArg (2^·) room.radix))
    (DescentOperandStateBanks.page f₀ j)) (data ((l).sourceID ((l).operandField f₀ j) x)) ports.operandLanes mem)

include archive sameRows width arities operands fits in
/-- For a complete family of geometric donors, read all previous arities, private or public
pointer headers, and all three range digits from the same native padded owner board. -/
theorem calendar_fibre_headers :
    (∀u n,(word_ u n ((l).arityField)).val=((book_ u).recipe hp).arity n) ∧
    (∀u n (j : Fin (((book_ u).recipe hp).arity n)) (f₀ : Fin 4),
      (word_ u n ((l).operandField (f₀.castLE (by decide : 4≤7)) (j.castLE (priorArgs u n)))).val=
        (pointer ⟨site u,n⟩ j.val).header f₀) ∧
    (∀u n (j : Fin (((book_ u).recipe hp).arity n)) (f₀ : Fin 3),
      (word_ u n ((l).operandField (DescentRetainedRangeDigits.page f₀) (j.castLE (priorArgs u n)))).val=
        atSlot (book_ u) n j.val f₀):=by
  constructor
  · intro u n
    exact calendar_arity_words (archive:=archive) (same:=sameRows u) (width:=width)
      (data:=data) (roles:=roles) (matrix:=matrix) (d₀:=donors u) (node:=n)
      (hp:=hp) (paid:=arities (row_ u).2) (fitsArg:=by rw [DescentRetainedRangeDigits.length _ _ hp];exact (priorArgs u n).trans_lt fits)
  constructor
  · intro u n j f₀
    apply calendar_header_words (archive:=archive) (same:=sameRows u) (width:=width)
      (data:=data) (roles:=roles) (matrix:=matrix) (d₀:=donors u) (node:=n)
    · exact operands _ _ _
    · exact j.isLt.trans_eq (DescentRetainedRangeDigits.length (spec.sites (site u)) n hp).symm
  · intro u n j f₀
    apply calendar_range_words (archive:=archive) (same:=sameRows u) (width:=width)
      (data:=data) (roles:=roles) (matrix:=matrix) (d₀:=donors u) (node:=n)
    · exact operands _ _ _
    · exact Or.inl (by exact j.isLt.trans_eq (DescentRetainedRangeDigits.length (spec.sites (site u)) n hp).symm)

end SourceFamily

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI
