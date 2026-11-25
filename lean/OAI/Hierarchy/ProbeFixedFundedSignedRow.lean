import OAI.Hierarchy.ProbeFixedFundedSignedParty
import OAI.Hierarchy.ProbeFixedFundedOccupiedRows
import OAI.Hierarchy.ProbeFixedWideSignedRowRead
import OAI.Hierarchy.ProbeFixedWideSignedControlFields

namespace OAI
/-! # Matrix of the entire selected ballot row, including every vacant site -/
noncomputable section
set_option quotPrecheck false
set_option maxRecDepth 8192
set_option maxHeartbeats 2300000
set_option backward.isDefEq.respectTransparency false
set_option cleanup.letToHave false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CoreRoute ReportSockets
open CatalystArchive StripChart CatalogueRows ColumnWires BoughtSockets
open WireTelescope Tagged ThreeFlat.RAM
open scoped Classical Fin.CommRing
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
  (h width : ℕ)
local notation "P" => v.widePlacement h width
local notation "boards" => v.nativeBoards P h width
local notation "A" => v.privateArena P h width
local notation "E" => v.publicHeader P h width
local notation "D" => 2^v.W
local notation "N" => Stages h D
local notation "r" => Fintype.card (Slots h D k)
local notation "num" => Fintype.card (Columns h D)*k
local notation "w" => Native.wordBits h D Native.copies
local notation "start" => v.catalystStaticStart P h width
local notation "decl" => declaredRows v.mesh (ownerLedger boards v.mesh (P).catalogue (P).routes F A)
local notation "cnt" => rowOnlyCount v.mesh decl
local notation "stride" => ownerRowFactor D k v.sampler.degree v.depth
  (max (Fintype.card (PayloadRole N k)) (Fintype.card (PurchasedRole v.depth k)))*2^h


local notation "page" => v.wideSignedPage h width
local notation "owners" => sinkBank start cnt r (P).catalogue.rows


local notation "stock" => v.fixedTerminalStock P h width
local notation "bits" => page stock
local notation "banks" => TerminalLayout.settlement bits stock
local notation "source" => TerminalLayout.source bits
local notation "table" => TerminalLayout.table bits
local notation "target" => TerminalLayout.destination bits
local notation "C" => v.wideSignedChart h width stock
local notation "g" => v.stamp P h width r banks source table target owners
local notation "order" => wideRouteOrder h D k


variable (size : ℕ) (extent : (v.privateArena (v.widePlacement h width) h width).endAddress v.mesh ≤ size) (M : ℕ) (π : Equiv.Perm (Fin (2^h)))
  (seed : Boot.Tape h (2^v.W)) (age : v.wideStockHeight≤h) (budget : v.keepLimit*width+1≤2^h) (small : width≤2^h)
local notation "reader" => v.wideSelector h width age budget small
local notation "es" => events v.mesh
local notation "L" => (reader).format.windows
local notation "mid" => v.wideSignedMidAt h width size stock M π order

local notation "funded" => v.wideFundedRaw h width v.maxBits seed
local notation "original" => v.wideSignedWords h width stock v.radius π.symm order funded
local notation "V" => v.catalystMarkets P h width
local notation "dims" => v.wide_stock_sizes h width age budget small
local notation "base" => v.wideOrigin h width size seed π
local notation "origin" b:arg => v.wideOrigin h width size ((L).header es b seed) π
local notation "slots" => (reader).format.slot
local notation "auth" => v.wide_signed_words_authentic h width stock v.radius π.symm order funded
local notation "heap" => (v.wideGeometryPrefix h width).2.1

open StripDirectory
local notation "slab" => v.slab (v.seed P h width) P width

open LinearAlgebra.SpectralBooks ChordGraph SiteTensor
open ThreeFlat.Diagonal.MotifOuterTerms
open WireTelescope.ChosenPackets WireTelescope.PacketTurns

open WideCPU

namespace FundedDate
variable {v h width size π seed age budget small} {a : Attempt} {tail x}
    {t : CalendarTape.Prefix (v.wideSelector h width age budget small).format.slot (events v.mesh)
      (v.wideOrigin h width size seed π) (.attempt a::tail) x} {c c' : ((v.wideSelector h width age budget small).format.slot (.attempt a)).choice x}
    (H : v.FundedDate h width size π seed age budget small t c)
    (H' : v.FundedDate h width size π seed age budget small t c')
local notation "initial" => origin H'.code
local notation "entry" => run C H'.prior initial
local notation "checkout" => checkedOut C ((A).endAddress v.mesh) initial
local notation "batch" => PurchaseStage.enabledBatch ((C).layout a) (repair C a)
local notation "snap" => HistogramShelf.snapshot C a x
local notation "fmt" => (reader).format
local notation "sig" => (catalogue F (v.configured (v.seed P h width)) v.cost).alphabet
local notation "root" => v.wideBallotRoot h a
local notation "K" => siteLast h D k+1
local notation "names" => (siteNumber h D k).toEmbedding
local notation "shape" => CatalogueRows.installedRows π.symm
  ((P).catalogue.physicalEnds (π:=π.symm)
    (marks:=v.birthMarks P h width r banks source table target owners (origin H.code)) (P).routes.directory
    (v.wideOrder h width) rfl) names (publicChord h D k)


local notation "I" => Fin ((C).layout a).candidates
local notation "J" => Fin (v.wideBallotParties h a)
local notation "picked" i:arg => (batch).selected snap ((i : I).val:Word w)
local notation "ballots" => {i : I // picked i} × J
variable (extent : (v.privateArena (v.widePlacement h width) h width).endAddress v.mesh ≤ size) (tall : v.ballotHeight≤h) (floor : v.widthFloor≤width)
local notation "chosen" u:arg => H.packetAt extent tall floor (u : ballots).1.val (u : ballots).1.property
local notation "atSite" => H.occupiedBallots extent tall floor
local notation "sh" => v.widePacketShape h width (.attempt a)
local notation "orig" => v.wideBallotRows h width r banks source table target owners a (entryMemory C initial a)
local notation "old" => (v.wideBallotShape P h width (.attempt a)).columns
local notation "extra" => ((v.widePacketRoles h*3)*5+(v.widePacketDegree+v.widePacketDegree))
local notation "middle" => PacketTurns.middleColumns (v.widePacketRoles h)
local notation "tagColumn" => ((((0 : Fin (sig+2)).castAdd extra).castAdd (v.wideBallotParties h a)).castAdd middle)
variable (selectorBits siteROM : ℕ) (strideBank : Bank) (preStart postStart : ℕ) (processing : Memory (Native.wordBits h (2^v.W) Native.copies))
local notation "fd" => v.widePacketFields h width selectorBits (.attempt a) siteROM strideBank preStart postStart
local notation "rawWords" => fun (u : ballots) (c : Fin (sh).columns)=>((fd).value u.2 c).eval processing (u.1.val.val:Word w)
private abbrev signedCheckoutWords := checkout

variable (arch : PrefixAgreement.Low ((v.privateArena (v.widePlacement h width) h width).endAddress v.mesh)
      processing (signedCheckoutWords H'))
    (rom : HistoryRoles.RoleROM.Mounted siteROM (SiteDirectory.table h (2^v.W) k) processing)
    (siteRoom : SiteDirectory.size h (2^v.W) k ≤ 2^(Native.wordBits h (2^v.W) Native.copies))
    (namesFit : siteLast h (2^v.W) k+1 ≤ 2^(Native.wordBits h (2^v.W) Native.copies))
    (codes : 1+v.menuCodes (Stages h (2^v.W)) ≤ 2^(Native.wordBits h (2^v.W) Native.copies))
    (tags : v.menuCodes (Stages h (2^v.W))*v.wideBallotParties h a+1 ≤ 2^(Native.wordBits h (2^v.W) Native.copies))

open LinearAlgebra.SpectralBooks SiteTensor ChordGraph
open WideControlJoin WideStack WireTelescope.PassMatrix SiteControls
open ThreeFlat.Routing
open WireTelescope.PacketNeighbor WireTelescope.PassMatrix.PartyPins HistoryRoles
open scoped BigOperators
variable {Ex Sel Data : Type} [Fintype Ex] [Fintype Sel] [Fintype Data]
    (unitCost ell : ℕ) (gate : Gate) (gateWidth : gate.W=Native.wordBits h (2^v.W) Native.copies)
local notation "g₀" => v.wideDated h width ell unitCost
local notation "deg" => v.widePacketDegree
local notation "cap" => v.wideNeighborCap width unitCost
local notation "p₀" => v.partyRoleBits h
local notation "e₀" => v.partyLaneBits h width a unitCost
variable (work : ℕ) (date : Fin (events v.mesh).length) (onDate : (events v.mesh).get date=.attempt a) (s : Fin (siteLast h (2^v.W) k+1))
    (wire : Bool→Fin v.widePacketDegree→Fin (v.wideNeighborCap width unitCost)→SitePins Ex Sel Data gate⊕Bool)
    (out : Memory gate.W) (ext : Ex→Bool) (sel : Sel→Bool) (data : Data→Bool)
local notation "seen" => Sum.elim ext (Sum.elim sel (Sum.elim data (gate.terminal out)))
local notation "fetch" => ballotWord (Ex:=Ex) (Sel:=Sel) («D»:=Data) gate g₀ work date s
local notation "atControl" f:arg => (out (controlAddress g₀ work date s f)).val
local notation "sqrt" => v.wideNeighborDigits width unitCost
local notation "dmd" => fun l=>(H.row extent tall floor l).input
local notation "M" => fun l=>(H.tender extent tall floor l).entry
local notation "supply" => fun l=>(H.tender extent tall floor l).post
variable (rest : Widths (siteLast h (2^v.W) k+1))
local notation "before" => ∑l,dmd l
local notation "after" => ∑l,supply l (c' l)
local notation "port" => (portGraph K).Port s
local notation "pass" => fun q:port=>rest q.val.1
local notation "want" => fun q:port=>before q.val.1
local notation "earned" => fun q:port=>after q.val.1
variable (x₀ : State (rest+(∑ z,(H.row extent tall floor z).input)) s) (y₀ : State (rest+(∑ z,(H.tender extent tall floor z).post (c' z))) s)
    (l : PassiveWindow.Parts ((portGraph (siteLast h (2^v.W) k+1)).Port s) (Fin v.widePacketDegree) (v.wideNeighborCap width unitCost) (fun edge=>(rest+(∑ z,(H.row extent tall floor z).input)) edge.val.1))
    (r' : PassiveWindow.Parts ((portGraph (siteLast h (2^v.W) k+1)).Port s) (Fin v.widePacketDegree) (v.wideNeighborCap width unitCost) (fun edge=>(rest+(∑ z,(H.tender extent tall floor z).post (c' z))) edge.val.1))

local notation "loc" => H.occupiedBallots extent tall floor
local notation "pre" => Function.uncurry (ChordAperture.canonical l (fun p d=>(x₀ p).val.testBit d))
local notation "post" => Function.uncurry (ChordAperture.canonical r' (fun p d=>(y₀ p).val.testBit d))
local notation "addr" j:arg => ballotAddress g₀ work date s j
local notation "shelf" site_:arg base_:arg f:arg => pageRead (DatedRoleSheets.bank (v.widePacketPhysical h width)
  base_ (v.widePacketShelf h) selectorBits f) strideBank site_ (d:=deg)
local notation "physical" u:arg => v.wideBallotSite P h width siteROM a (u:ballots).2
variable (dense : ∀i:Fin gate.u,(gate.addr i).val=i.val)
    (inside : ∀f:SiteControls.Field v.widePacketDegree,controlAddress (v.wideDated h width ell unitCost) work date s f<gate.u)
    (mode : ballotAddress (v.wideDated h width ell unitCost) work date s 0<gate.u) {tagBits : ℕ} (tagFit : v.signedPartyCount h a+1≤2^tagBits)
    (tagSmall : tagBits≤gate.W+1) (laneSmall : v.wideNeighborDigits width unitCost≤gate.W+1)

private theorem scatter_value_transfer {ι : Type} {sitesCount cols wordBits gateBits : ℕ}
    (place : ι ↪ Fin sitesCount) (stored : ι → Fin cols → Word wordBits)
    (lifted : ι → Fin cols → Word gateBits)
    (agree : ∀ i f, (stored i f).val = (lifted i f).val) (s : Fin sitesCount) (f : Fin cols) :
    (SiteScatter.table place stored s f).val = (SiteScatter.table place lifted s f).val := by
  by_cases hs : s ∈ Set.range place
  · obtain ⟨u,rfl⟩ := hs
    rw [SiteScatter.active,SiteScatter.active]
    exact agree u f
  · rw [SiteScatter.idle place stored s f hs,SiteScatter.idle place lifted s f hs]
    rfl

private theorem scatter_at_site {ι : Type} {sitesCount cols wordBits : ℕ}
    (place : ι ↪ Fin sitesCount) (stored : ι → Fin cols → Word wordBits)
    (s : Fin sitesCount) (i : ι) (located : place i = s) (f : Fin cols) :
    (SiteScatter.table place stored s f).val = (stored i f).val := by
  cases located
  exact congrArg Fin.val (SiteScatter.active place stored i f)

attribute [local irreducible] FundedDate.packetAt wideStockHeight widePlacement wideSignedWords
  siteNumber permutationFabric ProbeStage.rounds ElectedSource.site TypedWiring.value signedRow signedPartyAt
  widePacketFields DatedRoleSheets.bank

include gateWidth dense arch rom siteRoom namesFit codes tags in
theorem signed_row_entry (word : v.PartyWordBounds h width unitCost)
    (rowsFit : Fintype.card (Commodity (Fin (2^h)) N k)+(P).catalogue.rows≤2^w)
    (degreeFit : deg<2^w) (addressFit : ∀f:Fin (sh).columns,addr (f).val<gate.u)
    (written : ∀f:Fin (sh).columns,(out (addr (f).val)).val=(SiteScatter.table loc rawWords s f).val)
    (beforeFit : ∀p:port,(rest+before) p.val.1≤cap)
    (afterFit : ∀e,(rest+after) e≤cap)
    (roomL : ∀i,ChordAperture.room l i<cap) (roomR : ∀i,ChordAperture.room r' i<cap)
    (ctrl : ∀f,atControl f=expected pass want earned l r' f)
    (sourceBits : ∀i p,l.owner i=some p→∀q:Fin (l.width i),
      Sum.elim seen id (wire false i (q.castLE (l.within i)))=(x₀ p).val.testBit (l.base i+q.val))
    (targetBits : ∀i p,r'.owner i=some p→∀q:Fin (r'.width i),
      Sum.elim seen id (wire true i (q.castLE (r'.within i)))=(y₀ p).val.testBit (r'.base i+q.val))
    (preNbr : ∀u:ballots,loc u=s→NeighborReads processing (u.1.val.val:Word w) l
      (shelf (physical u) preStart 0) (shelf (physical u) preStart 2))
    (postNbr : ∀u:ballots,loc u=s→NeighborReads processing (u.1.val.val:Word w) r'
      (shelf (physical u) postStart 0) (shelf (physical u) postStart 2)) :
    TypedWiring.value (F:=F) («P»:=SitePins Ex Sel Data gate) (v.signedRow h width unitCost a gate g₀ work date s wire inside mode tagFit tagSmall laneSmall) seen=
      matrix M rest c' s x₀ y₀ := by
  let transfer : Word w→Word gate.W:=fun n=>⟨n.val,by rw [gateWidth];exact n.isLt⟩
  let ws:=fun (u:ballots) (f:Fin (sh).columns)=>transfer (rawWords u f)
  have tagAt (u:ballots) : (ws u tagColumn).val=(v.partyIndex h a (chosen u).atom u.2).val+1 :=
    H.occupied_tag H' extent tall floor selectorBits siteROM strideBank preStart postStart processing arch rom
      siteRoom codes tags u
  have tagWord : out (addr 0)=SiteScatter.table loc ws s tagColumn := by
    exact Fin.ext ((written tagColumn).trans (scatter_value_transfer loc rawWords ws (fun _ _=>rfl) s tagColumn))
  have readAt (u : ballots) (here : loc u = s) (f : Fin (sh).columns) (bit : ℕ) :
      Sum.elim seen id (fetch f.val bit) = ((rawWords u f).val.testBit bit) :=
    (ballotWord_read gate g₀ work date s out ext sel data dense f.val bit (addressFit f)).trans
      (congrArg (fun n : ℕ => n.testBit bit)
        ((written f).trans (scatter_at_site loc rawWords s u here f)))
  apply v.signedRow_value h width unitCost a gate g₀ work date s wire out ext sel data dense inside laneSmall
    dmd supply M rest c' x₀ y₀ l r' loc (fun u=>u.1.val) (fun u=>(chosen u).atom) Prod.snd
    mode tagFit tagSmall ws tagColumn tagAt tagWord
  · intro b p;cases b <;>first | exact beforeFit p | exact afterFit p.val.1
  · intro b i;cases b <;>first | exact roomL i | exact roomR i
  · intro b i q;cases b <;>exact ctrl _
  · intro b i endp;cases b <;>exact ctrl _
  · intro b i;cases b <;>exact ctrl _
  · exact sourceBits
  · exact targetBits
  · intro i q;exact ctrl _
  · intro i q b;cases b <;>exact ctrl _
  · intro u hu
    obtain ⟨⟨i,hit⟩,j⟩:=u
    have partyEq:=(H.packetAt extent tall floor i hit).installed.placed_site
      (H.packetAt extent tall floor i hit).atom root j
    let j' := j.cast ((H.packetAt extent tall floor i hit).installed.parties (H.packetAt extent tall floor i hit).atom root).symm
    have located : ((H.packetAt extent tall floor i hit).menu root).place j'=s:=partyEq.trans hu
    cases located
    exact FundedDate.signed_party_entry (v:=v) (h:=h) (width:=width) (size:=size) (π:=π) (seed:=seed)
      (age:=age) (budget:=budget) (small:=small) (a:=a) (tail:=tail) (x:=x) (t:=t) (c:=c) (c':=c')
      («V»:=SitePins Ex Sel Data gate) H extent tall floor i hit H' unitCost siteROM selectorBits strideBank preStart postStart
      processing j' seen (ballotWord (Ex:=Ex) (Sel:=Sel) («D»:=Data) gate g₀ work date
        (((H.packetAt extent tall floor i hit).menu root).place j'))
      rest x₀ y₀ l r' arch rom siteRoom namesFit rowsFit degreeFit codes tags word beforeFit afterFit
      (preNbr (⟨i,hit⟩,j) hu) (postNbr (⟨i,hit⟩,j) hu) (readAt (⟨i,hit⟩,j) hu)
  · intro i off
    exact (H.vacant extent tall floor _ i off (c' i)).2.2 _ _

end FundedDate
end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
