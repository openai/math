import OAI.Hierarchy.DescentTerminalIssuedCountChannel
import OAI.Hierarchy.DescentTerminalPrivateSourceChannels
import OAI.Hierarchy.DescentTerminalIssuedWidths

namespace OAI
/-! # Issuing private counts and widths into the same reached memory -/
namespace Hierarchy.DescentTerminalCountWidthPair
open DescentTerminalVertexFields DescentTerminalChronologicalBooks DescentKernelHistory
open DescentTerminalSiteShelves DescentTerminalRecipeRows DescentTerminalIssuedPrivateCount
open DescentSIMDLookup Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false

section Programs
variable {d q hid N A p blocks groups shops wb : ℕ}
    (source:Fin 3→Bank) (base out:ℕ) (m:Memory wb)
local notation "nRows" => blocks*shops
local notation "price" => DescentTerminalPointerFrame.size 3 d

def countProgram (wb d q hid N A groups blocks shops base:ℕ) (source:Fin 3→Bank) :=
  DescentTerminalPointerFrame.program wb base source (blocks*shops) (panel (d:=d) q hid N A groups)
def program (wb d q hid N A groups blocks shops p base out:ℕ) (source:Fin 3→Bank) :=
  (countProgram wb d q hid N A groups blocks shops base source).seq
    (DescentTerminalIssuedWidths.program wb out blocks shops hid groups p)

def counted (d q hid N A groups blocks shops base:ℕ) (source:Fin 3→Bank) (m:Memory wb) :=
  DescentTerminalPointerFrame.result base source (blocks*shops) (panel (d:=d) q hid N A groups) m
def final (d q hid N A groups blocks shops p base out:ℕ) (source:Fin 3→Bank) (m:Memory wb) :=
  DescentTerminalIssuedWidths.final out blocks shops hid groups p (counted d q hid N A groups blocks shops base source m)
def clocks (d blocks shops:ℕ) := ((4+10*DescentTerminalPointerFrame.size 3 d)+(4+(blocks*shops)*(16+26*3)))+(4+(blocks*shops)*6)

variable (ok : DescentTerminalPointerFrame.Room source base d (blocks*shops) wb)
    (apart : base + DescentTerminalPointerFrame.size 3 d + blocks*shops ≤ out)
    (room : out + blocks*shops < 2^wb)
local notation "warm" => counted d q hid N A groups blocks shops base source m
local notation "done" => final d q hid N A groups blocks shops p base out source m

include ok apart room in
theorem run :
    (program wb d q hid N A groups blocks shops p base out source).Exec m done (clocks d blocks shops) ∧
    CheapCode (program wb d q hid N A groups blocks shops p base out source) ∧
    ∀a,a<base ∨ out+nRows≤a→done a=m a := by
  obtain ⟨runCount,cheapCount,keepCount⟩ :=
    DescentTerminalPointerFrame.run base source (panel (d:=d) q hid N A groups) m ok
  obtain ⟨runWidths,cheapWidths,_,keepWidths⟩ :=
    DescentTerminalIssuedWidths.issued out blocks shops hid groups p warm room
  let countCode := countProgram wb d q hid N A groups blocks shops base source
  let widthCode := DescentTerminalIssuedWidths.program wb out blocks shops hid groups p
  refine ⟨@Procedure.Exec.then wb countCode widthCode m warm done
    ((4+10*price)+(4+nRows*(16+26*3))) (4+nRows*6) (@runCount) (@runWidths),
    @cheap_seq wb countCode widthCode (@cheapCount) (@cheapWidths), ?_⟩
  intro a away
  exact (keepWidths a (by rcases away with lo|hi <;> omega)).trans
    (keepCount a (by rcases away with lo|hi <;> omega))
end Programs

/-- Equality of one underlying bank word suffices for any primitive in that family. -/
theorem venue_same {q t hid N A p wb blocks groups shops:ℕ} (L:MaskedShelf blocks) (before after:Memory wb)
    (b:Fin blocks) (i:Fin shops) (g:Fin groups) (k:Key hid N A)
    (equal:(L.channel (finProdFinEquiv (b,(group k).succ))).read after (i.val:Computability.VPVNP.BurstRAM.Word wb)=
      (L.channel (finProdFinEquiv (b,(group k).succ))).read before (i.val:Computability.VPVNP.BurstRAM.Word wb)) :
    venueField (cellAt (measured (q:=q) (t:=t) (H:=hid) (N:=N) (A:=A) (w:=p) (groups:=groups) L after i)
      (finProdFinEquiv (g,b))) k=
    venueField (cellAt (measured (q:=q) (t:=t) (H:=hid) (N:=N) (A:=A) (w:=p) (groups:=groups) L before i)
      (finProdFinEquiv (g,b))) k := by
  simp only [venue_digit,cell_digit,measured,equal]

/-- Casts and wrapped bank indices stay inside their allocated interval. -/
theorem bank_before {w:ℕ} (before after:Memory w) (limit:ℕ) (frame:∀a,a<limit→after a=before a)
    (bank:Bank) (early:bank.base+bank.size≤limit) (u:Computability.VPVNP.BurstRAM.Word w) : bank.read after u=bank.read before u := by
  have short:=Nat.mod_lt u.val (show 0<bank.size from Nat.two_pow_pos _)
  exact frame (bank.base+u.val%bank.size) (by omega)

private abbrev pairedRow {blocks shops groups wb : ℕ} (q t hid N A p : ℕ)
    (channels : MaskAllocation.Channels blocks) (maskBase : ℕ)
    (b : Fin blocks) (i : Fin shops) (g : Fin groups) (mem : Memory wb)
    (k : Key hid N A) : ℕ :=
  venueField (cellAt (measured (q:=q) (t:=t) (H:=hid) (N:=N) (A:=A) (w:=p)
    (groups:=groups) (MaskAllocation.shelf (q:=q) (t:=t) (H:=hid) (N:=N) (A:=A)
      (p:=p) (groups:=groups) channels maskBase) mem i) (finProdFinEquiv (g,b))) k

private theorem paired_frame {q t hid N A p d blocks shops groups wb : ℕ}
    (source : Fin 3 → Bank) (channels : MaskAllocation.Channels blocks)
    (base out maskBase : ℕ) (b : Fin blocks) (i : Fin shops) (g : Fin groups)
    (initial countedMem finalMem : Memory wb)
    (ok : DescentTerminalPointerFrame.Room source base d (blocks*shops) wb)
    (apart : base + DescentTerminalPointerFrame.size 3 d + blocks*shops ≤ out)
    (countBase : (channels.primitive b 2).base =
      base + DescentTerminalPointerFrame.size 3 d + b.val*shops)
    (countSize : shops ≤ (channels.primitive b 2).size)
    (low : ∀ x, x < base → finalMem x = initial x)
    (widthLow : ∀ x, x < out → finalMem x = countedMem x) :
    let read := pairedRow (wb:=wb) q t hid N A p channels maskBase b i g
    read finalMem hiddenCount = read countedMem hiddenCount ∧
    (∀ k, (channels.primitive b (group k)).base + (channels.primitive b (group k)).size ≤ base →
      read finalMem k = read initial k) ∧
    (∀ f u, (source f).read finalMem u = (source f).read initial u) := by
  let shelf := MaskAllocation.shelf (q:=q) (t:=t) (H:=hid) (N:=N) (A:=A) (p:=p)
    (groups:=groups) channels maskBase
  refine ⟨?_, ?_, fun f u => bank_before initial finalMem base low (source f) (ok.source f).2.2 u⟩
  · have iw := i.isLt.trans_le (DescentTerminalPrivateSourceChannels.host_room source ok b)
    have offset : b.val*shops+i.val < blocks*shops := by
      have index := (finProdFinEquiv (b,i)).isLt
      change i.val + shops*b.val < blocks*shops at index
      calc
        b.val*shops+i.val = i.val+shops*b.val := by ac_rfl
        _ < blocks*shops := index
    have live : base + DescentTerminalPointerFrame.size 3 d + b.val*shops + i.val < out := by omega
    have bankRead : (channels.primitive b 2).read finalMem (i.val:Computability.VPVNP.BurstRAM.Word wb) =
        (channels.primitive b 2).read countedMem (i.val:Computability.VPVNP.BurstRAM.Word wb) := by
      simp only [Bank.read, Fin.val_cast_of_lt iw, Nat.mod_eq_of_lt (i.isLt.trans_le countSize), countBase]
      exact widthLow _ live
    apply venue_same (q:=q) (t:=t) (hid:=hid) (N:=N) (A:=A) (p:=p)
      shelf countedMem finalMem b i g hiddenCount
    have keyGroup : group (hiddenCount : Key hid N A) = (2 : Fin 8) := rfl
    simpa only [shelf, MaskAllocation.shelf, MaskAllocation.Channels.primitive_at, keyGroup] using bankRead
  · intro k early
    apply venue_same (q:=q) (t:=t) (hid:=hid) (N:=N) (A:=A) (p:=p)
      shelf initial finalMem b i g k
    simpa only [shelf, MaskAllocation.shelf, MaskAllocation.Channels.primitive_at] using
      bank_before initial finalMem base low (channels.primitive b (group k)) early
        (i.val:Computability.VPVNP.BurstRAM.Word wb)

section WarmCount
variable {q t hid N A p groups blocks shops wb d : ℕ}
    (st : DescentTerminalRecipeRows.Site)
    (rr : ∀ v : Fin st.nodes, DescentKernelHistory.Recipe (Fin t) (Fin (st.arity v)))
    (bn : DescentTerminalChronologicalBooks.Birth rr)
    (hH : ∀ v, Fintype.card (rr v).Hidden ≤ hid)
    (hN : ∀ v, Fintype.card (rr v).Node ≤ N)
    (hA : ∀ v u, (rr v).arity u ≤ A)
    (hw : ∀ v j, (rr v).width j ≤ p)
    (short : ∀ v, st.arity v ≤ q) (z : Fin st.nodes)
    (source : Fin 3 → Bank) (base maskBase : ℕ)
    (channels : MaskAllocation.Channels blocks) (m : Memory wb)
    (ok : DescentTerminalPointerFrame.Room source base d (blocks*shops) wb)
    (fit : groups * span q t hid N A p ≤ wb)
    (b : Fin blocks) (i : Fin shops) (g : Fin groups)
    (fromBase : ∀ f, (channels.primitive b (DescentTerminalPrivateSourceChannels.family f)).base =
      (source f).base + b.val*shops)
    (fromSize : ∀ f, shops ≤ (channels.primitive b (DescentTerminalPrivateSourceChannels.family f)).size)
    (covers : ∀ f : Fin 3, familySize (q:=q) (t:=t) (H:=hid) (N:=N) (A:=A) (w:=p)
      (DescentTerminalPrivateSourceChannels.family f) * groups ≤ d)
    (countBase : (channels.primitive b 2).base =
      base + DescentTerminalPointerFrame.size 3 d + b.val*shops)
    (countSize : shops ≤ (channels.primitive b 2).size)

local notation "countShelf" => MaskAllocation.shelf (q:=q) (t:=t) (H:=hid) (N:=N) (A:=A)
  (p:=p) (groups:=groups) channels maskBase
local notation "countVenue" mem => cellAt (measured (q:=q) (t:=t) (H:=hid) (N:=N) (A:=A)
  (w:=p) (groups:=groups) countShelf mem i) (finProdFinEquiv (g,b))
local notation "countNode" u => Fin.castLE (hN z) (ordinal (bn.atom z) u)

include hH hw short ok fit fromBase fromSize covers countBase countSize in
private theorem count_at_warm
    (population : venueField (countVenue m) nodeCount = Fintype.card (rr z).Node)
    (lengths : ∀ u, venueField (countVenue m) (nodeArity (countNode u)) = (rr z).arity u)
    (refs : ∀ u (j : Fin ((rr z).arity u)),
      venueField (countVenue m) (nodeArg (countNode u) (j.castLE (hA z u))) =
        ((rr z).operand u j).elim (fun x => x.val + 1) (fun x => q + (ordinal (bn.hidden z) x).val + 1)) :
    venueField (countVenue (counted d q hid N A groups blocks shops base source m)) hiddenCount =
      Fintype.card (rr z).UsedWord := by
  apply DescentTerminalIssuedPrivateCount.channel_count (q:=q) (t:=t) (hid:=hid) (N:=N) (A:=A) (p:=p)
    st rr bn hH hN hA hw short z base maskBase source channels m ok fit b i g countBase countSize
  exact DescentTerminalPrivateSourceChannels.receipts (q:=q) (t:=t) (H:=hid) (N:=N) (A:=A) (p:=p)
    source channels maskBase m b i g fromBase fromSize covers st rr bn hN hA z ok population lengths refs
end WarmCount

/-- Combine the two observed count equalities with the indexed width reads and memory frames. -/
private theorem join_reads {runs cheap unchanged earlier sources : Prop}
    {U I : Type*} {after before live limit width : ℕ}
    (exec : runs ∧ cheap ∧ unchanged) (frame : after = before ∧ earlier ∧ sources)
    (population : before = live) (restricted : live = limit)
    (field : I → ℕ) (number : U → I) (size : U → ℕ)
    (fieldWidth : ∀ i, field i = width) (wordWidth : ∀ u, size u = width) :
    runs ∧ cheap ∧ after = limit ∧ (∀ u, field (number u) = size u) ∧ earlier ∧ sources ∧ unchanged :=
  ⟨exec.1, exec.2.1, frame.1.trans (population.trans restricted),
    fun u => (fieldWidth (number u)).trans (wordWidth u).symm, frame.2.1, frame.2.2, exec.2.2⟩

section Core
variable {q t hid N A blocks shops groups wb d p : ℕ}
    (st : DescentTerminalRecipeRows.Site)
    (rr : ∀ v : Fin st.nodes, Recipe (Fin t) (Fin (st.arity v))) (names : Birth rr)
    (hH : ∀ v, Fintype.card (rr v).Hidden ≤ hid)
    (hN : ∀ v, Fintype.card (rr v).Node ≤ N)
    (hA : ∀ v u, (rr v).arity u ≤ A)
    (widths : ∀ v u, (rr v).width u = p)
    (short : ∀ v, st.arity v ≤ q) (z : Fin st.nodes)
    (used : Fintype.card (rr z).UsedWord = Fintype.card (rr z).Hidden)
    (source:Fin 3→Bank) (base out maskBase:ℕ) (channels:MaskAllocation.Channels blocks) (m:Memory wb)
local notation "nRows" => blocks*shops
local notation "price" => DescentTerminalPointerFrame.size 3 d
local notation "warm" => counted d q hid N A groups blocks shops base source m
local notation "done" => final d q hid N A groups blocks shops p base out source m
local notation "machine" => MaskAllocation.shelf (q:=q) (t:=t) (H:=hid) (N:=N) (A:=A) (p:=p) (groups:=groups) channels maskBase
local notation "meas" => measured (q:=q) (t:=t) (H:=hid) (N:=N) (A:=A) (w:=p) (groups:=groups) machine
variable (ok : DescentTerminalPointerFrame.Room source base d (blocks*shops) wb)
    (apart : base + DescentTerminalPointerFrame.size 3 d + blocks*shops ≤ out)
    (room : out + blocks*shops < 2^wb) (fit:groups*span q t hid N A p≤wb)
    (b:Fin blocks) (i:Fin shops) (g:Fin groups)
    (fromBase:∀f,(channels.primitive b (DescentTerminalPrivateSourceChannels.family f)).base=(source f).base+b.val*shops)
    (fromSize:∀f,shops≤(channels.primitive b (DescentTerminalPrivateSourceChannels.family f)).size)
    (covers : ∀ f : Fin 3, familySize (q:=q) (t:=t) (H:=hid) (N:=N) (A:=A) (w:=p)
      (DescentTerminalPrivateSourceChannels.family f) * groups ≤ d)
    (countBase:(channels.primitive b 2).base=base+DescentTerminalPointerFrame.size 3 d+b.val*shops)
    (countSize:shops≤(channels.primitive b 2).size)
    (widthBase:(channels.primitive b 4).base=out+b.val*shops)
    (widthSize:shops≤(channels.primitive b 4).size)
local notation "position" => finProdFinEquiv (g,b)
local notation "node" => fun u=>(ordinal (names.atom z) u).castLE (hN z)
local notation "hidden" => fun u=>(ordinal (names.hidden z) u).castLE (hH z)
local notation "rowAt" => fun mem k=>venueField (cellAt (meas mem i) position) k

attribute [local irreducible] Procedure.Exec CheapCode program counted DescentTerminalIssuedWidths.final

include ok apart room countBase countSize in
private theorem frame_after :
    rowAt done hiddenCount = rowAt warm hiddenCount ∧
    (∀ k, (channels.primitive b (group k)).base + (channels.primitive b (group k)).size ≤ base →
      rowAt done k = rowAt m k) ∧
    ∀ f u, (source f).read done u = (source f).read m u := by
  have exec := run (q:=q) (hid:=hid) (N:=N) (A:=A) (p:=p) (groups:=groups)
    source base out m ok apart room
  have scan := DescentTerminalIssuedWidths.issued out blocks shops hid groups p warm room
  exact paired_frame (q:=q) (t:=t) (hid:=hid) (N:=N) (A:=A) (p:=p)
    source channels base out maskBase b i g m warm done ok apart countBase countSize
    (fun a ha => exec.2.2 a (.inl ha)) (fun a ha => scan.2.2.2 a (.inl ha))

include room fit widthBase widthSize in
private theorem width_after (j : Fin hid) : rowAt done (hiddenWidth j) = p := by
  apply DescentTerminalIssuedWidths.width_read out warm machine room fit b _ _ i g j
  · simpa only [MaskAllocation.shelf, MaskAllocation.Channels.primitive_at] using widthBase
  · simpa only [MaskAllocation.shelf, MaskAllocation.Channels.primitive_at] using widthSize

attribute [local irreducible] final

set_option maxHeartbeats 1000000 in
include widths short used ok apart room fit fromBase fromSize covers countBase countSize widthBase widthSize in
private theorem issued_core (population:rowAt m nodeCount=Fintype.card (rr z).Node)
    (lengths:∀u,rowAt m (nodeArity (node u))=(rr z).arity u)
    (refs:∀u (j:Fin ((rr z).arity u)),rowAt m (nodeArg (node u) (j.castLE (hA z u)))=
      ((rr z).operand u j).elim (fun x=>x.val+1) (fun x=>q+(ordinal (names.hidden z) x).val+1)) :
    (program wb d q hid N A groups blocks shops p base out source).Exec m done (clocks d blocks shops) ∧
    CheapCode (program wb d q hid N A groups blocks shops p base out source) ∧
    rowAt done hiddenCount=Fintype.card (rr z).Hidden ∧
    (∀j,rowAt done (hiddenWidth (hidden j))=(rr z).width j) ∧
    (∀k,(channels.primitive b (group k)).base+(channels.primitive b (group k)).size≤base → rowAt done k=rowAt m k) ∧
    (∀f u,(source f).read done u=(source f).read m u) ∧
    ∀a,a<base ∨ out+nRows≤a→done a=m a := by
  exact join_reads
    (run (q:=q) (hid:=hid) (N:=N) (A:=A) (p:=p) (groups:=groups) source base out m ok apart room)
    (frame_after (q:=q) (t:=t) (hid:=hid) (N:=N) (A:=A) (p:=p)
      source base out maskBase channels m ok apart room b i g countBase countSize)
    (count_at_warm (q:=q) (t:=t) (hid:=hid) (N:=N) (A:=A) (p:=p)
      st rr names hH hN hA (fun v u => (widths v u).le) short z source base maskBase channels m
      ok fit b i g fromBase fromSize covers countBase countSize population lengths refs)
    used (fun j => rowAt done (hiddenWidth j)) (fun u => hidden u) (rr z).width
    (width_after (q:=q) (t:=t) (hid:=hid) (N:=N) (A:=A) (p:=p)
      source base out maskBase channels m room fit b i g widthBase widthSize) (widths z)
end Core

section Physical
open Computability.BorderVNP.Crossing DescentBundleHistory DescentTerminalGraphPositions
open ThreeFlat.Routing
variable {P U : Type} [Fintype P] {D S p q t hid N A blocks shops groups wb d : ℕ} {bits:P→ℕ}
    (G:Network D P bits) (hp:0<p) (L:Order G S p)
    (r:∀v:G.Site,BitRecipe U (Boundary G v) (boundaryWidth G v))
    (s:∀v,Shape p (r v)) (code:U×List (List SliceCode)→Fin t)
variable (birth : ∀ v : G.Site, ((s v).recipe hp).restricted.Node ↪ ℕ) (host : Fin S)
local notation "rs" => DescentTerminalBundleRows.recipes L
  (fun v => Recipe.restricted (Shape.recipe (hp := hp) (s v))) hp birth code host
local notation "site" => L.site host
variable (names : Birth (DescentTerminalBundleRows.recipes L
      (fun v => Recipe.restricted (Shape.recipe (hp := hp) (s v))) hp birth code host))
    (hH : ∀ z, Fintype.card (DescentTerminalBundleRows.recipes L
      (fun v => Recipe.restricted (Shape.recipe (hp := hp) (s v))) hp birth code host z).Hidden ≤ hid)
    (hN : ∀ z, Fintype.card (DescentTerminalBundleRows.recipes L
      (fun v => Recipe.restricted (Shape.recipe (hp := hp) (s v))) hp birth code host z).Node ≤ N)
    (hA : ∀ z u, (DescentTerminalBundleRows.recipes L
      (fun v => Recipe.restricted (Shape.recipe (hp := hp) (s v))) hp birth code host z).arity u ≤ A)
    (short : ∀ z, (L.site host).arity z ≤ q) (z : Fin (L.site host).nodes)
    (source:Fin 3→Bank) (base out maskBase:ℕ) (channels:MaskAllocation.Channels blocks) (m:Memory wb)
local notation "nRows" => blocks*shops
local notation "price" => DescentTerminalPointerFrame.size 3 d
local notation "warm" => counted d q hid N A groups blocks shops base source m
local notation "done" => final d q hid N A groups blocks shops p base out source m
local notation "machine" => MaskAllocation.shelf (q:=q) (t:=t) (H:=hid) (N:=N) (A:=A) (p:=p) (groups:=groups) channels maskBase
local notation "meas" => measured (q:=q) (t:=t) (H:=hid) (N:=N) (A:=A) (w:=p) (groups:=groups) machine
variable (ok : DescentTerminalPointerFrame.Room source base d (blocks*shops) wb)
    (apart : base + DescentTerminalPointerFrame.size 3 d + blocks*shops ≤ out)
    (room : out + blocks*shops < 2^wb) (fit:groups*span q t hid N A p≤wb)
    (b:Fin blocks) (i:Fin shops) (g:Fin groups)
    (fromBase:∀f,(channels.primitive b (DescentTerminalPrivateSourceChannels.family f)).base=(source f).base+b.val*shops)
    (fromSize:∀f,shops≤(channels.primitive b (DescentTerminalPrivateSourceChannels.family f)).size)
    (covers : ∀ f : Fin 3, familySize (q:=q) (t:=t) (H:=hid) (N:=N) (A:=A) (w:=p)
      (DescentTerminalPrivateSourceChannels.family f) * groups ≤ d)
    (countBase:(channels.primitive b 2).base=base+DescentTerminalPointerFrame.size 3 d+b.val*shops)
    (countSize:shops≤(channels.primitive b 2).size)
    (widthBase:(channels.primitive b 4).base=out+b.val*shops)
    (widthSize:shops≤(channels.primitive b 4).size)
local notation "position" => finProdFinEquiv (g,b)
local notation "node" => fun u=>(ordinal (names.atom z) u).castLE (hN z)
local notation "hidden" => fun u=>(ordinal (names.hidden z) u).castLE (hH z)
local notation "rowAt" => fun mem k=>venueField (cellAt (meas mem i) position) k

attribute [local irreducible] DescentTerminalBundleRows.recipes

set_option maxHeartbeats 2000000 in
include short ok apart room fit fromBase fromSize covers countBase countSize widthBase widthSize in
/-- The new count and every actual private width coexist in one final memory. All
previous source banks and earlier primitive families retain their readings. -/
theorem issued (population:rowAt m nodeCount=Fintype.card (rs z).Node)
    (lengths:∀u,rowAt m (nodeArity (node u))=(rs z).arity u)
    (refs:∀u (j:Fin ((rs z).arity u)),rowAt m (nodeArg (node u) (j.castLE (hA z u)))=
      ((rs z).operand u j).elim (fun x=>x.val+1) (fun x=>q+(ordinal (names.hidden z) x).val+1)) :
    (program wb d q hid N A groups blocks shops p base out source).Exec m done (clocks d blocks shops) ∧
    CheapCode (program wb d q hid N A groups blocks shops p base out source) ∧
    rowAt done hiddenCount=Fintype.card (rs z).Hidden ∧
    (∀j,rowAt done (hiddenWidth (hidden j))=(rs z).width j) ∧
    (∀k,(channels.primitive b (group k)).base+(channels.primitive b (group k)).size≤base → rowAt done k=rowAt m k) ∧
    (∀f u,(source f).read done u=(source f).read m u) ∧
    ∀a,a<base ∨ out+nRows≤a→done a=m a := by
  exact issued_core (q:=q) (t:=t) (hid:=hid) (N:=N) (A:=A) (p:=p)
    site rs names hH hN hA (DescentTerminalIssuedWidths.homed_width G hp L r s code birth host)
    short z (restricted_count G L hp (fun v => (s v).recipe hp) birth code host z)
    source base out maskBase channels m ok apart room fit b i g fromBase fromSize covers
    countBase countSize widthBase widthSize population lengths refs

end Physical
end
end Hierarchy.DescentTerminalCountWidthPair

end OAI
