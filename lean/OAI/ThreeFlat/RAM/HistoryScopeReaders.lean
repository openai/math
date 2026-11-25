import OAI.ThreeFlat.Diagonal.HistoryScopeOffsets
import OAI.ThreeFlat.Diagonal.ShrinkSupplySend
import OAI.ThreeFlat.Diagonal.ShrinkSelectedSupply
import OAI.ThreeFlat.Diagonal.ShrinkChildSend
import OAI.ThreeFlat.RAM.HistoryGeometryPointer
import OAI.ThreeFlat.RAM.HeaderScanProcedure
import OAI.ThreeFlat.RAM.ContractionMemory

namespace OAI
/-! # Reading the typed boundary source at an actual geometry descriptor -/

namespace ThreeFlat.RAM.HistoryScopeAddress

open LinearAlgebra.SpectralBooks Diagonal Diagonal.HistoryContraction Diagonal.MotifKernel
open scoped BigOperators Classical
noncomputable section

variable {h p : ℕ}

/-- The reads made by the address interpreter. The old half table is reached
through the absolute chronological child ID and that child's node header. -/
inductive Read (T : Layout) (m : ℕ → ℕ) (loc : Fin 4 → ℕ) : BitSource h p → Prop
  | zero (tag : loc 0=0) : Read T m loc (.constant false)
  | old (i : Fin p) (child header table start first : ℕ) (tag : loc 0=1)
      (node : m (T.childIDs+loc 1)=child) (halves : m (T.nodes+(8*child+6))=header)
      (rows : m (header+1)=table) (origin : m (T.childStarts+loc 1)=start)
      (half : m (table+(4*loc 2+3))=first) (pin : i.val=start+(first+loc 3)) :
      Read T m loc (.pin i)
  | fresh (i : Fin p) (table first : ℕ) (tag : loc 0=2)
      (rows : m (T.newHalves+1)=table) (half : m (table+(4*loc 2+3))=first)
      (pin : i.val=T.oldBits+(first+loc 3)) : Read T m loc (.pin i)
  | absorbed (i : Fin h) (start : ℕ) (tag : loc 0=3) (publicBits : T.publicPins=p)
      (origin : m (T.privateStarts+loc 1)=start) (bit : i.val=start+loc 2) :
      Read T m loc (.hidden i)

theorem Read.value {T : Layout} {m : ℕ→ℕ} {loc : Fin 4→ℕ} {s : BitSource h p}
    (r : Read T m loc s) :
    HistoryScopeAddress.value T m (loc 0) (loc 1) (loc 2) (loc 3) = BitLayout.sourceAddress s := by
  cases r with
  | zero tag => simp [HistoryScopeAddress.value,tag,BitLayout.sourceAddress]
  | old i child header table start first tag node halves rows origin half pin =>
    simp [HistoryScopeAddress.value,tag,node,halves,rows,origin,half,BitLayout.sourceAddress,pin]
  | fresh i table first tag rows half pin =>
    simp [HistoryScopeAddress.value,tag,rows,half,BitLayout.sourceAddress,pin]
  | absorbed i start tag publicBits origin bit =>
    simp [HistoryScopeAddress.value,tag,publicBits,origin,bit,BitLayout.sourceAddress,BitLayout.hiddenBase,Nat.add_assoc]

section Boundary
open LinearAlgebra.SpectralBooks
variable {V E U D Pins : Type} [Fintype V] [Fintype E] [Fintype U] [Fintype D]
  {G : PortGraph V E} {w : E→ℕ} {H : PortGraph U D} {b : D→ℕ}
  (A : WordLayout G w Pins) (B : WordLayout H b Pins) (own : V→U) (n : U→ℕ)
  (ord : ∀ u, Fin (n u) ≃ {i // own i=u}) (u : U)
  (T : Layout) (m : ℕ→ℕ) (loc : Fin 4→ℕ)

/-- True child and half prefixes give the original typed old-word pin. -/
theorem Read.oldPin (i : {x // own x=u}) (a : G.Port i.val) (j : Fin (w a.1.1))
    (child header table : ℕ) (tag : loc 0=1) (offset : loc 3=j.val)
    (node : m (T.childIDs+loc 1)=child) (halves : m (T.nodes+(8*child+6))=header)
    (rows : m (header+1)=table)
    (origin : m (T.childStarts+loc 1)=WordLayout.childStart A own n ord u i)
    (half : m (table+(4*loc 2+3))=A.ports.start i.val a) :
    Read (h:=h) T m loc (.pin (WordLayout.oldPin A B own n ord u i a j)) := by
  exact .old _ child header table _ _ tag node halves rows origin half
    (by rw [offset,WordLayout.oldPin_val])

/-- The new half occupies the public suffix after all old child words. -/
theorem Read.newPin (a : H.Port u) (j : Fin (b a.1.1)) (table : ℕ)
    (tag : loc 0=2) (offset : loc 3=j.val) (old : T.oldBits=WordLayout.prior A own n ord u)
    (rows : m (T.newHalves+1)=table) (half : m (table+(4*loc 2+3))=B.ports.start u a) :
    Read (h:=h) T m loc (.pin (WordLayout.newPin A B own n ord u a j)) := by
  exact .fresh _ table _ tag rows half (by rw [offset,old,WordLayout.newPin_val])

end Boundary

section Shrink
open Computability.VPVNP.Compression CompressorPacking
variable {Base H Tag L Pins E : Type} [AddCommGroup H] [AddCommGroup Tag] [AddCommGroup L]
  [Fintype Base] [Fintype H] [Fintype Tag] [Fintype L] [Fintype E] {d c Q : ℕ}
  (P : PackingData Base H Tag L d (c+1)) (key : Arc Base H Tag L d (c+1) ↪ ℕ)
  (w : Arc Base H Tag L d (c+1) → ℕ) (positive : 0<Q)
  (num : P.Motif ≃ (Site Base Tag L × Fin d) × Fin Q) (bundled : ∀ m,(num m).1=P.bundle m)
  (lay : Bool) (site : Site Base Tag L) (A : WordLayout (oldGraph P) w Pins)
  {G : PortGraph (Site Base Tag L) E} {width : E→ℕ} (B : WordLayout G width Pins)
local notation "own" => P.placement lay
local notation "count" => (fun _ : Site Base Tag L => d*2^(c+1))
local notation "ord" => Owner.childOrder P lay

/-- The shrink geometry's four words address the precise old source passed to
the occupied party, including the selected orientation and owned child. -/
theorem Read.oldShrinkRequest (motif : P.Motif) {party : Fin 6}
    (placed : partySite P lay motif party=site) (q : demandGraph.Port party)
    (j : Fin (demandWidth P w num motif q.val.1))
    (T : Layout) (m : ℕ→ℕ) (child header table : ℕ) :
    let req := ChildSend.request P key w positive num motif q.val.2 q.val.1 j
    let atSite := ChildSend.at_party key positive num bundled lay motif placed q j
    let i := ChildSend.ownedChild lay site req atSite
    let a := ChildSend.ownedPort lay site req atSite
    let loc := ChildSend.words P w lay site req atSite
    m (T.childIDs+loc 1)=child → m (T.nodes+(8*child+6))=header → m (header+1)=table →
    m (T.childStarts+loc 1)=WordLayout.childStart A own count ord site i →
    m (table+(4*loc 2+3))=A.ports.start i.val a →
    Read T m loc (oldPinSource (h:=h) P w key positive num lay site
      (WordLayout.oldPin A B own count ord site) motif party q j) := by
  intro req atSite i a loc node halves rows origin half
  rw [ChildSend.oldPinSource_request key positive num bundled lay site _ motif placed q j]
  exact Read.oldPin A B own count ord site T m loc i a req.2.2 child header table
    rfl rfl node halves rows origin half
end Shrink

/-- The absorbed edge order is the private order of the occupied motif tree. -/
theorem Read.privateBit {J E V : Type} [Fintype J] [Fintype E] [Fintype V] [DecidableEq V]
    {P : PortGraph J E} {place : J→V} {v : V} {I : E→Type} [∀ e, Fintype (I e)]
    (D : PrivateOrder P place v I) (a : Absorbed P place v) (j : Fin (D.width a.val))
    (T : Layout) (m : ℕ→ℕ) (loc : Fin 4→ℕ) (tag : loc 0=3) (offset : loc 2=j.val)
    (publicBits : T.publicPins=p) (origin : m (T.privateStarts+loc 1)=D.start a) :
    Read T m loc (.hidden (D.privateBit a j) : BitSource D.bits p) :=
  .absorbed _ _ tag publicBits origin (by rw [offset,PrivateOrder.privateBit_val])

/-- The source consumed by an occupied party is its actual private bit on an
absorbed edge and the relocated half of the successor on a crossing edge. -/
theorem Read.partySource {J E V : Type} [Fintype J] [Fintype E] [Fintype V] [DecidableEq V]
    {P : PortGraph J E} {place : J→V} {v : V} {I : E→Type} [∀ e, Fintype (I e)]
    (D : PrivateOrder P place v I) (cross : (a : ExternalAt P place v) → Fin (D.width a.val.val) → Fin p)
    (j : {j // place j=v}) (a : P.Port j.val) (bit : Fin (D.width a.1.1))
    (T : Layout) (m : ℕ→ℕ) (loc : Fin 4→ℕ)
    (inside : ∀ owner : wireOwner P.tail P.head place a.1.1=some v,
      Read T m loc (.hidden (D.privateBit ⟨a.1.1,owner⟩ bit) : BitSource D.bits p))
    (outside : ∀ (owner : wireOwner P.tail P.head place a.1.1=none)
      (incident : place (P.tail a.1.1)=v ∨ place (P.head a.1.1)=v),
      Read T m loc (.pin (cross ⟨⟨a.1.1,owner⟩,incident⟩ bit) : BitSource D.bits p)) :
    Read T m loc (D.partySource cross j a bit) := by
  by_cases live : wireOwner P.tail P.head place a.val.1=none
  · rw [D.crossing_request cross j a bit live]
    exact outside live (PrivateOrder.onSide j a live).property
  · have here:=PrivateOrder.owner_of_non_crossing j a live
    rw [D.absorbed_request cross j a bit here]
    exact inside here

section Supply
variable {O OE V E J Pins : Type} [Fintype O] [Fintype OE] [Fintype V] [Fintype E] [Fintype J]
    [DecidableEq V] {ne : ℕ} {G : PortGraph O OE} {w : OE→ℕ} {H : PortGraph V E} {b : E→ℕ}
    (A : WordLayout G w Pins) (B : WordLayout H b Pins) (own : O→V) (n : V→ℕ)
    (ord : ∀ v, Fin (n v) ≃ {i // own i=v}) (v : V)
    {M : PortGraph J (Fin ne)} {place : J→V} {I : Fin ne→Type} [∀ e,Fintype (I e)]
    (D : PrivateOrder M place v I)
local notation "P" => WordLayout.argSize A B own n ord v
local notation "fresh" => WordLayout.newPin A B own n ord v

omit [Fintype J] [(e : Fin ne) → Fintype (I e)] in
/-- Decode the actual private-width prefix or successor half prefix, according
to the placement of the occupied port. -/
theorem Read.occupiedSupply
    (ordered : StrictMono (fun i=>(D.edge i).val))
    (request : (a : ExternalAt M place v) → Fin (D.width a.val.val) → Σ q : H.Port v, Fin (b q.val.1))
    (cross : (a : ExternalAt M place v) → Fin (D.width a.val.val) → Fin P)
    (party : {j // place j=v}) (q : M.Port party.val) (bit : Fin (D.width q.val.1))
    (T : Layout) (m : ℕ→ℕ) (loc : Fin 4→ℕ) (table : ℕ)
    (halfOrdinal : H.Port v → ℕ)
    (publicBits : T.publicPins=P) (oldBits : T.oldBits=WordLayout.prior A own n ord v)
    (halfData : m (T.newHalves+1)=table)
    (halfPrefix : ∀ a : H.Port v, m (table+(4*halfOrdinal a+3))=B.ports.start v a)
    (privatePrefix : m (T.privateStarts+q.val.1.val)=
      ∑ e ∈ Finset.univ.filter (fun e=>wireOwner M.tail M.head place e=some v ∧ e<q.val.1),D.width e)
    (localFields : wireOwner M.tail M.head place q.val.1≠none → loc=![3,q.val.1.val,bit.val,0])
    (crossingFields : ∀ active : wireOwner M.tail M.head place q.val.1=none,
      let a:=PrivateOrder.onSide party q active
      let z:=request a bit
      loc=![2,0,halfOrdinal z.1,z.2.val] ∧ cross a bit=fresh z.1 z.2) :
    Read T m loc (D.partySource cross party q bit) := by
  by_cases active : wireOwner M.tail M.head place q.val.1=none
  · rw [D.crossing_request cross party q bit active]
    obtain ⟨fields,relocate⟩:=crossingFields active
    rw [relocate,fields]
    exact Read.newPin A B own n ord v T m _ _ _ table rfl rfl oldBits halfData (halfPrefix _)
  · have here:=PrivateOrder.owner_of_non_crossing party q active
    rw [D.absorbed_request cross party q bit here,localFields active]
    exact .absorbed _ _ rfl publicBits privatePrefix
      (D.privateBit_ordered ordered ⟨q.val.1,here⟩ bit)
end Supply

section HistogramRequest
open Computability.VPVNP.Compression CompressorPacking MotifOuterTerms MotifBinaryPacking
open private selectedSiteDecidableEq from OAI.ThreeFlat.Diagonal.ShrinkSelectedSupply
attribute [local instance 2000] selectedSiteDecidableEq
section Callbacks
variable {c d : ℕ} {V H Tag L F : Type} [Field F]
    [AddCommGroup H] [AddCommGroup Tag] [AddCommGroup L]
    [Fintype V] [Fintype H] [Fintype Tag] [Fintype L]
    (P : PackingData V H Tag L d c)
    (base : P.Motif → Fin 2 → ℕ) (r : P.Motif → ℕ)
    (T : ∀ m, FixedMotifTile demandGraph supplyGraph (base m) F)
    (x : Histories P base r T) (hn : ∀ a : Tag, -a = a)
    (good : TagConditions P.slots (shift P) P.offset) (lay : Bool)
    (n : Fin 4 → ℕ) (positive : ∀ i, 0 < n i) (order : ShrinkEdge P n ↪ ℕ)
    (hc : 2 ≤ c) (pad : ℕ) (padding : LiftedSlots (V × Tag) pad L) (v : Site V Tag L)

set_option quotPrecheck false
local notation "occupiedOrder" m:arg =>
  HistogramTileNetwork.order («k» := (T m).bits) ShrinkMotif.supply (partySite P lay m) v
    (T m).output (x m) (HistoryMaskOrder.order (fun e : Fin 8 =>
      wireOwner supplyGraph.tail supplyGraph.head (partySite P lay m) e = some v))
local notation "successorGraph" => outGraph P hn good lay n order hc pad padding
local notation "successorWidth" => outputWidth P base r T x hn good lay n order hc pad

/-- The successor layout for the graph and widths of the selected histogram. -/
abbrev histogramLayout (Pins : Type) := WordLayout successorGraph successorWidth Pins

/-- The emitted request accepts a bit in the occupied histogram's private order. -/
abbrev histogramRequest (m : P.Motif) :
    (a : ExternalAt supplyGraph (partySite P lay m) v) → Fin ((occupiedOrder m).width a.val.val) →
      Σ q : (successorGraph).Port v, Fin (successorWidth q.val.1) :=
  fun a bit => SupplySend.request P base r T x hn good lay n positive order hc pad padding v m a bit

/-- The same occupied bit selects a pin numbered by the successor word layout. -/
abbrev histogramCross (pin : (q : (successorGraph).Port v) → Fin (successorWidth q.val.1) → Fin p)
    (m : P.Motif) :
    (a : ExternalAt supplyGraph (partySite P lay m) v) → Fin ((occupiedOrder m).width a.val.val) → Fin p :=
  fun a bit => crossingPin P base r T x hn good lay n positive order hc pad padding v pin m a bit

end Callbacks

variable {c d : ℕ} {V H Tag L F Pins : Type} [Field F]
    [AddCommGroup H] [AddCommGroup Tag] [AddCommGroup L]
    [Fintype V] [Fintype H] [Fintype Tag] [Fintype L]
    (P : PackingData V H Tag L d (c+1))
    (base : P.Motif → Fin 2 → ℕ) (r : P.Motif → ℕ)
    (T : ∀ m, FixedMotifTile demandGraph supplyGraph (base m) F)
    (x : Histories P base r T) (hn : ∀ a : Tag, -a = a)
    (good : TagConditions P.slots (shift P) P.offset) (lay : Bool)
    (n : Fin 4 → ℕ) (positive : ∀ i, 0 < n i) (order : ShrinkEdge P n ↪ ℕ)
    (hc : 2 ≤ c+1) (pad : ℕ) (padding : LiftedSlots (V × Tag) pad L) (v : Site V Tag L)
    (m : P.Motif) (oldWidth : Arc V H Tag L d (c+1) → ℕ)

set_option quotPrecheck false
local notation "successorGraph" => outGraph P hn good lay n order hc pad padding
local notation "successorWidth" => outputWidth P base r T x hn good lay n order hc pad
local notation "place" => partySite P lay m
local notation "active" => fun e : Fin 8 => wireOwner supplyGraph.tail supplyGraph.head place e = some v
local notation "occupiedOrder" => HistogramTileNetwork.order («k» := (T m).bits) ShrinkMotif.supply
  place v (T m).output (x m) (HistoryMaskOrder.order active)
local notation "own" => P.placement lay
local notation "count" => fun _ : Site V Tag L => d*2^(c+1)
local notation "ord" => Owner.childOrder P lay

/-- The occupied reader on the old and successor layouts of an arbitrary shrinking packing. -/
abbrev Read.histogramSupply (O : WordLayout (oldGraph P) oldWidth Pins)
    (B : histogramLayout P base r T x hn good lay n order hc pad padding Pins) :=
  Read.occupiedSupply («G» := oldGraph P) (w := oldWidth) (H := successorGraph) (b := successorWidth)
    (ne := 8) (M := supplyGraph) («place» := place)
    (I := HistogramTileNetwork.Label (x m) (T m).output (T m).bits)
    O B own count ord v occupiedOrder (PrivateOrder.masked_order_strict active)
    (histogramRequest P base r T x hn good lay n positive order hc pad padding v m)
    (histogramCross P base r T x hn good lay n positive order hc pad padding v
      (WordLayout.newPin O B own count ord v) m)

set_option maxRecDepth 8192 in
/-- The four issued fields resolve the selected supply bit in the occupied layout. -/
theorem Read.histogramFields (O : WordLayout (oldGraph P) oldWidth Pins)
    (B : histogramLayout P base r T x hn good lay n order hc pad padding Pins)
    (G : LiftedSlots (V × Tag) (usedDegree n (c+1) d + pad) L)
    (party : {u // place u = v}) (q : supplyGraph.Port party.val)
    (bit : Fin (historyWidth P base r T x m q.val.1))
    (chart : Layout) (mem : ℕ → ℕ) (table : ℕ)
    (publicBits : chart.publicPins = WordLayout.argSize O B own count ord v)
    (oldBits : chart.oldBits = WordLayout.prior O own count ord v)
    (rows : mem (chart.newHalves+1) = table)
    (half : ∀ a : (successorGraph).Port v,
      mem (table+(4*SupplySend.halfOrdinal G a.val.1 a.val.2+3)) = B.ports.start v a)
    (privatePrefix : mem (chart.privateStarts+q.val.1.val) =
      ∑ e ∈ Finset.univ.filter (fun e => active e ∧ e < q.val.1), historyWidth P base r T x m e) :
    Read chart mem
      (SupplySend.fieldValues P hn good lay n positive order hc pad (historyWidth P base r T x) G
        m party.val q.val.1 bit)
      ((occupiedOrder).partySource
        (histogramCross P base r T x hn good lay n positive order hc pad padding v
          (WordLayout.newPin O B own count ord v) m) party q bit) := by
  apply Read.histogramSupply P base r T x hn good lay n positive order hc pad padding v m oldWidth
    O B party q bit chart mem _ table (fun a => SupplySend.halfOrdinal G a.val.1 a.val.2)
    publicBits oldBits rows half privatePrefix
  · intro absorbed
    exact dite_eq_right absorbed
  · intro crossing
    exact ⟨SupplySend.fieldValues_request P base r T x hn good lay n positive order hc pad padding
        G v m party q crossing bit,
      SupplySend.crossingPin_request P base r T x hn good lay n positive order hc pad padding v
        (WordLayout.newPin O B own count ord v) m (PrivateOrder.onSide party q crossing) bit⟩

/-- Fix the resident table before the caller supplies its two word layouts. -/
abbrev Read.histogramAtGraph
    (G : LiftedSlots (V × Tag) (usedDegree n (c+1) d + pad) L)
    (O : WordLayout (oldGraph P) oldWidth Pins)
    (B : histogramLayout P base r T x hn good lay n order hc pad padding Pins) :=
  Read.histogramFields P base r T x hn good lay n positive order hc pad padding v m oldWidth O B G

end HistogramRequest


end
end ThreeFlat.RAM.HistoryScopeAddress

namespace ThreeFlat.RAM.HistoryGeometryPointer
open Computability.VPVNP.BurstRAM PrivateRAM DescriptorExpr PhysicalPinsExpr Diagonal Diagonal.CompressorPacking.Native
open scoped Fin.CommRing Classical
open private shrinkField refreshField from OAI.ThreeFlat.RAM.HistoryGeometryPointer

variable {W h p : ℕ}

def layoutOf (vs : Fin 13 → Word W) : HistoryScopeAddress.Layout :=
  ⟨(vs 6).val,(vs 7).val,(vs 8).val,(vs 9).val,(vs 10).val,(vs 11).val,(vs 12).val⟩

def refreshRegs (m : Memory W) (vs : Fin 13 → Word W) (j : Fin 4) : Fin 7 → Word W :=
  ![m (vs 0).val,vs 1,vs 2,vs 3,vs 4,vs 5,(j.val:Word W)]

def ReadFits (m : Memory W) (vs : Fin 13 → Word W) (loc : Fin 4 → ℕ) : Prop :=
  HistoryScopeAddress.formula.Fits W (fun _=>0) (fun j=>(m j).val)
    ((layoutOf vs).args (loc 0) (loc 1) (loc 2) (loc 3))

open private v field halfOffset from OAI.ThreeFlat.RAM.HistoryScopeAddress

/-- Only addresses traversed by the selected region need to fit the native word. -/
theorem readFits_of_addresses (m : Memory W) (vs : Fin 13→Word W) (loc : Fin 4→ℕ)
    (scope : loc 0≤3) (word : 3<2^W) :
    let T := layoutOf vs
    let mu := fun j => (m j).val
    let child := mu (T.childIDs+loc 1)
    let header := mu (T.nodes+(8*child+6))
    (loc 0=1 → T.childIDs+loc 1<2^W ∧ T.nodes+(8*child+6)<2^W ∧
      header+1<2^W ∧ mu (header+1)+(4*loc 2+3)<2^W ∧ T.childStarts+loc 1<2^W) →
    (loc 0=2 → T.newHalves+1<2^W ∧ mu (T.newHalves+1)+(4*loc 2+3)<2^W) →
    (loc 0=3 → T.privateStarts+loc 1<2^W) → ReadFits m vs loc := by
  intro T mu child header old fresh privateRead
  have tags : loc 0=0 ∨ loc 0=1 ∨ loc 0=2 ∨ loc 0=3 := by omega
  have base : 2<2^W := by omega
  have one : 1<2^W := by omega
  have zero : 0<2^W := Nat.two_pow_pos _
  rcases tags with tag|tag|tag|tag
  · simp [ReadFits,HistoryScopeAddress.formula,HistoryScopeAddress.Layout.args,v,field,halfOffset,
      Formula.Fits,Formula.natural,natTest,tag,zero]
  · obtain ⟨a,b,c,d,e⟩ := old tag
    simp [ReadFits,HistoryScopeAddress.formula,HistoryScopeAddress.Layout.args,v,field,halfOffset,
      Formula.Fits,Formula.natural,natOp,natTest,opFits,tag,one,zero];
      simp_all only [T,mu,child,header,true_and]
  · obtain ⟨a,b⟩ := fresh tag
    simp [ReadFits,HistoryScopeAddress.formula,HistoryScopeAddress.Layout.args,v,field,halfOffset,
      Formula.Fits,Formula.natural,natOp,natTest,opFits,tag,base,one,zero];
      simp_all only [T,mu,true_and]
  · have a := privateRead tag
    simp [ReadFits,HistoryScopeAddress.formula,HistoryScopeAddress.Layout.args,v,field,halfOffset,
      Formula.Fits,Formula.natural,natOp,natTest,opFits,tag,word,base,one,zero];
      simp_all only [T]

private theorem read_resolve (field : Fin 4 → Term W 1 13) (m : Memory W) (vs : Fin 13→Word W)
    (loc : Fin 4 → ℕ) (s : BitSource h p) (values : ∀ j, (field j).eval (fun _=>0) m vs=(loc j:Word W))
    (fits : ReadFits m vs loc) (typed : HistoryScopeAddress.Read (layoutOf vs) (fun j=>(m j).val) loc s) :
    (resolve field).eval (fun _=>0) m vs=(BitLayout.sourceAddress s:Word W) := by
  have run := HistoryScopeAddress.eval W (fun _=>0) (fun j=>(m j).val) (layoutOf vs)
    (loc 0) (loc 1) (loc 2) (loc 3) fits
  simp only [Nat.cast_zero,Fin.cast_val_eq_self,typed.value] at run
  rw [resolves]
  refine Eq.trans (congrArg ((HistoryScopeAddress.program W).eval (fun _=>0) m) ?_) run
  funext i
  fin_cases i <;> simp [HistoryScopeAddress.Layout.args,layoutOf,values]

/-- The six geometry inputs of the shrink lookup use the actual source registers. -/
theorem read_shrink (S : Graph.Stage) (supply : Bool) (m : Memory W) (vs : Fin 13→Word W)
    (loc : Fin 4→ℕ) (s : BitSource h p)
    (fields : ∀ j : Fin 4, (HeaderScan.closed (ShrinkStage.BitOrigins.lookup S supply
      (.reg 0) (.reg 2) (.reg 3) (.reg 4) (.reg 5) (.lit j.val) : Formula 13)).eval Fin.elim0 m vs=(loc j:Word W))
    (fits : ReadFits m vs loc) (typed : HistoryScopeAddress.Read (layoutOf vs) (fun j=>(m j).val) loc s) :
    (shrink W S supply).eval (fun _=>0) m vs=(BitLayout.sourceAddress s:Word W) := by
  refine read_resolve (shrinkField S supply) m vs loc s ?_ fits typed
  intro j
  simpa only [shrinkField,Formula.eval_compile,HeaderScan.eval_closed,Function.comp_def] using fields j

/-- Refresh reads stageInfoPtr from the kernel register's pointed-to header. -/
theorem read_refresh (degree hgt pad : ℕ) (supply : Bool) (m : Memory W) (vs : Fin 13→Word W)
    (loc : Fin 4→ℕ) (s : BitSource h p)
    (fields : ∀ j : Fin 4, (HeaderScan.closed (RefreshParty.lookup degree hgt pad supply)).eval Fin.elim0 m
      (refreshRegs m vs j)=(loc j:Word W))
    (fits : ReadFits m vs loc) (typed : HistoryScopeAddress.Read (layoutOf vs) (fun j=>(m j).val) loc s) :
    (refresh W degree hgt pad supply).eval (fun _=>0) m vs=(BitLayout.sourceAddress s:Word W) := by
  refine read_resolve (refreshField degree hgt pad supply) m vs loc s ?_ fits typed
  intro j
  rw [refreshField,Term.eval_instantiate,Formula.eval_compile]
  have reg : (fun a => (![(.result 0 : Term W 1 13).load,.result 1,.result 2,.result 3,.result 4,.result 5,
      .literal (j.val:Word W)] a).eval (fun _=>0) m vs) = refreshRegs m vs j := by
    funext i
    fin_cases i <;> rfl
  rw [reg]
  simpa only [HeaderScan.eval_closed,Function.comp_def] using fields j

end ThreeFlat.RAM.HistoryGeometryPointer

end OAI
