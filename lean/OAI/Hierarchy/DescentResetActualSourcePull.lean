import OAI.Hierarchy.DescentResetSourceRelocation
import OAI.Hierarchy.DescentResetCompactSourceTicket
import OAI.Hierarchy.DescentResetSourceSeekRAM
import OAI.Hierarchy.DescentResetFieldReceipt

namespace OAI
/-! # Two reads of a real predecessor's source row in the packed reset RAM -/
noncomputable section
set_option quotPrecheck false

namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentCompiler DescentColonies DescentSharedCableNames DescentParallelBase DescentChosenRouter
open DescentResetCompactParent DescentResetCableSlots DescentResetOrdinalDigits DescentResetWireTags
open DescentRouterSlots DescentPackedTicketChronology DescentOrderedReset
open DescentResetLocalRoster
open scoped Classical BigOperators Fin.CommRing
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail w hist : ℕ}
  {input : Reached W G q ε S k i z D w hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset input ctl)
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "A" => input.placement
local notation "vertex" => B.frame.host.symm.toEmbedding.trans input.vertex
local notation "H₀" => input.placement.degree+2
local notation "Y" => (2^(Z).n:ℕ)
local notation "height" => GroupStage.depthBound D n f g
local notation "r" => (Z).k-(T).commonDepth
local notation "L" => (2^(S.groupWidth k tail i+k-(T).commonDepth)+1)*H₀*2^k
local notation "slots" => max Y (2^height)
local notation "pcCap" => max (Fintype.card (DescentCommonPalette.rotor (Z).graph).Edge) (2^(height+1))
local notation "Host" => Stage.Host (Fin (S.groupCount (i+1))) B.next.V k

open DescentPackedColony DescentSIMDLookup DescentPackedZip
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open DescentResetFieldAssembler
local notation "K" => totalLocal B
local notation "X" => 2^k
local notation "grp" => S.groupCount (i+1)
local notation "entry" => (Z).rawHostRank T vertex
variable {H M b a key Wd Δ : ℕ} (rack : Fin H→Option B.next.V)

def slotGate (j : Fin K) : ℕ→ℕ :=
  sourceSlotCode H₀ r Y L (A).cap slots pcCap (stemsCount B) (2^height) j.val K

def actualParentNumber (x : Fin X) (j : Fin K) (v : Fin H) (g : Fin grp) : ℕ :=
  (rack v).elim 0 (fun h=>(localOrigin B ((g,h),x) j).elim 0 (fun t=>wordNumber B ((g,h),x) t.val))

def actualAddress (capacity : B.next.placement.degree+1≤Δ) (x : Fin X) (j : Fin K) (v : Fin H) (g : Fin grp) :
    Option (DescentResetSourcePullRAM.Address Δ K) :=
  (rack v).bind (fun h=>(localOrigin B ((g,h),x) j).map (fun e=>
    ((sourceClass B ((g,h),x) e).castLE capacity,localRoster B _ (sourceOccurrence B _ e))))

theorem address_read (capacity : B.next.placement.degree+1≤Δ)
    (x : Fin X) (j : Fin K) (v : Fin H) (g : Fin grp) :
    (if (actualMeta B rack x j v g).live then
      (actualMeta B rack x j v g).src*K+slotGate B j (actualParentNumber B rack x j v g)+1 else 0)=
      DescentResetSourcePullRAM.number (actualAddress B rack capacity x j v g) := by
  cases here : rack v with
  | none=>simp [actualMeta,actualAddress,here,Meta.blank,DescentResetSourcePullRAM.number]
  | some h=>
    let u : Host:=((g,h),x)
    cases row : localOrigin B u j with
    | none=>simp [actualMeta,actualAddress,here,show localOrigin B ((g,h),x) j=none from row,«meta»,Meta.blank,DescentResetSourcePullRAM.number]
    | some t=>
      have address:=(local_read B u j t).1 row
      have rd : slotGate B j (wordNumber B u t.val)=(localRoster B _ (sourceOccurrence B u t)).val := by
        rw [slotGate,wordNumber,sourceSlotCode_read,←address]
        exact source_slot B u t
      simp only [actualMeta,actualParentNumber,actualAddress,here,Option.elim_some,Option.bind_some,
        show localOrigin B ((g,h),x) j=some t from row,Option.map_some,«meta»,ite_true,
        DescentResetSourcePullRAM.number,localClass_src,finProdFinEquiv_apply_val,Fin.val_castLE]
      change _+slotGate B j (wordNumber B u t.val)+1=_
      rw [rd]
      have linearize (q w n : ℕ) : q*n+w+1=w+n*q+1 := by
        rw [Nat.mul_comm q n,Nat.add_comm (n*q) w]
      exact linearize (sourceClass B u t).val (localRoster B _ (sourceOccurrence B u t)).val K

/-- Read a source-end value at a remote target, including absent physical hosts and ghost parents.
The receipt on each source bank is needed only at positions which are truly sources. -/
def actualLocal {a : ℕ} (value : ∀u : Host,Local (blocks B) u→Cell a)
    (x : Fin X) (j : Fin K) (v : Fin H) (g : Fin grp) : Cell a :=
  (rack v).elim 0 (fun h=>(localOrigin B ((g,h),x) j).elim 0 (value ((g,h),x)))

theorem actual_picked (capacity : B.next.placement.degree+1≤Δ) (name : B.next.V↪Fin H)
    (ordered : ∀x y : B.next.V,name x<name y ↔ entry x<entry y)
    (peer : Fin H→Fin Δ→Option (Fin H))
    (physical : ∀v u,rack v=some u→name u=v)
    (roster : ∀u,DescentSortedRoster.present peer (name u)=(insert u (B.next.placement.near u)).map name)
    (x : Fin X) (j : Fin K) (old : Fin K→Fin H→Fin grp→Cell a)
    (value : ∀u : Host,Local (blocks B) u→Cell a)
    (stored : ∀h g (e : Local (blocks B) ((g,h),x)),old (localRoster B _ (sourceOccurrence B _ e))
      (name ((blocks B).src e.val).1.2) g=value _ e) :
    DescentResetSourcePullRAM.picked (DescentSortedRoster.indexed peer) old (actualAddress B rack capacity x j)=
      actualLocal B rack value x j := by
  funext v g
  cases here : rack v with
  | none=>simp [DescentResetSourcePullRAM.picked,actualLocal,actualAddress,here]
  | some h=>
    let u : Host:=((g,h),x)
    cases row : localOrigin B u j with
    | none=>simp [DescentResetSourcePullRAM.picked,actualLocal,actualAddress,here,show localOrigin B ((g,h),x) j=none from row]
    | some e=>
      have atHost:=source_host B name ordered peer u (roster h) e ((sourceClass B u e).castLE capacity) rfl
      rw [physical v h here] at atHost
      simp only [actualLocal,actualAddress,DescentResetSourcePullRAM.picked,here,Option.bind_some,Option.elim_some,
        show localOrigin B ((g,h),x) j=some e from row,Option.map_some]
      change (DescentSortedRoster.indexed peer v ((sourceClass B u e).castLE capacity)).elim 0 _ = _
      rw [atHost]
      exact stored h g e

def sourceTicketCell (u : Host) (e : Local (blocks B) u) : Cell a := ((sourceTicket B e.val e.property.1).val:ℕ)
def atSourceAt (u : Host) (e : Local (blocks B) u) : Cell a :=
  (sumAt B (fieldNames B) (localRoster B) false ((blocks B).src e.val) (sourceOccurrence B u e):ℕ)

theorem atSource_field (x : Fin X) (j : Fin K) :
    actualLocal B rack (atSourceAt (a:=a) B) x j=actualOffset (b:=a) B rack x 2 j := by
  funext v g
  cases hv:rack v with
  | none=>simp [actualLocal,actualOffset,hv]
  | some h =>
    simp only [actualLocal,actualOffset,hv,Option.elim_some,rankAt]
    cases hr : localOrigin B ((g,h),x) j <;> rfl

theorem origin_offset (name : B.next.V↪Fin H) (physical : ∀u,rack (name u)=some u)
    (x : Fin X) (h : B.next.V) (g : Fin grp) (e : Local (blocks B) ((g,h),x)) :
    actualOffset (b:=a) B rack x 0 (localRoster B _ (sourceOccurrence B _ e))
      (name ((blocks B).src e.val).1.2) g=atSourceAt B ((g,h),x) e := by
  let u : Host:=((g,h),x)
  have same : ((g,((blocks B).src e.val).1.2),x)=(blocks B).src e.val :=
    DescentResetWindowResidentSources.source_at B.next.placement (B.next.order.trans Fin.valEmbedding) (blocks B) u e
  unfold actualOffset
  rw [physical]
  change (rankAt B ((g,((blocks B).src e.val).1.2),x) 0 _ : Cell a) = _
  rw [same,rankAt,source_lookup]
  rfl

/-- Operands from the same earlier packed columns used by the mixed original
comparison. The scratch destination is an address floor instead of an output. -/
structure PullChart (rack : Fin H→Option B.next.V) (b t a Δ M out : ℕ) (m : Memory Wd) where
  name : B.next.V↪Fin H
  ordered : ∀v u : B.next.V,name v<name u ↔ entry v<entry u
  anchor : ∀v u,rack v=some u→name u=v
  complete : ∀u,rack (name u)=some u
  peer : Fin H→Fin Δ→Option (Fin H)
  roster : ∀u,DescentSortedRoster.present peer (name u)=(insert u (B.next.placement.near u)).map name
  capacity : B.next.placement.degree+1≤Δ
  ports : Ports Δ
  actual : Mounted ports (DescentSortedRoster.indexed peer) m grp M
  original : Fin X→Fin K→Expr
  header : Fin X→Fin K→Expr
  origFit : ∀x j,(original x j).Fits Wd out
  headFit : ∀x j,(header x j).Fits Wd out
  originalRead : ∀x j,Source (original x j) (fun h g=>(actualParentNumber B rack x j h g:Cell t)) M m
  headerRead : ∀x j,Source (header x j) (fun h g=>DescentResetFieldAssembler.raw b (actualMeta B rack x j h g)) M m
  headerRoom : ∀x j h g s,digits (actualMeta B rack x j h g) s<2^b
  wordRoom : DescentResetParentCodec.capCount H₀ r Y L (A).cap slots pcCap≤2^t
  search : Fin K→Tables
  searchStatic : ∀j,Static (search j) (DescentResetSourceSeekRAM.select (b:=b) (t:=t) (Δ:=Δ) (slotGate B) j) M m
  searchRoom : ∀j,WordRoom (search j) (b*7) t M Wd out
  lookup : Fin (Δ*K)→Tables
  lookupStatic : ∀i,Static (lookup i)
    (DescentResetSourcePullRAM.take (b:=DescentResetSourceSeekRAM.keyBits Δ K) (a:=a) (Δ:=Δ) («K» := K) i) M m
  lookupRoom : ∀i,WordRoom (lookup i) (DescentResetSourceSeekRAM.keyBits Δ K) a M Wd out

variable {t out : ℕ} {m : Memory Wd}
def pull (chart : PullChart B rack b t a Δ M out m) (x : Fin X) (j : Fin K) (prior : Fin K→Bank) :=
  DescentResetSourcePullRAM.instruction chart.lookup ((chart.search j).read (chart.header x j) (chart.original x j)) chart.ports prior H

theorem actual_pull (chart : PullChart B rack b t a Δ M out m) (x : Fin X) (j : Fin K)
    (prior : Fin K→Bank) (old : Fin K→Fin H→Fin grp→Cell a)
    (value : ∀u : Host,Local (blocks B) u→Cell a)
    (accessible : ∀z,Accessible chart.ports (prior z) H grp M Wd out)
    (issued : ∀z,Reads (prior z) (old z) M m)
    (atSource : ∀h g (e : Local (blocks B) ((g,h),x)),old (localRoster B _ (sourceOccurrence B _ e))
      (chart.name ((blocks B).src e.val).1.2) g=value _ e) :
    (pull B rack chart x j prior).Fits Wd out ∧
      Source (pull B rack chart x j prior) (actualLocal B rack value x j) M m := by
  have num h g : actualParentNumber B rack x j h g<2^t := by
    cases hv:rack h with
    | none=>simp [actualParentNumber,hv]
    | some v=>cases he:localOrigin B ((g,v),x) j with
      | none=>simp [actualParentNumber,hv,he]
      | some e=>simpa [actualParentNumber,hv,he] using (wordNumber_lt B ((g,v),x) e.val).trans_le chart.wordRoom
  let ask:=actualAddress B rack chart.capacity x j
  have seek:=DescentResetSourceSeekRAM.source (slotGate B) j (chart.search j) (chart.header x j) (chart.original x j)
    out m (actualMeta B rack x j) (fun h g=>(actualParentNumber B rack x j h g:Cell t)) ask
    (chart.headerRoom x j) (fun h g=>by simpa only [Fin.val_cast_of_lt (num h g)] using address_read B rack chart.capacity x j h g)
    (chart.searchRoom j) (chart.headFit x j) (chart.origFit x j) (chart.searchStatic j) (chart.headerRead x j) (chart.originalRead x j)
  have small : Δ*K<2^(DescentResetSourceSeekRAM.keyBits Δ K):=Nat.le_pow_clog (by decide) (Δ*K+1)
  let boundary:Bank:=⟨out,0⟩
  have hit:=DescentResetSourcePullRAM.source chart.lookup _ chart.ports prior boundary m
    (DescentSortedRoster.indexed chart.peer) old ask small seek.1 accessible chart.actual issued seek.2 chart.lookupRoom chart.lookupStatic
  rw [actual_picked B rack chart.capacity chart.name chart.ordered chart.peer chart.anchor chart.roster x j old value atSource] at hit
  exact hit

theorem actual_pull_ticket (chart : PullChart B rack b t a Δ M out m) (x : Fin X) (j : Fin K)
    (prior : Fin K→Bank) (old : Fin K→Fin H→Fin grp→Cell a)
    (accessible : ∀z,Accessible chart.ports (prior z) H grp M Wd out)
    (issued : ∀z,Reads (prior z) (old z) M m)
    (tickets : ∀h g (e : Local (blocks B) ((g,h),x)),old (localRoster B _ (sourceOccurrence B _ e))
      (chart.name ((blocks B).src e.val).1.2) g=((sourceTicket B e.val e.property.1).val:ℕ)) :
    (pull B rack chart x j prior).Fits Wd out ∧
      Source (pull B rack chart x j prior) (actualLocal B rack (sourceTicketCell (a:=a) B) x j) M m :=
  actual_pull B rack chart x j prior old (sourceTicketCell B) accessible issued tickets

theorem actual_pull_atSource (chart : PullChart B rack b t a Δ M out m) (x : Fin X) (j : Fin K)
    (prior : Fin K→Bank)
    (accessible : ∀z,Accessible chart.ports (prior z) H grp M Wd out)
    (issued : ∀z,Reads (prior z) (actualOffset (b:=a) B rack x 0 z) M m) :
    (pull B rack chart x j prior).Fits Wd out ∧
      Source (pull B rack chart x j prior) (actualOffset (b:=a) B rack x 2 j) M m := by
  rw [←atSource_field]
  exact actual_pull B rack chart x j prior (actualOffset (b:=a) B rack x 0) (atSourceAt B) accessible issued
    (origin_offset B rack chart.name chart.complete x)

end Hierarchy.DescentSixParty.ClosedReset.Window
end

end OAI
