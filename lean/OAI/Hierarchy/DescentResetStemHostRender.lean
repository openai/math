import OAI.Hierarchy.DescentResetStemWord
import OAI.Hierarchy.DescentResetActualSourcePull
import OAI.Hierarchy.DescentResetStemHostRank
import OAI.Hierarchy.DescentResetStemMissing

namespace OAI
/-! # The source rank of an original stem from a single shared old-host word -/
noncomputable section
namespace Hierarchy.DescentResetStemWord
open DescentSIMDLookup DescentPackedZip DescentPacking.PackedMatch.Local.Gather DescentPackedFallbackTree.Image
open DescentResetParentCodec DescentSharedCableNames.Stage
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
variable {b w H G field M : ℕ}


def hostCode (self : ℕ) (missing : Bool) := 2*self+missing.toNat
def effective (D cap : ℕ) (s : Bool) (original h : Cell field) : ℕ :=
  let self:=h.val/2
  if s then
    match DescentSignedCableCodec.decode D cap (original.val:Cell (DescentSignedCableCodec.width D cap)) with
    | some live=>DescentResetStemCompactOrder.closeRank (decide (h.val%2=1)) self live.neighbor.val
    | none=>0
  else self

def truthful (D cap : ℕ) (s : Bool) (x : Fin 6→Cell field) : Fin 6→Cell field :=
  Function.update x 2 ((effective D cap s (x 0) (x 2):ℕ):Cell field)

def withHost (D k r Y L cap links prog b : ℕ) (s : Bool) (x : Fin 6→Cell field) : Cell b :=
  render D k r Y L cap links prog b s (truthful D cap s x)

theorem effective_read (D cap : ℕ) (s : Bool) (live : Live D cap) (orig h : Cell field) (self : ℕ) (miss : Bool)
    (data : orig.val=(DescentSignedCableCodec.encode (some live)).val)
    (heard : h.val=hostCode self miss) :
    effective D cap s orig h=(if s then DescentResetStemCompactOrder.closeRank miss self live.neighbor.val else self) := by
  have same : ((orig.val:ℕ):Cell (DescentSignedCableCodec.width D cap))=DescentSignedCableCodec.encode (some live):=by
    rw [data];apply Fin.ext;exact Nat.mod_eq_of_lt (DescentSignedCableCodec.encode (some live)).isLt
  rw [effective,same,DescentSignedCableCodec.decode_encode,heard]
  have div : hostCode self miss / 2 = self := by
    cases miss
    · change (2*self+0)/2=self
      omega
    · change (2*self+1)/2=self
      omega
  have mod : decide (hostCode self miss % 2 = 1) = miss := by cases miss <;> simp [hostCode]
  rw [div,mod]


/-- Every physical lane receives the emitted whole packed word with padding. -/
theorem runHost (D k r Y L cap links prog b : ℕ) (s : Bool) (tables : Fin 6→Tables) (reads : Fin 6→Expr)
    (menu : DescentSIMDLookup.Banks) (mid out : ℕ) (x : Fin H→Fin G→Fin 6→Cell field)
    (positive : 0<M) (mem : Memory w) (bounds : Bounds (w:=w) (d:=field) (M:=M) tables reads mid)
    (constants : ∀j,Static (tables j) (setField (d:=field) j) M mem)
    (sources : ∀j,Source (reads j) (fun a g=>x a g j) M mem) (room : mid+H*chunks G M<2^w)
    (fit : DescentSIMDLookup.Fits menu (field*6) b M H G w out)
    (rom : resident (withHost D k r Y L cap links prog b s ∘ (DescentSIMDLookup.encode field 6).symm) menu H G M mem)
    (dictLow : menu.dictionary.base+2^((field*6)*M)≤ mid) (maskLow : menu.mask.base+H*chunks G M≤ mid)
    (wire : menu.source.base=mid) :
    let op:=assembly tables reads
    let n:=H*chunks G M
    let dst:=imageBank H G M out menu (image mid n op mem)
    ((scan w mid n op).seq (DescentSIMDLookup.program menu out H G M w)).Exec mem dst
      ((4+n*(2*op.work+4))+(4+44*n)) ∧
    (∀p : Row H G M,dst (out+(row H G M p).val)=((data (fun a g=>withHost D k r Y L cap links prog b s (x a g)) p).val:Word w)) ∧
    (∀a g,digit b (lane g positive).val (dst (out+(row H G M (position a g positive)).val)).val=(withHost D k r Y L cap links prog b s (x a g)).val) ∧
    ∀addr,(addr< mid ∨ mid+n≤addr)→(addr<out ∨ out+n≤addr)→dst addr=mem addr :=
  DescentIssuedGoodHeaders.gathered_words _ tables reads menu mid out x positive mem bounds constants sources room fit rom dictLow maskLow wire

end Hierarchy.DescentResetStemWord
namespace Hierarchy.DescentSixParty.ClosedReset.Window
set_option quotPrecheck false
open DescentCompiler DescentColonies DescentSharedCableNames DescentParallelBase DescentChosenRouter
open DescentResetCompactParent DescentResetCableSlots DescentResetOrdinalDigits DescentResetWireTags
open DescentRouterSlots DescentPackedTicketChronology DescentOrderedReset
open DescentResetSourceTicketRAM DescentResetSourceTicketCompare
open DescentSIMDLookup DescentGL DescentResetStemCompactOrder DescentIssuedFallbackPanel
open scoped Classical BigOperators Fin.CommRing
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail w hist : ℕ}
  {input : Reached W G q ε S k i z D w hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset input ctl)
local notation "R" => B.reset.placement
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "A" => input.placement
local notation "old" => W.granular B.count (z*G.b) B.fit
local notation "birth" => DescentOrderedReset.grains W B.count B.order
local notation "coarse" => (Z).orderedReentry T birth
local notation "vertex" => B.frame.host.symm.toEmbedding.trans input.vertex
local notation "U" => Fintype.card input.V
local notation "H" => input.placement.degree+2
local notation "Y" => (2^(Z).n:ℕ)
local notation "height" => GroupStage.depthBound D n f g
local notation "r" => (Z).k-(T).commonDepth
local notation "L" => (2^(S.groupWidth k tail i+k-(T).commonDepth)+1)*H*2^k
local notation "slots" => max Y (2^height)
local notation "pcCap" => max (Fintype.card (DescentCommonPalette.rotor (Z).graph).Edge) (2^(height+1))
local notation "okCode" => fun t=>((T).codeLegal t).2
local notation "Host" => Stage.Host (Fin (S.groupCount (i+1))) B.next.V k
local notation "Kind" => (Bool×(old).graph.Edge) ⊕ ((Z).Fallback ⊕ ((R).Contact ⊕ PrivateOccurrence B))
local notation "Short" => DescentResetCompactParent.Word H r Y L (A).cap slots pcCap

local notation "tape" => (Z).nativeResetEdges T vertex birth


local notation "digits" => S.resetInputDigits ctl.base ctl.radix i
local notation "fitBlock" => B.frame.enough.trans (Nat.sub_le ..)
local notation "previous" => input.order.trans Fin.valEmbedding
local notation "groupTable" => fun u : Host=>groupDomain digits B.frame.basis fitBlock (B.frame.host.symm (receiverRoot B u).1) (receiverRoot B u).2
local notation "halo" => fun u : Host=>hostDomain A input.vertex (B.frame.host.symm (receiverRoot B u).1)

open DescentIssuedFallbackPanel DescentResetStemWord
open private Hierarchy.DescentSixParty.ClosedReset.Window.grain_at
  from OAI.Hierarchy.DescentResetStemRead
local notation "coarseFit" => (T).commonDepth
local notation "Slot" => Block (S.groupWidth k tail i+k-coarseFit)×Fin (2*(A).cap)
local notation "actor" => fun (u : Host) => B.frame.host.symm (receiverRoot B u).1
local notation "short" => fun (u : Host) => (receiverRoot B u).2
local notation "siteNames" => DescentPacking.PackedMatch.Local.Stage.cableNames k
  (DescentStageEdgeReceipt.groupRank (Fin.valEmbedding (n:=S.groupCount i)) (input.vertex.trans Fin.valEmbedding))

def oldSelfCode (u : Host) : ℕ:=hostCode (compress (halo u) (input.vertex (actor u)).val)
  (decide (actor u∉(A).near (actor u)))

/-- A genuine signed old grain, the two measured GL digits, one scalar
old-host descriptor and the already observed occupancy suffice at every
stem candidate. Inactive spoke rows are entirely zero. -/
theorem stem_number_raster (u : Host) (s : Bool) (slot : Slot) {field b : ℕ} (x : Fin 6→Cell field)
    (room : (A).degree+1<2^field)
    (chip : (x 0).val=(DescentSignedCableCodec.encode (Stage.signedPanel A previous S input.valid siteNames
      (donor digits B.frame.basis fitBlock (actor u) (short u) slot.1) slot.2)).val)
    (groupRead : (x 1).val=compress (groupTable u)
      (digits ((rearrange B.frame.basis).symm (oldCell B u.2 slot.1 u.1.1))).1.val)
    (self : (x 2).val=oldSelfCode B u)
    (blockRead : (x 3).val=((rearrange B.frame.basis).symm (oldCell B u.2 slot.1 u.1.1)).val%2^k)
    (active : ((x 4).val≠0) ↔ (localOrigin B u (stemIndex B s slot)).isSome=true)
    (zero : decide ((x 5).val≠0)=zeroCoarse B u) :
    withHost (A).degree k r Y L (A).cap slots pcCap b s x=
      (localOrigin B u (stemIndex B s slot)).elim 0 (fun t=>((wordNumber B u t.val:ℕ):Cell b)) := by
  cases site:localOrigin B u (stemIndex B s slot) with
  | none=>
    have none:(x 4).val=0:=by simpa only [site,Option.isSome_none,Bool.false_eq_true,iff_false,not_not] using active
    apply inactive
    simpa [truthful] using none
  | some e=>
    obtain ⟨j,peer,found⟩:=(stem_at_iff B u s slot e).mp site
    rw [Option.elim_some,peer]
    let a:=beforeStem B j
    let p:=port A s a
    let oldAt:=donor digits B.frame.basis fitBlock (actor u) (short u) slot.1
    have located: address A previous S input.valid p=(oldAt,slot.2):=
      (atSlot_iff A previous S input.valid s oldAt slot.2 a).mp ((Hierarchy.DescentSixParty.ClosedReset.Window.grain_at B u s slot j).mp found)
    have same:= (port_fst A s a).symm.trans (congrArg Prod.fst located)
    have hostEq:((A).pos (endSite A s a)).2=actor u:=congrArg (fun t:Stage.Host _ _ k=>t.1.2) same
    have data:(x 0).val=(DescentSignedCableCodec.encode (Stage.signedPanel A previous S input.valid
      siteNames p.1 (Stage.signed A previous S input.valid p.1.1 p.1.2 p.2))).val :=
      chip.trans (congrArg (fun q:Stage.Host (Fin (S.groupCount i)) input.V k×Fin (2*(A).cap)=>
        (DescentSignedCableCodec.encode (Stage.signedPanel A previous S input.valid siteNames q.1 q.2)).val) located).symm
    have honest:=data
    rw [Stage.signed_read] at honest
    have computed:=effective_read (A).degree (A).cap s _ (x 0) (x 2) _ _ honest self
    have actual:=source_halo A previous S input.valid (Fin.valEmbedding (n:=S.groupCount i)) input.vertex s a
    dsimp only at actual
    simp only [hostEq] at actual
    have trueRank:effective (A).degree (A).cap s (x 0) (x 2)=compress (halo u) (input.vertex ((A).pos (W.graph.src a.1)).2).val:=
      computed.trans actual
    have rankBound:(compress (halo u) (input.vertex ((A).pos (W.graph.src a.1)).2).val)<2^field:=
      (compress_bound ..).trans_lt ((host_bound A input.vertex (actor u)).trans_lt room)
    change render _ _ _ _ _ _ _ _ _ s _=_
    apply stem_word_read B u s j siteNames
    · simpa [truthful] using data
    · have read:=cell_group B u s slot j found
      exact (by simpa [truthful] using groupRead.trans read)
    · simp only [truthful,Function.update_self,trueRank,Fin.val_cast_of_lt rankBound]
      rfl
    · simpa [truthful] using blockRead.trans (cell_fine B u s slot j found)
    · simpa [truthful] using active.mpr (by simp [site])
    · simpa [truthful] using zero

variable {N field b M Wd : ℕ} (receivers : Fin N→Option B.next.V)
local notation "ng" => S.groupCount (i+1)

/-- The six observations actually needed at live grid points. Ghost rows
carry only the original inactive bit. -/
structure StemInputs (block : Block k) (s : Bool) (slot : Slot)
    (xs : Fin N→Fin ng→Fin 6→Cell field) : Prop where
  ghost : ∀v g₀,receivers v=none→(xs v g₀ 4).val=0
  chip : ∀v g₀ h₀,receivers v=some h₀→let u : Host:=((g₀,h₀),block)
    (xs v g₀ 0).val=(DescentSignedCableCodec.encode (Stage.signedPanel A previous S input.valid siteNames
      (donor digits B.frame.basis fitBlock (actor u) (short u) slot.1) slot.2)).val
  group : ∀v g₀ h₀,receivers v=some h₀→let u : Host:=((g₀,h₀),block)
    (xs v g₀ 1).val=compress (groupTable u)
      (digits ((rearrange B.frame.basis).symm (oldCell B block slot.1 g₀))).1.val
  self : ∀v g₀ h₀,receivers v=some h₀→(xs v g₀ 2).val=oldSelfCode B ((g₀,h₀),block)
  fine : ∀v g₀ h₀,receivers v=some h₀→(xs v g₀ 3).val=
    ((rearrange B.frame.basis).symm (oldCell B block slot.1 g₀)).val%2^k
  active : ∀v g₀ h₀,receivers v=some h₀→((xs v g₀ 4).val≠0 ↔
    (localOrigin B ((g₀,h₀),block) (stemIndex B s slot)).isSome=true)
  zero : ∀v g₀ h₀,receivers v=some h₀→decide ((xs v g₀ 5).val≠0)=zeroCoarse B ((g₀,h₀),block)

open DescentPackedZip DescentPacking.PackedMatch.Local.Gather DescentPackedFallbackTree.Image
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
theorem stem_read_number (block : Block k) (s : Bool) (slot : Slot)
    (xs : Fin N→Fin ng→Fin 6→Cell field) (observed : StemInputs B receivers block s slot xs)
    (hostRoom : (A).degree+1<2^field) (v : Fin N) (g₀ : Fin ng) : withHost (A).degree k r Y L (A).cap slots pcCap b s (xs v g₀)=
      (actualParentNumber B receivers block (stemIndex B s slot) v g₀:Cell b):=by
  cases hv:receivers v with
  | none=>simp [actualParentNumber,hv,withHost,render,truthful,observed.ghost _ _ hv]
  | some h₀=>
    have seen:=stem_number_raster (b:=b) B ((g₀,h₀),block) s slot (xs v g₀) hostRoom
      (observed.chip _ _ _ hv) (observed.group _ _ _ hv) (observed.self _ _ _ hv)
      (observed.fine _ _ _ hv) (observed.active _ _ _ hv) (observed.zero _ _ _ hv)
    cases hit:localOrigin B ((g₀,h₀),block) (stemIndex B s slot) <;>
      simpa only [actualParentNumber,hv,Option.elim_some,hit,Option.elim_none,Nat.cast_zero] using seen

theorem stem_sheet (block : Block k) (s : Bool) (slot : Slot)
    (tables : Fin 6→Tables) (reads : Fin 6→Expr) (menu : DescentSIMDLookup.Banks) (mid out : ℕ)
    (xs : Fin N→Fin ng→Fin 6→Cell field) (observed : StemInputs B receivers block s slot xs)
    (hostRoom : (A).degree+1<2^field) (positive : 0<M) (mem : Memory Wd)
    (bounds : Bounds (w:=Wd) (d:=field) (M:=M) tables reads mid)
    (constants : ∀j,Static (tables j) (setField (d:=field) j) M mem)
    (sources : ∀j,Source (reads j) (fun v g₀=>xs v g₀ j) M mem)
    (room : mid+N*chunks ng M<2^Wd) (fit : DescentSIMDLookup.Fits menu (field*6) b M N ng Wd out)
    (rom : resident (withHost (A).degree k r Y L (A).cap slots pcCap b s ∘ (DescentSIMDLookup.encode field 6).symm)
      menu N ng M mem) (dictLow : menu.dictionary.base+2^((field*6)*M)≤ mid)
    (maskLow : menu.mask.base+N*chunks ng M≤ mid) (wire : menu.source.base=mid) :
    let op:=assembly tables reads
    let n:=N*chunks ng M
    let dst:=imageBank N ng M out menu (image mid n op mem)
    ((scan Wd mid n op).seq (DescentSIMDLookup.program menu out N ng M Wd)).Exec mem dst
      ((4+n*(2*op.work+4))+(4+44*n)) ∧
    (∀p : Row N ng M,dst (out+(row N ng M p).val)=
      ((data (fun v g₀=>(actualParentNumber B receivers block (stemIndex B s slot) v g₀:Cell b)) p).val:Word Wd)) ∧
    ∀a,(a< mid ∨ mid+n≤a)→(a<out ∨ out+n≤a)→dst a=mem a := by
  intro op n dst
  obtain ⟨exec,read,digits_,stable⟩:=runHost (A).degree k r Y L (A).cap slots pcCap b s tables reads menu
    mid out xs positive mem bounds constants sources room fit rom dictLow maskLow wire
  refine ⟨exec,?_,stable⟩
  have point:=stem_read_number (b:=b) B receivers block s slot xs observed hostRoom
  intro p
  simpa only [point] using read p
end Hierarchy.DescentSixParty.ClosedReset.Window
end

end OAI
