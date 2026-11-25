import OAI.Hierarchy.DescentPaddedRasterValue
import OAI.Hierarchy.DescentOrdinaryOriginReturn
import OAI.Hierarchy.DescentOrdinaryOriginSupport
import OAI.Hierarchy.DescentReachedPaidRaster
import OAI.Hierarchy.DescentReachedAtomFieldRAM

namespace OAI
/-! The actual dated signed venue and full old archive supply every returned positive node ordinal. -/
namespace Hierarchy.DescentLocalArchiveOrder.PaddedOrigin
open DescentNetworkPartition Computability.BorderVNP.Crossing
open DescentKernelHistory DescentSixParty DescentSixParty.Chronology DescentCompiler DescentStageEdgeReceipt
open DescentCableDonorNames DescentOrdinaryLocalBirth DescentHostDegree DescentHostDirectory DescentOrdinaryDonorHalo
open DescentNetworkPartition Computability.BorderVNP.Crossing DescentSharedCableNames DescentSixParty.StarKeys
open DescentColonies DescentGL DescentWalshTables DescentPacking
open DescentGroupPeerOrder DescentPacking.PackedMatch.Local.Stage DescentSortedHaloRaster DescentHaloWalkRAM DescentSIMDLookup
open DescentScalarVenueMask DescentHostDirectory.SiteDecode DescentOrdinaryLocalBirth DescentSharedCableNames DescentPackedActorMask
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM DescentScalarBookReshape
open scoped Classical Fin.CommRing
set_option quotPrecheck false
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F}
variable {u q ε : ℝ} {S : AtomSchedule} {k i z D z' D' wire hist : ℕ}
    {cap : Reached W G q ε S k i z D wire hist}
    {he : 0≤ε} {T : StageInput W G u ε} {c : (T.result he).Choice}
    {n : Normalize ((T.result he).state c)} {target : Reached n.result G q ε S k (i+1) z' D' wire hist}
    (ticket : OrdinaryLink cap he T c n target) (arch : Archive W)
local notation "r" => BitDescription.scannedRows he T
local notation "capV" => Fin (S.groupCount i)×cap.V
local notation "sw" => branchWidth G (fun _ : (r).pairs=>T.z) ((r).profile c)
local notation "stepGraph" => rawGraph he T c
local notation "sel" => scanWorld he T c
local notation "next" => (ticket.advance arch).bit
local notation "units" => fun _ : (r).pairs=>T.z
local notation "stageLimit" => fun _ : (r).pairs=>le_refl T.z
local notation "layout" => bestLayout sw
local notation "group" => GadgetNetwork.newSite W.graph (r).pick layout (r).pack
local notation "M" => ticket.issued.common_chart he T c ((r).state c)

local notation "bookChart" => activeChart ticket
local notation "key" => (bookChart).key he T c
local notation "addr" => MarkedWorld.address sel key (bookChart).hub T.k (gainExponent 20 T.Δ)
local notation "C" => ↥(MarkedWorld.reclaimed sel key (bookChart).hub T.k (gainExponent 20 T.Δ))
local notation "venue" => addr ∘ group
local notation "base" => physicalBits G W.toWorld (r).pick units stageLimit ((r).profile c) arch.bit.recipe

local notation "A" => cap.placement
local notation "deg" => (A).degree
local notation "near" => groupedNear (A).near
local notation "bound" => DescentHaloWalkRAM.breadth deg*2^k
local notation "sites" => (A).site cap.vertex cap.valid.coordinates

local notation "roster" => hostRotor cap.vertex (hostRoster A (cap.vertex.trans Fin.valEmbedding))
local notation "reach" => Gather.reaching roster
local notation "halo" => reachedHalo ticket
local notation "name" => rackName (cap:=cap)

local notation "shelf"=>2^(packExponent 20 deg)+2
local notation "pitch"=>(2^(k+1)-1)*shelf
local notation "raw"=>2^(k+1)*shelf
local notation "used"=>fun p:(r).pairs=>(r).picked (p,0)
local notation "oldID"=>cap.order.trans Fin.valEmbedding
local notation "origin"=>outgoingSlot A oldID S cap.valid (r).pick used
local notation "breadth"=>DescentHaloWalkRAM.breadth deg
local notation "ticketSlots"=>1+(A).cap*6
local notation "moves"=>rotor A (groupRank Fin.valEmbedding (cap.vertex.trans Fin.valEmbedding))

open DescentPaidResidentCount
variable {mb : ℕ}
variable (tokens : Block k→Fin (1+cap.placement.cap*6)→Fin (Fintype.card cap.V)→Fin (S.groupCount i)→
  Ticket (DescentHaloWalkRAM.breadth cap.placement.degree) (2^(k+1)*(2^(packExponent 20 cap.placement.degree)+2)))
local notation "physical" => DescentScalarVenueMask.fields reach tokens (flags (cap:=cap)) k (gainExponent 20 deg) shelf pitch
local notation "stock" => Descriptors shelf k (A).pos (A).block (ticketParent (he:=he) (T:=T)) (ticketSlot (c:=c) ticket)
  (key∘group) cap.vertex (Function.Embedding.refl _) moves tokens
local notation "oldCensus" => fun x h g=>Census.count A (Equiv.refl _) cap.vertex mb h g x
local notation "bookCounts" => DescentOrdinaryAtomFieldRAM.RoleCounts.priorValue reach oldCensus
local notation "cost" => fun u : W.graph.Site=>((A).records u).length
local notation "dest" => n.destination∘rawInput he T c ((r).state c)

local notation "OH" => Fintype.card cap.V
local notation "OG" => S.groupCount i
local notation "NH" => Fintype.card target.V
local notation "NG" => S.groupCount (i+1)
variable (age : i<S.length) (radix : S.radix=2^k)
local notation "digits" => S.groupDigits age radix
local notation "coord" => DescentPaidResidentCount.occupies target.placement (Equiv.refl _) target.vertex


local notation "xn" => fun _ : (sel).graph.Site=>(0 : EuclideanSpace ℝ (Fin d))
local notation "yc" => fun _ : C=>(0 : EuclideanSpace ℝ (Fin d))
local notation "xnOk" => fun v : (sel).graph.Site=>(by simp : ‖xn v‖≤1)
local notation "ycOk" => fun v : C=>(by simp : ‖yc v‖≤1)
local instance : Fintype (DescentSixParty.Merged W.graph (r).pick layout (r).pack) := (sel).graph.finiteSite
local notation "first" => quotientBits stepGraph group xn xnOk base
local notation "second" => quotientBits (quotient stepGraph group xn xnOk) addr yc ycOk first
local notation "dest_" => n.destination∘rawInput he T c ((r).state c)
variable {K₀ : ℕ} (fits₀ : maxNodes arch.bit≤K₀)
local notation "oldN" => K₀
local notation "N₀" => DescentPackedActorMask.nodes bound oldN (A).cap
variable (prior : Local arch.bit)
local notation "ord₀" => fun u => ((bounded arch.bit prior u).trans (Fin.castLEEmb fits₀))
variable (priorCount : Block k → Fin (Fintype.card cap.V) → Fin (S.groupCount i) → Cell mb)
variable (old_live : ∀u,(priorCount (cap.placement.block u) (cap.vertex (cap.placement.pos u).2) (cap.placement.pos u).1).val=
    Fintype.card (arch.bit.recipe u).Node)
variable (old_empty : ∀b h g,(¬∃u,cap.placement.block u=b ∧ cap.vertex (cap.placement.pos u).2=h ∧ (cap.placement.pos u).1=g)→priorCount b h g=0)
local notation "priorData" => DescentOrdinaryAtomFieldRAM.RoleCounts.priorValue reach priorCount

/-- At any actual actor, including a zero-node actor, the two quotients have the same full node fiber. -/
def actorFiber (a : (stepGraph).Site) : ((next).recipe (dest_ a)).Node ≃ (second (venue a)).Node :=
  ((fiber ticket arch (dest_ a)).trans ((Equiv.refl _).subtypeEquiv (fun s=>by
    have loc := (Classical.choose_spec (M)).1.2 (rawNodeSite (he:=he) (T:=T) (c:=c) arch s) a
    cases s <;> exact ⟨fun h=>Subtype.ext (loc.mp h), fun h=>loc.mpr (congrArg Subtype.val h)⟩))).trans
    (coefficientFiber arch.bit (r).pick units stageLimit ((r).profile c) group addr xn yc xnOk ycOk _).symm

def originRaster (K' b : ℕ) (l : Fin pitch) (h : Fin OH) (g : Fin OG) : Cell (b*K') :=
  let _:=ticket
  let _:=arch
  DescentOrdinaryOriginMask.selection N₀ K' b (DescentPackedActorMask.occupied bound oldN (A).cap mb
    (DescentPackedActorMask.target (Packed.bits pitch) _ (Packed.token (some l)) (encode _ _ (physical h g)))
    (encode mb bound (priorData h g)))

def originBits (l : Fin pitch) (h : Fin OH) (g : Fin OG) : Cell (1*N₀) :=
  let _:=ticket
  let _:=arch
  DescentPackedActorMask.occupied bound oldN (A).cap mb
    (DescentPackedActorMask.target (Packed.bits pitch) _ (Packed.token (some l)) (encode _ _ (physical h g)))
    (encode mb bound (priorData h g))

def originIndex (a : (stepGraph).Site) : (second (venue a)).Node ↪ Fin N₀ :=
  short A oldID S cap.valid arch.bit (r).pick units stageLimit ((r).profile c) used group addr xn yc xnOk ycOk halo
    (reachedHalo_members ticket).1 (reachedHalo_members ticket).2 ord₀ (venue a)

set_option maxHeartbeats 1200000 in
include old_live old_empty in
theorem origin_mask_covers (auth : stock) (a : (stepGraph).Site) (l : Fin pitch)
    (name_ : localNumber k shelf (venue a).val=l.val) (z₀ : Fin N₀) :
    (encode 1 N₀).symm (originBits (K₀:=K₀) ticket arch tokens priorCount l
      (cap.vertex (venue a).val.1.2) (venue a).val.1.1) z₀≠0 ↔
      ∃u,originIndex ticket arch fits₀ prior a u=z₀ :=by
  let c₀:=venue a
  let wanted:=Packed.token (some l)
  let address:=physical (cap.vertex c₀.val.1.2) c₀.val.1.1
  let ss:=priorData (cap.vertex c₀.val.1.2) c₀.val.1.1
  have alive:wanted≠0:=fun eqn=>by have fail:=congrArg Fin.val eqn; change l.val+1=0 at fail; omega
  have dense (u : W.graph.Site) (n₀ : Fin oldN) : n₀.val<Fintype.card (arch.bit.recipe u).Node ↔
      ∃x,(ord₀) u x=n₀ :=old_dense_of_equiv (prior u) ((Finset.le_sup (f:=fun y=>Fintype.card (arch.bit.recipe y).Node) (Finset.mem_univ u)).trans fits₀) n₀
  have counted (d₀ : Fin bound) : (ss d₀).val=((donorAt halo c₀ d₀).map (fun u=>Fintype.card (arch.bit.recipe u).Node)).getD 0 :=by
    have h:=counted_prior ticket c₀ d₀ (fun u=>Fintype.card (arch.bit.recipe u).Node) priorCount old_live old_empty
    cases q : donorAt halo c₀ d₀ <;> simpa [ss,q] using h
  have oldAt:=old_venue ticket tokens auth c₀ l name_
  have bornAt:=born_venue ticket tokens auth c₀ l name_
  let state:=CandidateData.fromAddresses («K»:=oldN) wanted address ss
  change (encode 1 N₀).symm (DescentPackedActorMask.occupied bound oldN (A).cap mb
    (DescentPackedActorMask.target _ _ wanted (encode _ _ address)) (encode mb bound ss)) z₀≠0 ↔ _
  rw [issued_mask (K:=oldN) A wanted address ss alive,Equiv.symm_apply_apply]
  exact active_iff A oldID S cap.valid arch.bit (r).pick units stageLimit ((r).profile c) used group addr xn yc xnOk ycOk
    halo (reachedHalo_members ticket).1 (reachedHalo_members ticket).2 ord₀ c₀ state
    (fun _ _=>measured_old (count_read:=counted) (target_old:=oldAt) (old_dense:=dense) ..)
    (fun _ _ _=>measured_born (target_new:=bornAt) ..) z₀

include fits₀ old_live old_empty prior in
theorem origin_at_actor (auth : stock) (a : (stepGraph).Site) (l : Fin pitch)
    (name_ : localNumber k shelf (venue a).val=l.val) {K' b : ℕ} (wide : N₀<2^b) (j : Fin K') :
    (encode b K').symm (originRaster (K₀:=K₀) ticket arch tokens priorCount K' b l
        (cap.vertex (venue a).val.1.2) (venue a).val.1.1) j ≠0 ↔
      j.val<Fintype.card ((next).recipe (dest_ a)).Node :=by
  rw [Fintype.card_congr (actorFiber ticket arch a)]
  exact DescentOrdinaryOriginMask.population_iff (originIndex ticket arch fits₀ prior a) _
    (origin_mask_covers ticket arch tokens fits₀ prior priorCount old_live old_empty auth a l name_) wide j

local notation "regroup" => fun f x h g=>book (oldInput age radix f) x (hostIndex ticket h) g

include fits₀ prior old_live old_empty in
/-- At every compact host, group and block the densely repitched origin history
has positive slots exactly for the full archive. Vacant cells have identically zero support. -/
theorem origin_book_iff (auth : stock) {K' b : ℕ} (wide : N₀<2^b)
    (h : Fin NH) (g : Fin NG) (x : Block k) (j : Fin K') :
    (encode b K').symm ((regroup) (originRaster (K₀:=K₀) ticket arch tokens priorCount K' b) x h g) j≠0 ↔
    ∃v,coord h g x v ∧ j.val<Fintype.card ((next).recipe v).Node :=by
  let pair:=finProdFinEquiv.symm (hostIndex ticket h)
  change (encode b K').symm (originRaster (K₀:=K₀) ticket arch tokens priorCount K' b pair.2 pair.1
    ((digits).symm (finProdFinEquiv.symm (finProdFinEquiv (g,x))))) j≠0 ↔ _
  rw [Equiv.symm_apply_apply]
  by_cases exists_ : ∃v,coord h g x v
  · obtain ⟨a,hh,hg,hl⟩:=(actor_at ticket age radix h g x).mp exists_
    have placed :=(actor_coords ticket age radix a h g x).mpr ⟨hh,hg,hl⟩
    have support:=origin_at_actor ticket arch tokens fits₀ prior priorCount old_live old_empty auth a pair.2 hl wide j
    rw [hh,hg] at support
    rw [support]
    constructor
    · intro live;exact ⟨_,placed,live⟩
    · rintro ⟨v,other,live⟩
      have equal : v=dest_ a :=target.valid.coordinates (Prod.ext (Prod.ext (other.2.1.trans placed.2.1.symm)
        (target.vertex.injective (other.1.trans placed.1.symm))) (other.2.2.trans placed.2.2.symm))
      exact equal ▸ live
  · have noHit : ¬∃i,physical pair.1 ((digits).symm (g,x)) i=Packed.token (some pair.2) :=
      mt (actor_presence ticket tokens auth pair.1 _ pair.2).mp
        (mt (actor_at ticket age radix h g x).mpr exists_)
    have blank : originRaster (K₀:=K₀) ticket arch tokens priorCount K' b pair.2 pair.1 ((digits).symm (g,x))=0 :=
      DescentOrdinaryOriginMask.vacant _ _ _ (fun i hi=>noHit ⟨i,hi⟩)
    have zz : (encode b K').symm 0=fun _=>0 :=by
      apply (encode b K').symm_apply_eq.mpr
      symm
      apply Fin.ext
      change (finFunctionFinEquiv (fun _=>(0 : Cell b))).val=0
      simp
    rw [blank,zz]
    simp only [ne_eq,not_true_eq_false,false_iff,not_exists]
    exact fun v hv=>exists_ ⟨v,hv.1⟩

open DescentPackedColony DescentPackedZip

include age radix fits₀ prior old_live old_empty in
/-- The actual issuer's memory is read at every new site and padding cell. -/
theorem returned_full (auth : stock) {K' b lanes w : ℕ} (wide : N₀<2^b)
    (floor : ℕ) (terms : Fin pitch→Expr) (m : Memory w) (hm : 0<lanes)
    (fit : ∀l,(terms l).Fits w floor)
    (space : (⟨OH,pitch,NG,2^k,b*K',lanes⟩:DescentOrdinaryOriginReshape.Layout).finish floor<2^w)
    (received : ∀l,Source (terms l) (oldInput age radix (originRaster (K₀:=K₀) ticket arch tokens priorCount K' b) l) (lanes*2^k) m) :
    let L:DescentOrdinaryOriginReshape.Layout:=⟨OH,pitch,NG,2^k,b*K',lanes⟩
    let book_:=fun x h g=>book (oldInput age radix (originRaster (K₀:=K₀) ticket arch tokens priorCount K' b)) x (hostIndex ticket h) g
    (∀x,Reads (L.returned floor x) (book_ x) lanes (L.image floor terms m)) ∧
    ∀x h g j,(encode b K').symm (book_ x h g) j≠0 ↔
      ∃v,coord h g x v ∧ j.val<Fintype.card ((next).recipe v).Node :=by
  intro L book_
  have native:=L.originReturned floor terms m fit space hm (Nat.two_pow_pos _) _ received
  exact ⟨transferred ticket age radix _ (L.out floor) _ native,
    fun x h g j=>origin_book_iff ticket arch tokens age radix fits₀ prior priorCount old_live old_empty auth wide h g x j⟩

open DescentOrdinaryRasterReturn

include prior old_live old_empty fits₀ in
/-- The public host directory includes every original host, followed by padding. A complete
extra row is zero and genuinely contributes no predecessor, even at positive group count. -/
theorem wide_book_iff (auth : stock) {K' b H : ℕ} (wide : N₀<2^b) (hFit : OH≤H)
    (h : Fin (H*pitch)) (g : Fin NG) (x : Block k) (j : Fin K') :
    let rows:=oldInput age radix (originRaster (K₀:=K₀) ticket arch tokens priorCount K' b)
    let names:=target.vertex.trans ((hostIndex ticket).toEmbedding.trans (Fin.castLEEmb (Nat.mul_le_mul_right pitch hFit)))
    ((encode b K').symm (book (fun l=>extend (H:=H) (rows l)) x h g) j≠0) ↔
      ∃v,DescentPaidResidentCount.occupies target.placement (Equiv.refl _) names h g x v ∧
        j.val<Fintype.card ((next).recipe v).Node :=by
  intro rows names
  by_cases low : h.val<OH*pitch
  · let vHost : Fin (OH*pitch):=⟨h.val,low⟩
    let host:Fin NH:=(hostIndex ticket).symm vHost
    have alias_ : widen hFit vHost=h:=Fin.ext rfl
    rw [←alias_,padded_book vHost rows hFit]
    have semantic:=origin_book_iff ticket arch tokens age radix fits₀ prior priorCount old_live old_empty auth wide host g x j
    change (((encode b K').symm (book rows x (hostIndex ticket host) g)) j≠0) ↔ _ at semantic
    rw [show hostIndex ticket host=vHost from Equiv.apply_symm_apply ..] at semantic
    rw [semantic]
    apply exists_congr
    intro v
    apply and_congr_left
    intro _
    constructor
    · rintro ⟨hh,hg,hx⟩
      refine ⟨?_,hg,hx⟩
      change widen hFit (hostIndex ticket (target.vertex (target.placement.pos v).2))=widen hFit vHost
      rw [hh];exact congrArg (widen hFit) (Equiv.apply_symm_apply ..)
    · rintro ⟨hh,hg,hx⟩
      refine ⟨(hostIndex ticket).injective (Fin.ext ?_),hg,hx⟩
      rw [show hostIndex ticket host=vHost from Equiv.apply_symm_apply ..]
      change widen hFit (hostIndex ticket (target.vertex (target.placement.pos v).2))=widen hFit vHost at hh
      exact congrArg (fun y : Fin (H*pitch) => y.val) hh
  · have absent : ¬∃v,DescentPaidResidentCount.occupies target.placement (Equiv.refl _) names h g x v ∧
        j.val<Fintype.card ((next).recipe v).Node :=by
      rintro ⟨v,placed,_⟩
      apply low
      have equal : widen hFit (hostIndex ticket (target.vertex (target.placement.pos v).2))=h := placed.1
      exact (congrArg (fun y : Fin (H*pitch) => y.val) equal ▸
        (hostIndex ticket (target.vertex (target.placement.pos v).2)).isLt)
    have blank : book (fun l=>extend (H:=H) (rows l)) x h g=0 :=by
      obtain ⟨⟨q,l⟩,rfl⟩:=finProdFinEquiv.surjective h
      have old : ¬q.val<OH:=by
        intro isOld
        let compact := finProdFinEquiv ((⟨q.val,isOld⟩:Fin OH),l)
        have equal : (finProdFinEquiv (q,l)).val=compact.val := rfl
        exact low (equal ▸ compact.isLt)
      simp only [DescentScalarBookReshape.book, Equiv.symm_apply_apply,
        DescentOrdinaryRasterReturn.extend, dite_eq_right_iff]
      exact fun fit => False.elim (old fit)
    rw [blank]
    have zz : (encode b K').symm 0=fun _=>0 :=by
      apply (encode b K').symm_apply_eq.mpr
      symm
      apply Fin.ext
      change (finFunctionFinEquiv (fun _=>(0:Cell b))).val=0
      simp
    simp only [zz,ne_eq,not_true_eq_false,false_iff]
    exact absent

open DescentOrdinaryAtomFieldRAM.ScalarOperand

/-- Only the signed venue and old full population affect the new origin stamp. The old and
birth value columns in the same measured wire can be any of its seven operand projections. -/
def values {field : ℕ} (l : Fin pitch) (v : Values deg k K₀ (A).cap OH (NG*2^k) field (Packed.bits pitch) mb) :
    Values deg k K₀ (A).cap OH (NG*2^k) field (Packed.bits pitch) mb := {v with
  wanted:=fun _ _=>Packed.token (some l)
  venues:=fun h g=>physical h ((digits).symm (finProdFinEquiv.symm g))
  counts:=fun h g=>priorData h ((digits).symm (finProdFinEquiv.symm g))}

def dated (K' b lanes : ℕ) : DescentOrdinaryOriginMask.Return :=
  let _:=ticket
  ⟨deg,k,K₀,(A).cap,K',b,OH,pitch,NG,2^k,lanes⟩

include old_live old_empty prior fits₀ in
/-- The unique actual output, after the one shared signed-mask lookup and the native transpose.
It is legal to retain this bank through all later writes whose proven lower frame exceeds its end. -/
theorem measured_full {K' b w lanes field : ℕ} (auth : stock) (wide : N₀<2^b)
    (floor : ℕ) (C₀ : Fin pitch→Refs deg k K₀ (A).cap) (m : Memory w)
    (V : Fin pitch→Values deg k K₀ (A).cap OH (NG*2^k) field (Packed.bits pitch) mb)
    (hm : 0<lanes) (room : (dated (K₀:=K₀) ticket K' b lanes).finish floor<2^w)
    (valid : ∀l,Measured (C₀ l) (values tokens age radix priorCount l (V l)) K' (lanes*2^k) floor m) :
    let R:=dated (K₀:=K₀) ticket K' b lanes
    let T:=fun x h g=>book (oldInput age radix (originRaster (K₀:=K₀) ticket arch tokens priorCount K' b)) x (hostIndex ticket h) g
    (∀x,Reads (R.returned floor x) (T x) lanes (R.image C₀ floor m)) ∧
    (∀x h g j,(encode b K').symm (T x h g) j≠0 ↔ ∃v,coord h g x v ∧ j.val<Fintype.card ((next).recipe v).Node) ∧
    (∀later : Memory w,(∀i,i<R.finish floor→later i=R.image C₀ floor m i)→∀x,Reads (R.returned floor x) (T x) lanes later) :=by
  intro R T
  have native:=R.originReturned C₀ floor m hm (Nat.two_pow_pos _) (fun l=>values tokens age radix priorCount l (V l)) valid room
  have actual : ∀x,Reads (R.returned floor x) (T x) lanes (R.image C₀ floor m) :=
    transferred ticket age radix _ (R.grid.out (R.rowsAt floor)) _ native
  refine ⟨actual,fun x h g j=>origin_book_iff ticket arch tokens age radix fits₀ prior priorCount old_live old_empty auth wide h g x j,?_⟩
  intro later frame x p
  have inFrame:=(R.grid.returned_fits (R.rowsAt floor) x room)
  have hostCount_ : NH=OH*pitch :=by rw [ticket.hostCount];ring
  have size : (row NH NG lanes p).val<(R.returned floor x).size :=
    (row NH NG lanes p).isLt.trans_le ((Nat.mul_le_mul_right (chunks NG lanes) hostCount_.le).trans inFrame.2)
  exact (frame _ ((Nat.add_lt_add_left size _).trans_le inFrame.1.2.2)).trans (actual x p)

/-- Signed venues and donor populations are absent at unused public hosts.
The requested low ordinal is still generated by the same fixed calendar. -/
def wideValues {field H : ℕ} (l : Fin pitch)
    (v : Values deg k K₀ (A).cap H (NG*2^k) field (Packed.bits pitch) mb) :
    Values deg k K₀ (A).cap H (NG*2^k) field (Packed.bits pitch) mb := {v with
  wanted:=fun _ _=>Packed.token (some l)
  venues:=fun h g=>if active : h.val<OH then physical ⟨h.val,active⟩ ((digits).symm (finProdFinEquiv.symm g)) else fun _=>0
  counts:=fun h g=>if active : h.val<OH then priorData ⟨h.val,active⟩ ((digits).symm (finProdFinEquiv.symm g)) else fun _=>0}

theorem selection_extends {H field K' b : ℕ} (l : Fin pitch)
    (v : Values deg k K₀ (A).cap H (NG*2^k) field (Packed.bits pitch) mb) (h : Fin H) (g : Fin (NG*2^k)) :
    DescentOrdinaryOriginMask.selection N₀ K' b
      (DescentOrdinaryOriginMask.marked (wideValues tokens age radix priorCount l v) h g)=
      extend (oldInput age radix (originRaster (K₀:=K₀) ticket arch tokens priorCount K' b) l) h g :=by
  by_cases live : h.val<OH
  · simp only [wideValues,DescentOrdinaryOriginMask.marked,DescentOrdinaryRasterReturn.extend,dite_eq_left live,oldInput,originRaster]
  · simp only [wideValues,DescentOrdinaryOriginMask.marked,DescentOrdinaryRasterReturn.extend,dite_eq_right live]
    apply DescentOrdinaryOriginMask.vacant
    intro _ e
    have impossible:=congrArg Fin.val e
    change 0=l.val+1 at impossible
    omega

include fits₀ prior old_live old_empty in
/-- Every coordinate in the original public (potentially padded) host rectangle is read
from the real transpose. The lower frame makes the reissued role page durable afterwards. -/
theorem measured_public {H K' b w lanes field : ℕ} (auth : stock) (wide : N₀<2^b) (hFit : OH≤H)
    (floor : ℕ) (C₀ : Fin pitch→Refs deg k K₀ (A).cap) (m : Memory w)
    (V : Fin pitch→Values deg k K₀ (A).cap H (NG*2^k) field (Packed.bits pitch) mb)
    (hm : 0<lanes) (room : ({dated (K₀:=K₀) ticket K' b lanes with hosts:=H}:
      DescentOrdinaryOriginMask.Return).finish floor<2^w)
    (valid : ∀l,Measured (C₀ l) (wideValues tokens age radix priorCount l (V l)) K' (lanes*2^k) floor m) :
    let R:DescentOrdinaryOriginMask.Return:={dated (K₀:=K₀) ticket K' b lanes with hosts:=H}
    let names:=target.vertex.trans ((hostIndex ticket).toEmbedding.trans (Fin.castLEEmb (Nat.mul_le_mul_right pitch hFit)))
    let rows:=oldInput age radix (originRaster (K₀:=K₀) ticket arch tokens priorCount K' b)
    let table:=fun x=>book (fun l=>extend (H:=H) (rows l)) x
    (∀x,Reads (R.returned floor x) (table x) lanes (R.image C₀ floor m)) ∧
    (∀x h g j,(encode b K').symm (table x h g) j≠0 ↔
      ∃v,DescentPaidResidentCount.occupies target.placement (Equiv.refl _) names h g x v ∧
        j.val<Fintype.card ((next).recipe v).Node) ∧
    (∀later : Memory w,(∀i,i<R.finish floor→later i=R.image C₀ floor m i)→
      ∀x,Reads (R.returned floor x) (table x) lanes later) :=by
  intro R names rows table
  have native:=R.originReturned C₀ floor m hm (Nat.two_pow_pos _) (fun l=>wideValues tokens age radix priorCount l (V l)) valid room
  have eqRows : (fun l h g=>DescentOrdinaryOriginMask.selection N₀ K' b
      (DescentOrdinaryOriginMask.marked (wideValues tokens age radix priorCount l (V l)) h g)) =
      (fun l=>extend (H:=H) (rows l)) :=
    funext fun l=>funext fun h=>funext fun g=>selection_extends ticket arch tokens age radix priorCount l (V l) h g
  have actual : ∀x,Reads (R.returned floor x) (table x) lanes (R.image C₀ floor m) := by
    intro x
    change Reads _ (DescentScalarBookReshape.book (fun l=>DescentOrdinaryRasterReturn.extend (H:=H) (rows l)) x) _ _
    rw [←eqRows]
    exact native x
  refine ⟨actual,fun x h g j=>wide_book_iff ticket arch tokens age radix fits₀ prior priorCount old_live old_empty auth wide hFit h g x j,?_⟩
  intro later frame x row_
  have fit:=R.grid.returned_fits (R.rowsAt floor) x room
  have size:=(row (H*pitch) NG lanes row_).isLt.trans_le fit.2
  exact (frame _ ((Nat.add_lt_add_left size _).trans_le fit.1.2.2)).trans (actual x row_)

/-- The physical chronology records exactly which original actor supplied the selected node. -/
def originCandidate (v : n.result.graph.Site) (node : ((next).recipe v).Node) : Fin N₀ :=
  let a:=rawNodeSite (he:=he) (T:=T) (c:=c) arch (roots ticket arch ⟨v,node⟩)
  originIndex ticket arch fits₀ prior a (printed ticket arch v node node)

include old_live old_empty in
theorem origin_at_node (auth : stock) (v : n.result.graph.Site) (node : ((next).recipe v).Node)
    {b K' : ℕ} (wide : N₀<2^b) (fits : (advance ticket arch prior v node).val<K') :
    let bank:=book (oldInput age radix (originRaster (K₀:=K₀) ticket arch tokens priorCount K' b)) (target.placement.block v)
      (hostIndex ticket (target.vertex (target.placement.pos v).2)) (target.placement.pos v).1
    (((encode b K').symm bank) ⟨(advance ticket arch prior v node).val,fits⟩).val =
      (originCandidate ticket arch fits₀ prior v node).val+1:=by
  let a:=rawNodeSite (he:=he) (T:=T) (c:=c) arch (roots ticket arch ⟨v,node⟩)
  let l:=localIndex ticket arch v node
  let ids:=originIndex ticket arch fits₀ prior a
  let payload:=printed ticket arch v node node
  let bits_:=originBits (K₀:=K₀) ticket arch tokens priorCount l (cap.vertex (venue a).val.1.2) (venue a).val.1.1
  have low : localNumber k shelf (venue a).val=l.val:=by
    simp [l,localIndex,DescentPackedChildNeighbor.lowDigit,localNumber,packedNumber,currentLabel,a,splitKey]
    rfl
  have cover:=origin_mask_covers ticket arch tokens fits₀ prior priorCount old_live old_empty auth a l low
  have occ : (encode 1 N₀).symm bits_ (ids payload)≠0:=(cover _).2 ⟨payload,rfl⟩
  have rank : DescentPackedLocalAtoms.earlier ((encode 1 N₀).symm bits_) (ids payload)=(advance ticket arch prior v node).val:=by
    apply (DescentOrdinaryOriginMask.earlier_index ids bits_ cover payload).trans
    exact actual_ordinal ticket arch halo (reachedHalo_members ticket).1 (reachedHalo_members ticket).2
      prior ord₀ (reachedHalo_order ticket) (fun _ _=>rfl) v node
  dsimp only
  rw [selected_book ticket arch age radix v node]
  exact DescentOrdinaryOriginMask.stamp_at N₀ K' b bits_ ⟨_,fits⟩ (ids payload) occ rank wide

end
end Hierarchy.DescentLocalArchiveOrder.PaddedOrigin

end OAI
