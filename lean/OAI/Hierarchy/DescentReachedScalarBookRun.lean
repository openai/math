import OAI.Hierarchy.DescentReachedScalarReshape

namespace OAI
/-! # stage live ordinary scalar field from the native old-book and six-party donor pages -/
namespace Hierarchy.DescentLocalArchiveOrder
open DescentKernelHistory DescentSixParty DescentSixParty.Chronology DescentCompiler DescentStageEdgeReceipt
open DescentCableDonorNames DescentOrdinaryLocalBirth DescentHostDegree DescentHostDirectory
open DescentNetworkPartition Computability.BorderVNP.Crossing DescentSharedCableNames DescentSIMDLookup DescentPackedLocalAtoms
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM DescentScalarBookReshape DescentHaloWalkRAM
open DescentColonies DescentGL DescentWalshTables DescentPacking DescentSixParty.StarKeys DescentOrdinaryDonorHalo
open DescentPacking.PackedMatch.Local.Stage DescentGroupPeerOrder
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F}
variable {u q ε : ℝ} {S : AtomSchedule} {k i z D z' D' wire hist : ℕ}
    {cap : Reached W G q ε S k i z D wire hist}
    {he : 0≤ε} {T : StageInput W G u ε} {c : (T.result he).Choice}
    {n : Normalize ((T.result he).state c)} {target : Reached n.result G q ε S k (i+1) z' D' wire hist}
    (ticket : OrdinaryLink cap he T c n target) (arch : Archive W)
local notation "r" => BitDescription.scannedRows he T
local notation "sw" => branchWidth G (fun _ : (r).pairs=>T.z) ((r).profile c)
local notation "stepGraph" => rawGraph he T c
local notation "sel" => scanWorld he T c
local notation "next" => (ticket.advance arch).bit
local notation "units" => fun _ : (r).pairs=>T.z
local notation "stageLimit" => fun _ : (r).pairs=>le_refl T.z
local notation "layout" => bestLayout sw
local instance : Fintype (DescentSixParty.Merged W.graph (r).pick layout (r).pack) := (sel).graph.finiteSite
local notation "group" => GadgetNetwork.newSite W.graph (r).pick layout (r).pack
local notation "bookChart" => activeChart ticket
local notation "key" => (bookChart).key he T c
local notation "addr" => MarkedWorld.address sel key (bookChart).hub T.k (gainExponent 20 T.Δ)
local notation "C" => ↥(MarkedWorld.reclaimed sel key (bookChart).hub T.k (gainExponent 20 T.Δ))
local notation "venue" => addr ∘ group
local notation "stageBits" => physicalBits G W.toWorld (r).pick units stageLimit ((r).profile c) arch.bit.recipe
local notation "x₁" => fun _ : (sel).graph.Site=>(0 : EuclideanSpace ℝ (Fin d))
local notation "x₂" => fun _ : C=>(0 : EuclideanSpace ℝ (Fin d))
local notation "ok₁" => fun v : (sel).graph.Site=>(by simp : ‖x₁ v‖≤1)
local notation "ok₂" => fun v : C=>(by simp : ‖x₂ v‖≤1)
local notation "first" => quotientBits stepGraph group x₁ ok₁ stageBits
local notation "second" => quotientBits (quotient stepGraph group x₁ ok₁) addr x₂ ok₂ first
local notation "stage" => cap.placement
local notation "native" => cap.order.trans Fin.valEmbedding
local notation "use_" => fun j : (r).pairs=>(r).picked (j,0)
local notation "halo" => reachedHalo ticket
local notation "homes" => reachedHalo_members ticket
local notation "width" => ((stage).degree+1)^4*2^k
local notation "capK" => maxNodes arch.bit
local notation "capK'" => maxNodes next
local notation "actors" => DescentPackedActorMask.actors width (stage).cap
local notation "nodes" => Width width capK (stage).cap
local notation "HH" => Fintype.card target.V
local notation "GG" => S.groupCount (i+1)

variable {s nb mb M w : ℕ} (prior : Local arch.bit)
local notation "oldRank" => bounded arch.bit prior

variable (oldBank : DescentColonies.Block k→Fin (Fintype.card cap.V)→Fin (S.groupCount i)→Cell (s*maxNodes arch.bit))
    (newBank : DescentColonies.Block k→Fin cap.placement.cap→Fin 6→Fin (Fintype.card cap.V)→Fin (S.groupCount i)→Cell s)
variable (prev : ∀u,(arch.bit.recipe u).Node→Cell s) (fresh : (BitDescription.scannedRows he T).pairs→Fin 6→Cell s)
variable (oldWords : ∀(u : W.graph.Site) (t : (arch.bit.recipe u).Node),(encode s (maxNodes arch.bit)).symm (oldBank (cap.placement.block u) (cap.vertex (cap.placement.pos u).2) (cap.placement.pos u).1) (bounded arch.bit prior u t)=prev u t)
    (newWords : ∀(j : (BitDescription.scannedRows he T).pairs) (role : Fin 6),let u:=W.graph.src ((BitDescription.scannedRows he T).pick (j,0)); newBank (cap.placement.block u) (outgoingSlot cap.placement (cap.order.trans Fin.valEmbedding) S cap.valid (BitDescription.scannedRows he T).pick (fun j => (BitDescription.scannedRows he T).picked (j,0)) j) role (cap.vertex (cap.placement.pos u).2) (cap.placement.pos u).1=fresh j role)

local notation "oldH" => Fintype.card cap.V
local notation "oldG" => S.groupCount i
local notation "slots" => 2^(packExponent 20 (stage).degree)+2
local notation "pitch" => (2^(k+1)-1)*slots
local notation "root" => hostRotor cap.vertex (hostRoster stage (cap.vertex.trans Fin.valEmbedding))
local notation "walks" => Gather.reaching root
local notation "previousLane" => donorWord arch oldBank newBank
variable (age : i<S.length) (radix : S.radix=2^k)

def operand (h : Fin oldH) (g : Fin oldG) (j : Fin nodes) :=
  (DescentSortedRoster.indexed walks h (DescentOrdinaryAtomFieldRAM.bookRoot (stage).degree k capK (stage).cap j)).elim 0
    (fun u=>previousLane (DescentOrdinaryAtomFieldRAM.bookBlock (stage).degree k capK (stage).cap j) (DescentOrdinaryAtomFieldRAM.bookItem (stage).degree k capK (stage).cap j) u g)

variable (wanted : Fin ((2^(k+1)-1)*(2^(packExponent 20 cap.placement.degree)+2))→Fin (Fintype.card cap.V)→Fin (S.groupCount i)→Cell nb) (address : Fin ((2^(k+1)-1)*(2^(packExponent 20 cap.placement.degree)+2))→Fin (Fintype.card cap.V)→Fin (S.groupCount i)→Fin (DescentPackedActorMask.actors ((cap.placement.degree+1)^4*2^k) cap.placement.cap)→Cell nb)
    (count : Fin ((2^(k+1)-1)*(2^(packExponent 20 cap.placement.degree)+2))→Fin (Fintype.card cap.V)→Fin (S.groupCount i)→Fin ((cap.placement.degree+1)^4*2^k)→Cell mb)

/-- Exactly the closure of the paid old-geometry mask/gather/pack instruction
at fixed new local `(heap,slot)`. One column for each new local key. -/
def previousRaster (l : Fin pitch) (h : Fin oldH) (g : Fin oldG) : Cell (s*capK') :=
  pack s nodes capK' (DescentPackedActorMask.occupied width capK (stage).cap mb
    (DescentPackedActorMask.target nb actors (wanted l h g) (encode nb actors (address l h g))) (encode mb width (count l h g)))
    (encode s nodes (operand arch oldBank newBank h g))

variable (v : n.result.graph.Site) (node : (((ticket.advance arch).bit).recipe v).Node)
local notation "label_" => currentLabel ticket arch v node
local notation "loc" => localIndex ticket arch v node
local notation "rootKey" => splitKey (label_).val
local notation "oldHost" => cap.vertex (rootKey).2.1
local notation "oldGroup" => (rootKey).1
local notation "raster" => previousRaster ticket arch oldBank newBank wanted address count
local notation "address_" => address loc oldHost oldGroup
local notation "count_" => count loc oldHost oldGroup
local notation "want" => wanted loc oldHost oldGroup
local notation "slot" => outgoingSlot stage native S cap.valid (r).pick use_
local notation "bits_" => CandidateData.fromAddresses (K:=capK) want address_ count_

include prior in
theorem actual_raster
    (counted : ∀d,(count_ d).val=((donorAt halo label_ d).map (fun u=>Fintype.card (arch.bit.recipe u).Node)).getD 0)
    (oldAt : ∀d,address_ (DescentPackedActorMask.oldAddress (stage).cap d)=want ↔ ∃u,donorAt halo label_ d=some u ∧ venue (.inl u)=label_)
    (bornAt : ∀d e j,address_ (DescentPackedActorMask.bornAddress d (finProdFinEquiv (e,j)))=want ↔
      ∃p,donorAt halo label_ d=some (W.graph.src ((r).pick (p,0))) ∧ slot p=e ∧ venue (.inr (p,j))=label_)
    (alive : want≠0) : raster loc oldHost oldGroup=pack s nodes capK' (DescentPackedActorMask.occupied width capK (stage).cap mb
    (DescentPackedActorMask.target nb actors want (encode nb actors address_)) (encode mb width count_))
    (encode s nodes (rawFields (carried ticket arch oldBank label_) (created ticket newBank label_))) :=by
  have dense (u : W.graph.Site) (j : Fin capK) : j.val<Fintype.card (arch.bit.recipe u).Node ↔ ∃t,oldRank u t=j:=old_dense_of_equiv (prior u) (Finset.le_sup (f:=fun y=>Fintype.card (arch.bit.recipe y).Node) (Finset.mem_univ u)) j
  simp only [previousRaster,issued_mask stage want address_ count_ alive]
  apply pack_agrees
  intro j live
  have real:=active_iff stage native S cap.valid arch.bit (r).pick units stageLimit ((r).profile c) use_ group addr x₁ x₂ ok₁ ok₂ halo (homes).1 (homes).2 oldRank label_ bits_ (fun _ _ => measured_old (count_read:=counted) (target_old:=oldAt) (old_dense:=dense) ..) (fun _ _ _ => measured_born (target_new:=bornAt) ..) j
  obtain ⟨u,rfl⟩:=real.mp live
  exact candidate_word ticket arch prior oldBank newBank label_ u

theorem source_cast {A B H L a w : ℕ} (same:A=B) (name:Fin B→Fin A) (numeric:∀i,(name i).val=i.val) (xs:Fin H→Fin A→Cell a) (m:Memory w) (base : ℕ)
    (old : ∀p : Row H A L,m (base+(row H A L p).val)=((data xs p).val:Computability.VPVNP.BurstRAM.Word w)) :
    ∀p:Row H B L,m (base+(row H B L p).val)=((data (fun h g=>xs h (name g)) p).val:Computability.VPVNP.BurstRAM.Word w) :=by
  subst B
  have same':∀g,name g=g:=fun g=>Fin.ext (numeric g)
  simpa only [same'] using old

include age radix oldWords newWords in
/-- The final program uses only physically emitted previous-raster rows and
checks each input node/party against its actual source book. The returned
state contains the true next field at the canonical reached local number. -/
theorem issued_field
    (counted : ∀d,(count_ d).val=((donorAt halo label_ d).map (fun u=>Fintype.card (arch.bit.recipe u).Node)).getD 0)
    (oldAt : ∀d,address_ (DescentPackedActorMask.oldAddress (stage).cap d)=want ↔ ∃u,donorAt halo label_ d=some u ∧ venue (.inl u)=label_)
    (bornAt : ∀d e j,address_ (DescentPackedActorMask.bornAddress d (finProdFinEquiv (e,j)))=want ↔
      ∃p,donorAt halo label_ d=some (W.graph.src ((r).pick (p,0))) ∧ slot p=e ∧ venue (.inr (p,j))=label_)
    (alive : want≠0) (src : Bank) (base out : ℕ) (m : Memory w) (hm : 0<M) (wide : (s*capK')*M≤w)
    (fit : DescentScalarBookReshape.Room oldH pitch GG (2^k) (s*capK') M w base out src)
    (banks : ∀l(p : Row oldH oldG (M*2^k)),m (src.base+l.val*(oldH*chunks GG M)+(row oldH oldG (M*2^k) p).val)=((data (raster l) p).val:Computability.VPVNP.BurstRAM.Word w)) :
    let compiled:=DescentScalarBookReshape.program oldH pitch GG (2^k) (s*capK') M base out w src
    let state:=DescentScalarBookReshape.result oldH pitch GG (2^k) (s*capK') M base out src m
    let rows:=2^k*((oldH*pitch)*chunks GG M);let cost:=4+10*DescentScalarBookReshape.cells oldH pitch GG (2^k) (s*capK') M
    let amount:=s*capK';let h:=target.vertex (target.placement.pos v).2;let g:=(target.placement.pos v).1;let b:=target.placement.block v
    compiled.Exec m state (cost+(4+rows*54)) ∧
      digit s (advance ticket arch prior v node).val (digit amount (lane g hm).val (state (dest oldH pitch GG M out b+(row HH GG M (position h g hm)).val)).val)=
        (Sum.elim (fun u : NodeOrder.All arch.bit=>prev u.1 u.2) (fun j : (r).pairs×Fin 6=>fresh j.1 j.2) (roots ticket arch ⟨v,node⟩)).val :=by
  let digitMap:=S.groupDigits age radix
  have size:oldG=GG*2^k:=by simpa using Fintype.card_congr (digitMap.trans finProdFinEquiv)
  have numeric (g:Fin (GG*2^k)) : (digitMap.symm (finProdFinEquiv.symm g)).val=g.val:=by
    change (finProdFinEquiv (finProdFinEquiv.symm g)).val=g.val;rw [Equiv.apply_symm_apply]
  have input:=fun l=>source_cast size (fun g=>digitMap.symm (finProdFinEquiv.symm g)) numeric (raster l) m (src.base+l.val*(oldH*chunks GG M)) (banks l)
  obtain ⟨ran,posted,_⟩:=DescentScalarBookReshape.run base out src m (oldInput age radix raster) hm (Nat.two_pow_pos k) fit input
  refine ⟨ran,?_⟩
  apply printed_field ticket arch prior oldBank newBank prev fresh oldWords newWords v node want address_ count_ counted oldAt bornAt alive (dest oldH pitch GG M out) _
    (fun b h g=>DescentScalarBookReshape.book (oldInput age radix raster) b (hostIndex ticket h) g) hm wide (transferred ticket age radix raster out _ posted)
  rw [selected_book ticket arch age radix v node]
  exact actual_raster ticket arch prior oldBank newBank wanted address count v node counted oldAt bornAt alive

end
end Hierarchy.DescentLocalArchiveOrder

end OAI
