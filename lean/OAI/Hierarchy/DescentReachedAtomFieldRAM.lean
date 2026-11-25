import OAI.Hierarchy.DescentOrdinaryPopulationWord
import OAI.Hierarchy.DescentOrdinaryPrimitiveWords
import OAI.Hierarchy.DescentReachedAtomHalo
import OAI.Hierarchy.DescentOrdinaryAtomVenueRead

namespace OAI
/-! # Reading the packed coefficient field at the actual reached node number -/
namespace Hierarchy.DescentLocalArchiveOrder
open DescentKernelHistory DescentSixParty DescentSixParty.Chronology DescentCompiler DescentStageEdgeReceipt
open DescentCableDonorNames DescentOrdinaryLocalBirth DescentHostDegree DescentHostDirectory
open DescentNetworkPartition Computability.BorderVNP.Crossing DescentSharedCableNames DescentSIMDLookup DescentPackedLocalAtoms
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
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
local notation "admit" => fun _ : (r).pairs=>le_refl T.z
local notation "layout" => bestLayout sw
local notation "group" => GadgetNetwork.newSite W.graph (r).pick layout (r).pack
local notation "bookChart" => activeChart ticket
local notation "key" => (bookChart).key he T c
local notation "addr" => MarkedWorld.address sel key (bookChart).hub T.k (gainExponent 20 T.Δ)
local notation "C" => ↥(MarkedWorld.reclaimed sel key (bookChart).hub T.k (gainExponent 20 T.Δ))
local notation "venue" => addr ∘ group
local notation "base" => physicalBits G W.toWorld (r).pick units admit ((r).profile c) arch.bit.recipe
local notation "x₁" => fun _ : (sel).graph.Site=>(0 : EuclideanSpace ℝ (Fin d))
local notation "x₂" => fun _ : C=>(0 : EuclideanSpace ℝ (Fin d))
local notation "ok₁" => fun v : (sel).graph.Site=>(by simp : ‖x₁ v‖≤1)
local notation "ok₂" => fun v : C=>(by simp : ‖x₂ v‖≤1)
local instance : Fintype (DescentSixParty.Merged W.graph (r).pick layout (r).pack) := (sel).graph.finiteSite
local notation "first" => quotientBits stepGraph group x₁ ok₁ base
local notation "second" => quotientBits (quotient stepGraph group x₁ ok₁) addr x₂ ok₂ first
local notation "A" => cap.placement
local notation "native" => cap.order.trans Fin.valEmbedding
local notation "use_" => fun j : (r).pairs=>(r).picked (j,0)
local notation "halo" => reachedHalo ticket
local notation "homes" => reachedHalo_members ticket
local notation "width" => ((A).degree+1)^4*2^k
local notation "capK" => maxNodes arch.bit
local notation "capK'" => maxNodes next
local notation "actors" => DescentPackedActorMask.actors width (A).cap
local notation "nodes" => Width width capK (A).cap
local notation "HH" => Fintype.card target.V
local notation "GG" => S.groupCount (i+1)

variable {s nb mb M w : ℕ} (prior : Local arch.bit)
local notation "oldRank" => bounded arch.bit prior

/-- Fetching an old book or a new role field uses the very same previous
rack, group and block as the donor's site. The new fields are indexed by
the distinct first grain of the selected thick cable. -/
def carried (bank : DescentColonies.Block k→Fin (Fintype.card cap.V)→Fin (S.groupCount i)→Cell (s*capK))
    (label : C) (slot : Fin width) (node : Fin capK) : Cell s :=
  (donorAt halo label slot).elim 0 (fun u=>(encode s capK).symm (bank ((A).block u) (cap.vertex ((A).pos u).2) ((A).pos u).1) node)

def created (bank : DescentColonies.Block k→Fin (A).cap→Fin 6→Fin (Fintype.card cap.V)→Fin (S.groupCount i)→Cell s)
    (label : C) (slot : Fin width) (edge : Fin (A).cap) (role : Fin 6) : Cell s :=
  (donorAt halo label slot).elim 0 (fun u=>bank ((A).block u) edge role (cap.vertex ((A).pos u).2) ((A).pos u).1)

variable (oldBank : DescentColonies.Block k→Fin (Fintype.card cap.V)→Fin (S.groupCount i)→Cell (s*maxNodes arch.bit))
    (newBank : DescentColonies.Block k→Fin cap.placement.cap→Fin 6→Fin (Fintype.card cap.V)→Fin (S.groupCount i)→Cell s)
variable (prev : ∀u,(arch.bit.recipe u).Node→Cell s) (fresh : (BitDescription.scannedRows he T).pairs→Fin 6→Cell s)
variable (oldWords : ∀(u : W.graph.Site) (t : (arch.bit.recipe u).Node),(encode s (maxNodes arch.bit)).symm (oldBank (cap.placement.block u) (cap.vertex (cap.placement.pos u).2) (cap.placement.pos u).1) (bounded arch.bit prior u t)=prev u t)
    (newWords : ∀(j : (BitDescription.scannedRows he T).pairs) (role : Fin 6),let u:=W.graph.src ((BitDescription.scannedRows he T).pick (j,0)); newBank (cap.placement.block u) (outgoingSlot cap.placement (cap.order.trans Fin.valEmbedding) S cap.valid (BitDescription.scannedRows he T).pick (fun j => (BitDescription.scannedRows he T).picked (j,0)) j) role (cap.vertex (cap.placement.pos u).2) (cap.placement.pos u).1=fresh j role)

include oldWords in
private theorem kept_at (label : C) (u : W.graph.Site) (same : venue (.inl u)=label) (t : (arch.bit.recipe u).Node) :
    carried ticket arch oldBank label (oldSlot (r).pick units ((r).profile c) group addr halo (homes).1 label u same) (oldRank u t)=prev u t :=by
  have seen : donorAt halo label (oldSlot (r).pick units ((r).profile c) group addr halo (homes).1 label u same)=some u:=
    (donorAt_eq halo label).2 ⟨same ▸ (homes).1 u,rfl⟩
  simpa only [carried,seen,Option.elim_some] using oldWords u t

include newWords in
private theorem born_at (label : C) (j : (r).pairs) (role : Fin 6) (same : venue (.inr (j,role))=label) :
    created ticket newBank label (birthSlot (r).pick units ((r).profile c) group addr halo (homes).2 label j role same) (outgoingSlot A native S cap.valid (r).pick use_ j) role=fresh j role :=by
  have seen : donorAt halo label (birthSlot (r).pick units ((r).profile c) group addr halo (homes).2 label j role same)=some (W.graph.src ((r).pick (j,0))):=
    (donorAt_eq halo label).2 ⟨same ▸ (homes).2 j role,rfl⟩
  simpa only [created,seen,Option.elim_some] using newWords j role

variable (v : n.result.graph.Site) (node : ((ticket.advance arch).bit.recipe v).Node)
local notation "label" => currentLabel ticket arch v node
local notation "storage" => target.placement.block v
local notation "rack" => target.vertex (target.placement.pos v).2
local notation "batch" => (target.placement.pos v).1
local notation "before" => carried ticket arch oldBank label
local notation "births" => created ticket newBank label
local notation "slot" => outgoingSlot A native S cap.valid (r).pick use_
local notation "words" => rawFields before births

include oldWords newWords in
/-- The chosen index and owner are the actual successor archive's local
number and site placement. The two sides consume the original physical
scalar word and the just-issued primitive field at their genuine coordinates. -/
theorem printed_field (wanted : Cell nb) (address : Fin actors→Cell nb) (count : Fin width→Cell mb)
    (counted : ∀d,(count d).val=((donorAt halo label d).map (fun u=>Fintype.card (arch.bit.recipe u).Node)).getD 0)
    (oldAt : ∀d,address (DescentPackedActorMask.oldAddress (A).cap d)=wanted ↔ ∃u,donorAt halo label d=some u ∧ venue (.inl u)=label)
    (bornAt : ∀d e j,address (DescentPackedActorMask.bornAddress d (finProdFinEquiv (e,j)))=wanted ↔
      ∃p,donorAt halo label d=some (W.graph.src ((r).pick (p,0))) ∧ slot p=e ∧ venue (.inr (p,j))=label)
    (alive : wanted≠0) (out : DescentColonies.Block k→ℕ) (mem : Memory w)
    (table : DescentColonies.Block k→Fin HH→Fin GG→Cell (s*capK')) (lanes : 0<M) (room_ : (s*capK')*M≤w)
    (stored : ∀b (p : Row HH GG M),mem (out b+(row HH GG M p).val)=((data (table b) p).val:Computability.VPVNP.BurstRAM.Word w))
    (issued : table storage rack batch=pack s nodes capK' (DescentPackedActorMask.occupied width capK (A).cap mb
      (DescentPackedActorMask.target nb actors wanted (encode nb actors address)) (encode mb width count)) (encode s nodes words)) :
    digit s (advance ticket arch prior v node).val (digit (s*capK') (lane batch lanes).val
      (mem (out storage+(row HH GG M (position rack batch lanes)).val)).val)=
      (Sum.elim (fun o : NodeOrder.All arch.bit=>prev o.1 o.2) (fun j : (r).pairs×Fin 6=>fresh j.1 j.2) (roots ticket arch ⟨v,node⟩)).val :=by
  let actual:=printed ticket arch v node node
  have dense (u : W.graph.Site) (j : Fin capK) : j.val<Fintype.card (arch.bit.recipe u).Node ↔ ∃t,oldRank u t=j:=
    old_dense_of_equiv (prior u) (Finset.le_sup (f := fun y => Fintype.card (arch.bit.recipe y).Node) (Finset.mem_univ u)) j
  have small : Fintype.card (second label).Node≤capK' :=
    (Fintype.card_congr (printed ticket arch v node)).symm.le.trans (Finset.le_sup (f := fun y => Fintype.card ((next).recipe y).Node) (Finset.mem_univ v))
  have seen:=physical_field A native S cap.valid arch.bit (r).pick units admit ((r).profile c) use_ group addr x₁ x₂ ok₁ ok₂
    halo (homes).1 (homes).2 oldRank label before births prev fresh (kept_at ticket arch prior oldBank prev oldWords label)
    (born_at ticket newBank fresh newWords label) wanted address count counted oldAt bornAt dense alive small (table storage) mem (out storage) lanes rack batch room_ (stored storage) issued actual
  have ordinal := actual_ordinal ticket arch halo (homes).1 (homes).2 prior oldRank (reachedHalo_order ticket) (fun _ _=>rfl) v node
  let cell := digit (s*capK') (lane batch lanes).val
    (mem (out storage + (row HH GG M (position rack batch lanes)).val)).val
  refine (congrArg (fun index : ℕ => digit s index cell) ordinal.symm).trans (seen.trans ?_)
  let read := Sum.elim (fun o : NodeOrder.All arch.bit => prev o.1 o.2) (fun j : (r).pairs×Fin 6 => fresh j.1 j.2)
  have source := (coefficientFiber_read arch.bit (r).pick units admit ((r).profile c) group addr x₁ x₂ ok₁ ok₂ label actual).symm.trans
    (printed_origin ticket arch v node node)
  refine Eq.trans ?_ (congrArg (fun o => (read o).val) source)
  let fiber := roster arch.bit (r).pick units admit ((r).profile c) group addr x₁ x₂ ok₁ ok₂ label actual
  have evaluate (entry : Σt : {t : GadgetNetwork.Site (I := (r).pairs) W.graph // venue t = label}, (base t.val).Node) :
      (historyField arch.bit (r).pick units admit ((r).profile c) prev fresh entry.1.val entry.2).val =
        (read (origin arch.bit (r).pick units admit ((r).profile c) group addr label entry)).val := by
    rcases entry with ⟨⟨u|⟨j,t⟩,h⟩,y⟩ <;> rfl
  exact evaluate fiber

/-- Padding does not depend on whether zero is a valid payload. Every chosen
active position has strictly smaller rank than the entire active support. -/
theorem unused_digit {X : Type} [Fintype X] {W K a : ℕ} (ids : X↪Fin W) (mask : Fin W→Cell 1) (values : Fin W→Cell a)
    (active : ∀j,mask j≠0 ↔ ∃x,ids x=j) (j : Fin K) (late : Fintype.card X≤j.val) :
    digit a j.val (pack a W K (encode 1 W mask) (encode a W values)).val=0 :=by
  have image : present mask=Finset.univ.map ids:=by ext y;simp [present,active,Finset.mem_map]
  have size:(present mask).card=Fintype.card X:=by rw [image,Finset.card_map,Finset.card_univ]
  have absent : ¬∃i : Fin W,mask i≠0 ∧ earlier mask i=j.val:=by
    rintro ⟨i,yes,at_⟩
    have strict : ((present mask).filter (· < i))⊂present mask:=
      (Finset.ssubset_iff_of_subset (Finset.filter_subset ..)).2 ⟨i,by simp [present,yes],by simp⟩
    have small:=Finset.card_lt_card strict
    change earlier mask i<(present mask).card at small
    rw [at_,size] at small;omega
  simp [pack,field,absent,digit_encode]

include prior in
theorem printed_unused (wanted : Cell nb) (address : Fin actors→Cell nb) (count : Fin width→Cell mb)
    (counted : ∀d,(count d).val=((donorAt halo label d).map (fun u=>Fintype.card (arch.bit.recipe u).Node)).getD 0)
    (oldAt : ∀d,address (DescentPackedActorMask.oldAddress (A).cap d)=wanted ↔ ∃u,donorAt halo label d=some u ∧ venue (.inl u)=label)
    (bornAt : ∀d e j,address (DescentPackedActorMask.bornAddress d (finProdFinEquiv (e,j)))=wanted ↔
      ∃p,donorAt halo label d=some (W.graph.src ((r).pick (p,0))) ∧ slot p=e ∧ venue (.inr (p,j))=label)
    (alive : wanted≠0) (out : DescentColonies.Block k→ℕ) (mem : Memory w)
    (table : DescentColonies.Block k→Fin HH→Fin GG→Cell (s*capK')) (lanes : 0<M) (room_ : (s*capK')*M≤w)
    (stored : ∀b (p : Row HH GG M),mem (out b+(row HH GG M p).val)=((data (table b) p).val:Computability.VPVNP.BurstRAM.Word w))
    (issued : table storage rack batch=pack s nodes capK' (DescentPackedActorMask.occupied width capK (A).cap mb
      (DescentPackedActorMask.target nb actors wanted (encode nb actors address)) (encode mb width count)) (encode s nodes words))
    (j : Fin capK') (outside : Fintype.card ((next).recipe v).Node≤j.val) :
    digit s j.val (digit (s*capK') (lane batch lanes).val
      (mem (out storage+(row HH GG M (position rack batch lanes)).val)).val)=0 :=by
  let p:=position rack batch lanes
  have atBatch:p.2.val*M+(lane batch lanes).val=(batch).val:=Nat.div_add_mod' ..
  have real:(⟨_,atBatch.trans_lt (batch).isLt⟩:Fin GG)=batch:=Fin.ext atBatch
  have scalar := (data (table storage) p).isLt.trans_le (Nat.pow_le_pow_right (by decide) room_)
  rw [stored,Fin.val_cast_of_lt scalar,data,digit_encode,dite_eq_left (atBatch.trans_lt (batch).isLt),real]
  change digit s j.val (table storage rack batch).val = 0
  rw [issued]
  have dense (u : W.graph.Site) (j : Fin capK) : j.val<Fintype.card (arch.bit.recipe u).Node ↔ ∃t,oldRank u t=j:=old_dense_of_equiv (prior u) (Finset.le_sup (f := fun y => Fintype.card (arch.bit.recipe y).Node) (Finset.mem_univ u)) j
  let state:=CandidateData.fromAddresses (K:=capK) wanted address count
  have mask:=issued_mask (K:=capK) A wanted address count alive
  rw [mask]
  apply unused_digit (short A native S cap.valid arch.bit (r).pick units admit ((r).profile c) use_ group addr x₁ x₂ ok₁ ok₂ halo (homes).1 (homes).2 oldRank label) state.active words
  · intro j
    exact active_iff A native S cap.valid arch.bit (r).pick units admit ((r).profile c) use_ group addr x₁ x₂ ok₁ ok₂ halo (homes).1 (homes).2 oldRank label state (fun _ _ => measured_old (count_read:=counted) (target_old:=oldAt) (old_dense:=dense) ..)
      (fun _ _ _ => measured_born (target_new:=bornAt) ..) j
  · exact (Fintype.card_congr (printed ticket arch v node)).symm.le.trans outside

include prior in
/-- The same signed donor and birth mask used by the operand writer gives the complete
local archive population at a nonempty destination, including unpaid hub nodes. -/
theorem full_population (wanted : Cell nb) (address : Fin actors→Cell nb) (count : Fin width→Cell mb)
    (counted : ∀d,(count d).val=((donorAt halo label d).map (fun u=>Fintype.card (arch.bit.recipe u).Node)).getD 0)
    (oldAt : ∀d,address (DescentPackedActorMask.oldAddress (A).cap d)=wanted ↔ ∃u,donorAt halo label d=some u ∧ venue (.inl u)=label)
    (bornAt : ∀d e j,address (DescentPackedActorMask.bornAddress d (finProdFinEquiv (e,j)))=wanted ↔
      ∃p,donorAt halo label d=some (W.graph.src ((r).pick (p,0))) ∧ slot p=e ∧ venue (.inr (p,j))=label)
    (alive : wanted≠0) (K' : ℕ) :
    DescentOrdinaryPopulation.compress K' (DescentPackedActorMask.occupied width capK (A).cap mb
      (DescentPackedActorMask.target nb actors wanted (encode nb actors address)) (encode mb width count)) =
      DescentOrdinaryPopulation.fill K' (Fintype.card ((next).recipe v).Node) :=by
  have dense (u : W.graph.Site) (j : Fin capK) : j.val<Fintype.card (arch.bit.recipe u).Node ↔
      ∃t,oldRank u t=j :=old_dense_of_equiv (prior u) (Finset.le_sup (f := fun y => Fintype.card (arch.bit.recipe y).Node) (Finset.mem_univ u)) j
  let state:=CandidateData.fromAddresses (K:=capK) wanted address count
  rw [issued_mask A wanted address count alive, Fintype.card_congr (printed ticket arch v node)]
  apply DescentOrdinaryPopulation.compress_mask
    (short A native S cap.valid arch.bit (r).pick units admit ((r).profile c) use_ group addr x₁ x₂ ok₁ ok₂ halo (homes).1 (homes).2 oldRank label)
  exact fun j=>active_iff A native S cap.valid arch.bit (r).pick units admit ((r).profile c) use_
    group addr x₁ x₂ ok₁ ok₂ halo (homes).1 (homes).2 oldRank label state
    (fun _ _ => measured_old (count_read:=counted) (target_old:=oldAt) (old_dense:=dense) ..)
    (fun _ _ _ => measured_born (target_new:=bornAt) ..) j

section Primitive
open DescentPrimitivePalette DescentCompiler
variable {seed Z p : ℕ} (op : RotorSpec) (menu : Runnable F op) (limit : T.z≤Z)
variable (encoding : Encoding (Label G seed Z op) (dictionary G op menu p) arch.bit)

/-- Active primitive fields reserve value zero even when the underlying
primitive's dictionary ordinal is zero. -/
def roleToken (role : Label G seed Z op) : Cell (Packed.bits (colors G seed Z op)) :=
  Packed.token (some ((codec (G:=G) op).store role))

theorem role_fold (o : NodeOrder.All next) :
    (Sum.elim (fun old : NodeOrder.All arch.bit=>roleToken op (encoding.atNode old))
      (fun j : (r).pairs×Fin 6=>roleToken op (bornLabel (s:=seed) op (c:=c) limit j.1 j.2)) (roots ticket arch o)).val=
      ((codec (G:=G) op).store (((Encoding.scanned G op menu encoding T he c limit).follow n).atNode o)).val+1 :=by
  rw [ordinary_at op menu ticket arch encoding limit o]
  cases roots ticket arch o <;> rfl
end Primitive

end
end Hierarchy.DescentLocalArchiveOrder

end OAI
