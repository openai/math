import OAI.Hierarchy.DescentDensePhysicalOrder
import OAI.Hierarchy.DescentGroupHostOrdinal
import OAI.Hierarchy.DescentOrdinaryEdgeTape
import OAI.Hierarchy.DescentEdgeTapePrefix
import OAI.Hierarchy.DescentNextCoordinates
import OAI.Hierarchy.DescentVenueCodes
import OAI.Hierarchy.DescentPhysicalOrder
import OAI.Hierarchy.DescentMatchedTableOrder
import OAI.Hierarchy.DescentCableDonorNames

namespace OAI
/-! # Dense successor cable IDs from the chronological sparse stage table -/

namespace Hierarchy.DescentStageEdgeReceipt
open DescentSixParty DescentSixParty.StarKeys DescentSixParty.MarkedWorld DescentHostDirectory DescentCableUnbundling
open DescentPacking
open ThreeFlat.RAM Computability.VPVNP.BurstRAM
open scoped Classical BigOperators Fin.CommRing
noncomputable section

/-- The sparse source table and the field of every surviving chunk which a
native prefix program reads before emitting its dense successor identifier. -/
structure Tape (E : Type) [Fintype E] where
  Parent : Type
  [parents : Fintype Parent]
  order : E↪Fin (Fintype.card E)
  slots : ℕ
  rank : Parent↪ℕ
  inSlots : ∀u,rank u<slots
  span : Parent→ℕ
  owner : E→Parent
  offset : E→ℕ
  offsetFits : ∀e,offset e<span (owner e)
  read : ∀e,(order e).val=ProtocolRAMPortRanks.«prefix» span rank (owner e)+offset e
  /-- Lexicographic ancestry within a new source, with an old source, old
  outgoing cable, physical role and child offset in that order. -/
  ancestry : E↪ℕ := order.trans Fin.valEmbedding
  /-- Dense input order for the next stage, after physical relabeling. -/
  selector : E↪Fin (Fintype.card E) := order
attribute [instance] Tape.parents

namespace Tape
open DescentSixParty
noncomputable section

/-- The same physical sparse source supplies each renamed cable. -/
def names {E : Type} [Fintype E] (T : Tape E) (e : Equiv.Perm E) : Tape E where
  Parent := T.Parent
  parents := T.parents
  order := e.symm.toEmbedding.trans T.order
  slots := T.slots
  rank := T.rank
  inSlots := T.inSlots
  span := T.span
  owner := T.owner ∘ e.symm
  offset := T.offset ∘ e.symm
  offsetFits _i := T.offsetFits _
  read _i := T.read _
  ancestry := e.symm.toEmbedding.trans T.ancestry
  selector := (Fintype.equivFin _).toEmbedding

@[simp] theorem names_order {E : Type} [Fintype E] (T : Tape E) (e : Equiv.Perm E) (i : E) :
    (T.names e).order (e i)=T.order i := by simp [names]

def afterNames {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {S : MarkedWorld F d P bits}
    (n : Normalize S) (T : Tape n.result.graph.Edge) (s : Equiv.Perm n.result.graph.Site) (e : Equiv.Perm n.result.graph.Edge) :
    Tape (n.appendNames s e).result.graph.Edge := (n.appendNames_result s e).symm ▸
      (show Tape (PhysicalRename.world n.result s e).graph.Edge from T.names e)

end
end Tape

theorem Tape.native {E : Type} [Fintype E] (T : Tape E) {w counts starts : ℕ} (m : Memory w)
    (sep : counts+T.slots≤ starts) (fit : starts+T.slots+1<2^w)
    (loaded : ∀i<T.slots,m (counts+i)=(DescentEdgeTapePrefix.row T.span T.rank i:Word w)) :
    let result := ProtocolRAMEndpointPrefix.image starts (DescentEdgeTapePrefix.before T.span T.rank) m T.slots
    (ProtocolRAMEndpointPrefix.exclusive w counts starts T.slots).Exec m result (10+(3+12*T.slots)) ∧
      ∀e,result (starts+T.rank (T.owner e))+(T.offset e:Word w)=((T.order e).val:Word w) := by
  refine ⟨DescentEdgeTapePrefix.physical T.span T.rank m sep fit loaded,fun e=>?_⟩
  rw [DescentEdgeTapePrefix.physical_read T.span T.rank m (T.owner e) (T.inSlots _).le,T.read,Nat.cast_add]

variable {V J : Type} [Fintype V] [Fintype J] [DecidableEq V] [DecidableEq J]

def hostRank {K : Type} [Fintype K] (rank : K↪ℕ) (k slots : ℕ) : Host K k slots↪ℕ where
  toFun x := packedNumber rank k slots x.val
  inj' := fun x y eqn=>Subtype.ext (packed_inj rank.injective x.property y.property eqn)

def thickKey {K : Type} (c : K×(ℕ×ℕ)) : Key K := (c.1,c.2,0)
def colonyRank {K : Type} [Fintype K] {C : Type} (rank : K↪ℕ) (k : ℕ)
    (col : C↪K×(ℕ×ℕ)) (ok : ∀c,thickKey (col c)∈keys k 1) : C↪ℕ where
  toFun c := packedNumber rank k 1 (thickKey (col c))
  inj' := by
    intro a b eqn
    have h := packed_inj rank.injective (ok a) (ok b) eqn
    apply col.injective
    exact congrArg (fun k : Key K => (k.1,k.2.1)) h

namespace Tape
variable {E U : Type} [Fintype E]
/-- Group active cables by the actual next source. Empty cables follow the
entire active band, so they do not change any active dense rank. -/
def grouped (t : Tape E) (src : E→U) (site : U↪ℕ) : E↪ℕ :=
  let B:=pitch t.ancestry
  let f : E→Fin B:=fun e=>⟨t.ancestry e,Nat.lt_succ_of_le (Finset.le_sup (Finset.mem_univ e))⟩
  DescentCableDonorNames.sourceGrouped src site f
    (fun _x _y _ eqn=>t.ancestry.injective (congrArg Fin.val eqn))

def sourceKey (t : Tape E) (src : E→U) (site : U↪ℕ) (width : E→ℕ) : E↪ℕ where
  toFun e:=if 0<width e then (t.grouped src site) e else pitch (t.grouped src site)+(t.order e).val
  inj' := by
    intro x y eqn
    have bound (z : E) : t.grouped src site z<pitch (t.grouped src site) :=
      Nat.lt_succ_of_le (Finset.le_sup (Finset.mem_univ z))
    by_cases xw : 0<width x <;> by_cases yw : 0<width y
    · exact (t.grouped src site).injective (by simpa only [ite_eq_left xw,ite_eq_left yw] using eqn)
    · simp only [ite_eq_left xw,ite_eq_right yw] at eqn;have := bound x;omega
    · simp only [ite_eq_right xw,ite_eq_left yw] at eqn;have := bound y;omega
    · apply t.order.injective
      apply Fin.ext
      simp only [ite_eq_right xw,ite_eq_right yw] at eqn
      omega

theorem sourceKey_lt (t : Tape E) (src : E→U) (site : U↪ℕ) (width : E→ℕ) (x y : E)
    (xp : 0<width x) (yp : 0<width y) (same : src x=src y) :
    t.sourceKey src site width x<t.sourceKey src site width y ↔ t.ancestry x<t.ancestry y := by
  simp only [sourceKey,Function.Embedding.coeFn_mk,ite_eq_left xp,ite_eq_left yp,grouped,
    DescentCableDonorNames.grouped_val,same,Nat.add_lt_add_iff_left]
end Tape

variable {F P I C H : Type} [Field F] [Fintype I] [DecidableEq H] {d : ℕ} {bits : P→ℕ}
variable (W : MarkedWorld F d P bits) (G : PoweredGadget F)
set_option quotPrecheck false
local notation "N" => W.graph
variable (edge : W.graph.Edge↪Fin (Fintype.card W.graph.Edge)) (pair : I≃Fin (Fintype.card I))
variable (pick : I×Fin 2↪W.graph.Edge) (z : I→ℕ) (hz : ∀i,0<z i)
variable (fit : ∀i s,W.graph.width (pick (i,s))=z i*G.b) (pack : W.graph.Site→C) (p : I→Profile G.C)
local notation "sel" => W.selected G pick z hz fit pack p
variable (key : (W.selected G pick z hz fit pack p).graph.Site↪Key H)
variable (flag : H→Bool) (k g q : ℕ)
variable (old : ∀e∈W.core,q∣W.graph.width e) (picked : ∀j,pick j∈W.core) (affected : ∀i,q∣z i)
local notation "coarse" => coalesced sel key flag k g
local notation "rep" => repetitions W G pick z hz fit pack p key flag k g q
local notation "survivorRank" => survivorNumber W G (dense edge) pair pick z hz fit pack p key flag k g
local notation "inj" => survivorNumber_inj W G (dense edge) pair pick z hz fit pack p key flag k g
local notation "part" => pieceUnit (coarse).graph (coarse).core rep q

local notation "childWorld" => (subroundNormalize W G pick z hz fit pack p key flag k g q old picked affected).result
local notation "oldOrd" => Fintype.card (N).Edge
local notation "siteOrd" => Fintype.card (N).Site
local notation "childBound" => (Finset.univ.sup (span (coarse).graph (coarse).core rep)+1)

def ancestryTicket (e : (childWorld).graph.Edge) :
    DescentCableDonorNames.Ticket siteOrd oldOrd childBound :=
  let a:=(part e).1.val.val
  let t:=DescentCableDonorNames.anchor pick a
  ⟨Fintype.equivFin (N).Site ((N).src t),edge t,DescentCableDonorNames.role a,
    ⟨(part e).2.val,(part e).2.isLt.trans_le ((Finset.le_sup (s:=Finset.univ) (f:=span (coarse).graph (coarse).core rep)
      (Finset.mem_univ (part e).1)).trans (Nat.le_succ _))⟩⟩

theorem ancestryTicket_injective : Function.Injective
    (ancestryTicket W G edge pick z hz fit pack p key flag k g q old picked affected) := by
  intro x y eqn
  have cable:=congrArg DescentCableDonorNames.Ticket.old eqn
  have role:=congrArg DescentCableDonorNames.Ticket.rawRole eqn
  have raw:=DescentCableDonorNames.identify pick (edge.injective cable) role
  have own : (part x).1=(part y).1:=Subtype.ext (Subtype.ext raw)
  have digit:=congrArg (fun t : DescentCableDonorNames.Ticket siteOrd oldOrd childBound=>t.child.val) eqn
  apply (part).injective
  exact Sigma.ext own ((Fin.heq_ext_iff (congrArg (span (coarse).graph (coarse).core rep) own)).mpr digit)

def ordinary : Tape (subroundNormalize W G pick z hz fit pack p key flag k g q old picked affected).result.graph.Edge where
  Parent := (coarse).graph.Edge
  order := (chronological (coarse).graph (coarse).core rep q survivorRank inj).toEmbedding
  slots := Fintype.card (N).Edge+10*Fintype.card I
  rank := ⟨survivorRank,inj⟩
  inSlots e := edgeNumber_room W (dense edge) pair e.val.val
  span := span (coarse).graph (coarse).core rep
  owner e := (part e).1
  offset e := (part e).2.val
  offsetFits e := (part e).2.isLt
  read e := chronological_read (coarse).graph (coarse).core rep q survivorRank inj e
  ancestry := (⟨ancestryTicket W G edge pick z hz fit pack p key flag k g q old picked affected,
      ancestryTicket_injective W G edge pick z hz fit pack p key flag k g q old picked affected⟩ : _ ↪ _).trans
      ((⟨DescentCableDonorNames.code,DescentCableDonorNames.code_injective⟩ : _ ↪ _).trans Fin.valEmbedding)

/-- A public tape must be the native sparse enumeration of the actual selected
source and generated pair arms. This relation records the source of the
layout, the two quotient maps, the original edge identifier and the physical
colony order used to address the nine-word matched rows. -/
inductive Issued (W : MarkedWorld F d P bits) (G : PoweredGadget F)
    (oldID : W.graph.Edge↪Fin (Fintype.card W.graph.Edge)) {H : Type} [Fintype H] [DecidableEq H]
    (rootRank : H↪ℕ) : (S : MarkedWorld F d P bits)→
      (norm : Normalize S)→Tape norm.result.graph.Edge→Prop where
  | stage {C : Type} [Fintype C] [DecidableEq C] (home : W.graph.Site→C) (color : W.graph.Site→Bool) (bin : ℕ)
      (col : C↪H×(ℕ×ℕ)) (same : ∀e∈W.core,color (W.graph.src e)=color (W.graph.dst e))
      (z : NativePair W.graph W.core home color bin→ℕ) (hz : ∀i,0<z i)
      (fit : ∀i s,W.graph.width (colorPick W.graph W.core home color bin (i,s))=z i*G.b)
      (profiles : NativePair W.graph W.core home color bin→Profile G.C)
      (hub : H→Bool) (k g q : ℕ) (legal : ∀c,thickKey (col c)∈keys k 1)
      (old : ∀e∈W.core,q∣W.graph.width e) (used : ∀j,colorPick W.graph W.core home color bin j∈W.core)
      (cut : ∀i,q∣z i) :
      Issued W G oldID rootRank _
        (subroundNormalize W G (colorPick W.graph W.core home color bin) z hz fit
          (coloredPack W.graph W.core home color bin) profiles
          (nativeKey W.graph W.core home color bin col same (bestLayout (branchWidth G z profiles)))
          hub k g q old used cut)
        (ordinary W G oldID (PairRAM.globalNumberBy W.graph W.core home color bin (originalId C))
          (colorPick W.graph W.core home color bin) z hz fit (coloredPack W.graph W.core home color bin) profiles
          (nativeKey W.graph W.core home color bin col same (bestLayout (branchWidth G z profiles)))
          hub k g q old used cut)
  | named {state : MarkedWorld F d P bits} (n : Normalize state) (t : Tape n.result.graph.Edge)
      (kept : Issued W G oldID rootRank state n t) (siteRank : n.result.graph.Site↪ℕ) :
      Issued W G oldID rootRank state
        (n.appendNames (DescentPhysicalOrder.rename siteRank)
          (DescentPhysicalOrder.rename (t.sourceKey n.result.graph.src siteRank n.result.graph.width)))
        (Tape.afterNames n t (DescentPhysicalOrder.rename siteRank)
          (DescentPhysicalOrder.rename (t.sourceKey n.result.graph.src siteRank n.result.graph.width)))


end
end Hierarchy.DescentStageEdgeReceipt

end OAI
