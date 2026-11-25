import OAI.Hierarchy.DescentOrdinaryBornOriginal
import OAI.Hierarchy.DescentReachedSourceOperand
import OAI.Hierarchy.DescentReachedPrimitiveOrigin

namespace OAI
/-! Original flattened operand sources before the two ordinary contractions. -/
namespace Hierarchy.DescentOrdinaryRawOperandOrigin
open Computability.BorderVNP.Crossing DescentKernelHistory DescentSixParty GadgetNetwork DescentBundleHistory
open DescentOperandPhysicalInput DescentOrdinaryBorn
open scoped Classical
noncomputable section
set_option quotPrecheck false
variable {F P I : Type} [Field F] [Fintype I] {d p Z : ℕ} {bits:P→ℕ}
    (W:MarkedWorld F d P bits) (B:BitDescription W) (G:PoweredGadget F)
    (pick:I×Fin 2↪W.graph.Edge) (z:I→ℕ) (room:∀i,z i≤Z) (pr:I→Profile G.C)
    (hp:0<p) (old:∀v,Shape p (B.recipe v))
    (edges:∀e,p∣W.graph.width e) (pins:∀a,p∣bits a) (units:∀i,p∣z i)
local notation "raw" => physical W.graph pick (branchWidth G z pr)
local notation "layout" => physicalShape W B G pick z room pr hp old edges pins units
local notation "carry" v => carriedMap W G pick z pr v

def previousIndex (v:W.graph.Site) (u:(B.recipe v).Node)
    (j:Fin ((((layout) (.inl v)).recipe hp).arity u)) : Fin (((old v).recipe hp).arity u) :=
  j.cast (rerouteLen hp (old v) (carry v) u)

/-- Both cases of this equality refer to the same physical operand ordinal. Public
words follow the actual gadget's incidence map, and private words keep their owner. -/
theorem raw_old_read (v:W.graph.Site) (u:(B.recipe v).Node)
    (j:Fin ((((layout) (.inl v)).recipe hp).arity u)) :
    let earlier:=previousIndex W B G pick z room pr hp old edges pins units v u j
    earlier.val=j.val ∧
    (((layout) (.inl v)).recipe hp).operand u j=
      (((old v).recipe hp).operand u earlier).map (carry v).map id :=
by
  let earlier := previousIndex W B G pick z room pr hp old edges pins units v u j
  refine ⟨rfl,?_⟩
  exact reroute_operand hp (old v) (carry v) u earlier

open private Hierarchy.DescentKernelHistory.oldTarget from OAI.Hierarchy.DescentGadgetHistory in
private theorem old_pin (v:W.graph.Site) (a:Attached (raw) (.inl v))
    (s:BlockRef p (boundaryWidth W.graph v)) (n:ℕ)
    (endpoint:((carry v).map s).port=.inr a) (chunk:s.block=n) :
    s.exteriorAt W.graph v a.val n := by
  rcases s with ⟨e|pin,offset,width⟩
  · change oldBoundary W.graph pick (branchWidth G z pr) v (.inl e)=.inr a at endpoint
    by_cases left:W.graph.src e.val=v
    · simp [oldBoundary,left] at endpoint
    · let dst := e.property.resolve_left left
      have disjoint (o : Option (I × Fin 2)) (chosen : GadgetNetwork.selected W.graph pick e.val=o) :
          Hierarchy.DescentKernelHistory.oldTarget W.graph pick (branchWidth G z pr)
            v e.val dst o chosen ≠ .inr a := by
        cases o <;> intro bad <;> cases bad
      rw [oldBoundary, dite_eq_right left] at endpoint
      exact False.elim (disjoint _ rfl endpoint)
  · have hit:(⟨pin.val,congrArg Sum.inl pin.property⟩:Attached (raw) (.inl v))=a:=
      Sum.inr.inj endpoint
    exact ⟨pin,congrArg Subtype.val hit,rfl,chunk⟩

/-- A raw exterior word comes from an old operand reading the same immutable pin
and the same p-word. Newborn sites have no attached public pins. -/
theorem pin_source (v:(raw).Site) (u:((layout v).recipe hp).Node)
    (j:Fin (((layout v).recipe hp).arity u)) (a:Attached (raw) v) (n:ℕ)
    (fits:(n+1)*p≤bits a.val) (received:((layout v).recipe hp).operand u j=.inl ⟨.inr a,n,fits⟩) :
    ∃(donor:NodeOrder.All B)(k:Fin (((old donor.1).recipe hp).arity donor.2)),
      (NodeOrder.physicalNames B G pick z room pr ⟨v,u⟩)=.inl donor ∧ k.val=j.val ∧
      ∃word,((old donor.1).recipe hp).operand donor.2 k=.inl word ∧
        word.exteriorAt W.graph donor.1 a.val n := by
  cases v with
  | inl v =>
    let k:=previousIndex W B G pick z room pr hp old edges pins units v u j
    refine ⟨⟨v,u⟩,k,rfl,rfl,?_⟩
    have equality:=((raw_old_read W B G pick z room pr hp old edges pins units v u j).2).symm.trans received
    change (((old v).recipe hp).operand u k).map (carry v).map id=Sum.inl _ at equality
    cases source:((old v).recipe hp).operand u k with
    | inr h => simp [source] at equality
    | inl b =>
      rw [source] at equality
      have split:((carry v).map b)=⟨.inr a,n,fits⟩:=Sum.inl.inj equality
      exact ⟨b,rfl,old_pin W G pick z pr v a b n (congrArg BlockRef.port split) (congrArg BlockRef.block split)⟩
  | inr pair =>
    have impossible:Sum.inl (W.graph.attach a.val)=Sum.inr pair:=a.property
    contradiction

/-- At each valid newborn slot, one occurrence supplies both the actual recipe operand
and the mouth on the physical birth tape, including its side, edge name and word. -/
theorem raw_born_read (fit:∀i s,W.graph.width (pick (i,s))=z i*G.b)
    (i:I) (party:Fin 6) (j:Fin ((((layout) (.inr (i,party))).recipe hp).arity ()))
    (edge:W.graph.Edge≃Fin (Fintype.card W.graph.Edge)) (pair:I≃Fin (Fintype.card I)) :
    ∃o:Occurrence W G pick z pr p i party,
      (occurrences W G pick z pr p i party)[j.val]?=some o ∧
      mouth (actual G p) (z i) (DescentPacking.PackedMatch.LayoutSum.profileCode G.C (pr i)).val
        party j.val=some (occurrenceMouth W G pick z pr o) ∧
      (((layout) (.inr (i,party))).recipe hp).operand () j=.inl (occurrenceBlock W G pick z pr hp o) ∧
      let m:=occurrenceMouth W G pick z pr o
      let b:=occurrenceBlock W G pick z pr hp o
      b.block=m.chunk ∧ ∃e,b.port=.inl e ∧
        MarkedWorld.edgeNumber W edge pair e.val=bornName W pick edge pair i m.origin ∧
        (if m.target then (raw).dst e.val else (raw).src e.val)=.inr (i,party) := by
  let sh:=(layout) (.inr (i,party))
  let xs:=occurrences W G pick z pr p i party
  have live:j.val<(sh.keys ()).length:=j.isLt
  have ok:j.val<xs.length:=by
    simpa only [sh,physical_original W G pick z pr room hp B old edges pins units,List.length_map] using live
  let o:=xs[j.val]'ok
  have at_:xs[j.val]?=some o:=List.getElem?_eq_getElem ok
  obtain ⟨m,key⟩:=synchronized W G pick z pr room hp B old edges pins units fit i party j.val
  change _=(xs[j.val]?).map _ at m key
  rw [at_] at m key
  have origin:(sh.keys ())[j.val]?=some (.inl (occurrenceBlock W G pick z pr hp o)) := key
  have word: (sh.keys ())[j.val]=.inl (occurrenceBlock W G pick z pr hp o):=by
    apply Option.some.inj
    simpa only [List.getElem?_eq_getElem live] using origin
  refine ⟨o,at_,m,?_,occurrence_incidence W G pick z pr hp o edge pair⟩
  change ((sh.keys ())[j.val]).map id (privateIndex hp)=_
  rw [word]
  rfl

/-- Classification of the actual printed source at every occupied row and slot. Its
index type uses the inverse of the very same source-root chart as the native pickup. -/
def RootRead (edge:W.graph.Edge≃Fin (Fintype.card W.graph.Edge)) (pair:I≃Fin (Fintype.card I))
    (root:NodeOrder.All B ⊕ (I×Fin 6)) :
    let t:=(NodeOrder.physicalNames B G pick z room pr).symm root
    Fin (((layout t.1).recipe hp).arity t.2) → Prop :=
  match root with
  | .inl ⟨v,u⟩ => fun j=>
    ∃k:Fin (((old v).recipe hp).arity u),k.val=j.val ∧
      (((layout) (.inl v)).recipe hp).operand u j=
        (((old v).recipe hp).operand u k).map (carry v).map id
  | .inr (i,party) => fun j=>
    ∃o:Occurrence W G pick z pr p i party,
      (occurrences W G pick z pr p i party)[j.val]?=some o ∧
      mouth (actual G p) (z i) (DescentPacking.PackedMatch.LayoutSum.profileCode G.C (pr i)).val
        party j.val=some (occurrenceMouth W G pick z pr o) ∧
      (((layout) (.inr (i,party))).recipe hp).operand () j=.inl (occurrenceBlock W G pick z pr hp o) ∧
      let m:=occurrenceMouth W G pick z pr o
      let b:=occurrenceBlock W G pick z pr hp o
      b.block=m.chunk ∧ ∃e,b.port=.inl e ∧
        MarkedWorld.edgeNumber W edge pair e.val=bornName W pick edge pair i m.origin ∧
        (if m.target then (raw).dst e.val else (raw).src e.val)=.inr (i,party)

theorem root_read (fit:∀i s,W.graph.width (pick (i,s))=z i*G.b)
    (edge:W.graph.Edge≃Fin (Fintype.card W.graph.Edge)) (pair:I≃Fin (Fintype.card I))
    (root:NodeOrder.All B ⊕ (I×Fin 6)) :
    ∀j,RootRead W B G pick z room pr hp old edges pins units edge pair root j := by
  rcases root with ⟨v,u⟩|⟨i,party⟩
  · intro j
    exact ⟨_,raw_old_read W B G pick z room pr hp old edges pins units v u j⟩
  · intro j
    exact raw_born_read W B G pick z room pr hp old edges pins units fit i party j edge pair

end
end Hierarchy.DescentOrdinaryRawOperandOrigin

namespace Hierarchy.DescentLocalArchiveOrder
open Computability.BorderVNP.Crossing DescentSixParty DescentSixParty.Chronology DescentStageEdgeReceipt
open DescentCompiler DescentKernelHistory DescentBundleHistory DescentHostDirectory DescentHostDegree
open DescentPackedOperand DescentNetworkPartition
open scoped Classical
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F] {d p R : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F}
variable {u q ε : ℝ} {S : AtomSchedule} {k i z D z' D' wire hist : ℕ}
    {cap : Reached W G q ε S k i z D wire hist}
    {he : 0≤ε} {T : StageInput W G u ε} {c : (T.result he).Choice}
    {n : Normalize ((T.result he).state c)} {target : Reached n.result G q ε S k (i+1) z' D' wire hist}
    (ticket : OrdinaryLink cap he T c n target) (arch : Archive W)
    (hp : 0<p) (one : 1≤R) (pin : ∀x,p∣bits x) (sh : WorldShape p R arch.bit) (unit : p∣T.z)
local notation "r" => BitDescription.scannedRows he T
local notation "uni" => fun _ : (r).pairs=>T.z
local notation "room" => fun _ : (r).pairs=>le_refl T.z
local notation "whole" => fun _ : (r).pairs=>unit
local notation "prof" => (r).profile c
local notation "after" => afterOrdinary hp one pin ticket arch sh unit
local notation "M" => rawGraph he T c
local notation "baseShape" => physicalShape W arch.bit G (r).pick uni room prof hp sh.sites sh.edges pin whole
local notation "next" => (ticket.advance arch).bit
local notation "names" => NodeOrder.physicalNames arch.bit G (r).pick uni room prof
local notation "source" x => (names).symm (roots ticket arch x)
/-- The real source ticket drives both the RAM candidate selection and the raw
operand classification. This also covers old private uses and every newborn mouth. -/
theorem registered_operand {bound:ℕ} (fits₀:maxNodes arch.bit≤bound)
    (priorOrder:Local arch.bit)
    (edge:W.graph.Edge≃Fin (Fintype.card W.graph.Edge)) (pair:(r).pairs≃Fin (Fintype.card (r).pairs))
    (x:NodeOrder.All next) (j:Fin ((((after).sites x.1).recipe hp).arity x.2)) :
    let saved:=roots ticket arch x
    let slot:=sourceIndex ticket arch hp one pin sh unit x j
    slot.val=j.val ∧ PaddedOrigin.OriginOperands ticket arch fits₀ priorOrder
      (currentLabel ticket arch x.1 x.2) saved (PaddedOrigin.originCandidate ticket arch fits₀ priorOrder x.1 x.2) ∧
      DescentOrdinaryRawOperandOrigin.RootRead W arch.bit G (r).pick uni room prof hp sh.sites sh.edges pin whole
        edge pair saved slot := by
  exact ⟨sourceIndex_val ticket arch hp one pin sh unit x j,
    PaddedOrigin.origin_operands ticket arch fits₀ priorOrder x.1 x.2,
    DescentOrdinaryRawOperandOrigin.root_read W arch.bit G (r).pick uni room prof hp sh.sites sh.edges pin whole
      (r).fit edge pair _ _⟩

/-- The pin branch of the reached source classification determines an actual old scalar,
its matching source-root selection and the same flattened operand slot. -/
theorem original_pin_source (x:NodeOrder.All next)
    (j:Fin ((((after).sites x.1).recipe hp).arity x.2)) (a:Attached (M) (source x).1)
    (lane:ℕ) (fits:(lane+1)*p≤bits a.val)
    (raw:((baseShape (source x).1).recipe hp).operand (source x).2
      (sourceIndex ticket arch hp one pin sh unit x j)=.inl ⟨.inr a,lane,fits⟩) :
    ∃(donor:NodeOrder.All arch.bit)(k:Fin (((sh.sites donor.1).recipe hp).arity donor.2)),
      roots ticket arch x=.inl donor ∧ k.val=j.val ∧
      (∃word,((sh.sites donor.1).recipe hp).operand donor.2 k=.inl word ∧
        word.exteriorAt W.graph donor.1 a.val lane) ∧
      ∃finalWord,(((after).sites x.1).recipe hp).operand x.2 j=.inl finalWord ∧
        finalWord.exteriorAt n.result.graph x.1 a.val lane := by
  have result := DescentOrdinaryRawOperandOrigin.pin_source W arch.bit G
    (r).pick uni room prof hp sh.sites sh.edges pin whole (source x).1 (source x).2
    (sourceIndex ticket arch hp one pin sh unit x j) a lane fits raw
  rcases result with ⟨donor,sourceSlot,root,address,prior⟩
  refine ⟨donor,sourceSlot,((names).apply_symm_apply (roots ticket arch x)).symm.trans root,
    address.trans (sourceIndex_val ticket arch hp one pin sh unit x j),prior,?_⟩
  exact original_pin ticket arch hp one pin sh unit x j a lane fits raw

end
end Hierarchy.DescentLocalArchiveOrder

end OAI
