import OAI.ThreeFlat.Diagonal.PhysicalShrinkActualOutput
import OAI.ThreeFlat.Diagonal.ShrinkArchiveLayer
import OAI.ThreeFlat.Diagonal.ShrinkArchiveTransport
import OAI.ThreeFlat.Diagonal.NumberedArchiveSites
import OAI.ThreeFlat.Diagonal.ProgramDirectory

namespace OAI
/-! # The numbered archive step of the native shrink writer -/
namespace ThreeFlat.Diagonal.PhysicalStage
open Computability.VPVNP.BurstRAM PrivateRAM RAM Computability.VPVNP.Compression CompressorPacking
open Native Native.ShrinkStage Native.Placement Native.Graph MotifKernel PhysicalShrink
open Native.ShrinkStage.Resident
open NavigationDirectory NavigationPass ShrinkStageNav NavigationNodeRows
open scoped Classical BigOperators
noncomputable section
variable {F : Type} [Field F]

open private CopiesAt copiesAt_lanes shrinkMove_copiesAt sitesAfterCast sitesAfterCast_number
  ParentAt parentAt_lanes shrinkMove_parentAt from OAI.ThreeFlat.Diagonal.ShrinkArchiveTransport

section
variable {V H Tag L : Type} [AddCommGroup H] [AddCommGroup Tag] [AddCommGroup L]
variable [Fintype V] [Fintype H] [Fintype Tag] [Fintype L] {degree colors : ℕ}

@[instance_reducible]
private noncomputable def physicalActiveFintype (packing : PackingData V H Tag L degree colors)
    (layout : Bool) (site : Computability.VPVNP.Compression.Site V Tag L) :
    Fintype (Active (partySite packing layout) site) := by
  classical
  infer_instance

end

attribute [local instance 2000] physicalActiveFintype

variable (T : ShrinkMotif.Table F) (s D rem : ℕ) (hD : 0<D)
variable (small : ((2^(2*(2^s)+1)*(2^s)*(2^s):ℕ):ℝ)/D≤1/1024) (A : State (2^s) (shrinkCharge s+rem))
set_option quotPrecheck false
local notation "M" => shrinkBinary T s D rem hD small A
local notation "B" => shrinkRecordState s rem A
local notation "P" => shrinkRecordPacking s rem A
local notation "packingBits" => CompressorPacking.tagBits (2^s)
local notation "S" => shrinkStage s D
local notation "x" => dims S (Fintype.card (B).Base) packingBits rem
local notation "supply" => shrinkIssuedWords T s D rem hD small A

open private hist_at_value from OAI.ThreeFlat.Diagonal.PhysicalShrinkActualOutput
open private tag_size rawConditions from OAI.ThreeFlat.Diagonal.PhysicalShrinkSuccessor

open Lean Elab Term in
local elab "archivePopulation% " i:term:max : term => do
  let index ← elabTerm i none
  let domain ← Meta.whnf (← Meta.inferType index)
  unless domain.isAppOfArity ``Fin 1 do throwError "expected a histogram ordinal; found {domain}"
  let cardinal := domain.getAppArgs[0]!.consumeMData
  unless cardinal.isAppOfArity ``Fintype.card 2 do
    throwError "expected a finite histogram population; found cardinality {cardinal}"
  return ← instantiateMVars cardinal.getAppArgs[1]!

section BranchOrdinal
attribute [local irreducible] Finset.sum Finset.univ Fintype.card Fintype.equivFin
  ShrinkMotif.chooseWidths PhysicalShrink.r shrinkingGraph SlotRefinement.actualWidth

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem archive_branch_read (b : Fin (M).rules.count) {fin : Fintype (shrinkRecordHists T s rem A)}
    (i : Fin (@Fintype.card _ fin)) (atIndex : i.val=b.val) :
    issued T P (shrinkRecordWidth s rem A) (shrinkRecordCode s rem A)
      (by have := Nat.two_pow_pos s; omega : 2≤2*2^s+1) ((@Fintype.equivFin _ fin).symm i) =
        supply b := by
  unfold shrinkIssuedWords shrinkIssuedBranch
  apply congrArg (issued T P (shrinkRecordWidth s rem A) (shrinkRecordCode s rem A) _)
  exact hist_at_value i (b.cast (shrinkBinary_ruleCount T s D rem hD small A)) atIndex

-- Expose the two already elaborated word arrays that control the active-site sums.
open Lean Elab Tactic Meta in
local elab "archive_word_equality " h:ident : tactic => withMainContext do
  let goal ← getMainGoal
  let type ← whnf (← instantiateMVars (← goal.getType))
  unless type.isAppOfArity ``Eq 3 do
    throwError "expected an equality of native copy sums; found {type.getAppFn}"
  let readWords (term : Lean.Expr) : TacticM Lean.Expr := do
    let args := term.getAppArgs
    unless term.isAppOf ``Finset.sum do throwError "expected a finite copy sum; found {term}"
    let rows := args[args.size-2]!.getAppArgs
    let active := rows[0]!.consumeMData
    let some choice := active.find? (fun e => e.isAppOfArity ``ShrinkMotif.chooseWidths 3)
      | throwError "expected a selected active-site width array; found {active}"
    return choice.getAppArgs.back!
  let left ← readWords type.getAppArgs[1]!
  let right ← readWords type.getAppArgs[2]!
  let equality ← mkEq right left
  let proof ← mkFreshExprSyntheticOpaqueMVar equality
  let next ← goal.assert h.getId equality proof
  let (_, next) ← next.intro1P
  replaceMainGoal [proof.mvarId!, next]

-- Instantiate histogram ordinal invariance at the finite populations of these exact two reads.
open Lean Elab Tactic Meta in
local elab "archive_match_reads " coord:term:max : tactic => withMainContext do
  let goal ← getMainGoal
  let type ← whnf (← instantiateMVars (← goal.getType))
  let some (_, left, right) := type.eq? | throwError "expected equality of issued word arrays"
  let histogram (words : Lean.Expr) : TacticM (Lean.Expr × Lean.Expr × Lean.Expr) := do
    let words := words.consumeMData
    unless words.isAppOf ``PhysicalShrink.issued do throwError "expected issued words; found {words.getAppFn}"
    let hist := words.appArg!.consumeMData
    let index := hist.appArg!.consumeMData
    let idxType ← whnf (← inferType index)
    unless idxType.isAppOfArity ``Fin 1 do throwError "expected a finite ordinal; found {idxType.getAppFn}"
    let card := idxType.appArg!.consumeMData
    unless card.isAppOfArity ``Fintype.card 2 do throwError "expected the original branch count; found {card.getAppFn}"
    return (card.getAppArgs[0]!, card.appArg!, index)
  let (population, first, i) ← histogram left
  let (_, second, j) ← histogram right
  let coordinate ← Elab.Term.elabTerm coord none
  let equal := mkAppN (mkConst ``hist_at_value) #[population, first, second, i, j, coordinate]
  goal.assign (← mkCongrArg right.consumeMData.appFn! equal)
  replaceMainGoal []

private theorem active_sum_of_words_eq {WordArray : Type} (rows : WordArray → Type)
    (copies : (w : WordArray) → rows w → ℕ) (left right : WordArray)
    (words : right = left) (source : Fintype (rows left)) (target : Fintype (rows right)) :
    (@Finset.univ _ source).sum (copies left) = (@Finset.univ _ target).sum (copies right) := by
  subst right
  exact congrArg (fun inst : Fintype (rows left) => (@Finset.univ _ inst).sum (copies left))
    (Subsingleton.elim source target)

-- Specialize the sum law at the two enumerations already present in the goal.
open Lean Elab Tactic Meta in
local elab "archive_sum_of_words " h:ident : tactic => withMainContext do
  let goal ← getMainGoal
  let some (_, leftSum, rightSum) := (← whnf (← goal.getType)).eq?
    | throwError "expected an equality of active-site sums"
  let words ← getFVarFromUserName h.getId
  let some (wordType, rightWords, leftWords) := (← inferType words).eq?
    | throwError "expected an equality of issued words"
  let sumData (term : Lean.Expr) : TacticM (Lean.Expr × Lean.Expr × Lean.Expr) := do
    let args := term.getAppArgs
    unless term.isAppOf ``Finset.sum do throwError "expected a finite sum"
    let univ := args[args.size-2]!
    unless univ.isAppOfArity ``Finset.univ 2 do throwError "expected the complete active-site enumeration"
    return (univ.getAppArgs[0]!, univ.appArg!, args.back!)
  let (active, source, count) ← sumData leftSum
  let (_, target, _) ← sumData rightSum
  let (rows, copies) ← withLocalDeclD `w wordType fun w => do
    let withWords (e : Lean.Expr) := e.replace fun part => if part == leftWords then some w else none
    return (← mkLambdaFVars #[w] (withWords active), ← mkLambdaFVars #[w] (withWords count))
  goal.assign (mkAppN (mkConst ``active_sum_of_words_eq)
    #[wordType, rows, copies, leftWords, rightWords, words, source, target])
  replaceMainGoal []

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1500000 in
theorem shrinkBinary_copies_at (branch : Fin (M).rules.count) (v : ((M).next branch).Site) :
    let j := shrinkNextOrder T s D rem hD small A branch (((M).next branch).chart.symm v)
    let site := (shrinkPackOrder s D rem A).symm j
    (shrinkBinary_siteCopies T s D rem hD small A).copies branch v =
      ∑ a : Active (partySite P (ShrinkMotif.chooseWidths (supply branch))) site,
        shrinkRecordCopies T s rem A a.val := by
  let G : ℕ→ℕ→ℕ→Prop := fun i z n =>
    ∀ (b : Fin (M).rules.count) (j : Fin (x).outputSites), i=b.val → z=j.val →
      n=∑ a : Active (partySite P (ShrinkMotif.chooseWidths (supply b))) ((shrinkPackOrder s D rem A).symm j),
        shrinkRecordCopies T s rem A a.val
  have indexed : CopiesAt (R := M) (shrinkBinary_siteCopies T s D rem hD small A) G := by
    unfold shrinkBinary_siteCopies
    apply copiesAt_lanes
    unfold shrinkRaw_siteCopies
    apply shrinkMove_copiesAt
    intro i site
    dsimp only
    intro b j ib sj
    have siteId : shrinkPackOrder s D rem A site=j :=
      Fin.ext ((shrinkPackOrder_val s D rem A site).trans sj)
    rw [←siteId,Equiv.symm_apply_apply]
    archive_word_equality words
    · unfold shrinkIssuedWords shrinkIssuedBranch
      archive_match_reads ib.symm
    · archive_sum_of_words words
  exact indexed branch v branch (shrinkNextOrder T s D rem hD small A branch (((M).next branch).chart.symm v)) rfl
    (shrinkNextOrder_val T s D rem hD small A branch (((M).next branch).chart.symm v)).symm

end BranchOrdinal

private theorem motif_order_sum {α : Type*} [Fintype α] {n : ℕ}
    (order : Fin n ≃ α) (copies : α → ℕ) :
    (List.ofFn (fun i => copies (order i))).sum = ∑ a, copies a := by
  rw [List.sum_ofFn]
  exact order.sum_comp copies

/-- The real compact motif row list carries exactly the local copy charge used by the run. -/
theorem shrinkLayerData_motif_sum {K W : ℕ} (c : Cursor) (branch : Fin (M).rules.count)
    (O : ∀site, Incidents.SiteOrder («S» := shrinkStage s D) P (B).order (ShrinkMotif.chooseWidths (supply branch)) site W)
    (v : ((M).next branch).Site) :
    ((shrinkLayerData (K:=K) T s D rem hD small A c branch O).motifCopies
      ((shrinkArchiveSites (K:=K) T s D rem hD small A c branch).ord v)).sum =
      (shrinkBinary_siteCopies T s D rem hD small A).copies branch v := by
  rw [shrinkBinary_copies_at]
  let j := shrinkNextOrder T s D rem hD small A branch (((M).next branch).chart.symm v)
  let site := (shrinkPackOrder s D rem A).symm j
  exact @motif_order_sum _ (physicalActiveFintype P (ShrinkMotif.chooseWidths (supply branch)) site)
    _ (O site).equiv (fun a => shrinkRecordCopies T s rem A a.val)

private theorem shrinkInputLanes (s rem : ℕ) :
    shrinkCharge s+rem=(2*2^s+1)+(s+(CompressorPacking.tagBits (2^s)+rem)) := by simp [shrinkCharge,Nat.add_assoc]

/-- The original physical site, in the position coordinates read by the shrink child table. -/
@[instance_reducible]
def shrinkOldPosition : A.Site ≃ ChildRows.Actual P :=
  ((sitesAfterCast (shrinkInputLanes s rem) A).trans (B).chart.symm).trans
    (StageAddress.splitSite (shrinkRecordLane s rem))

private theorem oldNumber_split (v : (B).Base × BitWord ((2*2^s+1)+(s+(packingBits+rem)))) :
    ChildRows.oldNumber P (B).order (StageAddress.splitSite (shrinkRecordLane s rem) v) =
      Halves.siteNumber (B).order v := by
  change ((B).order v.1).val * (2^rem*2^packingBits*2^s*2^(2*2^s+1)) +
      (Demand.laneOrdinal P (shrinkRecordLane s rem v.2)).val =
    ((B).order v.1).val * 2^((2*2^s+1)+(s+(packingBits+rem))) + (tagOrdinal _ v.2).val
  rw [Demand.split_lane_ordinal P (fun _=>rfl)]
  simp only [pow_add]
  ac_rfl

theorem shrinkOldPosition_number (v : A.Site) :
    ChildRows.oldNumber P (B).order (shrinkOldPosition s rem A v) =
      Halves.siteNumber A.order (A.chart.symm v) :=
  (oldNumber_split s rem A _).trans (sitesAfterCast_number (shrinkInputLanes s rem) A v)

private theorem oldNumber_injective {base slot : Type} [AddCommGroup slot]
    {vertices slots colors tags lanes : ℕ}
    (packing : PackingData base slot (BitWord tags) (BitWord lanes) slots colors)
    (number : base ≃ Fin vertices) : Function.Injective (ChildRows.oldNumber packing number) := by
  let unpack := (StageAddress.reshuffle (V:=base) (c:=colors) (H:=slot)
    (Tag:=BitWord tags) (L:=BitWord lanes)).symm
  let E := unpack.trans (RefreshStageLayout.pair number (Demand.laneOrdinal packing))
  have ord (a : ChildRows.Actual packing) : (E a).val=ChildRows.oldNumber packing number a :=
    RefreshStageLayout.pair_index number (Demand.laneOrdinal packing) (unpack a)
  intro a b h
  exact E.injective (Fin.ext ((ord a).trans (h.trans (ord b).symm)))

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1500000 in
/-- The archived owner of a packed old position is the exact selected move's mathematical parent. -/
theorem shrink_parent_number (branch : Fin (M).rules.count) (v : A.Site) :
    Halves.siteNumber ((M).next branch).order (((M).next branch).chart.symm ((M).parent branch v)) =
      Incidents.siteNumber (B).order
        ((P).placement (ShrinkMotif.chooseWidths (supply branch)) (shrinkOldPosition s rem A v)) := by
  let G : ℕ→ℕ→ℕ→Prop := fun i n k =>
    ∀ (b : Fin (M).rules.count) (a : ChildRows.Actual P), i=b.val → n=ChildRows.oldNumber P (B).order a →
      k=Incidents.siteNumber (B).order ((P).placement (ShrinkMotif.chooseWidths (supply b)) a)
  have indexed : ParentAt M G := by
    unfold shrinkBinary
    apply parentAt_lanes
    unfold shrinkRaw
    apply shrinkMove_parentAt T B (shrinkRecordLane s rem) P rfl
      (rawConditions s rem B) (Nat.two_pow_pos s) hD small (tag_size s)
      (shrinkRecordCode s rem A) (shrinkRecordRoot s D rem A) G
    intro i v
    dsimp only
    intro b a ib va
    have pa : StageAddress.splitSite (shrinkRecordLane s rem) ((B).chart.symm v)=a :=
      oldNumber_injective P (B).order ((oldNumber_split s rem A _).trans va)
    subst a
    exact congrArg (fun words => Incidents.siteNumber (B).order
      ((P).placement (ShrinkMotif.chooseWidths words)
        (StageAddress.splitSite (shrinkRecordLane s rem) ((B).chart.symm v))))
      (archive_branch_read T s D rem hD small A b (fin := archivePopulation% i) i ib)
  exact indexed branch v branch _ rfl (shrinkOldPosition_number s rem A v).symm

private def shrinkPackedSuccessor (branch : Fin (M).rules.count) :
    ((M).next branch).Site ≃ Computability.VPVNP.Compression.Site (B).Base (BitWord packingBits) (BitWord rem) :=
  (((M).next branch).chart.symm.trans (shrinkNextOrder T s D rem hD small A branch)).trans
    (shrinkPackOrder s D rem A).symm

private theorem shrinkPackedSuccessor_parent (branch : Fin (M).rules.count) (v : A.Site) :
    shrinkPackedSuccessor T s D rem hD small A branch ((M).parent branch v) =
      (P).placement (ShrinkMotif.chooseWidths (supply branch)) (shrinkOldPosition s rem A v) := by
  apply (shrinkPackOrder s D rem A).injective
  simp only [shrinkPackedSuccessor,Equiv.trans_apply,Equiv.apply_symm_apply]
  exact Fin.ext ((shrinkNextOrder_val T s D rem hD small A branch _).trans
    ((shrink_parent_number T s D rem hD small A branch v).trans (shrinkPackOrder_val s D rem A _).symm))

/-- Enumerate the physical parent fiber in the exact order of the native child words. -/
def shrinkChildFiber (branch : Fin (M).rules.count) (v : ((M).next branch).Site) :
    Fin (2^s*2^(2*2^s+1)) ≃ {a // (M).parent branch a=v} := by
  let U := shrinkOldPosition s rem A
  let V := shrinkPackedSuccessor T s D rem hD small A branch
  let lay := ShrinkMotif.chooseWidths (supply branch)
  have comm (a : A.Site) : V ((M).parent branch a)=(P).placement lay (U a) :=
    shrinkPackedSuccessor_parent T s D rem hD small A branch a
  refine (Owner.childOrder P lay (V v)).trans
    { toFun := fun a => ⟨U.symm a.val,V.injective (by rw [comm,U.apply_symm_apply,a.property])⟩
      invFun := fun a => ⟨U a.val,by rw [←comm,a.property]⟩
      left_inv := fun a=>Subtype.ext (U.apply_symm_apply a.val)
      right_inv := fun a=>Subtype.ext (U.symm_apply_apply a.val) }

/-- The absolute child identifier in the native descriptor uses the numbered predecessor layer. -/
theorem shrink_child_id {K W : ℕ} (c : Cursor) (branch : Fin (M).rules.count)
    (O : ∀site,Incidents.SiteOrder («S» := shrinkStage s D) P (B).order (ShrinkMotif.chooseWidths (supply branch)) site W)
    (old : A.ArchiveSites) (numbered : old.Numbered) (first : old.layer.first=c.node)
    (v : ((M).next branch).Site) (j : Fin (2^s*2^(2*2^s+1))) :
    (shrinkLayerData (K:=K) T s D rem hD small A c branch O).child
        ((shrinkArchiveSites (K:=K) T s D rem hD small A c branch).ord v) j =
      old.id ((shrinkChildFiber T s D rem hD small A branch v j).val) := by
  let U := shrinkOldPosition s rem A
  let V := shrinkPackedSuccessor T s D rem hD small A branch
  let a := (Owner.childOrder P (ShrinkMotif.chooseWidths (supply branch)) (V v) j).val
  change c.node+ChildRows.oldNumber P (B).order a = old.layer.first+(old.ord (U.symm a)).val
  rw [first,numbered]
  apply congrArg (c.node+·)
  have h := shrinkOldPosition_number s rem A (U.symm a)
  change ChildRows.oldNumber P (B).order (U (U.symm a)) = _ at h
  rwa [U.apply_symm_apply] at h

section ArchiveAssembly

theorem shrinkArchive_numbered {K : ℕ} (c : Cursor) (branch : Fin (M).rules.count) :
    (shrinkArchiveSites (K:=K) T s D rem hD small A c branch).Numbered := by
  intro v
  exact shrinkNextOrder_val T s D rem hD small A branch (((M).next branch).chart.symm v)

private theorem shrinkOldCount (old : A.ArchiveSites) : old.layer.count=(x).originalSites := by
  have count : old.layer.count=Fintype.card A.Base*2^(shrinkCharge s+rem) := by
    simpa [BitWord] using Fintype.card_congr (old.ord.symm.trans A.chart.symm)
  have start : (x).originalSites=Fintype.card (B).Base*2^(shrinkCharge s+rem) :=
    (PhysicalStage.Program.shrink_positions s 0 rem (Fintype.card (B).Base)).1
  rw [start,shrink_record_base]
  exact count

def shrinkArchiveStep {K W : ℕ} (c : Cursor) (branch : Fin (M).rules.count)
    (O : ∀v,Incidents.SiteOrder («S» := shrinkStage s D) P (B).order (ShrinkMotif.chooseWidths (supply branch)) v W)
    (old : A.ArchiveSites) (numbered : old.Numbered) (first : old.layer.first=c.node) :
    (M).ArchiveStep branch old (shrinkBinaryCharge T s D rem hD small A branch) where
  sites := shrinkArchiveSites (K:=K) T s D rem hD small A c branch
  data := shrinkLayerData (K:=K) T s D rem hD small A c branch O
  row := {
    contiguous := by
      change c.node+(x).originalSites=old.layer.first+old.layer.count
      rw [first,shrinkOldCount s D rem A old]
    nonleaf := by change (1 : ℕ) ≠ 0; decide
    children := shrinkChildFiber T s D rem hD small A branch
    childId := shrink_child_id (K:=K) T s D rem hD small A c branch O old numbered first
    fresh := fun v=>by simp only [shrinkLayerData_half_sum,shrinkLayerData_motif_sum,shrinkBinaryCharge] }
  ownerPtr := (allocate K c (.shrink x)).words 44


end ArchiveAssembly
end
end ThreeFlat.Diagonal.PhysicalStage

end OAI
