import OAI.Hierarchy.DescentMeasuredFallbackSelection
import OAI.Hierarchy.DescentMeasuredFallbackLaneClock

namespace OAI
/-! # Word counts and addresses of the four actual fallback tree operands -/
namespace Hierarchy.DescentTreeLaneProgram
open Computability.BorderVNP.Crossing DescentKernelHistory DescentRouterSlots DescentContactTree DescentResetGates
open DescentOrderedReset DescentOrderedWords DescentTreeGateRefs DescentNamedContact
open DescentFallbackOperandBranch DescentFallbackItemSelect
open scoped BigOperators Classical
noncomputable section
set_option quotPrecheck false
variable {I C R W : Type} [Fintype I] [Fintype C] [Fintype R] [Fintype W]
variable (D : ℕ) (contact : I→C) (input : Bool→I→R) (site : Bool→R→W) (owner : Bool→C→W)
variable (align : ∀s i,site s (input s i)=owner s (contact i)) (cfg : Config) (p : ℕ) (hp : 0<p)
variable (s : Bool) (w : W) {depth n : ℕ} (book : LinkId owner s w ↪ Node depth) (key : I↪Fin n)
local notation "wt" => fun _ : I=>cfg.batches*p
local notation "B" => DescentRouterBank.network D contact input site owner wt
local notation "lp" => link contact owner s w
local notation "N" => DescentFixedExceptionalRouter.device D contact input site owner wt s w book
local notation "code" => DescentFixedNamedContact.code book lp
local notation "ids" => itemKey key contact owner s w
local notation "ops" => program D contact input site owner align cfg.batches p hp s w book key
local notation "atNode" k:arg i:arg => (⟨k,prefixAt code (k).val i⟩ : Physical.Site depth)

private def rootCell (one : Subsingleton (InputId site s w)) (e : DescentRouterSlots.Item contact owner s w) :
    Cell code 0 (prefixAt code 0 e) ≃ Fibre (input s) (input s e.val) where
  toFun j:=⟨j.val.val,congrArg Subtype.val (one.elim (root contact input site owner s w align j.val)
    (root contact input site owner s w align e))⟩
  invFun j:=⟨⟨j.val,((align s j.val).symm.trans (congrArg (site s) j.property)).trans
    ((align s e.val).trans e.property)⟩,funext (fun i=>Fin.elim0 i)⟩
  left_inv _:=Subtype.ext (Subtype.ext rfl)
  right_inv _:=Subtype.ext rfl

private def leafCell (e : DescentRouterSlots.Item contact owner s w) :
    Cell code depth (prefixAt code depth e) ≃ Fibre contact (contact e.val) := by
  have eqn (u : DescentRouterSlots.Item contact owner s w) : prefixAt code depth u=book (lp u) := by
    funext j
    simp [prefixAt,DescentFixedNamedContact.code,j.isLt]
  exact {
    toFun j:=⟨j.val.val,congrArg Subtype.val (book.injective ((eqn j.val).symm.trans (j.property.trans (eqn e))))⟩
    invFun j:=⟨⟨j.val,(congrArg (owner s) j.property).trans e.property⟩,by
      rw [eqn,eqn]
      exact congrArg book (Subtype.ext j.property)⟩
    left_inv _:=Subtype.ext (Subtype.ext rfl)
    right_inv _:=Subtype.ext rfl }

private theorem before_equiv {α β : Type*} [Fintype α] [Fintype β] (g : α≃β)
    (a : α↪Fin n) (b : β↪Fin n) (same : ∀i,b (g i)=a i) (x : α) :
    (DescentOrderedWords.before a x).card=(DescentOrderedWords.before b (g x)).card := by
  classical
  let perm : {i // a i<a x} ≃ {j // b j<b (g x)} :=g.subtypeEquiv (fun i=>by simp only [same])
  simpa only [DescentOrderedWords.before,Fintype.card_subtype] using Fintype.card_congr perm

def measuredWord {Q : Type} {width : Q→ℕ} (cfg : Config) (p : ℕ)
    (l : DescentLaneGates.Lane p width) (items : Fin cfg.count→DescentFallbackItemSelect.Item)
    (live : Finset (Fin cfg.count)) (j : Fin cfg.count) (node : ℕ) : Prop :=
  l.start=cfg.startWord items live j node*p ∧ l.bundleStart=cfg.startWord items live j node ∧
    l.count (fun a=>width a/p)=cfg.visibleWords items live j node

omit [Fintype R] in
include hp in
private theorem physical_words {q : Physical.Site depth} (l : DescentLaneGates.Lane p (boundaryWidth N q))
    (items : Fin cfg.count→DescentFallbackItemSelect.Item) (live : Finset (Fin cfg.count))
    (j : Fin cfg.count) (node : ℕ) {α : Type} [Fintype α] (ord : α↪Fin n) (x : α) (b : Fin cfg.batches)
    (rankEq : rank items live j=(DescentOrderedWords.before ord x).card)
    (phase : node%cfg.batches=b.val) (start : l.start=batchStart ord x cfg.batches p b) (stride : l.stride=1)
    (bits : boundaryWidth N q l.port=live.card*(cfg.batches*p)) :
    measuredWord cfg p l items live j node := by
  exact DescentMeasuredFallbackLaneClock.lane_clock cfg items live j node ord x b l
    (fun a=>boundaryWidth N q a/p) hp rankEq phase start stride (by rw [bits,←Nat.mul_assoc,Nat.mul_div_cancel _ hp])

private def portSize : ((N).Edge ⊕ DescentNetworkSubstitution.Slot B (s,w))→ℕ :=
  Sum.elim (N).width (DescentNetworkSubstitution.slotWidth B (s,w))

omit [Fintype R] in
private theorem portSize_fields {q : Physical.Site depth} (l : DescentLaneGates.Lane p (boundaryWidth N q)) :
    portSize D contact input site owner cfg p s w book (physicalFields D contact input site owner cfg.batches p s w book l).1=
      boundaryWidth N q l.port := by
  cases eqn:l.port <;> simp only [physicalFields,portSize,boundaryWidth,eqn] <;> rfl

variable (Y : ℕ) (e : DescentRouterSlots.Item contact owner s w) (b : Fin cfg.batches)
variable (items : Fin cfg.count→DescentFallbackItemSelect.Item) (live : Finset (Fin cfg.count))
variable (j : Fin cfg.count) (node : ℕ) (phase : node%cfg.batches=b.val)
local notation "pop" k:arg => live.card=Fintype.card (Cell code k (prefixAt code k e))
local notation "prior" k:arg => rank items live j=(DescentOrderedWords.before
  (Contact.cellKey ids code k (prefixAt code k e)) ⟨e,rfl⟩).card
local notation "lane" k:arg a:arg => (((ops Y (atNode k e)).op (⟨e,rfl⟩,b)).arg (a : Fin 2))
include phase

omit [Fintype R] in
/-- Actual bit start, first word, and truncated word count at the root operand. -/
theorem previous_root_words (sole : Subsingleton (InputId site s w)) (population : pop 0) (ranked : prior 0) :
    measuredWord cfg p (lane (0 : Fin (depth+1)) 0) items live j node := by
  have laneData :=previous_fields D contact input site owner align cfg.batches p hp s w book key Y e b (0 : Fin (depth+1))
  simp only [Fin.cases_zero] at laneData
  have start:=congrArg (fun z=>z.2.1) laneData
  have stride:=congrArg (fun z=>z.2.2) laneData
  have extent:=congrArg (fun z=>portSize D contact input site owner cfg p s w book z.1) laneData
  rw [portSize_fields] at extent
  let perm:=rootCell contact input site owner align s w book sole e
  let ord:=fibreKey key (input s) (input s e.val)
  have counts:=Fintype.card_congr perm
  have firstRank:=before_equiv perm (Contact.cellKey ids code 0 (prefixAt code 0 e)) ord
    (fun _=>rfl) ⟨e,rfl⟩
  apply physical_words D contact input site owner cfg p hp s w book _ items live j node ord
    ⟨e.val,rfl⟩ b (ranked.trans firstRank) phase start stride
  rw [population,counts,extent]
  change (∑ _ : Fibre (input s) (input s e.val),cfg.batches*p)=_
  simp

omit [Fintype R] in
/-- Actual bit start, first word, and truncated word count at the previous operand. -/
theorem previous_cell_words (t : Fin depth) (population : pop (t.val+1)) (ranked : prior (t.val+1)) :
    measuredWord cfg p (lane t.succ 0) items live j node := by
  have laneData :=previous_fields D contact input site owner align cfg.batches p hp s w book key Y e b t.succ
  simp only [Fin.cases_succ] at laneData
  have start:=congrArg (fun z=>z.2.1) laneData
  have stride:=congrArg (fun z=>z.2.2) laneData
  have extent:=congrArg (fun z=>portSize D contact input site owner cfg p s w book z.1) laneData
  rw [portSize_fields] at extent
  apply physical_words D contact input site owner cfg p hp s w book _ items live j node
    (Contact.cellKey ids code (t.val+1) (prefixAt code (t.val+1) e)) ⟨e,rfl⟩ b ranked phase start stride
  rw [population,extent]
  change (∑ _ : Cell code (t.val+1) (prefixAt code (t.val+1) e),cfg.batches*p)=_
  simp

omit [Fintype R] in
/-- Actual bit start, first word, and truncated word count at the leaf operand. -/
theorem following_leaf_words  (population : pop depth) (ranked : prior depth) :
    measuredWord cfg p (lane (Fin.last depth) 1) items live j node := by
  have laneData :=following_fields D contact input site owner align cfg.batches p hp s w book key Y e b (Fin.last depth)
  simp only [Fin.lastCases_last] at laneData
  have start:=congrArg (fun z=>z.2.1) laneData
  have stride:=congrArg (fun z=>z.2.2) laneData
  have extent:=congrArg (fun z=>portSize D contact input site owner cfg p s w book z.1) laneData
  rw [portSize_fields] at extent
  let perm:=leafCell contact owner s w book e
  let ord:=fibreKey key contact (contact e.val)
  have counts:=Fintype.card_congr perm
  have firstRank:=before_equiv perm (Contact.cellKey ids code depth (prefixAt code depth e)) ord
    (fun _=>rfl) ⟨e,rfl⟩
  apply physical_words D contact input site owner cfg p hp s w book _ items live j node ord
    ⟨e.val,rfl⟩ b (ranked.trans firstRank) phase start stride
  rw [population,counts,extent]
  change DescentNetworkSubstitution.slotWidth B (s,w) (linkSlot D contact input site owner wt s w (lp e))=_
  rw [linkWidth]
  change (∑ _ : Fibre contact (contact e.val), cfg.batches*p) = _
  simp

omit [Fintype R] in
/-- Actual bit start, first word, and truncated word count at the following operand. -/
theorem following_cell_words (t : Fin depth) (population : pop (t.val+1)) (ranked : prior (t.val+1)) :
    measuredWord cfg p (lane t.castSucc 1) items live j node := by
  have laneData :=following_fields D contact input site owner align cfg.batches p hp s w book key Y e b t.castSucc
  simp only [Fin.lastCases_castSucc] at laneData
  have start:=congrArg (fun z=>z.2.1) laneData
  have stride:=congrArg (fun z=>z.2.2) laneData
  have extent:=congrArg (fun z=>portSize D contact input site owner cfg p s w book z.1) laneData
  rw [portSize_fields] at extent
  apply physical_words D contact input site owner cfg p hp s w book _ items live j node
    (Contact.cellKey ids code (t.val+1) (prefixAt code (t.val+1) e)) ⟨e,rfl⟩ b ranked phase start stride
  rw [population,extent]
  change (∑ _ : Cell code (t.val+1) (prefixAt code (t.val+1) e),cfg.batches*p)=_
  simp

end
end Hierarchy.DescentTreeLaneProgram

end OAI
