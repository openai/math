import OAI.Hierarchy.DescentReachedSourceOperand
import OAI.Hierarchy.DescentPrivateBookTransport

namespace OAI
/-! Endpoint and word offset of a final public-pin operand on the original matched geometry. -/
namespace Hierarchy.DescentBundleHistory
open Computability.BorderVNP.Crossing DescentNetworkPartition DescentKernelHistory
open scoped Classical
noncomputable section
set_option quotPrecheck false
variable {P C Tag : Type} [Fintype C] {d d₁ p : ℕ} {bits : P→ℕ}
variable (N : Network d P bits) (loc : N.Site→C) (pt : C→EuclideanSpace ℝ (Fin d₁))
    (ok : ∀t,‖pt t‖≤1)
variable (r : SiteBits (U:=Tag) N) (hp : 0<p)
local notation "Q" => quotient N loc pt ok
def inputPin {d p:ℕ} {Y:Type} (N:Network d P bits) (v:N.Site) :
    BlockRef p (boundaryWidth N v)⊕Y → Option (P×ℕ)
  | .inl b=>b.pinPayload N v
  | .inr _=>none

theorem inputPin_quotient (v:N.Site) (x:BlockRef p (boundaryWidth N v) ⊕ Private (r v) p) :
    inputPin Q (loc v) (nextArg N loc pt ok r hp v x)=inputPin N v x :=by
  rcases x with ⟨e|z,k,fit⟩|⟨h,j⟩
  · by_cases same:loc (N.src e.val)=loc (N.dst e.val) <;>
      simp [nextArg,wordTransfer,quotientMap,quotientBlock,inputPin,BlockRef.pinPayload,same]
  · rfl
  · rfl

theorem inputPin_origin {Y : Type} (v : N.Site)
    (a : BlockRef p (boundaryWidth N v) ⊕ Y) (label : P) (chunk : ℕ)
    (h : inputPin N v a = some (label, chunk)) :
    ∃ t : Attached N v, ∃ fits : (chunk+1)*p ≤ bits t.val,
      t.val = label ∧ a = .inl ⟨.inr t, chunk, fits⟩ := by
  cases a with
  | inr a => contradiction
  | inl b =>
    have ext := (BlockRef.pinPayload_iff N v b label chunk).mp h
    rcases b with ⟨port,offset,size⟩
    obtain ⟨t,same,portEq,offsetEq⟩ := ext
    dsimp only at portEq offsetEq
    subst port
    subst offset
    exact ⟨t,size,same,rfl⟩

end
end Hierarchy.DescentBundleHistory

namespace Hierarchy.DescentBundleHistory
open Computability.BorderVNP.Crossing DescentSixParty DescentSixParty.GadgetNetwork DescentKernelHistory
open DescentNetworkPartition DescentHostDirectory
open scoped Classical
noncomputable section
set_option quotPrecheck false
variable {F P I V T : Type} [Field F] [Fintype I] [DecidableEq T] {d p R Z : ℕ}
    {bits : P → ℕ} {W : MarkedWorld F d P bits} (B : BitDescription W)
    (G : PoweredGadget F) (pick : I × Fin 2 ↪ W.graph.Edge)
    (z : I → ℕ) (hz : ∀ i, 0 < z i) (fit : ∀ i j, W.graph.width (pick (i,j)) = z i * G.b)
    (room : ∀ i, z i ≤ Z) (pack : W.graph.Site → V) (prof : I → Profile G.C)
    (hp : 0 < p) (one : 1 ≤ R) (pin : ∀ a, p ∣ bits a) (sh : WorldShape p R B)
    (whole : ∀ i, p ∣ z i)
local notation "sel" => W.selected G pick z hz fit pack prof
local notation "sbit" => B.selected G pick z hz fit room pack prof
local notation "ss" => sh.selected hp one pin G pick z hz fit room pack prof whole
local notation "net" => physical W.graph pick (branchWidth G z prof)
local notation "grp" => newSite W.graph pick (bestLayout (branchWidth G z prof)) pack
local notation "oldBits" => physicalBits G W.toWorld pick z room prof B.recipe
local notation "oldShape" => physicalShape W B G pick z room prof hp sh.sites sh.edges pin whole
variable (key : (W.selected G pick z hz fit pack prof).graph.Site → Key T) (flag : T → Bool) (k g : ℕ)
local notation "addr" => MarkedWorld.address sel key flag k g
local notation "reclaimed" => ↥(MarkedWorld.reclaimed sel key flag k g)
local notation "x₁" => fun _ : Merged W.graph pick (bestLayout (branchWidth G z prof)) pack => (0 : EuclideanSpace ℝ (Fin d))
local notation "x₂" => fun _ : reclaimed => (0 : EuclideanSpace ℝ (Fin d))
local notation "ok₁" => fun t : Merged W.graph pick (bestLayout (branchWidth G z prof)) pack => (by simp : ‖x₁ t‖ ≤ 1)
local notation "ok₂" => fun t : reclaimed => (by simp : ‖x₂ t‖ ≤ 1)
local notation "firstNet" => quotient net grp x₁ ok₁
local notation "firstBits" => quotientBits net grp x₁ ok₁ oldBits
local notation "lastWorld" => (sel).coalesced key flag k g
local notation "destShape" => (ss).coalesced key flag k g
local notation "destBits" => (sbit).coalesced key flag k g
local notation "Values" => (Σ t, BlockRef p (boundaryWidth (lastWorld).graph t) ⊕ Private ((destBits).recipe t) p)

set_option backward.isDefEq.lazyProjDelta false
set_option backward.isDefEq.lazyWhnfCore false

variable {Y : MarkedWorld F d P bits} {BY : BitDescription Y} {s : WorldShape p R BY}

local notation "receiptTy" => selectedBookOperandReceipt B G pick z hz fit room pack prof hp one pin sh whole key flag k g
local notation "readValue" => selectedSourceArgument B G pick z hz fit room pack prof hp pin sh whole key flag k g

theorem selectedSourcePin_eq (src : NodeOrder.Global (N:=net) oldBits)
    (i : Fin (((oldShape src.1).recipe hp).arity src.2)) :
    inputPin (lastWorld).graph (addr (grp src.1)) (readValue src i) =
      inputPin net src.1 (((oldShape src.1).recipe hp).operand src.2 i) := by
  dsimp only [selectedSourceArgument, BitDescription.coalesced, BitDescription.selected,
    MarkedWorld.coalesced, MarkedWorld.selected, recorded, recordedBits]
  exact (inputPin_quotient firstNet addr x₂ ok₂ firstBits hp _ _).trans
    (inputPin_quotient net grp x₁ ok₁ oldBits hp _ _)

theorem selectedBook_final_pin (book : SiteBooks hp s destShape)
    (x : NodeOrder.All BY) (j : Fin (((s.sites x.1).recipe hp).arity x.2))
    (src : NodeOrder.Global (N:=net) oldBits) (receipt : receiptTy book x j src)
    (pinRef : Attached Y.graph x.1) (chunk : ℕ) (fits : (chunk+1)*p ≤ bits pinRef.val)
    (found : ((s.sites x.1).recipe hp).operand x.2 j = .inl ⟨.inr pinRef,chunk,fits⟩) :
    ∃ a : Attached net src.1, ∃ full : (chunk+1)*p ≤ bits a.val, a.val = pinRef.val ∧
      ((oldShape src.1).recipe hp).operand src.2 receipt.choose = .inl ⟨.inr a,chunk,full⟩ := by
  obtain ⟨before,routed,named⟩ := WordBook.public_origin _ _ (book.atSite x.1) x.2 j _ found
  have previous : before.pinPayload (lastWorld).graph (book.home x.1) = some (pinRef.val,chunk) :=
    (book.pinPayload x.1 before).symm.trans
      (congrArg (fun t => BlockRef.pinPayload Y.graph x.1 t) named)
  let payload (t : Values) := inputPin (lastWorld).graph t.1 t.2
  have agree := congrArg payload receipt.choose_spec.2
  have beforeRead := congrArg (inputPin (lastWorld).graph (book.home x.1)) routed
  apply inputPin_origin net
  exact (selectedSourcePin_eq B G pick z hz fit room pack prof hp pin sh whole key flag k g src receipt.choose).symm.trans
    (agree.symm.trans (beforeRead.trans previous))

end
end Hierarchy.DescentBundleHistory

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
set_option backward.isDefEq.lazyProjDelta false
set_option backward.isDefEq.lazyWhnfCore false
attribute [local irreducible] BitDescription.scannedRows
local notation "r" => BitDescription.scannedRows he T
local notation "uni" => fun _ : (r).pairs=>T.z
local notation "pos" => fun _ : (r).pairs=>T.unitPos
local notation "room" => fun _ : (r).pairs=>le_refl T.z
local notation "whole" => fun _ : (r).pairs=>unit
local notation "prof" => (r).profile c
local notation "after" => afterOrdinary hp one pin ticket arch sh unit
local notation "chart" => privateChart ticket arch hp one pin sh unit
local notation "bk" => privateBooks ticket arch hp one pin sh unit
local notation "M" => rawGraph he T c
local notation "baseShape" => physicalShape W arch.bit G (r).pick uni room prof hp sh.sites sh.edges pin whole
local notation "next" => (ticket.advance arch).bit
local notation "source" => operandSource ticket arch

attribute [local irreducible] operandSource

/-- An actual exterior result cannot originate at a cable or at a private operand.
The immutable public name and its p-word offset both survive the original two quotient
maps and every subsequent genuine renaming or cable split. -/
theorem final_pin_source (x:NodeOrder.All next) (j:Fin ((((after).sites x.1).recipe hp).arity x.2))
    (z:Attached n.result.graph x.1) (k:ℕ) (fits:(k+1)*p≤bits z.val)
    (found:(((after).sites x.1).recipe hp).operand x.2 j=.inl ⟨.inr z,k,fits⟩) :
    ∃a:Attached (M) (source x).1,∃full:(k+1)*p≤bits a.val,a.val=z.val ∧
      ((baseShape (source x).1).recipe hp).operand (source x).2
        (sourceIndex ticket arch hp one pin sh unit x j)=.inl ⟨.inr a,k,full⟩ :=by
  exact selectedBook_final_pin arch.bit G (r).pick uni pos (r).fit room (r).pack prof hp one pin sh whole
    ((chart).key he T c) (chart).hub T.k (gainExponent 20 T.Δ) (bk) x j (source x)
    (source_read ticket arch hp one pin sh unit x j) z k fits found

end
end Hierarchy.DescentLocalArchiveOrder

end OAI
