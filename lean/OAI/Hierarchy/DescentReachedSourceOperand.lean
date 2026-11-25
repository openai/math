import OAI.Hierarchy.DescentReachedPrivateBasis
import OAI.Hierarchy.DescentQuotientSourceOperand

namespace OAI
/-! The selected origin, operand index and p-word at each genuinely occupied ordinary row. -/
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
local notation "wireFits" => physical_multiple W G pick z prof sh.edges whole
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
local notation "firstNames" => NodeOrder.physicalNames B G pick z room prof
local notation "selectNames" => NodeOrder.selectedNames B G pick z hz fit room pack prof
local notation "lastNames" => NodeOrder.coalescedNames (sbit) key flag k g
local notation "Values" => (Σ t, BlockRef p (boundaryWidth (lastWorld).graph t) ⊕ Private ((destBits).recipe t) p)
local notation "read₁" => nextArg net grp x₁ ok₁ oldBits hp
local notation "read₂" => nextArg (sel).graph addr x₂ ok₂ (sbit).recipe hp

local notation "rawNames" =>
  (NodeOrder.quotientNames firstNet addr x₂ ok₂ firstBits).trans (NodeOrder.quotientNames net grp x₁ ok₁ oldBits)
local notation "lastNet" => quotient firstNet addr x₂ ok₂
local notation "lastBits" => quotientBits firstNet addr x₂ ok₂ firstBits
local notation "firstShape" => quotientShape net grp x₁ ok₁ oldBits oldShape wireFits
local notation "lastShape" => quotientShape firstNet addr x₂ ok₂ firstBits firstShape (fun e => wireFits e.val)

set_option backward.isDefEq.lazyProjDelta false
set_option backward.isDefEq.lazyWhnfCore false
def coalescedPhysicalNode (node : NodeOrder.All destBits) : NodeOrder.Global (N:=lastNet) lastBits := by
  dsimp only [BitDescription.coalesced, BitDescription.selected, MarkedWorld.coalesced,
    MarkedWorld.selected, recorded, recordedBits] at node
  exact node

def coalescedPhysicalOrigin (node : NodeOrder.All destBits) :=
  rawNames (coalescedPhysicalNode B G pick z hz fit room pack prof key flag k g node)

theorem selected_coalesced_origin (node : NodeOrder.All destBits)
    (src : NodeOrder.Global (N:=net) oldBits)
    (named : (firstNames) src = selectNames (lastNames node)) :
    coalescedPhysicalOrigin B G pick z hz fit room pack prof key flag k g node = src :=
  (firstNames).injective named.symm

theorem selected_coalesced_source_operand (node : NodeOrder.All destBits)
    (j : Fin ((((destShape).sites node.1).recipe hp).arity node.2))
    (src : NodeOrder.Global (N:=net) oldBits)
    (named : (firstNames) src = selectNames (lastNames node)) :
    ∃ a : Fin (((oldShape src.1).recipe hp).arity src.2), a.val = j.val ∧
      (⟨node.1, ((((destShape).sites node.1).recipe hp).operand node.2 j)⟩ : Values) =
        ⟨addr (grp src.1), read₂ (grp src.1) (read₁ src.1 (((oldShape src.1).recipe hp).operand src.2 a))⟩ := by
  let rawNode : NodeOrder.Global (N:=lastNet) lastBits := by
    dsimp only [BitDescription.coalesced, BitDescription.selected, MarkedWorld.coalesced,
      MarkedWorld.selected, recorded, recordedBits] at node
    exact node
  let arg : Fin (((lastShape rawNode.1).recipe hp).arity rawNode.2) := by
    dsimp only [WorldShape.coalesced, WorldShape.selected, Shape.coalesced, Shape.selected,
      BitDescription.coalesced, BitDescription.selected, MarkedWorld.coalesced,
      MarkedWorld.selected, recorded, recordedBits] at j
    exact j
  have raw := source_operand net grp x₁ ok₁ oldBits oldShape wireFits hp addr x₂ ok₂ rawNode arg
  have idSource : rawNames rawNode = src := (firstNames).injective named.symm
  dsimp only at raw
  rw [idSource] at raw
  dsimp only [WorldShape.coalesced, WorldShape.selected, Shape.coalesced, Shape.selected,
    BitDescription.coalesced, BitDescription.selected, MarkedWorld.coalesced,
    MarkedWorld.selected, recorded, recordedBits]
  exact raw

variable {Y : MarkedWorld F d P bits} {BY : BitDescription Y} {s : WorldShape p R BY}

def selectedBookOperandReceipt (book : SiteBooks hp s destShape) (x : NodeOrder.All BY) (j : Fin (((s.sites x.1).recipe hp).arity x.2))
    (src : NodeOrder.Global (N:=net) oldBits) : Prop :=
  let atSite := book.atSite x.1
  ∃ a : Fin (((oldShape src.1).recipe hp).arity src.2), a.val = j.val ∧
    (⟨book.home x.1, (((destShape).sites (book.home x.1)).recipe hp).operand
      (atSite.node x.2) (j.cast (atSite.length x.2))⟩ : Values) =
      ⟨addr (grp src.1), read₂ (grp src.1) (read₁ src.1 (((oldShape src.1).recipe hp).operand src.2 a))⟩

theorem selectedBookOperandReceipt_of_names (book : SiteBooks hp s destShape) (x : NodeOrder.All BY) (j : Fin (((s.sites x.1).recipe hp).arity x.2))
    (src : NodeOrder.Global (N:=net) oldBits)
    (named : (firstNames) src = selectNames (lastNames (book.nodeAt hp x))) :
    selectedBookOperandReceipt B G pick z hz fit room pack prof hp one pin sh whole key flag k g book x j src :=
  selected_coalesced_source_operand B G pick z hz fit room pack prof hp one pin sh whole key flag k g
    (book.nodeAt hp x) (j.cast ((book.atSite x.1).length x.2)) src named

local notation "receiptTy" => selectedBookOperandReceipt B G pick z hz fit room pack prof hp one pin sh whole key flag k g
def selectedSourceArgument (src : NodeOrder.Global (N:=net) oldBits) (i : Fin (((oldShape src.1).recipe hp).arity src.2)) :
    BlockRef p (boundaryWidth (lastWorld).graph (addr (grp src.1))) ⊕ Private ((destBits).recipe (addr (grp src.1))) p :=
  read₂ (grp src.1) (read₁ src.1 (((oldShape src.1).recipe hp).operand src.2 i))
local notation "readValue" => selectedSourceArgument B G pick z hz fit room pack prof hp pin sh whole key flag k g

theorem selectedBook_public_iff (book : SiteBooks hp s destShape)
    (x : NodeOrder.All BY) (j : Fin (((s.sites x.1).recipe hp).arity x.2)) (src : NodeOrder.Global (N:=net) oldBits)
    (receipt : receiptTy book x j src) :
    (∃ b, ((s.sites x.1).recipe hp).operand x.2 j = .inl b) ↔ ∃ b, readValue src receipt.choose = .inl b := by
  let Public (v : Values) := ∃ b, v.2 = .inl b
  have same := congrArg Public receipt.choose_spec.2
  constructor
  · rintro ⟨b, h⟩
    obtain ⟨w, hw, _⟩ := WordBook.public_origin _ _ (book.atSite x.1) x.2 j b h
    exact same.mp ⟨w, hw⟩
  · intro h
    obtain ⟨w, hw⟩ := same.mpr h
    exact ⟨_, (book.atSite x.1).publicHit x.2 j w hw⟩

theorem selectedBook_original_pin (book : SiteBooks hp s destShape)
    (x : NodeOrder.All BY) (j : Fin (((s.sites x.1).recipe hp).arity x.2)) (src : NodeOrder.Global (N:=net) oldBits)
    (receipt : receiptTy book x j src)
    (a : Attached net src.1) (w : ℕ) (fits : (w+1)*p ≤ bits a.val)
    (previous : ((oldShape src.1).recipe hp).operand src.2 receipt.choose = .inl ⟨.inr a, w, fits⟩) :
    ∃ b, ((s.sites x.1).recipe hp).operand x.2 j = .inl b ∧ b.exteriorAt Y.graph x.1 a.val w := by
  let PinAt (u : Values) := ∃ b, u.2 = .inl b ∧ b.exteriorAt (lastWorld).graph u.1 a.val w
  have same := congrArg PinAt receipt.choose_spec.2
  have pinRead : PinAt ⟨addr (grp src.1),readValue src receipt.choose⟩ := by
    dsimp only [PinAt, selectedSourceArgument]
    rw [previous]
    let atLast : Attached (lastWorld).graph (addr (grp src.1)) := ⟨a.val, congrArg (addr ∘ grp) a.property⟩
    exact ⟨⟨.inr atLast, w, fits⟩, rfl, atLast, rfl, rfl, rfl⟩
  obtain ⟨b, hit, here⟩ := same.mpr pinRead
  exact ⟨_, (book.atSite x.1).publicHit x.2 j b hit, book.exterior _ b _ _ here⟩

variable {ValueKey : Type}
local notation "Labels" => ∀ v : reclaimed, ((((destShape).sites v).recipe hp).UsedWord → ValueKey)
def selectedBookSample (labels : Labels) (data : Values) : Option ValueKey :=
  match data.2 with
  | .inl _ => none
  | .inr h => if mem : (((destShape).sites data.1).recipe hp).Used h then some (labels data.1 ⟨h,mem⟩) else none
local notation "sample" => selectedBookSample B G pick z hz fit room pack prof hp one pin sh whole key flag k g

def selectedSourceSample (labels : Labels) (src : NodeOrder.Global (N:=net) oldBits)
    (i : Fin (((oldShape src.1).recipe hp).arity src.2)) : Option ValueKey :=
  sample labels ⟨addr (grp src.1), readValue src i⟩

def selectedSourceEncoding (labels : Labels) (v : (net).Site)
    (t : Private ((destBits).recipe (addr (grp v))) p) (sig : ValueKey) : Prop :=
  ∀ mem : (((destShape).sites (addr (grp v))).recipe hp).Used t, labels (addr (grp v)) ⟨t,mem⟩ = sig

def selectedSourceArrives (src : NodeOrder.Global (N:=net) oldBits)
    (i : Fin (((oldShape src.1).recipe hp).arity src.2))
    (t : Private ((destBits).recipe (addr (grp src.1))) p) : Prop :=
  readValue src i = .inr t

def selectedSourceKeyClaim (labels : Labels) (src : NodeOrder.Global (N:=net) oldBits)
    (i : Fin (((oldShape src.1).recipe hp).arity src.2)) (kw : ValueKey) : Prop :=
  ∀ t sig, selectedSourceArrives B G pick z hz fit room pack prof hp pin sh whole key flag k g src i t →
    selectedSourceEncoding B G pick z hz fit room pack prof hp one pin sh whole key flag k g labels src.1 t sig → kw = sig

theorem selectedBook_private (book : SiteBooks hp s destShape)
    (x : NodeOrder.All BY) (j : Fin (((s.sites x.1).recipe hp).arity x.2))
    (src : NodeOrder.Global (N:=net) oldBits) (receipt : receiptTy book x j src)
    (labels : Labels) (h : ((s.sites x.1).recipe hp).UsedWord)
    (hit : ((s.sites x.1).recipe hp).operand x.2 j = .inr h.val) :
    selectedSourceSample B G pick z hz fit room pack prof hp one pin sh whole key flag k g labels src receipt.choose =
      some (labels (book.home x.1) ((book.atSite x.1).word h)) := by
  unfold selectedSourceSample
  refine (congrArg (sample labels) receipt.choose_spec.2.symm).trans ?_
  have phys := ((book.atSite x.1).hit x.2 j h).mp hit
  simp only [selectedBookSample, phys, ((book.atSite x.1).word h).property, dite_eq_left]

theorem selectedBook_private_key (book : SiteBooks hp s destShape)
    (x : NodeOrder.All BY) (j : Fin (((s.sites x.1).recipe hp).arity x.2))
    (src : NodeOrder.Global (N:=net) oldBits) (receipt : receiptTy book x j src)
    (labels : Labels) (h : ((s.sites x.1).recipe hp).UsedWord)
    (hit : ((s.sites x.1).recipe hp).operand x.2 j = .inr h.val)
    (t : Private ((destBits).recipe (addr (grp src.1))) p) (sig : ValueKey)
    (arrived : readValue src receipt.choose = .inr t)
    (encoded : selectedSourceEncoding B G pick z hz fit room pack prof hp one pin sh whole key flag k g labels src.1 t sig) :
    labels (book.home x.1) ((book.atSite x.1).word h) = sig := by
  have sampled := selectedBook_private B G pick z hz fit room pack prof hp one pin sh whole key flag k g book x j src receipt labels h hit
  unfold selectedSourceSample at sampled
  rw [arrived] at sampled
  simp only [selectedBookSample] at sampled
  split at sampled
  · rename_i mem
    exact (Option.some.inj sampled).symm.trans (encoded mem)
  · contradiction

local notation "bookWord" => DescentLocalArchiveOrder.coalescedBookWord sh hp one pin G pick z hz fit room pack prof whole key flag k g
local notation "bookOrigin" => doubleOrigin net grp x₁ ok₁ oldBits oldShape wireFits hp addr x₂ ok₂

theorem selected_coalesced_inherited (v : (net).Site) (w : ((oldShape v).recipe hp).UsedWord) :
    ∃ t : Private ((destBits).recipe (addr (grp v))) p,
      read₂ (grp v) (read₁ v (.inr w.val)) = .inr t ∧
      ∀ used : (((destShape).sites (addr (grp v))).recipe hp).Used t,
        bookOrigin ⟨addr (grp v), bookWord (addr (grp v)) ⟨t,used⟩⟩ = .inr (.inr ⟨v,w⟩) := by
  dsimp only [WorldShape.coalesced, WorldShape.selected, Shape.coalesced, Shape.selected,
    BitDescription.coalesced, BitDescription.selected, MarkedWorld.coalesced,
    MarkedWorld.selected, recorded, recordedBits, DescentLocalArchiveOrder.coalescedBookWord, Function.Embedding.refl_apply]
  exact inherited_capture net grp x₁ ok₁ oldBits oldShape wireFits hp addr x₂ ok₂ v w

theorem selected_coalesced_first (v : (net).Site) (e : Incident (net) v) (j : ℕ)
    (fits : (j+1)*p ≤ (net).width e.val) (same : grp ((net).src e.val) = grp ((net).dst e.val)) :
    ∃ t : Private ((destBits).recipe (addr (grp v))) p,
      read₂ (grp v) (read₁ v (.inl ⟨.inl e,j,fits⟩)) = .inr t ∧
      ∀ used : (((destShape).sites (addr (grp v))).recipe hp).Used t,
        bookOrigin ⟨addr (grp v), bookWord (addr (grp v)) ⟨t,used⟩⟩ =
          .inr (.inl ⟨e.val,⟨j,(Nat.le_div_iff_mul_le hp).mpr fits⟩⟩) := by
  dsimp only [WorldShape.coalesced, WorldShape.selected, Shape.coalesced, Shape.selected,
    BitDescription.coalesced, BitDescription.selected, MarkedWorld.coalesced,
    MarkedWorld.selected, recorded, recordedBits, DescentLocalArchiveOrder.coalescedBookWord, Function.Embedding.refl_apply]
  exact first_capture net grp x₁ ok₁ oldBits oldShape wireFits hp addr x₂ ok₂ v e j fits same

theorem selected_coalesced_second (v : (net).Site) (e : Incident (net) v) (j : ℕ)
    (fits : (j+1)*p ≤ (net).width e.val) (distinct : grp ((net).src e.val) ≠ grp ((net).dst e.val))
    (same : addr (grp ((net).src e.val)) = addr (grp ((net).dst e.val))) :
    ∃ t : Private ((destBits).recipe (addr (grp v))) p,
      read₂ (grp v) (read₁ v (.inl ⟨.inl e,j,fits⟩)) = .inr t ∧
      ∀ used : (((destShape).sites (addr (grp v))).recipe hp).Used t,
        bookOrigin ⟨addr (grp v), bookWord (addr (grp v)) ⟨t,used⟩⟩ =
          .inl ⟨e.val,⟨j,(Nat.le_div_iff_mul_le hp).mpr fits⟩⟩ := by
  dsimp only [WorldShape.coalesced, WorldShape.selected, Shape.coalesced, Shape.selected,
    BitDescription.coalesced, BitDescription.selected, MarkedWorld.coalesced,
    MarkedWorld.selected, recorded, recordedBits, DescentLocalArchiveOrder.coalescedBookWord, Function.Embedding.refl_apply]
  exact second_capture net grp x₁ ok₁ oldBits oldShape wireFits hp addr x₂ ok₂ v e j fits distinct same

theorem carriedOutsideBook (labels : Labels) (src : NodeOrder.Global (N:=net) oldBits)
    (i : Fin (((oldShape src.1).recipe hp).arity src.2)) (kw : ValueKey)
    (claim : selectedSourceKeyClaim B G pick z hz fit room pack prof hp one pin sh whole key flag k g labels src i kw)
    (prior : ((oldShape src.1).recipe hp).UsedWord)
    (read : ((oldShape src.1).recipe hp).operand src.2 i = .inr prior.val) (donor : ValueKey)
    (encode : ∀ (t : Private ((destBits).recipe (addr (grp src.1))) p)
      (mem : (((destShape).sites (addr (grp src.1))).recipe hp).Used t),
      bookOrigin ⟨addr (grp src.1), bookWord (addr (grp src.1)) ⟨t,mem⟩⟩ = .inr (.inr ⟨src.1,prior⟩) →
      labels (addr (grp src.1)) ⟨t,mem⟩ = donor) : kw = donor := by
  obtain ⟨t,arrived,origin⟩ := selected_coalesced_inherited B G pick z hz fit room pack prof hp one pin sh whole key flag k g src.1 prior
  apply claim t donor
  · unfold selectedSourceArrives selectedSourceArgument
    rw [read]
    exact arrived
  · exact fun mem => encode t mem (origin mem)

theorem capturedOutsideBook (labels : Labels) (src : NodeOrder.Global (N:=net) oldBits)
    (i : Fin (((oldShape src.1).recipe hp).arity src.2)) (kw : ValueKey) (claim : selectedSourceKeyClaim B G pick z hz fit room pack prof hp one pin sh whole key flag k g labels src i kw)
    (e : Incident net src.1) (chunk : ℕ) (fits : (chunk+1)*p ≤ (net).width e.val)
    (read : ((oldShape src.1).recipe hp).operand src.2 i = .inl ⟨.inl e,chunk,fits⟩)
    (meet : addr (grp ((net).src e.val)) = addr (grp ((net).dst e.val))) (keyOf : Bool → ValueKey)
    (encode : ∀ (second : Bool) (t : Private ((destBits).recipe (addr (grp src.1))) p)
      (used : (((destShape).sites (addr (grp src.1))).recipe hp).Used t),
      let word : WireWord net p := ⟨e.val,⟨chunk,(Nat.le_div_iff_mul_le hp).mpr fits⟩⟩
      bookOrigin ⟨addr (grp src.1), bookWord (addr (grp src.1)) ⟨t,used⟩⟩ =
        (if second then .inl word else .inr (.inl word)) →
      labels (addr (grp src.1)) ⟨t,used⟩ = keyOf second) :
    kw = keyOf (decide (grp ((net).src e.val) ≠ grp ((net).dst e.val))) := by
  by_cases first : grp ((net).src e.val) = grp ((net).dst e.val)
  · obtain ⟨t, transferred, origin⟩ := selected_coalesced_first B G pick z hz fit room pack prof hp one pin sh whole
      key flag k g src.1 e chunk fits first
    rw [show decide (grp ((net).src e.val) ≠ grp ((net).dst e.val)) = false from by simp [first]]
    apply claim t _
    · unfold selectedSourceArrives selectedSourceArgument
      rw [read]
      exact transferred
    · exact fun used => encode false t used (origin used)
  · obtain ⟨t, transferred, origin⟩ := selected_coalesced_second B G pick z hz fit room pack prof hp one pin sh whole
      key flag k g src.1 e chunk fits first meet
    rw [show decide (grp ((net).src e.val) ≠ grp ((net).dst e.val)) = true from by simp [first]]
    apply claim t _
    · unfold selectedSourceArrives selectedSourceArgument
      rw [read]
      exact transferred
    · exact fun used => encode true t used (origin used)

section

local instance inheritedSourceMergedSites : Fintype (Merged W.graph pick (bestLayout (branchWidth G z prof)) pack) :=
  mergedFinite W.graph pick (bestLayout (branchWidth G z prof)) pack
open DescentCompiler DescentPackedOperand DescentCableDonorNames
variable {J U : Type} [Fintype J] [DecidableEq J] [Fintype U] [DecidableEq U]
  {price ε : ℝ} {stageK epoch D K : ℕ}
  (A : GroupStage W G price ε J U stageK) (native : W.graph.Edge ↪ ℕ) (sched : AtomSchedule)
  (ready : A.StateBounds sched epoch)
  (halo : Halo (↥(MarkedWorld.reclaimed (W.selected G pick z hz fit pack prof) key flag k g)) W.graph.Site D)
  (rawHere : ∀ e : (physical W.graph pick (branchWidth G z prof)).Edge,
    W.graph.src (DescentCableDonorNames.anchor pick e) ∈ halo.member
      (MarkedWorld.address (W.selected G pick z hz fit pack prof) key flag k g
        (newSite W.graph pick (bestLayout (branchWidth G z prof)) pack
          ((physical W.graph pick (branchWidth G z prof)).src e))))
  (oldHere : ∀ v : W.graph.Site, v ∈ halo.member
    (MarkedWorld.address (W.selected G pick z hz fit pack prof) key flag k g
      (newSite W.graph pick (bestLayout (branchWidth G z prof)) pack (.inl v))))
  (slot : ∀ v, DescentLocalPrivateNames.Slot ((sh.sites v).recipe hp) ↪ Fin K)
local notation "peerTy" => ∀ site : reclaimed, DescentPrivateRawLabels.LocalWire (W:=W) (G:=G) (p:=p) pick z prof (addr ∘ grp) site → ℕ
local notation "rawLabels" => DescentPrivateRawLabels.privateKey (W:=W) (G:=G) (p:=p) (K:=K) (I:=I) (Z:=Z)
  (T:=Merged W.graph pick (bestLayout (branchWidth G z prof)) pack) (C:=reclaimed) (b₁:=d) (b₂:=d) A native sched ready B pick z hz fit room prof hp sh.sites sh.edges pin whole grp addr x₁ x₂ ok₁ ok₂ halo rawHere oldHere slot

def selectedPhysicalBookKey (peer : peerTy) (site : reclaimed) :=
  (bookWord site).trans (rawLabels site (peer site))

local notation "regularLabels" => selectedPhysicalBookKey B G pick z hz fit room pack prof hp one pin sh whole key flag k g A native sched ready halo rawHere oldHere slot

def selectedInheritedKey (src : NodeOrder.Global (N:=net) oldBits) (prior : ((oldShape src.1).recipe hp).UsedWord) : DescentPackedOperand.Key :=
  let donor := DescentPrivateRawLabels.carried (c:=addr (grp src.1)) B pick z room prof hp sh.sites sh.edges pin whole
    grp addr halo oldHere slot ⟨⟨src.1,prior⟩,rfl⟩
  DescentPackedOperand.Key.carried donor.1.val donor.2.val

attribute [local irreducible] DescentPrivateRawLabels.privateKey DescentPrivateRawLabels.carried DescentLocalArchiveOrder.coalescedBookWord
theorem selectedBook_label_inherited (peer : peerTy) (src : NodeOrder.Global (N:=net) oldBits)
    (prior : ((oldShape src.1).recipe hp).UsedWord)
    (t : Private ((destBits).recipe (addr (grp src.1))) p) (mem : (((destShape).sites (addr (grp src.1))).recipe hp).Used t)
    (origin : bookOrigin ⟨addr (grp src.1), bookWord (addr (grp src.1)) ⟨t,mem⟩⟩ = .inr (.inr ⟨src.1,prior⟩)) :
    regularLabels peer (addr (grp src.1)) ⟨t,mem⟩ =
      selectedInheritedKey B G pick z hz fit room pack prof hp pin sh whole key flag k g halo oldHere slot src prior := by
  dsimp only [selectedPhysicalBookKey, Function.Embedding.trans_apply, selectedInheritedKey]
  let carriedSource : {w : OccupiedWord net oldBits oldShape hp // addr (grp w.1) = addr (grp src.1)} :=
    ⟨⟨src.1,prior⟩,rfl⟩
  have fromSource := DescentPrivateRawLabels.inherited_key (W:=W) (G:=G) (p:=p) (K:=K) (I:=I) (Z:=Z)
    (T:=Merged W.graph pick (bestLayout (branchWidth G z prof)) pack) (C:=reclaimed) (b₁:=d) (b₂:=d) (c:=addr (grp src.1))
    A native sched ready B pick z hz fit room prof hp sh.sites sh.edges
    pin whole grp addr x₁ x₂ ok₁ ok₂ halo rawHere oldHere slot carriedSource
    (peer (addr (grp src.1))) (bookWord (addr (grp src.1)) ⟨t,mem⟩)
  exact fromSource origin

theorem selectedBook_carried_key (peer : peerTy) (src : NodeOrder.Global (N:=net) oldBits)
    (i : Fin (((oldShape src.1).recipe hp).arity src.2)) (kw : DescentPackedOperand.Key)
    (claim : selectedSourceKeyClaim B G pick z hz fit room pack prof hp one pin sh whole key flag k g
      (fun site => (regularLabels peer site).toFun) src i kw)
    (prior : ((oldShape src.1).recipe hp).UsedWord)
    (read : ((oldShape src.1).recipe hp).operand src.2 i = .inr prior.val) :
    kw = selectedInheritedKey B G pick z hz fit room pack prof hp pin sh whole key flag k g halo oldHere slot src prior := by
  apply carriedOutsideBook B G pick z hz fit room pack prof hp one pin sh whole key flag k g
    (fun site => (regularLabels peer site).toFun) src i kw claim prior read _
  exact selectedBook_label_inherited B G pick z hz fit room pack prof hp one pin sh whole key flag k g
    A native sched ready halo rawHere oldHere slot peer src prior

theorem capturedLabelAtWire (peer : peerTy)
    (src : NodeOrder.Global (N:=net) oldBits)
    (i : Fin (((oldShape src.1).recipe hp).arity src.2)) (kw : DescentPackedOperand.Key)
    (e : Incident net src.1) (chunk : ℕ) (fits : (chunk+1)*p ≤ (net).width e.val)
    (read : ((oldShape src.1).recipe hp).operand src.2 i = .inl ⟨.inl e,chunk,fits⟩)
    (meet : addr (grp ((net).src e.val)) = addr (grp ((net).dst e.val))) :
    let home := e.property.elim (congrArg (addr ∘ grp)) (fun eqn => meet.trans (congrArg (addr ∘ grp) eqn))
    let w : DescentPrivateRawLabels.LocalWire (W:=W) (G:=G) (p:=p) pick z prof (addr ∘ grp) (addr (grp src.1)) :=
      ⟨⟨e.val,⟨chunk,(Nat.le_div_iff_mul_le hp).mpr fits⟩⟩,home⟩
    let field := fun (b : Bool) => (if b then DescentPackedOperand.Key.second else DescentPackedOperand.Key.first)
      (DescentPrivateRawLabels.root (W:=W) (G:=G) (p:=p) pick z prof (addr∘grp) halo rawHere w).val (peer _ w)
      (11*(DescentPrivateRawLabels.old A native sched ready pick z hz fit prof (addr∘grp) hp w).val +
        (DescentCableDonorNames.role e.val).val) chunk
    selectedSourceKeyClaim B G pick z hz fit room pack prof hp one pin sh whole key flag k g
      (fun v => (regularLabels peer v).toFun) src i kw →
      kw = field (decide (grp ((net).src e.val) ≠ grp ((net).dst e.val))) := by
  intro home w field claimed
  apply capturedOutsideBook B G pick z hz fit room pack prof hp one pin sh whole key flag k g
    (fun v => (regularLabels peer v).toFun) src i kw claimed e chunk fits read meet field
  intro second t used word origin
  dsimp only [selectedPhysicalBookKey, Function.Embedding.trans_apply]
  have fromSource := DescentPrivateRawLabels.capture_key (W:=W) (G:=G) (p:=p) (K:=K) (I:=I) (Z:=Z)
    (T:=Merged W.graph pick (bestLayout (branchWidth G z prof)) pack) (C:=reclaimed) (b₁:=d) (b₂:=d) (c:=addr (grp src.1))
    A native sched ready B pick z hz fit room prof hp sh.sites sh.edges pin whole grp addr x₁ x₂ ok₁ ok₂ halo rawHere oldHere slot w
    (peer (addr (grp src.1))) second (bookWord (addr (grp src.1)) ⟨t,used⟩)
  exact fromSource origin

end

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
local notation "sel" => scanWorld he T c
local notation "selectedShape" => sh.selected hp one pin G (r).pick uni pos (r).fit room (r).pack prof whole
local notation "cut" => (ticket.quantum.symm ▸ ticket.cuts)
local notation "after" => afterOrdinary hp one pin ticket arch sh unit
local notation "chart" => privateChart ticket arch hp one pin sh unit
local notation "addr" => MarkedWorld.address sel ((chart).key he T c) (chart).hub T.k (gainExponent 20 T.Δ)
local notation "C" => ↥(MarkedWorld.reclaimed sel ((chart).key he T c) (chart).hub T.k (gainExponent 20 T.Δ))
local notation "pre" => (selectedShape).coalesced ((chart).key he T c) (chart).hub T.k (gainExponent 20 T.Δ)
local notation "bk" => privateBooks ticket arch hp one pin sh unit
local notation "group" => GadgetNetwork.newSite W.graph (r).pick (bestLayout (branchWidth G uni prof)) (r).pack
local instance sourceOperandMergedFintype : Fintype (DescentSixParty.Merged W.graph (r).pick (bestLayout (branchWidth G uni prof)) (r).pack) :=
  DescentSixParty.mergedFinite W.graph (r).pick (bestLayout (branchWidth G uni prof)) (r).pack
local notation "loc" => addr ∘ group
local notation "x₁" => fun _ : (sel).graph.Site=>(0 : EuclideanSpace ℝ (Fin d))
local notation "x₂" => fun _ : C=>(0 : EuclideanSpace ℝ (Fin d))
local notation "ok₁" => fun x : (sel).graph.Site=> (by simp : ‖x₁ x‖≤1)
local notation "ok₂" => fun x : C=> (by simp : ‖x₂ x‖≤1)
local notation "M" => rawGraph he T c
local notation "base" => physicalBits G W.toWorld (r).pick uni room prof arch.bit.recipe
local notation "baseShape" => physicalShape W arch.bit G (r).pick uni room prof hp sh.sites sh.edges pin whole
local notation "selectedDesc" => arch.bit.selected G (r).pick uni pos (r).fit room (r).pack prof
local notation "quot" => (sel).graph
local notation "r₁" => (selectedDesc).recipe
local notation "q₂" => ((sel).coalesced ((chart).key he T c) (chart).hub T.k (gainExponent 20 T.Δ)).graph
local notation "r₂" => ((selectedDesc).coalesced ((chart).key he T c) (chart).hub T.k (gainExponent 20 T.Δ)).recipe
local notation "firstRead" => nextArg M group x₁ ok₁ base hp
local notation "secondRead" => fun v : (M).Site => nextArg quot addr x₂ ok₂ r₁ hp (group v)
local notation "next" => (ticket.advance arch).bit
local notation "names" => NodeOrder.physicalNames arch.bit G (r).pick uni room prof
def operandSource (x : NodeOrder.All next) : NodeOrder.Global (N:=M) base :=
  (names).symm (roots ticket arch x)
local notation "source" => operandSource ticket arch
local notation "values" => (Σ t,BlockRef p (boundaryWidth q₂ t)⊕Private (r₂ t) p)
local notation "printedNodes" => NodeOrder.coalescedNames selectedDesc ((chart).key he T c) (chart).hub T.k (gainExponent 20 T.Δ)
local notation "selectedNodes" => NodeOrder.selectedNames arch.bit G (r).pick uni pos (r).fit room (r).pack prof

private theorem operandSource_named (x : NodeOrder.All next) :
    (names) (source x) = selectedNodes (printedNodes ((bk).nodeAt hp x)) :=
  ((names).apply_symm_apply _).trans (private_roots ticket arch hp one pin sh unit x).symm

theorem source_node (x : NodeOrder.All next) :
    coalescedPhysicalOrigin arch.bit G (r).pick uni pos (r).fit room (r).pack prof
      ((chart).key he T c) (chart).hub T.k (gainExponent 20 T.Δ) ((bk).nodeAt hp x) = source x :=
  selected_coalesced_origin arch.bit G (r).pick uni pos (r).fit room (r).pack prof
    ((chart).key he T c) (chart).hub T.k (gainExponent 20 T.Δ) ((bk).nodeAt hp x) (source x)
    (operandSource_named ticket arch hp one pin sh unit x)

attribute [local irreducible] operandSource

theorem source_read (x : NodeOrder.All next) (j : Fin ((((after).sites x.1).recipe hp).arity x.2)) :
    selectedBookOperandReceipt arch.bit G (r).pick uni pos (r).fit room (r).pack prof
      hp one pin sh whole ((chart).key he T c) (chart).hub T.k (gainExponent 20 T.Δ)
      (bk) x j (source x) := by
  apply selectedBookOperandReceipt_of_names
  exact operandSource_named ticket arch hp one pin sh unit x

theorem source_public (x : NodeOrder.All next) (j : Fin ((((after).sites x.1).recipe hp).arity x.2))
    (word : BlockRef p (boundaryWidth (q₂) ((bk).home x.1)))
    (hit : (((pre).sites ((bk).home x.1)).recipe hp).operand (((bk).atSite x.1).node x.2)
      (j.cast (((bk).atSite x.1).length x.2))=.inl word) :
    (((after).sites x.1).recipe hp).operand x.2 j=.inl (((bk).atSite x.1).publicWord word) :=
  ((bk).atSite x.1).publicHit x.2 j word hit

def sourceIndex (x : NodeOrder.All next) (j : Fin ((((after).sites x.1).recipe hp).arity x.2)) :=
  (source_read ticket arch hp one pin sh unit x j).choose

theorem sourceIndex_val (x : NodeOrder.All next) (j : Fin ((((after).sites x.1).recipe hp).arity x.2)) :
    (sourceIndex ticket arch hp one pin sh unit x j).val=j.val :=
  (source_read ticket arch hp one pin sh unit x j).choose_spec.1

local notation "routedValue" => selectedSourceArgument arch.bit G (r).pick uni pos (r).fit room (r).pack prof hp
  pin sh whole ((chart).key he T c) (chart).hub T.k (gainExponent 20 T.Δ)
local notation "pubProof" => selectedBook_public_iff arch.bit G (r).pick uni pos (r).fit room (r).pack prof
  hp one pin sh whole ((chart).key he T c) (chart).hub T.k (gainExponent 20 T.Δ) (bk)

theorem public_source (x : NodeOrder.All next) (j : Fin ((((after).sites x.1).recipe hp).arity x.2))
    {b₀ : BlockRef p (boundaryWidth n.result.graph x.1)} (read : (((after).sites x.1).recipe hp).operand x.2 j = .inl b₀) :
    ∃ b, routedValue (source x) (sourceIndex ticket arch hp one pin sh unit x j) = .inl b :=
  (pubProof x j (source x) (source_read ticket arch hp one pin sh unit x j)).mp ⟨b₀, read⟩

theorem public_of_source (x : NodeOrder.All next) (j : Fin ((((after).sites x.1).recipe hp).arity x.2))
    {b₀ : BlockRef p (boundaryWidth q₂ (loc (source x).1))}
    (routed : routedValue (source x) (sourceIndex ticket arch hp one pin sh unit x j) = .inl b₀) :
    ∃ b, (((after).sites x.1).recipe hp).operand x.2 j = .inl b :=
  (pubProof x j (source x) (source_read ticket arch hp one pin sh unit x j)).mpr ⟨b₀, routed⟩

theorem original_pin (x : NodeOrder.All next) (j : Fin ((((after).sites x.1).recipe hp).arity x.2))
    (a : Attached M (source x).1) (k : ℕ) (fits : (k+1)*p ≤ bits a.val)
    (previous : ((baseShape (source x).1).recipe hp).operand (source x).2 (sourceIndex ticket arch hp one pin sh unit x j) =
      .inl ⟨.inr a,k,fits⟩) :
    ∃b,(((after).sites x.1).recipe hp).operand x.2 j = .inl b ∧ b.exteriorAt n.result.graph x.1 a.val k :=
  selectedBook_original_pin arch.bit G (r).pick uni pos (r).fit room (r).pack prof
    hp one pin sh whole ((chart).key he T c) (chart).hub T.k (gainExponent 20 T.Δ) (bk)
    x j (source x) (source_read ticket arch hp one pin sh unit x j) a k fits previous

private abbrev sourcePeer :=
  ∀ h : C, DescentPrivateRawLabels.LocalWire (W:=W) (G:=G) (p:=p) (r).pick uni prof loc h → ℕ

variable {K:ℕ} (slots:∀v,DescentLocalPrivateNames.Slot ((sh.sites v).recipe hp)↪Fin K)
    (peer : sourcePeer ticket arch hp one pin sh unit)

theorem private_tag (v:n.result.graph.Site) (u:(((after).sites v).recipe hp).UsedWord) :
    ((reachedPrivateKey ticket arch hp one pin sh unit slots peer v u).fields 0)<3 :=
  DescentPrivateRawLabels.privateKey_tag cap.placement (cap.order.trans Fin.valEmbedding) S cap.valid
    arch.bit (r).pick uni pos (r).fit room prof hp sh.sites sh.edges pin whole group addr x₁ x₂ ok₁ ok₂
    (chartHalo (cap:=cap) (c:=c) chart) (chartHalo_members ticket chart).1 (chartHalo_members ticket chart).2.1
    slots ((bk).home v) (peer ((bk).home v))
    (physicalBookWord ticket arch hp one pin sh unit ((bk).home v) (((bk).atSite v).word u))

local notation "halo" => chartHalo (cap:=cap) (c:=c) chart
local notation "reaches" => chartHalo_members ticket chart
local notation "codeAt" => bookWordKey ticket arch hp one pin sh unit slots

local notation "labels" => fun v : C => (codeAt v (peer v)).toFun
local notation "bookSample" => selectedBookSample arch.bit G (r).pick uni pos (r).fit room (r).pack prof
  hp one pin sh whole ((chart).key he T c) (chart).hub T.k (gainExponent 20 T.Δ)

def selectedPrivate := bookSample labels

local notation "sourceSample" => selectedSourceSample (ValueKey:=Key) arch.bit G (r).pick uni pos (r).fit room (r).pack prof
  hp one pin sh whole ((chart).key he T c) (chart).hub T.k (gainExponent 20 T.Δ)
local notation "sourceEncoding" => selectedSourceEncoding (ValueKey:=Key) arch.bit G (r).pick uni pos (r).fit room (r).pack prof
  hp one pin sh whole ((chart).key he T c) (chart).hub T.k (gainExponent 20 T.Δ)
local notation "atKey" => reachedPrivateKey ticket arch hp one pin sh unit slots peer
local notation "wordLabels" => fun v : C => (codeAt v (peer v)).toFun

private theorem operandBookKey (v : n.result.graph.Site) (h : (((after).sites v).recipe hp).UsedWord) :
    codeAt ((bk).home v) (peer ((bk).home v)) (((bk).atSite v).word h) = atKey v h := rfl

theorem source_private (x : NodeOrder.All next) (j : Fin ((((after).sites x.1).recipe hp).arity x.2))
    (h : (((after).sites x.1).recipe hp).UsedWord)
    (hit : (((after).sites x.1).recipe hp).operand x.2 j = .inr h.val) :
    sourceSample wordLabels (source x) (sourceIndex ticket arch hp one pin sh unit x j) =
      some (atKey x.1 h) :=
  (selectedBook_private arch.bit G (r).pick uni pos (r).fit room (r).pack prof hp one pin sh whole
    ((chart).key he T c) (chart).hub T.k (gainExponent 20 T.Δ) (bk) x j (source x)
    (source_read ticket arch hp one pin sh unit x j) wordLabels h hit).trans
    (congrArg some (operandBookKey ticket arch hp one pin sh unit slots peer x.1 h))

local notation "oldHidden" => fun v : (M).Site => ((baseShape v).recipe hp).UsedWord
local notation "oldCode" => DescentPrivateRawLabels.carried (W:=W) (G:=G) (p:=p) arch.bit (r).pick uni room prof hp sh.sites
  sh.edges pin whole group addr halo (reaches).2.1 slots
local notation "keyAt" => reachedPrivateKey ticket arch hp one pin sh unit slots peer

theorem private_at_key (x:NodeOrder.All next) (j:Fin ((((after).sites x.1).recipe hp).arity x.2))
    (h:(((after).sites x.1).recipe hp).UsedWord) (hit:(((after).sites x.1).recipe hp).operand x.2 j=.inr h.val)
    (t:Private (r₂ (loc (source x).1)) p) (sig:Key)
    (arrived : routedValue (source x) (sourceIndex ticket arch hp one pin sh unit x j) = .inr t)
    (encoded : sourceEncoding wordLabels (source x).1 t sig) :
    keyAt x.1 h=sig :=
  (operandBookKey ticket arch hp one pin sh unit slots peer x.1 h).symm.trans
    (selectedBook_private_key arch.bit G (r).pick uni pos (r).fit room (r).pack prof hp one pin sh whole
      ((chart).key he T c) (chart).hub T.k (gainExponent 20 T.Δ) (bk) x j (source x)
      (source_read ticket arch hp one pin sh unit x j) wordLabels h hit t sig arrived encoded)

local notation "sourceClaim" => selectedSourceKeyClaim (ValueKey:=Key) arch.bit G (r).pick uni pos (r).fit room (r).pack prof hp one pin sh whole
  ((chart).key he T c) (chart).hub T.k (gainExponent 20 T.Δ)
local notation "keyClaims" => fun (x : NodeOrder.All next) (j : Fin ((((after).sites x.1).recipe hp).arity x.2))
  (h : (((after).sites x.1).recipe hp).UsedWord) => sourceClaim wordLabels (source x) (sourceIndex ticket arch hp one pin sh unit x j) (keyAt x.1 h)

theorem reachedSourceClaim (x:NodeOrder.All next) (j:Fin ((((after).sites x.1).recipe hp).arity x.2))
    (h:(((after).sites x.1).recipe hp).UsedWord)
    (hit:(((after).sites x.1).recipe hp).operand x.2 j=.inr h.val) :
    keyClaims x j h :=
  private_at_key ticket arch hp one pin sh unit slots peer x j h hit

local notation "exactInherited" => selectedInheritedKey arch.bit G (r).pick uni pos (r).fit room (r).pack prof hp pin sh whole
  ((chart).key he T c) (chart).hub T.k (gainExponent 20 T.Δ) halo (reaches).2.1 slots

attribute [local irreducible] DescentPrivateRawLabels.privateKey DescentPrivateRawLabels.carried coalescedBookWord

theorem carried_private (x:NodeOrder.All next) (j:Fin ((((after).sites x.1).recipe hp).arity x.2))
    (h:(((after).sites x.1).recipe hp).UsedWord) (hit:(((after).sites x.1).recipe hp).operand x.2 j=.inr h.val)
    (prior:oldHidden (source x).1)
    (earlier:((baseShape (source x).1).recipe hp).operand (source x).2
      (sourceIndex ticket arch hp one pin sh unit x j)=.inr prior.val) :
    keyAt x.1 h = exactInherited (source x) prior :=
  selectedBook_carried_key arch.bit G (r).pick uni pos (r).fit room (r).pack prof hp one pin sh whole
    ((chart).key he T c) (chart).hub T.k (gainExponent 20 T.Δ) cap.placement (cap.order.trans Fin.valEmbedding) S cap.valid
    halo (reaches).1 (reaches).2.1 slots peer (source x) (sourceIndex ticket arch hp one pin sh unit x j) (keyAt x.1 h)
    (reachedSourceClaim ticket arch hp one pin sh unit slots peer x j h hit) prior earlier

set_option maxHeartbeats 850000 in
theorem captured_private (x:NodeOrder.All next) (j:Fin ((((after).sites x.1).recipe hp).arity x.2))
    (h:(((after).sites x.1).recipe hp).UsedWord) (hit:(((after).sites x.1).recipe hp).operand x.2 j=.inr h.val)
    (e:Incident (M) (source x).1) (k:ℕ) (full:(k+1)*p≤(M).width e.val)
    (earlier:((baseShape (source x).1).recipe hp).operand (source x).2
      (sourceIndex ticket arch hp one pin sh unit x j)=.inl ⟨.inl e,k,full⟩)
    (meet:loc ((M).src e.val)=loc ((M).dst e.val)) :
    let who:=e.property.elim (congrArg (loc)) (fun t=>meet.trans (congrArg (loc) t))
    let w:DescentPrivateRawLabels.LocalWire (W:=W) (G:=G) (p:=p) (r).pick uni prof loc (loc (source x).1):=
      ⟨⟨e.val,⟨k,(Nat.le_div_iff_mul_le hp).mpr full⟩⟩,who⟩
    let nextCut:=decide (group ((M).src e.val)≠group ((M).dst e.val))
    keyAt x.1 h=(if nextCut then Key.second else Key.first)
      (DescentPrivateRawLabels.root (W:=W) (G:=G) (p:=p) (r).pick uni prof loc halo (reaches).1 w).val (peer _ w)
      (11*(DescentPrivateRawLabels.old cap.placement (cap.order.trans Fin.valEmbedding) S cap.valid
        (r).pick uni pos (r).fit prof loc hp w).val+(DescentCableDonorNames.role e.val).val) k :=by
  exact capturedLabelAtWire arch.bit G (r).pick uni pos (r).fit room (r).pack prof
    hp one pin sh whole ((chart).key he T c) (chart).hub T.k (gainExponent 20 T.Δ)
    cap.placement (cap.order.trans Fin.valEmbedding) S cap.valid halo (reaches).1 (reaches).2.1 slots peer
    (source x) (sourceIndex ticket arch hp one pin sh unit x j) (keyAt x.1 h) e k full earlier meet (reachedSourceClaim ticket arch hp one pin sh unit slots peer x j h hit)

end
end Hierarchy.DescentLocalArchiveOrder

end OAI
