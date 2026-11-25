import OAI.Hierarchy.TraceReceiverSeedDimensions
import OAI.Hierarchy.PhysicalTraceContraction
import OAI.ThreeFlat.Diagonal.TraceCursorWordLayout
import OAI.ThreeFlat.Diagonal.TraceBitSourceOwner
import OAI.ThreeFlat.Diagonal.TraceBucketInitial

namespace OAI
/-! # The owned input words and actual seed trees for the complete native verifier

The zero cursor uses all original pins in its clipped input bucket. All other
cursors use only relay gates. The last bucket can contain a single input bit.
-/

noncomputable section
open private mapSource from OAI.ThreeFlat.BitNetwork.PinMap
open private firstPin from OAI.ThreeFlat.Diagonal.LaneInitialNetwork
namespace Hierarchy.TraceReceiverSeedWords
open ThreeFlat Diagonal Diagonal.LaneCursor Diagonal.LaneCursor.RowLayout
open Diagonal.HistoryContraction Diagonal.TraceSourceOwner TraceDistribution
open Computability.VPVNP Computability.VPVNP.BurstRAM Computability.VPVNP.BurstRAM.PrivateRAM Computability.VPVNP.RAMMemory
open scoped Classical

variable {F : Type} [Field F] [Fintype F] {k low W pc regs words S base fuel : ℕ}
    (M : Machine W pc regs words) (t : NativeTrace.Fits M S base ((k+1)+low) fuel)
    (hF : Fintype.card F ≤ 2^W) (st : Word W)
set_option quotPrecheck false

local notation "I" => bitIndex hF t.width t.labels base st t.header t.time regs words t.grid
local notation "P" => layout M t hF st
local notation "depth" => (k+1)+low
local notation "off" => 1+(depth+depth)
local notation "slots" => (TraceStaticRow.gateTable hF t.width t.labels base fuel st regs words depth).cells
local notation "V" => PairedCursor.Site (k+1)

/-- Native `bitIndex.ext` is the original ordered slice, including its clipped tail. -/
def source (v : V) (j : Fin (width M t hF st v)) : Fin S :=
  if zero : v.1=0 then ((I v.2).ext (Fin.cast (by simp [width,zero]) j)).val
  else Fin.elim0 (j.cast (by simp [width,zero]))

theorem source_owner (v : V) (j : Fin (width M t hF st v)) :
    PairedCursor.owner P (source M t hF st v j) = v := by
  by_cases zero : v.1=0
  · let z := ((I v.2).ext (Fin.cast (by simp [width,zero]) j))
    have e : source M t hF st v j=z.val := by simp [source,zero,z]
    rw [e]
    exact Prod.ext zero.symm z.property
  · exact Fin.elim0 (j.cast (by simp [width,zero]))

theorem source_val (v : V) (j : Fin (width M t hF st v)) :
    (source M t hF st v j).val = (finFunctionFinEquiv v.2).val*pinSpan 1 low+j.val := by
  by_cases zero : v.1=0
  · simp only [source,dite_eq_left zero]
    rfl
  · exact Fin.elim0 (j.cast (by simp [width,zero]))

/-- Each original bit occurs in exactly one zero-cursor bucket. -/
theorem source_bijective : Function.Bijective (fun z : Σ v : V, Fin (width M t hF st v) =>
    source M t hF st z.1 z.2) := by
  constructor
  · rintro ⟨v,i⟩ ⟨u,j⟩ same
    have sites := congrArg (PairedCursor.owner P) same
    change PairedCursor.owner P (source M t hF st v i) =
      PairedCursor.owner P (source M t hF st u j) at sites
    rw [source_owner,source_owner] at sites
    subst u
    apply congrArg (fun a : Fin (width M t hF st v) =>
      (⟨v, a⟩ : Σ z : V, Fin (width M t hF st z)))
    apply Fin.ext
    have eq := congrArg Fin.val same
    change (source M t hF st v i).val=(source M t hF st v j).val at eq
    simpa only [source_val,Nat.add_right_inj] using eq
  · intro j
    let lane := (splitRow _ _ ((P).pinRow j)).1
    let i := (I lane).ext.symm ⟨j,rfl⟩
    refine ⟨⟨(0,lane),i.cast (by simp [width])⟩,?_⟩
    simp [source,i]

variable (B : PhysicalStage.Block F) (hk : 2≤k+1)
local notation "A" => B.cursorState hk low off slots
local notation "ext" => width M t hF st
local notation "src" => source M t hF st

def wordsLayout : WordLayout (A).shape.graph (A).width (Fin S → Bool) :=
  B.cursorLayout hk low off slots ext (fun v pin j => pin (src v j))

local notation "L" => wordsLayout M t hF st B hk

theorem seed_read (v : V) (pin : Fin S → Bool) (j : Fin (ext v)) :
    (L).pin v pin j=pin (src v j) := rfl

theorem portWidth (v : V) : BucketIndex.ports B.cursorCopies (I v.2).t=(L).ports.halfBits v :=
  B.cursor_half_width hk low off slots ext (fun z (x : Fin S → Bool) j => x (src z j)) v

private def halfWire (v : V) (j : Fin (BucketIndex.ports B.cursorCopies (I v.2).t)) :
    Fin ((L).ports.form.width v) := Fin.natAdd (ext v) (j.cast (portWidth M t hF st B hk v))

/-- Actual traced table rows at cursor zero, and the actual relay network at
all later cursor coordinates. Readdressing changes no gate or hidden bit. -/
def forest : Forest F (L).ports.form := fun v => .atom <|
  let I' := I v.2
  let hw := halfWire M t hF st B hk v
  if first : v.1=0 then
    let A' := bitAddress hF t.width t.labels base st t.header t.time regs words t.grid v.2 I'
    let sourcePin (j : Fin I'.x) : Fin ((L).ports.form.width v) :=
      (j.cast (by change I'.x=ext v;simp [I',width,first])).castAdd _
    (I'.firstNetwork (r:=B.cursorCopies) A' v.1).restrictPins (some ∘ Fin.append sourcePin hw)
  else (RelayNetwork.network (r:=B.cursorCopies) I'.tag (P).mask v.1).restrictPins (some ∘ hw)

omit [Field F] [Fintype F] in
private theorem same_network {p q : ℕ} (N : BitNetwork F p) (wire : Fin p → Fin q)
    (arity : p=q) (same : ∀ i, (wire i).val=i.val) : HEq (N.restrictPins (some ∘ wire)) N := by
  subst q
  have ident : wire=id := funext fun i=>Fin.ext (same i)
  rw [ident]
  apply heq_of_eq
  cases N with
  | mk hidden cells rows tables =>
    change BitNetwork.mk hidden cells (fun i a=>_) tables=BitNetwork.mk hidden cells rows tables
    congr 1
    funext i a
    change mapSource (some ∘ id) (rows i a)=rows i a
    cases rows i a <;> rfl

/-- Compiling the zero cursor emits exactly the original native four-word row
stream. The port order and every absolute encoded pin address are preserved. -/
theorem forest_first (v : V) (first : v.1=0) :
    let I' := I v.2
    let addr := bitAddress hF t.width t.labels base st t.header t.time regs words t.grid v.2 I'
    HEq (forest M t hF st B hk v).compile (I'.firstNetwork (r:=B.cursorCopies) addr v.1) := by
  dsimp only
  simp only [forest,dite_eq_left first,Tree.compile]
  apply same_network
  · change (I v.2).x+_ = ext v+(L).ports.halfBits v
    rw [portWidth M t hF st B hk v]
    simp [width,first]
  · intro j
    refine Fin.addCases (fun a=>?_) (fun a=>?_) j
    · erw [Fin.append_left];rfl
    · erw [Fin.append_right]
      change ext v+_=(I v.2).x+_
      simp [width,first]

/-- Every positive cursor uses the physical relay gate rows in their original order. -/
theorem forest_later (v : V) (later : v.1≠0) :
    HEq (forest M t hF st B hk v).compile
      (RelayNetwork.network (F:=F) (r:=B.cursorCopies) (I v.2).tag (P).mask v.1) := by
  simp only [forest,dite_eq_right later,Tree.compile]
  apply same_network
  · change BucketIndex.ports B.cursorCopies (I v.2).t = ext v+(L).ports.halfBits v
    rw [portWidth M t hF st B hk v]
    simp [width,later]
  · intro j
    simp [halfWire,width,later]

/-- A numerical row address in the actual compiled tree. -/
def metadataAt {n : ℕ} (tag : ((Fin 3→Bool)→F)→ℕ) (N : BitNetwork F n) (row : ℕ) (col : Fin 4) : ℕ :=
  if h : row < N.cells then RAM.HistoryCompiledRows.metadata tag N ⟨row,h⟩ col else 0

omit [Field F] [Fintype F] in
theorem metadataAt_cell {n : ℕ} (tag : ((Fin 3→Bool)→F)→ℕ) (N : BitNetwork F n)
    (i : Fin N.cells) (col : Fin 4) : metadataAt tag N i.val col = RAM.HistoryCompiledRows.metadata tag N i col :=
  dite_eq_left i.isLt

omit [Field F] [Fintype F] in
private theorem transfer_row {n m : ℕ} {N : BitNetwork F n} {T : BitNetwork F m}
    (ports : n=m) (eqv : HEq N T) (tag : ((Fin 3→Bool)→F)→ℕ) (row : ℕ) (col : Fin 4) :
    metadataAt tag N row col = metadataAt tag T row col := by
  subst m
  cases eq_of_heq eqv
  rfl

/-- The numerical four-word row returned by the physical zero-cursor leaf is
exactly the corresponding row of the tree that enters repeated assembly. -/
theorem forest_first_row (v : V) (first : v.1=0) (tag : ((Fin 3→Bool)→F)→ℕ) (row : ℕ) (col : Fin 4) :
    let addr := bitAddress hF t.width t.labels base st t.header t.time regs words t.grid v.2 (I v.2)
    metadataAt tag (forest M t hF st B hk v).compile row col =
      metadataAt tag ((I v.2).firstNetwork (r:=B.cursorCopies) addr v.1) row col := by
  dsimp only
  apply transfer_row _ (forest_first M t hF st B hk v first)
  change ext v+(L).ports.halfBits v = (I v.2).x + BucketIndex.ports B.cursorCopies (I v.2).t
  rw [portWidth M t hF st B hk v]
  simp [width,first]

/-- A positive-cursor leaf returns the rows of the selected relay tree using
its true arity, register number and finite-field table. -/
theorem forest_later_row (v : V) (later : v.1≠0) (tag : ((Fin 3→Bool)→F)→ℕ) (row : ℕ) (col : Fin 4) :
    metadataAt tag (forest M t hF st B hk v).compile row col =
      metadataAt tag (RelayNetwork.network (F:=F) (r:=B.cursorCopies) (I v.2).tag (P).mask v.1) row col := by
  apply transfer_row _ (forest_later M t hF st B hk v later)
  change ext v+(L).ports.halfBits v = BucketIndex.ports B.cursorCopies (I v.2).t
  rw [portWidth M t hF st B hk v]
  simp [width,later]

omit [Fintype F] in
private theorem first_rewire {p n k low offsets nslots r H : ℕ} {U : BitNetwork F p}
    {T : RowLayout U (k+1) low offsets nslots} {lane : Lane (k+1)} (U₀ : BucketIndex T lane)
    (address : BitNetwork.Rectangular.Address U₀.h H) (i : Fin (k+1)) (first : i=0)
    (pin : Fin p → Bool) (o a : BucketIndex.PortData r offsets low nslots)
    (get : Fin n → Bool) (extmap : Fin U₀.x → Fin n) (half : Fin (BucketIndex.ports r U₀.t) → Fin n)
    (hs : ∀ j,get (extmap j)=pin (U₀.ext j).val) (hh : ∀ j,get (half j)=RelayNetwork.pins U₀.tag o a j) :
    ((U₀.firstNetwork (r:=r) address i).restrictPins (some ∘ Fin.append extmap half)).eval get=
      portTensor T.mask (T.localTensor pin) i lane o a := by
  rw [BitNetwork.restrictPins_eval,BucketIndex.firstNetwork_eval]
  have ev:=U₀.initial_eval i pin o a
  rw [decide_eq_true first] at ev
  have eq : (fun j=>(((some ∘ Fin.append extmap half) j).map get).getD false)=
      U₀.initialInputs pin o a true := by
    simp only [BucketIndex.initialInputs,firstPin]
    funext j
    refine Fin.addCases (fun z=>?_) (fun z=>?_) j
    · simpa only [Function.comp_apply,Option.map_some,Option.getD_some,Fin.append_left] using hs z
    · simpa only [Function.comp_apply,Option.map_some,Option.getD_some,Fin.append_right] using hh z
  exact (congrArg (U₀.initialNetwork (r:=r) true i).eval eq).trans ev

omit [Fintype F] in
private theorem later_rewire {p n k low offsets nslots r : ℕ} {U : BitNetwork F p}
    {T : RowLayout U (k+1) low offsets nslots} {lane : Lane (k+1)} (U₀ : BucketIndex T lane)
    (i : Fin (k+1)) (later : i≠0)
    (pin : Fin p → Bool) (o a : BucketIndex.PortData r offsets low nslots)
    (get : Fin n → Bool) (half : Fin (BucketIndex.ports r U₀.t) → Fin n)
    (hh : ∀ j,get (half j)=RelayNetwork.pins U₀.tag o a j) :
    ((RelayNetwork.network U₀.tag T.mask i).restrictPins (some ∘ half)).eval get=
      portTensor T.mask (T.localTensor pin) i lane o a := by
  rw [BitNetwork.restrictPins_eval]
  have ev:=U₀.initial_eval i pin o a
  rw [decide_eq_false later] at ev
  exact (congrArg (RelayNetwork.network (r:=r) U₀.tag T.mask i).eval (funext hh)).trans ev

set_option maxHeartbeats 1600000 in
/-- The exposed value of each seed tree is exactly the repeated compressor's
initial physical factor on every original input and boundary assignment. -/
theorem forest_values (pin : Fin S → Bool) :
    (L).ports.form.values (forest M t hF st B hk) pin = Physical.seed B hk P pin := by
  funext v x
  let I' := I v.2
  let out := B.cursorOut hk low off slots v.1 v.2 x
  let inc := B.cursorIn hk low off slots v.1 v.2 x
  have encoded := B.cursor_encode hk low off slots ext (fun z (a : Fin S → Bool) j => a (src z j)) v x
  have half (j : Fin (BucketIndex.ports B.cursorCopies I'.t)) :
      (L).ports.form.read v pin x (halfWire M t hF st B hk v j)=RelayNetwork.pins I'.tag out inc j := by
    exact (Fin.append_right ..).trans (congrFun encoded j)
  change ((forest M t hF st B hk v).compile.eval ((L).ports.form.read v pin x)) =
    portTensor (P).mask ((P).localTensor pin) v.1 v.2 out inc
  by_cases first : v.1=0
  · simp only [forest,dite_eq_left first,Tree.compile]
    refine first_rewire I' _ v.1 first pin out inc _ _ _ ?_ half
    intro z
    apply (Fin.append_left _ _ _).trans
    change pin (src v (z.cast _))=pin (I'.ext z).val
    simp only [source,dite_eq_left first]
    apply congrArg (fun u : Fin I'.x=>pin (I'.ext u).val)
    exact Fin.ext rfl
  · simp only [forest,dite_eq_right first,Tree.compile]
    exact later_rewire I' v.1 first pin out inc _ _ half


end Hierarchy.TraceReceiverSeedWords

end
end OAI
