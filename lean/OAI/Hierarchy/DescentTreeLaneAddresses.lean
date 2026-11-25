import OAI.Hierarchy.DescentTreeLaneProgram
import OAI.Hierarchy.DescentOrderedOffsetTable

namespace OAI
/-! # Physical addresses of the two operands of an ordered fallback tree -/

namespace Hierarchy.DescentTreeLaneProgram
open Computability.BorderVNP.Crossing DescentKernelHistory DescentRouterSlots DescentContactTree DescentResetGates
open DescentOrderedReset DescentOrderedWords DescentTreeGateRefs
open scoped BigOperators Classical
noncomputable section

/-- Earlier live items in the actual cable's chronological key order, followed by
the first bit of the requested batch of the current item. -/
def batchStart {A : Type*} [Fintype A] {n : ℕ} (ids : A ↪ Fin n)
    (i : A) (m p : ℕ) (batch : Fin m) : ℕ :=
  (before ids i).card * (m*p) + batch.val*p

/-- The same ordinal computed from the physical list of live IDs.  The scan
visits each list cell exactly once, including IDs after the requested one. -/
theorem batchStart_scan {A : Type*} [Fintype A] {n : ℕ} (ids : A ↪ Fin n)
    (i : A) (m p : ℕ) (batch : Fin m) (directory : List A)
    (distinct : directory.Nodup) (all : ∀ a, a ∈ directory) :
    let read := scan (fun a => (ids a).val) (fun _ => m*p) (ids i).val directory
    (read.1 + batch.val*p, read.2) = (batchStart ids i m p batch, directory.length) := by
  rw [scan_offset ids (fun _ => m*p) directory distinct all i]
  simp [batchStart,offset]

/-- Compute the starts of every item in every fiber simultaneously. The stored
offset is independent of the batch, so each lane adds just its within-item position. -/
theorem shared_starts {A C : Type*} [Fintype A] [DecidableEq C] {n : ℕ}
    (key : A ↪ Fin n) (tag : A → C) (m p : ℕ) (directory : List A)
    (sorted : directory.Pairwise (fun x y => key x < key y)) (distinct : directory.Nodup)
    (whole : ∀ i, i ∈ directory) :
    let rows := makeOffsets tag (fun _ => m*p) (fun _ => 0) directory
    rows.2 = directory.length ∧ ∀ i, ∃ start, (i,start) ∈ rows.1 ∧ ∀ b : Fin m,
      start + b.val*p = batchStart ((Function.Embedding.subtype (fun j => tag j = tag i)).trans key)
        ⟨i,rfl⟩ m p b := by
  refine ⟨visits _ _ _ _,fun i => ?_⟩
  refine ⟨_,realised tag (fun _ => m*p) key directory sorted distinct whole i,fun b => ?_⟩
  rw [←fibre_offset tag (fun _ => m*p) key i]
  simp [batchStart,offset]

private theorem bitIndex_start {A : Type*} [Fintype A] {n : ℕ} (ids : A ↪ Fin n)
    (i : A) (m p : ℕ) (hp : 0<p) (b : Fin m) :
    (bitIndex ids (fun _ => m*p) ⟨i,finProdFinEquiv (b,⟨0,hp⟩)⟩).val =
      batchStart ids i m p b := by
  change offset ids (fun _ => m*p) i + (0+p*b.val) = _
  simp [offset,batchStart,Nat.mul_comm]

variable {I C R W : Type} [Fintype I] [Fintype C] [Fintype R] [Fintype W]
variable (D : ℕ) (contact : I→C) (input : Bool→I→R) (site : Bool→R→W) (owner : Bool→C→W)
variable (align : ∀s i,site s (input s i)=owner s (contact i)) (m p : ℕ) (hp : 0<p)
variable (s : Bool) (w : W) {depth n : ℕ} (book : LinkId owner s w ↪ Node depth) (key : I↪Fin n)
local notation "wt" => fun _ : I=>m*p
local notation "B" => DescentRouterBank.network D contact input site owner wt
local notation "lp" => link contact owner s w
local notation "N" => DescentFixedExceptionalRouter.device D contact input site owner wt s w book
local notation "code" => DescentFixedNamedContact.code book lp
local notation "ids" => itemKey key contact owner s w
local notation "operations" => program D contact input site owner align m p hp s w book key

/-- Drop the local attachment proofs, preserving the actual edge or slot, bit offset and stride. -/
def physicalFields {q : (N).Site} (l : DescentLaneGates.Lane p (boundaryWidth N q)) :
    ((N).Edge ⊕ DescentNetworkSubstitution.Slot B (s,w)) × ℕ × ℕ :=
  (Sum.map Subtype.val Subtype.val l.port,l.start,l.stride)

local notation "fields" => physicalFields D contact input site owner m p s w book

private def referenceFields {q : (N).Site} (ref : BitRef (boundaryWidth N q)) :
    ((N).Edge ⊕ DescentNetworkSubstitution.Slot B (s,w)) × ℕ × ℕ :=
  (Sum.map Subtype.val Subtype.val ref.1,ref.2.val,1)

local notation "refFields" => referenceFields D contact input site owner m p s w book

open private DescentTreeLaneProgram.packets DescentTreeLaneProgram.segment
  from OAI.Hierarchy.DescentTreeLaneProgram
open private DescentTreeGateRefs.childBit from OAI.Hierarchy.DescentTreeGateRefs

omit [Fintype R] in
private theorem first_fields (Y : ℕ) (i : Item contact owner s w) (b : Fin m) (k : Fin (depth+1)) :
    fields (((operations Y (⟨k, prefixAt code k.val i⟩ : Physical.Site depth)).op (⟨i,rfl⟩,b)).arg (0 : Fin 2)) =
    let ref := previous D contact input site owner wt align s w book key i (finProdFinEquiv (b,⟨0,hp⟩)) k
    refFields ref := by
  rfl

omit [Fintype R] in
private theorem last_fields (Y : ℕ) (i : Item contact owner s w) (b : Fin m) (k : Fin (depth+1)) :
    fields (((operations Y (⟨k, prefixAt code k.val i⟩ : Physical.Site depth)).op (⟨i,rfl⟩,b)).arg (1 : Fin 2)) =
    let ref := following D contact input site owner wt s w book key i (finProdFinEquiv (b,⟨0,hp⟩)) k
    refFields ref := by
  rfl

omit [Fintype R] in
/-- At the root, the first operand reads the installed input slot.  At positive
depth it reads the incoming edge indexed by the actual path prefix of the item. -/
theorem previous_fields (Y : ℕ) (i : Item contact owner s w) (b : Fin m) (k : Fin (depth+1)) :
    fields (((operations Y (⟨k, prefixAt code k.val i⟩ : Physical.Site depth)).op (⟨i,rfl⟩,b)).arg (0 : Fin 2)) =
    Fin.cases
      (.inr (rootSlot D contact input site owner wt s w (root contact input site owner s w align i)),
       batchStart (fibreKey key (input s) (input s i.val)) ⟨i.val,rfl⟩ m p b,1)
      (fun t => (.inl ⟨t,prefixAt code (t.val+1) i⟩,
        batchStart (Contact.cellKey ids code (t.val+1) (prefixAt code (t.val+1) i)) ⟨i,rfl⟩ m p b,1)) k := by
  rw [first_fields]
  refine Fin.cases ?_ (fun t => ?_) k <;>
    simp only [previous,Fin.cases_zero,Fin.cases_succ] <;>
    simp only [referenceFields,sourceAt,DescentTreeGateRefs.childBit,Sum.map_inr,Sum.map_inl,
      DescentRouterSlots.amount] <;>
    rw [← bitIndex_start _ _ m p hp b]

omit [Fintype R] in
/-- Before the last level the second operand reads the actual outgoing child
edge.  At the leaf it reads the contact slot at the chronological contact-fiber address. -/
theorem following_fields (Y : ℕ) (i : Item contact owner s w) (b : Fin m) (k : Fin (depth+1)) :
    fields (((operations Y (⟨k, prefixAt code k.val i⟩ : Physical.Site depth)).op (⟨i,rfl⟩,b)).arg (1 : Fin 2)) =
    Fin.lastCases
      (.inr (linkSlot D contact input site owner wt s w (lp i)),
       batchStart (fibreKey key contact (contact i.val)) ⟨i.val,rfl⟩ m p b,1)
      (fun t => (.inl ⟨t,prefixAt code (t.val+1) i⟩,
        batchStart (Contact.cellKey ids code (t.val+1) (prefixAt code (t.val+1) i)) ⟨i,rfl⟩ m p b,1)) k := by
  rw [last_fields]
  refine Fin.lastCases ?_ (fun t => ?_) k <;>
    simp only [following,Fin.lastCases_last,Fin.lastCases_castSucc] <;>
    simp only [referenceFields,linkAt,DescentTreeGateRefs.childBit,Sum.map_inr,
      Sum.map_inl,DescentRouterSlots.amount] <;>
    rw [← bitIndex_start _ _ m p hp b]; rfl

end
end Hierarchy.DescentTreeLaneProgram

end OAI
