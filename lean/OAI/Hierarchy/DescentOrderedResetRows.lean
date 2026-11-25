import OAI.Hierarchy.DescentOrderedWords
import OAI.Hierarchy.DescentRouterSlots
import OAI.Hierarchy.DescentWholeGrain
import OAI.Hierarchy.DescentCableUnbundling

namespace OAI
/-! # Chronological cable units and their order in actual reset fibers -/

namespace Hierarchy.DescentOrderedReset
open DescentOrderedWords DescentRouterSlots DescentNamedContact DescentSixParty
open Computability.BorderVNP.Crossing
open scoped Classical BigOperators
noncomputable section
variable {I C R W : Type} [Fintype I] [Fintype C] [Fintype R] [Fintype W] {M : ℕ}

/-- Actual grain ordinal is the prefix of earlier whole wires followed by
the within-wire grain ordinal. This works on sparse installed wire IDs. -/
def grains {F P : Type} [Field F] {D : ℕ} {bits : P→ℕ} (A : MarkedWorld F D P bits)
    (count : A.graph.Edge→ℕ) (key : A.graph.Edge ↪ Fin M) :
    (Σe : A.graph.Edge,Fin (count e)) ↪ Fin (∑e,count e) :=
  (address key count).toEmbedding

theorem grain_read {F P : Type} [Field F] {D : ℕ} {bits : P→ℕ} (A : MarkedWorld F D P bits)
    (count : A.graph.Edge→ℕ) (key : A.graph.Edge ↪ Fin M) (e : A.graph.Edge) (j : Fin (count e)) :
    (grains A count key ⟨e,j⟩).val=offset key count e+j.val := rfl

/-- The physical splitter uses low-order consecutive digits for the piece:
on input and output the original bit is the same public arithmetic address. -/
def grainDigit {m q w : ℕ} (fit : w=m*q) (i : Fin m) (j : Fin q) : Fin w :=
  Fin.cast fit.symm (finProdFinEquiv (i,j))

@[simp] theorem grainDigit_val {m q w : ℕ} (fit : w=m*q) (i : Fin m) (j : Fin q) :
    (grainDigit fit i j).val=j.val+q*i.val := rfl

theorem actual_grain_digit {D : ℕ} {P : Type} {bits : P→ℕ} (N : Network D P bits)
    (core : Finset N.Edge) (m : N.Edge→ℕ) (q : ℕ) (fit : ∀e∈core,N.width e=m e*q)
    (old : N.Assignment) (e : ↥core) (i : Fin (m e.val)) (j : Fin q) :
    DescentCableUnbundling.assignmentEquiv N core m q fit old (.inr ⟨e,i⟩) j =
      old e.val (grainDigit (fit e.val e.property) i j) := rfl

/-- A local subword inherits its source ID; restricting again leaves the
numerical key of every surviving occurrence unchanged. -/
def restrictKey {U : Type*} {L : ℕ} (key : U ↪ Fin L) (condition : U→Prop) :
    {i // condition i} ↪ Fin L := (Function.Embedding.subtype condition).trans key

variable (key : I ↪ Fin M) (contact : I→C) (wt : I→ℕ)

def fibreKey (c : C) : Fibre contact c ↪ Fin M := restrictKey key (fun i=>contact i=c)
def itemKey (owner : Bool→C→W) (s : Bool) (w : W) : Item contact owner s w ↪ Fin M :=
  restrictKey key (fun i=>owner s (contact i)=w)
def cellKey (dest : I→ℕ→Bool) (d : ℕ) (node : DescentContactTree.Node d) :
    DescentContactTree.Cell dest d node ↪ Fin M :=
  restrictKey key (fun i=>DescentContactTree.prefixAt dest d i=node)

def words : Ports (width contact wt) ≃ DescentContactTree.Physical.Row wt where
  toFun x i := decode (fibreKey key contact (contact i)) (fun t=>wt t.val) (x (contact i)) ⟨i,rfl⟩
  invFun y c := (decode (fibreKey key contact c) (fun t=>wt t.val)).symm (fun t=>y t.val)
  left_inv x := by
    funext c
    apply (decode (fibreKey key contact c) (fun t=>wt t.val)).injective
    rw [Equiv.apply_symm_apply]
    funext t;rcases t with ⟨i,rfl⟩;rfl
  right_inv y := by funext i;simp

omit [Fintype C] in
theorem words_read (x : Ports (width contact wt)) (i : I) (j : Fin (wt i)) :
    words key contact wt x i j =
      x (contact i) (bitIndex (fibreKey key contact (contact i)) (fun t=>wt t.val) ⟨⟨i,rfl⟩,j⟩) := rfl

/-- Conjugating each entire cable once implements the ordered read at either
terminal, for precisely the source fiber of that installed cable. -/
def physicalWords (x : Ports (width contact wt)) : Ports (width contact wt) :=
  fun c=>x c ∘ permutation (fibreKey key contact c) (fun t=>wt t.val)

omit [Fintype C] in
theorem decode_words (x : Ports (width contact wt)) :
    labels contact wt (physicalWords key contact wt x)=words key contact wt x := by
  funext i
  exact (congrFun (decode_eq (fibreKey key contact (contact i)) (fun t=>wt t.val) (x (contact i))) ⟨i,rfl⟩).symm

variable (input : Bool→I→R) (site : Bool→R→W) (owner : Bool→C→W)
    (align : ∀s i,site s (input s i)=owner s (contact i)) (s : Bool) (w : W)
variable (D : ℕ)

/-- Explicit sibling-fiber address of an input packet and its actual within-item digit. -/
def sourceAt (i : Item contact owner s w) (j : Fin (wt i.val)) :
    Fin (width (input s) wt (input s i.val)) :=
  bitIndex (fibreKey key (input s) (input s i.val)) (fun t=>wt t.val) ⟨⟨i.val,rfl⟩,j⟩

def linkAt (i : Item contact owner s w) (j : Fin (wt i.val)) :
    Fin (width contact wt (contact i.val)) :=
  bitIndex (fibreKey key contact (contact i.val)) (fun t=>wt t.val) ⟨⟨i.val,rfl⟩,j⟩

omit [Fintype C] [Fintype R] [Fintype W] in
theorem source_at_value (i : Item contact owner s w) (j : Fin (wt i.val)) :
    (sourceAt key contact wt input owner s w i j).val=
      offset (fibreKey key (input s) (input s i.val)) (fun t=>wt t.val) ⟨i.val,rfl⟩+j.val := rfl

omit [Fintype C] [Fintype W] in
theorem link_at_value (i : Item contact owner s w) (j : Fin (wt i.val)) :
    (linkAt key contact wt owner s w i j).val=
      offset (fibreKey key contact (contact i.val)) (fun t=>wt t.val) ⟨i.val,rfl⟩+j.val := rfl


local notation "bank" => DescentRouterBank.network D contact input site owner wt
local notation "lens" => DescentNetworkSubstitution.slotWidth bank (s,w)

def slotSource (p : Ports lens) (i : Item contact owner s w) (j : Fin (wt i.val)) : Bool :=
  p (rootSlot D contact input site owner wt s w (root contact input site owner s w align i))
    (sourceAt key contact wt input owner s w i j)

def slotTarget (p : Ports lens) (i : Item contact owner s w) (j : Fin (wt i.val)) : Bool :=
  p (linkSlot D contact input site owner wt s w (link contact owner s w i))
    (Fin.cast (linkWidth D contact input site owner wt s w _).symm (linkAt key contact wt owner s w i j))

omit [Fintype R] in
theorem visible_read (p : Ports (DescentRouterBank.publicWidth input wt)) (links : (bank).Assignment)
    (i : Item contact owner s w) (j : Fin (wt i.val)) :
    let z := DescentNetworkSubstitution.visible bank links p (s,w)
    slotSource key contact wt input site owner align s w D z i j =
      p (s,input s i.val) (sourceAt key contact wt input owner s w i j) ∧
    slotTarget key contact wt input site owner s w D z i j =
      links (contact i.val) (linkAt key contact wt owner s w i j) := by
  cases s <;> exact ⟨rfl,rfl⟩

omit [Fintype R] in
/-- Reading a real good or fallback site before and after the router bank
returns precisely the corresponding ordered source and contact digits. -/
theorem ordered_feed (ports : (s : Bool)→Ports (width (input s) wt)) (links : Ports (width contact wt))
    (i : Item contact owner s w) (j : Fin (wt i.val)) :
    let x := fun s=>labels (input s) wt (physicalWords key (input s) wt (ports s))
    let z := labels contact wt (physicalWords key contact wt links)
    let F := DescentRouterBank.feed D contact input site owner wt x z s w
    sourceWord D contact input site owner wt s w align F i j=ports s (input s i.val) (sourceAt key contact wt input owner s w i j) ∧
    targetWord D contact input site owner wt s w F i j=links (contact i.val) (linkAt key contact wt owner s w i j) := by
  simp only [source_feed,target_feed,decode_words]
  exact ⟨rfl,rfl⟩

end
end Hierarchy.DescentOrderedReset

end OAI
