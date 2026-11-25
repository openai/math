import OAI.Hierarchy.DescentTerminalPorts
import OAI.Hierarchy.ProtocolRAMPortRanks
import OAI.Hierarchy.ProtocolStackContraction

namespace OAI
/-! # The actual terminal graph evaluated on paired physical slots -/

namespace Hierarchy.DescentTerminalPorts
open Computability.BorderVNP.Crossing ThreeFlat.Routing CallPool
open ProtocolStackContraction
open scoped Classical BigOperators
noncomputable section
variable {D : ℕ} {P : Type*} {bits : P → ℕ} (N : Network D P bits)

/-- Only pairs realized by original cables have groups. Parallel cables
and loops retain their own cable ordinals. -/
abbrev Group := {g : N.Site × N.Site // ∃ e : N.Edge,(N.src e,N.dst e)=g}

def group (e : N.Edge) : Group N := ⟨(N.src e,N.dst e),e,rfl⟩

theorem groups_le_edges : Fintype.card (Group N)≤Fintype.card N.Edge := by
  apply Fintype.card_le_of_surjective (group N)
  rintro ⟨v,e,rfl⟩
  exact ⟨e,rfl⟩

abbrev CableAt (g : Group N) := {e : N.Edge // group N e=g}

def groupPieces (w : ℕ) (g : Group N) := ∑ e : CableAt N g,poolBatchCount (N.width e.val) w

def groupedPiece (w : ℕ) : Piece N w ≃ ((g : Group N) ×
    ((e : CableAt N g) × Fin (poolBatchCount (N.width e.val) w))) where
  toFun u := ⟨group N u.1,⟨u.1,rfl⟩,u.2⟩
  invFun u := ⟨u.2.1.val,u.2.2⟩
  left_inv _ := rfl
  right_inv := by rintro ⟨g,⟨⟨e,h⟩,k⟩⟩; subst g; rfl

/-- Each side uses precisely the same pair group and cable/piece index.
The offset is the prefix of previous actual cable records in physical
address order, followed by the piece ordinal within its own cable. -/
def cableIndex (w : ℕ) (code : N.Edge ↪ ℕ) : Piece N w ≃ Edge (groupPieces N w) :=
  (groupedPiece N w).trans (Equiv.sigmaCongrRight fun g=>ProtocolRAMPortRanks.enumerate
    (fun e : CableAt N g=>poolBatchCount (N.width e.val) w) (fun e=>code e.val)
    (code.injective.comp Subtype.val_injective))

theorem cableIndex_group (w : ℕ) (code : N.Edge ↪ ℕ) (u : Piece N w) :
    (cableIndex N w code u).1=group N u.1 := rfl

theorem cableIndex_number (w : ℕ) (code : N.Edge ↪ ℕ) (u : Piece N w) :
    (cableIndex N w code u).2.val =
      ProtocolRAMPortRanks.prefix (fun e : CableAt N (group N u.1) => poolBatchCount (N.width e.val) w)
        (fun e=>code e.val) ⟨u.1,rfl⟩ + u.2.val := rfl

theorem groupPieces_total (w : ℕ) (code : N.Edge ↪ ℕ) :
    (∑ g,groupPieces N w g) = Fintype.card (Piece N w) := by
  simpa only [Edge,Fintype.card_sigma,Fintype.card_fin] using (Fintype.card_congr (cableIndex N w code)).symm

section Pool
variable {G : Type} [Fintype G] {w cap : ℕ} {sz : G → ℕ}
    (number : Piece N w ≃ Edge sz) (landing : ∀g,Bool → Fin (sz g) ↪ Fin cap)

def slotOf (side : Bool) (u : Piece N w) : Slot G cap :=
  let q := number u
  (some q.1,side,landing q.1 side q.2)

omit [Fintype G] in
theorem slotOf_encode (blank : Fin w → Bool) (a : Edge sz → Fin w → Bool) (side : Bool) (u : Piece N w) :
    encode landing blank a (slotOf N number landing side u)=a (number u) :=
  encode_active landing blank a _ _ _

def tableOf {F : Type*} (T : N.Tables F) (hw : 0<w) (x : Ports bits)
    (s : Slot G cap → Fin w → Bool) (v : N.Site) : F :=
  T v (fun e i=>s (slotOf N number landing (decide (N.src e.val≠v)) (batchIndex hw e.val i))
    ⟨i.val%w,Nat.mod_lt _ hw⟩) (fun p=>x p.val)

omit [Fintype G] in
theorem tableOf_encode {F : Type*} (T : N.Tables F) (hw : 0<w) (x : Ports bits)
    (blank : Fin w → Bool) (a : Edge sz → Fin w → Bool) (v : N.Site) :
    tableOf N number landing T hw x (encode landing blank a) v =
      localTable N T hw (fun u=>a (number u)) x v := by
  simp only [tableOf,localTable,slotOf_encode]

/-- With any faithful numbering of the actual pieces in the purchased
pool, the two half-slot arrays recover the original network value. -/
theorem physical_value_of {F : Type*} [CommSemiring F] (T : N.Tables F) (hw : 0<w) (x : Ports bits) :
    let blank : Fin w → Bool := fun _=>false
    (∑ s : Slot G cap → Fin w → Bool,
      (if Linked landing s then (1:F) else 0)*
      (if Padding landing blank s then
        (if Slack N (fun u=>s (slotOf N number landing false u)) then
          ∏ v,tableOf N number landing T hw x s v else 0) else 0))=N.value T x := by
  intro blank
  let rest (s : Slot G cap → Fin w → Bool) : F :=
    if Slack N (fun u=>s (slotOf N number landing false u)) then
      ∏ v,tableOf N number landing T hw x s v else 0
  change (∑ s,(if Linked landing s then (1:F) else 0)*(if Padding landing blank s then rest s else 0))=_
  rw [contract landing blank rest,value_words N T hw x]
  simp only [rest,slotOf_encode,tableOf_encode]
  let reindex := (Equiv.arrowCongr number (Equiv.refl (Fin w → Bool))).symm
  exact reindex.sum_comp (fun z : Words N w=>if Slack N z then ∏ v,localTable N T hw z x v else 0)
end Pool

variable {w cap : ℕ} (code : N.Edge ↪ ℕ)
    (place : ∀ g, Bool → Fin (groupPieces N w g) ↪ Fin cap)

def halfSlot (side : Bool) (u : Piece N w) : Slot (Group N) cap :=
  slotOf N (cableIndex N w code) place side u

theorem halfSlot_encode (blank : Fin w → Bool) (a : Edge (groupPieces N w) → Fin w → Bool)
    (side : Bool) (u : Piece N w) :
    encode place blank a (halfSlot N code place side u)=a (cableIndex N w code u) :=
  encode_active place blank a _ _ _

/-- A local site reads its actual side of every incident cable. On a loop
the local table has one cable argument, and uses its source side. -/
def physicalTable {F : Type*} (T : N.Tables F) (hw : 0<w) (x : Ports bits)
    (s : Slot (Group N) cap → Fin w → Bool) (v : N.Site) : F :=
  tableOf N (cableIndex N w code) place T hw x s v

theorem physicalTable_encode {F : Type*} (T : N.Tables F) (hw : 0<w) (x : Ports bits)
    (blank : Fin w → Bool) (a : Edge (groupPieces N w) → Fin w → Bool) (v : N.Site) :
    physicalTable N code place T hw x (encode place blank a) v =
      localTable N T hw (fun u=>a (cableIndex N w code u)) x v :=
  tableOf_encode N (cableIndex N w code) place T hw x blank a v

private theorem same_universe {A : Type*} (s t : Fintype A) :
    @Finset.univ A s=@Finset.univ A t := congrArg (fun v=>@Finset.univ A v) (Subsingleton.elim s t)

set_option maxHeartbeats 1000000 in
/-- Fixing every exterior cable word, the sum on the actual two terminal
boards is the entire original network value. High slack and unallocated
slots must both vanish, so each real assignment contributes only once. -/
theorem physical_value {F : Type*} [CommSemiring F] (T : N.Tables F) (hw : 0<w) (x : Ports bits) :
    let blank : Fin w → Bool := fun _=>false
    (∑ s : Slot (Group N) cap → Fin w → Bool,
      (if Linked place s then (1:F) else 0)*
      (if Padding place blank s then
        (if Slack N (fun u=>s (halfSlot N code place false u)) then
          ∏ v, physicalTable N code place T hw x s v else 0) else 0))=N.value T x := by
  let actual := physical_value_of N (cableIndex N w code) place T hw x
  refine Eq.trans ?_ actual
  apply Finset.sum_congr
  · exact same_universe _ _
  · intro s _
    simp only [halfSlot,physicalTable]
    congr! 15

end
end Hierarchy.DescentTerminalPorts

end OAI
