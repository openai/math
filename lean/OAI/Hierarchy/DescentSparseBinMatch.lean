import OAI.Hierarchy.DescentSparseFirstFit
import OAI.Hierarchy.DescentPackSelectionCounters

namespace OAI
/-! # Padded native first-fit on the sorted sparse directory -/

noncomputable section
namespace Hierarchy.DescentPacking.Sparse
open Computability.VPVNP.BurstRAM PrivateRAM FirstFitRAM
open scoped Classical Fin.CommRing
variable {I C A P : Type*} [Fintype A] [DecidableEq A] [Fintype P] [DecidableEq P]
variable [Fintype C] [DecidableEq C]

/-- Compile all aperture rows, including unused rows at the very end. -/
structure Expansion (A P : Type*) [Fintype A] [Fintype P] where
  slot : A ↪ P
  padding : List P
  sequence : binOrder P=(binOrder A).map slot++padding
  apart : ∀p∈padding,∀a,slot a≠p

/-- Assign logical local names the actual physical ordinal used by the RAM's
left-to-right search. -/
def position (n : ℕ) : Equiv.Perm (Fin n) :=
  (Fintype.equivFin (Fin n)).trans (finCongr (Fintype.card_fin _))

def padSlot {m n : ℕ} (h : m≤n) : Fin m ↪ Fin n :=
  (position m).toEmbedding.trans ((Fin.castLEEmb h).trans (position n).symm.toEmbedding)

theorem pad_prefix {m n : ℕ} (h : m≤n) :
    (binOrder (Fin n)).take m=(binOrder (Fin m)).map (padSlot h) := by
  apply List.ext_getElem
  · simp [binOrder,Nat.min_eq_left h]
  · intro i hi hj
    apply (position n).injective
    apply Fin.ext
    simp [binOrder,position,padSlot]

def padded {m n : ℕ} (h : m≤n) : Expansion (Fin m) (Fin n) := by
  have seq : binOrder (Fin n)=(binOrder (Fin m)).map (padSlot h)++(binOrder (Fin n)).drop m := by
    rw [←pad_prefix h,List.take_append_drop]
  refine ⟨padSlot h,(binOrder (Fin n)).drop m,seq,?_⟩
  have unique : (binOrder (Fin n)).Nodup := (List.nodup_finRange _).map (Fintype.equivFin (Fin n)).symm.injective
  rw [seq,List.nodup_append] at unique
  intro p hp a
  exact unique.2.2 _ (List.mem_map.mpr ⟨a,mem_binOrder _,rfl⟩) _ hp

namespace Expansion

def Fits (D : Expansion A P) (localCap : A→ℕ) (observed : P→ℕ) :=
  (∀a,observed (D.slot a)=localCap a) ∧ ∀p∈D.padding,observed p=0

omit [DecidableEq P] [DecidableEq A] in
theorem choose [Nonempty A] (D : Expansion A P) (cap : A→ℕ) (obs : P→ℕ) (need : ℕ)
    (h : D.Fits cap obs) : firstFit need obs=(firstFit need cap).map D.slot := by
  classical
  have head : ((binOrder A).map D.slot).find? (fun p=>decide (need≤obs p))=(firstFit need cap).map D.slot := by
    rw [List.find?_map]
    simp only [Function.comp_def,h.1,firstFit]
  rw [firstFit,D.sequence,List.find?_append,head]
  cases chos : firstFit need cap with
  | some a => rfl
  | none =>
    have pos := firstFit_none chos (Classical.choice (inferInstance : Nonempty A))
    have tail : D.padding.find? (fun p=>decide (need≤obs p))=none := by
      apply List.find?_eq_none.mpr
      intro p hp
      simp [h.2 p hp,show need≠0 by omega]
    simp [tail]

theorem consume (D : Expansion A P) (cap : A→ℕ) (obs : P→ℕ) (need : ℕ) (p : Option A)
    (h : D.Fits cap obs) :
    D.Fits (DescentPacking.consume need cap p) (DescentPacking.consume need obs (p.map D.slot)) := by
  cases p with
  | none => exact h
  | some a =>
    constructor
    · intro b
      by_cases eqn : b=a
      · subst b
        simp [DescentPacking.consume,h.1]
      · have neq : D.slot b≠D.slot a := fun e=>eqn (D.slot.injective e)
        simp [DescentPacking.consume,eqn,neq,h.1]
    · intro q hq
      simp [DescentPacking.consume,(D.apart q hq a).symm,h.2 q hq]

def put (D : Expansion A P) (r : I×Option A) : I×Option P := (r.1,r.2.map D.slot)

theorem decisions [Nonempty A] (D : Expansion A P) (amount : I→ℕ) (xs : List I) (cap : A→ℕ)
    (obs : P→ℕ) (h : D.Fits cap obs) :
    (pack amount xs obs).decisions=(pack amount xs cap).decisions.map D.put := by
  induction xs generalizing cap obs with
  | nil => rfl
  | cons i xs ih =>
    rw [pack_decisions_cons,pack_decisions_cons,List.map_cons,D.choose cap obs (amount i) h]
    apply congrArg₂ List.cons rfl
    exact ih _ _ (D.consume cap obs (amount i) _ h)

theorem assigned_put (D : Expansion A P) (amount : I→ℕ) (a : A) (xs : List (I×Option A)) :
    assigned amount (D.slot a) (xs.map D.put)=assigned amount a xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    obtain ⟨i,_|b⟩ := x <;> simp [put,assigned,ih]

theorem prior [Nonempty A] (D : Expansion A P) (amount : I→ℕ) (xs : List I)
    (cap : A→ℕ) (obs : P→ℕ) (h : D.Fits cap obs) (t : ℕ) (a : A) :
    assigned amount (D.slot a) ((pack amount xs obs).decisions.take t)=
      assigned amount a ((pack amount xs cap).decisions.take t) := by
  rw [D.decisions amount xs cap obs h,←List.map_take]
  exact D.assigned_put ..

theorem full_prior [Nonempty A] {neighbors : Finset C} (short : Directory neighbors A) (D : Expansion A P)
    (amount : I→ℕ) (xs : List I) (cap : C→ℕ) (obs : P→ℕ) (h : D.Fits (cap ∘ short.name) obs)
    (supported : ∀v,0<cap v→v∈keep neighbors) (t : ℕ) (a : A) :
    assigned amount (D.slot a) ((pack amount xs obs).decisions.take t)=
      assigned amount (short.name a) ((pack amount xs cap).decisions.take t) :=
  (D.prior amount xs _ obs h t a).trans (short.prior amount xs cap supported t a).symm

/-- The chosen local tag is a word produced by the executed previous search.
It points to a sorted aperture slot, leaving every original item name intact. -/
theorem native_decisions {w : ℕ} [Nonempty A] (D : Expansion A P) (amount : I→ℕ) (xs : List I)
    (cap : A→ℕ) (obs : P→ℕ) (h : D.Fits cap obs) (m : Memory w) (p : SelectionTrace.Layout)
    (room : SelectionTrace.Room w (Fintype.card P) p) (fits : xs.length≤p.slots)
    (values : capacityWords p.caps obs m) (bounded : ∀v,obs v<2^w)
    (input : ∀i : Fin xs.length,m (p.need+i.val)=(amount (xs.get i):Word w))
    (widths : ∀i∈xs,amount i<2^w) (j : Fin (pack amount xs cap).decisions.length) :
    SelectionTrace.final p (Fintype.card P) m (p.tag j.val)=
      (binTag (((pack amount xs cap).decisions.get j).2.map D.slot):Word w) := by
  let rows := (pack amount xs cap).decisions
  have lengths := congrArg List.length (D.decisions amount xs cap obs h)
  simp only [List.length_map] at lengths
  let i : Fin (pack amount xs obs).decisions.length := ⟨j.val,j.isLt.trans_eq lengths.symm⟩
  have read := SelectionTrace.decisions amount xs obs m room fits values bounded input widths i
  have same : (pack amount xs obs).decisions[i.val]=D.put (rows[j.val]) := by
    simp only [D.decisions amount xs cap obs h,List.getElem_map]
    rfl
  simpa only [List.get_eq_getElem,same,put,rows] using read

end Expansion
end Hierarchy.DescentPacking.Sparse

end
end OAI
