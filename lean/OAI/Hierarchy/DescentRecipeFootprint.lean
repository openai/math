import OAI.Hierarchy.DescentHistoryLanes

namespace OAI
/-! # Under positive-width cable subdivisions an atom's total bit incidence never grows -/

namespace Hierarchy.DescentKernelHistory
open Computability.BorderVNP.Crossing DescentCableUnbundling
open scoped Classical BigOperators
noncomputable section

variable {A B C X Y : Type}

def bitCost (w : A→ℕ) : List A→ℕ
  | []=>0
  | a::as=>max 1 (w a)+bitCost w as

theorem length_le_bitCost (w : A→ℕ) (l : List A) : l.length≤bitCost w l := by
  induction l with
  | nil=>rfl
  | cons a l ih=>simp only [List.length_cons,bitCost];omega

theorem bitCost_append (w : A→ℕ) (l m : List A) :
    bitCost w (l++m)=bitCost w l+bitCost w m := by
  induction l with
  | nil=>simp [bitCost]
  | cons a l ih=>simp [bitCost,ih,Nat.add_assoc]

theorem bitCost_map (w : A→ℕ) (f : B→A) (l : List B) :
    bitCost w (l.map f)=bitCost (w∘f) l := by
  induction l with
  | nil=>rfl
  | cons b l ih=>simp [bitCost,ih]

theorem bitCost_const (n : ℕ) (l : List A) :
    bitCost (fun _ : A=>n) l=l.length*(max 1 n) := by
  induction l with
  | nil=>simp [bitCost]
  | cons a l ih=>simp [bitCost,ih,Nat.add_mul,Nat.add_comm]

theorem bitCost_gather (wo : A→ℕ) (wn : B→ℕ) (f : A→List B) (paid : ∀a,bitCost wn (f a)≤max 1 (wo a))
    (l : List A) : bitCost wn (l.flatMap f)≤bitCost wo l := by
  induction l with
  | nil=>rfl
  | cons a l ih=>simpa only [List.flatMap_cons,bitCost_append,bitCost] using Nat.add_le_add (paid a) ih

def operandSize (r : Recipe X A) (width : A→ℕ) : A⊕r.Hidden→ℕ := Sum.elim width r.width

def atomFootprint (r : Recipe X A) (width : A→ℕ) (v : r.Node) :=
  bitCost (operandSize r width) (List.ofFn (r.operand v))

theorem arity_le_footprint (r : Recipe X A) (width : A→ℕ) (v : r.Node) :
    r.arity v≤atomFootprint r width v := by
  simpa [atomFootprint] using length_le_bitCost (operandSize r width) (List.ofFn (r.operand v))

theorem split_footprint (r : Recipe X A) (parts : A→List B) (old : A→ℕ) (new : B→ℕ)
    (paid : ∀a,bitCost new (parts a)≤max 1 (old a)) (v : r.Node) :
    atomFootprint (splitLanes r parts) new v≤atomFootprint r old v := by
  let expand : A⊕r.Hidden→List (B⊕r.Hidden) := Sum.elim (fun a=>(parts a).map Sum.inl) (fun h=>[Sum.inr h])
  let before := List.ofFn (r.operand v)
  have groups : physicalArgs r parts v=before.map expand := by
    rw [show before=List.ofFn (r.operand v) from rfl,←List.ofFn_comp']
    apply congrArg List.ofFn
    funext j
    cases e : r.operand v j <;> simp [expand]
  have flat : List.ofFn ((splitLanes r parts).operand v)=(physicalArgs r parts v).flatten := by
    exact List.ofFn_get (physicalArgs r parts v).flatten
  change bitCost _ (List.ofFn ((splitLanes r parts).operand v))≤bitCost _ before
  rw [flat,groups,←List.flatMap_def]
  apply bitCost_gather
  rintro (a|h)
  · change bitCost (Sum.elim new r.width) ((parts a).map (Sum.inl : B→B⊕r.Hidden))≤max 1 (old a)
    exact (bitCost_map (Sum.elim new r.width) (Sum.inl : B→B⊕r.Hidden) (parts a)).le.trans (paid a)
  · simp [expand,bitCost,operandSize,splitLanes]

variable {D : ℕ} {P : Type} {bits : P→ℕ} (N : Network D P bits)

def boundaryWidth (v : N.Site) : Boundary N v→ℕ := Sum.elim (fun e=>N.width e.val) (fun p=>bits p.val)

variable (core : Finset N.Edge) (m : N.Edge→ℕ) (q : ℕ)
variable (fit : ∀e∈core,N.width e=m e*q)
local notation "Q" => network N core m q

include fit in
theorem lane_bits (positive : 0<q) (v : N.Site) (ref : Boundary N v) :
    bitCost (boundaryWidth (Q) v) (laneNames N core m q v ref)≤max 1 (boundaryWidth N v ref) := by
  cases ref with
  | inr p=>simp [laneNames,boundaryWidth,bitCost]
  | inl e=>
    by_cases h : e.val∈core
    · simp only [laneNames,h,dite_eq_left]
      have c : ∀u : Fin (m e.val),boundaryWidth (Q) v
          (.inl ⟨.inr ⟨⟨e.val,h⟩,u⟩,e.property⟩)=q := fun _=>rfl
      let f : Fin (m e.val)→Boundary (Q) v := fun u=>.inl ⟨.inr ⟨⟨e.val,h⟩,u⟩,e.property⟩
      rw [show List.ofFn f=(List.ofFn id).map f by rw [←List.ofFn_comp'];rfl,bitCost_map]
      change bitCost (fun _ : Fin (m e.val)=>q) (List.ofFn id)≤_
      rw [bitCost_const,List.length_ofFn,Nat.max_eq_right (by omega : 1≤q)]
      exact (fit e.val h).ge.trans (le_max_right 1 _)
    · simp [laneNames,h,boundaryWidth,bitCost]

include fit in
theorem actual_split_bits (positive : 0<q) (v : N.Site) (r : Recipe X (Boundary N v)) (i : r.Node) :
    atomFootprint (splitLanes r (laneNames N core m q v)) (boundaryWidth (Q) v) i≤atomFootprint r (boundaryWidth N v) i :=
  split_footprint r _ _ _ (lane_bits N core m q fit positive v) i

end
end Hierarchy.DescentKernelHistory

end OAI
