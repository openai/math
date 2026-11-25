import OAI.Hierarchy.TickResourceBounds

namespace OAI
/-! # Paying for the actual header, paired endpoint pins and remaining advice -/

namespace Hierarchy.FactorPinIntervals
open scoped BigOperators Classical
noncomputable section

variable {E : Type} [Fintype E] {S N k : ℕ} (origin : Fin S → Fin N)
    (port : E × Bool ↪ Fin S) (direction : E → Fin k)
    (paired : ∀ e, origin (port (e,true))=origin (port (e,false)))

def adviceCount (i : Fin N) : ℕ :=
  (Finset.univ.filter (fun j => origin j=i ∧ j ∉ Set.range port)).card

def pairCount (i : Fin N) (h : Fin k) : ℕ :=
  (Finset.univ.filter (fun e => direction e=h ∧ origin (port (e,false))=i)).card

include paired in
/-- Each occurrence owns exactly one pin for each advice bit and two for each
labelled pair, regardless of the order of these bits in its interval list. -/
theorem pinCount (i : Fin N) : (Finset.univ.filter (fun j => origin j=i)).card =
    adviceCount origin port i + 2*∑ h, pairCount origin port direction i h := by
  classical
  let bits := Finset.univ.filter (fun j => origin j=i)
  let rails := Finset.univ.filter (fun e => origin (port (e,false))=i)
  have both (e : E) (s : Bool) : origin (port (e,s))=origin (port (e,false)) := by
    cases s with
    | false => rfl
    | true => exact paired e
  have mapped : bits.filter (fun j => j ∈ Set.range port)=
      (rails ×ˢ (Finset.univ : Finset Bool)).map port := by
    ext j
    constructor
    · intro h
      obtain ⟨hown,u,rfl⟩ := Finset.mem_filter.mp h
      apply Finset.mem_map.mpr
      refine ⟨u,Finset.mem_product.mpr ⟨?_,Finset.mem_univ _⟩,rfl⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (both u.1 u.2).symm.trans (Finset.mem_filter.mp hown).2⟩
    · intro h
      obtain ⟨u,hu,rfl⟩ := Finset.mem_map.mp h
      exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        (both u.1 u.2).trans (Finset.mem_filter.mp (Finset.mem_product.mp hu).1).2⟩,⟨u,rfl⟩⟩
  have total := Finset.card_filter_add_card_filter_not (s:=bits) (fun j => j ∈ Set.range port)
  rw [mapped,Finset.card_map,Finset.card_product,Finset.card_univ,Fintype.card_bool] at total
  have other : (bits.filter (fun j => j ∉ Set.range port)).card=adviceCount origin port i := by
    simp only [bits,adviceCount,Finset.filter_filter]
  have grouped : rails.card=∑ h, pairCount origin port direction i h := by
    rw [Finset.card_eq_sum_card_fiberwise (s:=rails) (t:=Finset.univ)
      (f:=direction) (fun _ _ => Finset.mem_univ _)]
    apply Finset.sum_congr rfl
    intro h _
    simp only [rails,pairCount,Finset.filter_filter,and_comm]
  rw [other,grouped] at total
  change bits.card=_
  omega

include paired in
theorem list_pinCount (xs : List (Fin N)) :
    (xs.map (fun i => (Finset.univ.filter (fun j => origin j=i)).card)).sum =
    (xs.map (adviceCount origin port)).sum +
      2*∑ h, (xs.map (fun i => pairCount origin port direction i h)).sum := by
  induction xs with
  | nil => simp
  | cons i xs ih =>
    simp only [List.map_cons,List.sum_cons,Finset.sum_add_distrib,ih,
      pinCount origin port direction paired i]
    ring

include paired in
/-- A global mean and one-item-per-class rounding allowance for each resource
pay for each real assigned row, including a public header of length at most H. -/
theorem allocated_pin_room {T m w cap d H budget : ℕ} (cost : Fin N → Fin m → ℕ)
    (a : Fin m) (coord : Fin k → Fin m)
    (accountA : ∀ i, cost i a=adviceCount origin port i)
    (accountP : ∀ i h, cost i (coord h)=pairCount origin port direction i h)
    (width : ∀ i j, cost i j ≤ 2^w) (bounded : ∀ i j, cost i j ≤ cap)
    (avgA : 4*((List.finRange N).map (fun i => cost i a)).sum ≤ T*budget)
    (avgP : ∀ h, 4*((List.finRange N).map (fun i => cost i (coord h))).sum ≤ T*budget)
    (err : 4*((20*(w+1)+2)^m)*cap ≤ budget)
    (combined : H+(2*k+1)*budget ≤ d)
    (t : Fin T) (header : List Bool) (hH : header.length ≤ H) :
    header.length+((FactorAllocation.factors w cost (List.finRange N) t).map
      (fun i => (Finset.univ.filter (fun j => origin j=i)).card)).sum ≤ d := by
  let xs := FactorAllocation.factors w cost (List.finRange N) t
  have bound (j : Fin m) (h : 4*((List.finRange N).map (fun i => cost i j)).sum ≤ T*budget) :
      (xs.map (fun i => cost i j)).sum ≤ budget := by
    simpa only [Nat.one_mul,xs] using
      (GridScale.resource_fits (m:=budget) (C:=1) cost (List.finRange N) j t
        (fun i _ => width i) (fun i _ => bounded i) (by simpa using h) (by simpa using err))
  have ha := bound a avgA
  simp only [accountA] at ha
  have each (j : Fin k) : (xs.map (fun i => pairCount origin port direction i j)).sum ≤ budget := by
    simpa only [accountP] using bound (coord j) (avgP j)
  have hp : (∑ j, (xs.map (fun i => pairCount origin port direction i j)).sum) ≤ k*budget := by
    simpa using Finset.sum_le_sum (s:=Finset.univ) (fun j _ => each j)
  change header.length+(xs.map _).sum≤d
  rw [list_pinCount origin port direction paired]
  calc
    _ ≤ H+(budget+2*(k*budget)) := Nat.add_le_add hH (Nat.add_le_add ha (Nat.mul_le_mul_left _ hp))
    _ = H+(2*k+1)*budget := by ring
    _ ≤ _ := combined

/-- The actual native admission matrix uses one column for the complete
input fiber. This specialization charges the published matrix directly. -/
theorem allocated_input_room {T m w cap d H budget : ℕ} (cost : Fin N→Fin m→ℕ) (column : Fin m)
    (actual : ∀ f, cost f column=(Finset.univ.filter (fun j=>origin j=f)).card)
    (width : ∀ f j,cost f j≤2^w) (bounded : ∀ f j,cost f j≤cap)
    (avg : 4*((List.finRange N).map (fun f=>cost f column)).sum ≤ T*budget)
    (err : 4*((20*(w+1)+2)^m)*cap ≤ budget) (combined : H+budget≤d)
    (t : Fin T) (header : List Bool) (hH : header.length≤H) :
    header.length+((FactorAllocation.factors w cost (List.finRange N) t).map
      (fun f=>(Finset.univ.filter (fun j=>origin j=f)).card)).sum≤d := by
  have h := GridScale.resource_fits (m:=budget) (C:=1) cost (List.finRange N) column t
    (fun i _=>width i) (fun i _=>bounded i) (by simpa using avg) (by simpa using err)
  simp only [Nat.one_mul,actual] at h
  exact (Nat.add_le_add hH h).trans combined

end
end Hierarchy.FactorPinIntervals

end OAI
