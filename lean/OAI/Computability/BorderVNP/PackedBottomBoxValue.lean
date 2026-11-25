import OAI.Computability.BorderVNP.PackedBottomBoxInterpreter
import OAI.Computability.BorderVNP.PackedBottomBankLanes
import OAI.Computability.BorderVNP.PackedInheritedFieldWeight
import OAI.Computability.BorderVNP.PackedInheritedStaging

/-! # Summing the checked private guesses of a repeated original box

A private scalar factor reads a sign and an optional gadget position. The other
private rows and public incidence ties enforce the physical work layout. Once
these wiring checks pass, the free guesses are exactly the original fine wire
choices, independently in each copy.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited

/-- The scalar attached to a single successful observation of the sparse evaluator. -/
def fieldEntry {K : Type*} [Field K] (values : ℕ → K) (obs : Bool × Option ℕ) : K :=
  (if obs.1 then -1 else 1) * obs.2.elim 1 values

/-- Multiplication of the individual signed entries implements the evaluator's
joint parity and product of selected scalars, including zero-valued scalars. -/
theorem fieldWeight_eq_prod {K : Type*} [Field K] (values : ℕ → K) (obs : List (Bool × Option ℕ)) :
    fieldWeight values obs = (obs.map (fieldEntry values)).prod := by
  induction obs with
  | nil => simp [fieldWeight]
  | cons o os ih =>
    rw [List.map_cons,List.prod_cons,← ih]
    have shift (b : Bool) : (os.map Prod.fst).foldl Bool.xor b =
        (b ^^ (os.map Prod.fst).foldl Bool.xor false) := by
      simpa only [Bool.xor_false] using
        (List.foldl_assoc (op := Bool.xor) (l := os.map Prod.fst) (a₁ := b) (a₂ := false))
    rcases o with ⟨b,g⟩
    cases b <;> cases g <;>
      cases h : (os.map Prod.fst).foldl Bool.xor false <;>
      simp [fieldWeight,fieldEntry,shift true,h]

end Packing.Inherited

namespace Packing.BottomRepeat

open Crossing CellSparse Inherited BottomReports
open scoped Classical

variable {R : Type*} [CommSemiring R]

private theorem mapM_product {α β : Type*} (xs : List α) (read : α → Option β) (entry : β → R) :
    (xs.mapM read).elim 0 (fun os => (os.map entry).prod) =
      (xs.map (fun x => (read x).elim 0 entry)).prod := by
  induction xs with
  | nil => rfl
  | cons a as ih =>
    rw [List.map_cons,List.prod_cons,← ih]
    cases ha : read a <;> cases ht : as.mapM read <;>
      simp [List.mapM_cons,ha,ht,Option.pure_def]

/-- The product of the privately interpreted scalar factors for a single copy.
An absent row contributes zero. -/
def boxProduct (entry : (Bool × Option ℕ) → R) (fs : List Factor)
    (bank : ℕ → Bool) (stride c : ℕ) : R :=
  (fs.map (fun f => (f.observe bank (c*stride) c).elim 0 entry)).prod

variable {D qe qa : ℕ} {A : Type} [Fintype A] {width : A → ℕ}
variable (N : Network D A width) (edges : N.Edge ↪ Fin qe) (ports : A ↪ Fin qa) (v : N.Site)

/-- At any physical bank satisfying the public ties, the scalar read of the
actual private program is the product of the copy-local factor products. -/
theorem bornWith_product (copies capFine stride : ℕ) (box : List Factor)
    (bank : ℕ → Bool) (entry : (Bool × Option ℕ) → R)
    (ht : ∀ r ∈ ties N edges ports v copies capFine stride, r.Valid [box] bank) :
    ((bornWith N edges ports v copies capFine stride box).observe bank).elim 0
      (fun os => (os.map entry).prod) = ∏ c : Fin copies, boxProduct entry box bank stride c.val := by
  rw [Site.observe,ite_eq_left ((bornWith_rows_valid N edges ports v copies capFine stride box bank).mpr ht),
    Directory.observations,mapM_product,bornWith_occurrences]
  rw [List.map_flatMap,List.flatMap_def,List.prod_flatten]
  simp only [List.map_map,Function.comp_def]
  rw [Fin.prod_univ_def]
  congr 1
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp [boxProduct]

/-- Physical lane checks in all copies for a fixed choice of supplied inputs
and externally prescribed uses. -/
def WorkChecks (s : Slab) (copies : ℕ)
    (u : Fin copies → Fin s.supplied → Bool) (x : Fin copies → Fin s.incoming → Bool)
    (use : Fin copies → Fin s.used → Bool) (work : Fin (copies*s.stride) → Bool) : Prop :=
  ∀ c : Fin copies, s.Checks (fun j => if h : j < s.stride then work (finProdFinEquiv (c,⟨j,h⟩)) else false)
    (u c) (x c) (use c)

/-- The native bottom-site value reindexed by the original independent fine-wire
guesses. Public padding and the copy-local work checks come from the physical
wiring predicate. A wiring failure contributes zero even when all scalar factors
would otherwise have valid rows. -/
theorem bornWith_value_reindex (copies : ℕ) (s : Slab) (fs wiring : List Factor)
    (input : Fin (incoming (wide N copies) v) → Bool)
    (u : Fin copies → Fin s.supplied → Bool) (x : Fin copies → Fin s.incoming → Bool)
    (use : Fin copies → Fin s.used → Bool) (pad : Prop)
    (entry : (Bool × Option ℕ) → R)
    (neutral : ∀ f ∈ wiring, ∀ bank off copy o, f.observe bank off copy = some o → entry o = 1)
    (checked : ∀ work : Fin (copies*s.stride) → Bool,
      ((∀ r ∈ ties N edges ports v copies s.capFine s.stride,
        r.Valid [fs ++ wiring] (bits work input)) ∧ ∀ c : Fin copies, ∀ f ∈ wiring,
        (f.observe (bits work input) (c.val*s.stride) c.val).isSome = true) ↔
      WorkChecks s copies u x use work ∧ pad) :
    (bornWith N edges ports v copies s.capFine s.stride (fs ++ wiring)).value
      (fun os => (os.map entry).prod) input =
      if pad then ∑ g : Fin copies → Fin s.guessed → Bool,
        ∏ c : Fin copies, boxProduct entry fs
          (bits ((s.checkedGuessEquiv copies u x use g).val) input) s.stride c.val else 0 := by
  let site := bornWith N edges ports v copies s.capFine s.stride (fs ++ wiring)
  let P := WorkChecks s copies u x use
  let term := fun work : Fin (copies*s.stride) → Bool =>
    ∏ c : Fin copies, boxProduct entry fs (bits work input) s.stride c.val
  have point (work : Fin (copies*s.stride) → Bool) :
      (site.observe (bits work input)).elim 0 (fun os => (os.map entry).prod) =
      if P work ∧ pad then term work else 0 := by
    by_cases h : P work ∧ pad
    · obtain ⟨ht,hw⟩ := (checked work).mpr h
      rw [ite_eq_left h,bornWith_product N edges ports v copies s.capFine s.stride (fs ++ wiring)
        (bits work input) entry ht]
      apply Finset.prod_congr rfl
      intro c _
      simp only [boxProduct,List.map_append,List.prod_append]
      suffices h₁ : (wiring.map (fun f => (f.observe (bits work input) (c.val*s.stride) c.val).elim 0 entry)).prod = 1 by
        rw [h₁,mul_one]
      apply List.prod_eq_one
      intro y hy
      obtain ⟨f,hf,rfl⟩ := List.mem_map.mp hy
      cases ho : f.observe (bits work input) (c.val*s.stride) c.val with
      | none => have bad := hw c f hf; simp [ho] at bad
      | some o => exact neutral f hf _ _ _ o ho
    · rw [ite_eq_right h]
      cases ho : site.observe (bits work input) with
      | none => rfl
      | some os =>
        have accepted : (site.observe (bits work input)).isSome = true := by rw [ho]; rfl
        have ha := (bornWith_accepts N edges ports v copies s.capFine s.stride
          (fs ++ wiring) (bits work input)).mp accepted
        exact (h ((checked work).mp ⟨ha.1,fun c f hf => ha.2 c.val c.isLt f (List.mem_append_right fs hf)⟩)).elim
  change (∑ work : Fin (copies*s.stride) → Bool,
    (site.observe (bits work input)).elim 0 (fun os => (os.map entry).prod)) = _
  simp_rw [point]
  by_cases hp : pad
  · simp only [hp,and_true,ite_true]
    rw [← Finset.sum_filter,Finset.sum_subtype (p := P) _ (fun _ => by simp) term]
    exact ((s.checkedGuessEquiv copies u x use).sum_comp (fun w => term w.val)).symm
  · simp [hp]

end Packing.BottomRepeat

namespace Packing.BottomGridBank

open Crossing CellSparse CellAddresses GridBoxes BottomReports Inherited
open scoped Classical

variable {D H : ℕ} {P C Q A : Type} [Fintype P] [Fintype C] [Fintype Q] [Fintype A]
variable (N : Network D P (fun _ => 1)) (cell : N.Site → C)
variable (position : C → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1}) {src dst : Q → C}
variable (pack : (N.cellNetwork cell position).ChannelPacking src dst H)
variable (width : A → ℕ) (owner : A → C) (lane : P ↪ (a : A) × Fin (width a))
variable (aligned : ∀ p, owner (lane p).1 = cell (N.attach p))
variable {ne np qe qa : ℕ} (edgeID : N.Edge ↪ Fin ne) (portID : P ↪ Fin np)
variable (channelID : Q ↪ Fin qe) (groupID : A ↪ Fin qa) (v : C)

/-- Every successful private fine tie, fine padding check or physical grid padding
check returns the positive sign and no gadget position. -/
theorem wiring_neutral (capFine : ℕ) (f : Factor)
    (hf : f ∈ wiring N cell position pack width owner lane aligned edgeID portID channelID groupID v capFine)
    (bank : ℕ → Bool) (off copy : ℕ) (o : Bool × Option ℕ) (ho : f.observe bank off copy = some o) :
    o = (false,none) := by
  simp only [wiring,List.mem_append,fineTies,List.mem_ofFn,fineZeros,List.mem_map,GridPadding.factors] at hf
  rcases hf with ((⟨k,rfl⟩ | ⟨k,_,rfl⟩) | ⟨k,_,rfl⟩)
  · rw [compareUse_observe] at ho
    split at ho <;> simp_all
  all_goals
    rw [GridPadding.observe_zero] at ho
    split at ho <;> simp_all

end Packing.BottomGridBank

end BorderVNP
end Computability
end OAI
