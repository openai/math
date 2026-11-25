import OAI.ThreeFlat.Diagonal.MotifIntegerChoice
import OAI.ThreeFlat.RAM.PhysicalPinsNat

namespace OAI
/-! # Native fixed-width expressions for compressor motif records

The address registers are the starts of the demand and histogram records.
The base grid and alphabet are fixed constants. Each expression emits a
fixed finite instruction fragment independent of the demand and of word
width, including the candidate comparisons for the tile index.
-/

namespace ThreeFlat.RAM.MotifRows

open Computability.VPVNP.BurstRAM PrivateRAM DescriptorExpr PhysicalPinsExpr
open Diagonal.MotifIntegerChoice
open scoped BigOperators

variable {w n k : ℕ}

def field (base : Formula n) (i : ℕ) : Formula n := .load (.op .add base (.lit i))

def plus (x y : Formula n) : Formula n := .op .add x y

def totals : List (Formula n) → Formula n := List.foldr plus (.lit 0)

def biggest : List (Formula n) → Formula n :=
  List.foldr (fun x y => .select .lt x y y x) (.lit 0)

def sumFields (size : ℕ) (p : Formula n) : Formula n :=
  totals ((List.finRange size).map fun i => field p i.val)

def required (bad width : Formula n) (tileWidth : ℕ) : Formula n :=
  if tileWidth = 0 then .select .eq width (.lit 0) (.lit 0) bad
  else .op .div (.op .add width (.lit (tileWidth-1))) (.lit tileWidth)

def scoreRow {edges : ℕ} (base : Fin edges → ℕ) (p : Formula n) : Formula n :=
  let bad := plus (.lit 1) (sumFields edges p)
  biggest ((List.finRange edges).map fun i => required bad (field p i.val) (base i))

/-- One coordinate of the supply segment, including the repeated selector bits. -/
def outputWidth {size : ℕ} (pool : Fin size → ℕ) (counts copies : Formula n) (selectorBits : ℕ) : Formula n :=
  plus (.op .mul copies (.lit selectorBits)) (totals ((List.finRange size).map fun i => .op .mul (field counts i.val) (.lit (pool i))))

/-- Check the entire canonical histogram against the proposed repetition count. -/
def admission (size : ℕ) (counts copies : Formula n) : Formula n :=
  .select .eq (sumFields size counts) copies (.lit 1) (.lit 0)

/-- Select a numbered grid tile from a nonempty fixed ordered table, carrying
its score so later comparisons refer to the current winner's exact score. -/
def better (old next : Formula n × Formula n) : Formula n × Formula n :=
  (.select .lt next.1 old.1 next.1 old.1, .select .lt next.1 old.1 next.2 old.2)

def choice {edges : ℕ} (first : Fin edges → ℕ) (more : List (Fin edges → ℕ)) (p : Formula n) :
    Formula n × Formula n :=
  (more.zipIdx.map (fun z => (scoreRow z.1 p, .lit (z.2+1)))).foldl better (scoreRow first p,.lit 0)

section Sound
variable (u : ℕ) (data : Param → ℕ) (mem : ℕ → ℕ) (vs : Fin n → ℕ)

local notation "V" => Formula.natural u data mem vs

theorem field_value (p : Formula n) (i : ℕ) : V (field p i) = mem (V p + i) := rfl

theorem totals_value (l : List (Formula n)) : V (totals l) = (l.map V).sum := by
  induction l with
  | nil => rfl
  | cons x l ih => exact congrArg (V x + ·) ih

theorem biggest_le (l : List (Formula n)) (r : ℕ) : V (biggest l) ≤ r ↔ ∀ a ∈ l, V a ≤ r := by
  induction l with
  | nil => simp [biggest,Formula.natural]
  | cons x l ih =>
    change (if decide (V x < V (biggest l)) then V (biggest l) else V x) ≤ r ↔ _
    simp only [decide_eq_true_eq, List.mem_cons, forall_eq_or_imp, ← ih]
    split_ifs <;> omega

theorem sumFields_value (size : ℕ) (p : Formula n) :
    V (sumFields size p) = ∑ i : Fin size, mem (V p + i.val) := by
  rw [sumFields, totals_value, List.map_map]
  simp only [← List.ofFn_id, List.map_ofFn, Function.comp_def, field_value, List.sum_ofFn, id_eq]

theorem required_value (bad b : Formula n) (d : ℕ) : V (required bad b d) = need (V bad) (V b) d := by
  by_cases h : d=0
  · by_cases z : V b = 0 <;> simp [h,required,need,Formula.natural,natTest,z]
  · simp only [required,h,ite_false,Formula.natural,natOp,need]
    congr 1
    omega

theorem score_value {e : ℕ} (d : Fin e → ℕ) (p : Formula n) :
    V (scoreRow d p) = score (fun i : Fin e => mem (V p + i.val)) (fun _ : Unit => d) () := by
  apply Nat.le_antisymm
  · apply (biggest_le ..).mpr
    intro x hx
    obtain ⟨i, _,rfl⟩ := List.mem_map.mp hx
    rw [required_value, field_value]
    change need (1 + V (sumFields e p)) _ _ ≤ _
    rw [sumFields_value]
    exact Finset.le_sup (f := fun i => need (sentinel (fun i : Fin e => mem (V p+i.val))) (mem (V p+i.val)) (d i)) (Finset.mem_univ i)
  · apply Finset.sup_le
    intro i _
    have h := (biggest_le u data mem vs _ _).mp (le_refl (V (scoreRow d p))) _
      (List.mem_map.mpr ⟨i,List.mem_finRange i,rfl⟩)
    rw [required_value, field_value] at h
    simpa only [plus, Formula.natural, natOp, sumFields_value, sentinel] using h

theorem admission_value (size : ℕ) (counts copies : Formula n) :
    V (admission size counts copies) = if (∑ i : Fin size, mem (V counts+i.val)) = V copies then 1 else 0 := by
  simp [admission,Formula.natural,natTest,sumFields_value]

theorem outputWidth_value {size : ℕ} (pool : Fin size → ℕ) (counts copies : Formula n) (sb : ℕ) :
    V (outputWidth pool counts copies sb) = V copies * sb + ∑ i : Fin size, mem (V counts + i.val) * pool i := by
  change _ + V (totals _) = _
  rw [totals_value,List.map_map]
  simp only [← List.ofFn_id, List.map_ofFn, Function.comp_def, List.sum_ofFn, Formula.natural, natOp, field]
  rfl

def evalPair (z : Formula n × Formula n) := (V z.1, V z.2)

private theorem better_value (z t : Formula n × Formula n) : evalPair u data mem vs (better z t) =
    if V t.1 < V z.1 then evalPair u data mem vs t else evalPair u data mem vs z := by
  by_cases h : V t.1 < V z.1 <;> simp [better,evalPair,Formula.natural,natTest,h]

private theorem fold_value (z : Formula n × Formula n) (rows : List (Formula n × Formula n)) :
    evalPair u data mem vs (rows.foldl better z) =
      best Prod.fst (evalPair u data mem vs z) (rows.map (evalPair u data mem vs)) := by
  induction rows generalizing z with
  | nil => rfl
  | cons j l ih =>
    rw [List.foldl_cons,List.map_cons,best,ih,better_value]
    rfl

/-- The actual two return expressions contain the integer score and tile index
of the first winning input table row. -/
theorem choice_value {e : ℕ} (first : Fin e → ℕ) (more : List (Fin e → ℕ)) (p : Formula n) :
    let sc := fun d : Fin e → ℕ => score (fun i : Fin e => mem (V p + i.val)) (fun _ : Unit => d) ()
    evalPair u data mem vs (choice first more p) = best Prod.fst (sc first,0)
      (more.zipIdx.map fun z => (sc z.1, z.2+1)) := by
  dsimp only
  rw [choice,fold_value,List.map_map]
  simp only [evalPair,Function.comp_def,score_value,Formula.natural]

end Sound

/-- This native ROM evaluates the motif arithmetic, with a path length
determined by the grid alone. -/
theorem steps (p : Param → Fin k) (f : Formula n) :
    ((f.compile p : Term w k n)).steps = 2*f.work+1 := by rw [Term.steps_eq,Formula.binds_compile]

end ThreeFlat.RAM.MotifRows

end OAI
