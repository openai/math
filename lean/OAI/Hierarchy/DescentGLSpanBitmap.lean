import OAI.Hierarchy.DescentGLNativeSelection

namespace OAI
/-! # Bitmap of all binary linear combinations of the fixed rows -/

namespace Hierarchy.DescentGL
open scoped BigOperators

/-- Enumerate the binary coefficient tuples once, in two halves. -/
def coefficients : (h : ℕ) → List (Bits h)
  | 0 => [Fin.elim0]
  | h+1 => let old := coefficients h
           old.map (Fin.cons 0) ++ old.map (Fin.cons 1)

@[simp] theorem length_coefficients (h : ℕ) : (coefficients h).length=2^h := by
  induction h with
  | zero => rfl
  | succ h ih => simp [coefficients,ih,pow_succ,Nat.mul_two]

/-- Count list-constructor visits during the two maps and the append in
`coefficients`. Each half has exactly the old length. -/
def coefficientListVisits : (h : ℕ) → ℕ
  | 0 => 1
  | h+1 => coefficientListVisits h + 3*2^h

theorem coefficientListVisits_succ (h : ℕ) : coefficientListVisits (h+1) =
    coefficientListVisits h + 3*(coefficients h).length := by simp [coefficientListVisits]

theorem coefficientListVisits_add_two (h : ℕ) : coefficientListVisits h+2=3*2^h := by
  induction h with
  | zero => rfl
  | succ h ih => simp only [coefficientListVisits,pow_succ]; omega

theorem mem_coefficients {h : ℕ} (c : Bits h) : c ∈ coefficients h := by
  induction h with
  | zero => simp [coefficients,Subsingleton.elim c Fin.elim0]
  | succ h ih =>
    have two : ∀ z : ZMod 2,z=0 ∨ z=1 := by decide
    rcases two (c 0) with first | first
    · apply List.mem_append_left
      exact List.mem_map.mpr ⟨Fin.tail c,ih _,by rw [←first,Fin.cons_self_tail]⟩
    · apply List.mem_append_right
      exact List.mem_map.mpr ⟨Fin.tail c,ih _,by rw [←first,Fin.cons_self_tail]⟩

/-- Compute one bit of a binary linear combination, counting each field
multiplication and addition. -/
def combineCoordinate {k : ℕ} : (h : ℕ) → (Fin h → Bits k) → Bits h → Fin k → ZMod 2 × ℕ
  | 0,_,_,_ => (0,0)
  | h+1,rows,c,b =>
    let rest := combineCoordinate h (Fin.tail rows) (Fin.tail c) b
    (c 0*rows 0 b+rest.1,rest.2+2)

theorem combineCoordinate_spec {k h : ℕ} (rows : Fin h → Bits k) (c : Bits h) (b : Fin k) :
    (combineCoordinate h rows c b).1=∑ a,c a*rows a b := by
  induction h with
  | zero => simp [combineCoordinate]
  | succ h ih => rw [Fin.sum_univ_succ]; simp [combineCoordinate,ih,Fin.tail]

theorem combineCoordinate_cost {k h : ℕ} (rows : Fin h → Bits k) (c : Bits h) (b : Fin k) :
    (combineCoordinate h rows c b).2=2*h := by
  induction h with
  | zero => rfl
  | succ h ih => simp [combineCoordinate,ih,Nat.mul_succ]

/-- Encode output bits little-endian, charging one doubling and one addition
per bit. The supplied bit computations are each evaluated once. -/
def packCosted : (k : ℕ) → (Fin k → ZMod 2 × ℕ) → Fin (2^k) × ℕ
  | 0,_ => (⟨0,by decide⟩,0)
  | k+1,f =>
    let low := f 0
    let rest := packCosted k (Fin.tail f)
    (⟨(low.1 : Fin 2).val + 2*rest.1.val,by
      have bound (a b n : ℕ) (ha : a<2) (hb : b<n) : a+2*b<n*2 := by omega
      rw [pow_succ]
      exact bound ((low.1 : Fin 2).val) rest.1.val _ (low.1 : Fin 2).isLt rest.1.isLt⟩,low.2+rest.2+2)

theorem packCosted_val {k : ℕ} (f : Fin k → ZMod 2 × ℕ) :
    ((packCosted k f).1 : ℕ)=∑ i : Fin k, ((f i).1 : Fin 2).val * 2^i.val := by
  induction k with
  | zero => simp [packCosted]
  | succ k ih =>
    rw [Fin.sum_univ_succ]
    simp only [packCosted,Fin.val_zero,pow_zero,mul_one,Fin.val_succ,pow_succ,ih,Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    dsimp [Fin.tail]
    ring

theorem packCosted_cost {k b : ℕ} (f : Fin k → ZMod 2 × ℕ) (hb : ∀ i,(f i).2=b) :
    (packCosted k f).2=k*(b+2) := by
  induction k with
  | zero => simp [packCosted]
  | succ k ih =>
    change (f 0).2+(packCosted k (Fin.tail f)).2+2=_
    rw [hb,ih (Fin.tail f) (fun i => hb i.succ)]
    ring

def combinationAddress {h k : ℕ} (rows : Fin h → Bits k) (c : Bits h) : Fin (2^k) × ℕ :=
  packCosted k (combineCoordinate h rows c)

theorem combinationAddress_spec {h k : ℕ} (rows : Fin h → Bits k) (c : Bits h) :
    (combinationAddress rows c).1 = finFunctionFinEquiv ((fun b => ∑ a, c a*rows a b) : Bits k) := by
  apply Fin.ext
  simp only [combinationAddress,packCosted_val,combineCoordinate_spec]
  exact (finFunctionFinEquiv_apply (show Fin k → Fin 2 from fun b => ∑ a, c a*rows a b)).symm

theorem combinationAddress_cost {h k : ℕ} (rows : Fin h → Bits k) (c : Bits h) :
    (combinationAddress rows c).2=k*(2*h+2) :=
  packCosted_cost _ (combineCoordinate_cost rows c)

/-- Use one random-access write to a Boolean vector for each combination. -/
def markCombinations {h k : ℕ} (rows : Fin h → Bits k) :
    List (Bits h) → Vector Bool (2^k) → Vector Bool (2^k) × ℕ
  | [],out => (out,0)
  | c::cs,out =>
    let addr := combinationAddress rows c
    let rest := markCombinations rows cs (out.set addr.1.val true addr.1.isLt)
    (rest.1,addr.2+1+rest.2)

theorem markCombinations_spec {h k : ℕ} (rows : Fin h → Bits k) (cs : List (Bits h))
    (out : Vector Bool (2^k)) (i : Fin (2^k)) :
    (markCombinations rows cs out).1[i.val]=true ↔ out[i.val]=true ∨
      ∃ c∈cs,(combinationAddress rows c).1=i := by
  induction cs generalizing out with
  | nil => simp [markCombinations]
  | cons c cs ih =>
    simp only [markCombinations,ih,Vector.getElem_set,List.mem_cons]
    by_cases eqn : (combinationAddress rows c).1=i
    · simp [eqn]
    · have val : (combinationAddress rows c).1.val≠i.val := fun same => eqn (Fin.ext same)
      simp [val,eqn,exists_or,or_and_right]

theorem markCombinations_cost {h k : ℕ} (rows : Fin h → Bits k) (cs : List (Bits h))
    (out : Vector Bool (2^k)) :
    (markCombinations rows cs out).2=cs.length*(k*(2*h+2)+1) := by
  induction cs generalizing out with
  | nil => simp [markCombinations]
  | cons c cs ih =>
    simp only [markCombinations,combinationAddress_cost,ih,List.length_cons]
    ring

def spanBitmap {h k : ℕ} (rows : Fin h → Bits k) : Vector Bool (2^k) × ℕ :=
  let filled := markCombinations rows (coefficients h) (Vector.replicate (2^k) false)
  (filled.1,coefficientListVisits h+2^k+filled.2)

theorem spanBitmap_cost {h k : ℕ} (rows : Fin h → Bits k) :
    (spanBitmap rows).2 = coefficientListVisits h+2^k+2^h*(k*(2*h+2)+1) := by
  simp [spanBitmap,markCombinations_cost]

theorem spanBitmap_spec {h k : ℕ} (rows : Fin h → Bits k) (i : Fin (2^k)) :
    (spanBitmap rows).1[i.val]=true ↔ ∃ c : Bits h,(combinationAddress rows c).1=i := by
  simp [spanBitmap,markCombinations_spec,mem_coefficients]

noncomputable section

private abbrev chart (k : ℕ) := (Pi.basisFun (ZMod 2) (Fin k)).dualBasis.equivFun

/-- The native input consists of the binary coefficient rows already fixed. -/
def storedRows {h k : ℕ} (hk : h<k) (base : Layout k) (a : Fin h) : Bits k :=
  chart k (rowFunctional base (a.castLE hk.le))

theorem stored_address {h k : ℕ} (hk : h<k) (base : Layout k) (c : Bits h) :
    (combinationAddress (storedRows hk base) c).1 =
      rowIndex k (∑ a : Fin h,c a • rowFunctional base (a.castLE hk.le)) := by
  rw [combinationAddress_spec]
  change finFunctionFinEquiv _ = finFunctionFinEquiv (chart k _)
  apply congrArg (fun f : Bits k => finFunctionFinEquiv f)
  funext b
  simp [storedRows,map_sum,map_smul,Finset.sum_apply]

theorem spanBitmap_legal {h k : ℕ} (hk : h<k) (base : Layout k) (i : Fin (2^k)) :
    (spanBitmap (storedRows hk base)).1[i.val]=false ↔ i∈legalMenu hk base := by
  have marked : (spanBitmap (storedRows hk base)).1[i.val]=true ↔
      (rowIndex k).symm i ∈ Submodule.span (ZMod 2)
        (Set.range fun a : Fin h => rowFunctional base (a.castLE hk.le)) := by
    rw [spanBitmap_spec,Submodule.mem_span_range_iff_exists_fun (ZMod 2)]
    apply exists_congr
    intro c
    rw [stored_address]
    exact (rowIndex k).eq_symm_apply.symm
  simp only [legalMenu,Finset.mem_filter,Finset.mem_univ,true_and,←marked]
  cases (spanBitmap (storedRows hk base)).1[i.val] <;> simp

end
end Hierarchy.DescentGL

end OAI
