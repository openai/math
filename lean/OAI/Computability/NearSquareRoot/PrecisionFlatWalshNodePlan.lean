import OAI.Computability.NearSquareRoot.PrecisionPlanNode
import OAI.Computability.NearSquareRoot.KernelPassBank
import OAI.Computability.NearSquareRoot.PrecisionFlatWalshNodeIndex
import OAI.Computability.NearSquareRoot.PrecisionFlatWalshKernel

/-! # Restricting a physical row plan to a kernel address fiber

The output at fixed spectator coordinates is the complex extension of
the plan's rational matrix. Sequential and parallel composition use
the same row ordering as the physical interpreter.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

noncomputable section

namespace FlatWalshNode

open IntegerMultiplication Matrix Finset PhysicalWalsh PhysicalWalshNode KernelPass

/-- The rational plan matrix acting on complex-valued entries in its row bank. -/
def complexAt {A i o : ℕ} (p : Plan A i o) (h : ℕ)
    (x : Fin i → Addr A h → ℂ) : Fin o → Addr A h → ℂ :=
  Function.curry (((p.eval h).map (algebraMap ℚ ℂ)).mulVec (Function.uncurry x))

theorem complexAt_rat {A i o : ℕ} (p : Plan A i o) (h : ℕ) (x : Bank A h i) (j : Fin o) (z : Addr A h) :
    complexAt p h (fun b y => (x b y : ℂ)) j z = (p.applyAt h x j z : ℂ) :=
  ((algebraMap ℚ ℂ).map_mulVec (p.eval h) (Function.uncurry x) (j,z)).symm

private theorem seqAt {A i j o h : ℕ} (p : Plan A j o) (q : Plan A i j) (x : Fin i → Addr A h → ℂ) :
    complexAt (p.seq q) h x = complexAt p h (complexAt q h x) := by
  simp [complexAt, Plan.eval, Matrix.map_mul, Matrix.mulVec_mulVec]

private theorem parallelAt {A i j o v h : ℕ} (p : Plan A i o) (q : Plan A j v)
    (x : Fin i → Addr A h → ℂ) (y : Fin j → Addr A h → ℂ) :
    complexAt (p.parallel q) h (Fin.append x y) = Fin.append (complexAt p h x) (complexAt q h y) := by
  classical
  funext b z
  refine Fin.addCases (fun left => ?_) (fun right => ?_) b <;>
    simp only [complexAt, Plan.eval, directSum, Function.curry_apply, Matrix.mulVec, dotProduct,
      Matrix.map_apply, Fintype.sum_prod_type, Function.uncurry, Fin.append_left, Fin.append_right,
      Fin.addCases_left, Fin.addCases_right] <;>
    rw [Fin.sum_univ_add] <;> simp

private theorem xorTwice {A h : ℕ} (gate : Fin A × Fin A) (x : Addr A h) :
    xorColumn gate ∘ (xorColumn gate ∘ x) = x := by
  funext t i b
  by_cases hgate : gate.1 ≠ gate.2
  · by_cases htarget : i = gate.1
    · subst i
      have he (v : ZMod 2) : v+v = 0 := by fin_cases v <;> decide
      simp [Function.comp_def, xorColumn, hgate, hgate.symm, add_assoc, he]
    · simp [xorColumn, htarget]
  · simp [xorColumn,hgate]

private theorem xorAt {A h : ℕ} (gate : Fin A × Fin A) (x : Fin 1 → Addr A h → ℂ)
    (b : Fin 1) (y : Addr A h) :
    complexAt (.xor gate) h x b y = x 0 (xorColumn gate ∘ y) := by
  have eqv (v : Addr A h) : y = xorColumn gate ∘ v ↔ v = xorColumn gate ∘ y := by
    constructor <;> rintro rfl <;> exact (xorTwice gate _).symm
  classical
  simp [complexAt,Plan.eval,Matrix.map,Matrix.mulVec,dotProduct,Fintype.sum_prod_type,eqv,apply_ite,ite_mul]

/-- A family of address locations for which physical lookup, routing, and
the recursive child preserve the fixed spectators. -/
theorem idealPlanFiber {a W : ℕ} (s : Shape) (h : ℕ)
    (loc : Addr (a+1) h → ℕ) (child : Fin (a+1) → Shape → IdealRow → IdealRow)
    (route : ∀ gate z, xorIndex a gate s (loc z) = loc (xorColumn gate ∘ z))
    (lookup : ∀ {q} (test : Column (a+1) → Fin q → ZMod 2) z,
      KernelScaleBank.signature (coords a W) test s (loc z) = ∑ t, test (z t))
    (rec : ∀ j (v : IdealRow) z, child j s v (loc z) =
      ∑ t : Addr (a+1) h, (↑(∏ n, childEntry j (z n) (t n)) : ℂ) * v (loc t))
    {i o : ℕ} (p : Plan (a+1) i o) (x : Fin i → IdealRow) :
    (fun j z => (idealOps a W child).applyPlan p s x j (loc z)) =
      complexAt p h (fun j z => x j (loc z)) := by
  classical
  induction p with
  | mix c =>
    funext b y
    simp [Ops.applyPlan,idealOps,complexAt,Plan.eval,Matrix.map,Matrix.mulVec,dotProduct,Fintype.sum_prod_type,apply_ite,ite_mul]
  | xor g =>
    funext b y
    simp [Ops.applyPlan,idealOps,route,xorAt]
  | scale q test table =>
    funext b y
    simp [Ops.applyPlan,idealOps,lookup,complexAt,Plan.eval,Matrix.map,Matrix.mulVec,dotProduct,Fintype.sum_prod_type,apply_ite,ite_mul]
  | child j =>
    funext b y
    simp [Ops.applyPlan,idealOps,rec,complexAt,Plan.eval,Matrix.map,Matrix.mulVec,dotProduct,Fintype.sum_prod_type]
  | seq p q ihp ihq =>
    rw [seqAt, ← ihq]
    exact ihp _
  | @parallel i j o v p q ihp ihq =>
    let u := fun b z => x b (loc z)
    let xl := fun b : Fin i => x (b.castAdd j)
    let xr := fun b : Fin j => x (b.natAdd i)
    have hs : Fin.append (fun b z => xl b (loc z)) (fun b z => xr b (loc z)) = u :=
      Fin.append_castAdd_natAdd (f := u)
    change _ = complexAt (p.parallel q) h u
    rw [← hs, parallelAt]
    funext b z
    refine Fin.addCases (fun left => ?_) (fun right => ?_) b <;>
      simp only [Ops.applyPlan, Fin.append_left, Fin.append_right]
    · exact congrFun (congrFun (ihp xl) left) z
    · exact congrFun (congrFun (ihq xr) right) z

/-- At a physical lane ordinal the scale signature and XOR routing already
preserve the spectators. Only the recursive child's local equation is needed. -/
theorem plan_on_rowPos {a W : ℕ} (s : Shape) (g : ℕ) (t : Fin s.suff)
    (child : Fin (a+1) → Shape → IdealRow → IdealRow)
    (rec : ∀ axis v z, child axis s v (rowPos a s g z t) =
      ∑ u : NodeAddress a s, (↑(∏ n, childEntry axis (z n) (u n)) : ℂ) * v (rowPos a s g u t))
    {i o : ℕ} (p : Plan (a+1) i o) (x : Fin i → IdealRow) :
    (fun j z => (idealOps a W child).applyPlan p s x j (rowPos a s g z t)) =
      complexAt p ((a+1)^(s.level-1)) (fun j z => x j (rowPos a s g z t)) :=
  idealPlanFiber s _ _ child (fun gate u => xorIndex_rowPos a gate s g u t)
    (fun test z => by simp only [KernelScaleBank.signature, coord_rowPos]; rfl) rec p x

/-- A certified plan performs an independent full active Walsh transform
in each physical lane and spectator fiber. -/
theorem correct_on_rowPos {a W : ℕ} (s : Shape) (g : ℕ) (t : Fin s.suff)
    (child : Fin (a+1) → Shape → IdealRow → IdealRow)
    (rec : ∀ axis v z, child axis s v (rowPos a s g z t) =
      ∑ u : NodeAddress a s, (↑(∏ n, childEntry axis (z n) (u n)) : ℂ) * v (rowPos a s g u t))
    (p : Plan (a+1) W W) (hp : Correct p) (x : Fin W → IdealRow) (j : Fin W) (z : NodeAddress a s) :
    (idealOps a W child).applyPlan p s x j (rowPos a s g z t) =
      ∑ u : NodeAddress a s, BoxFin.flatWalsh Finset.univ (KernelScaleLayout.rank z) (KernelScaleLayout.rank u) *
        x j (rowPos a s g u t) := by
  classical
  have hr := congrFun (congrFun (plan_on_rowPos (W := W) s g t child rec p x) j) z
  change _ = complexAt p _ _ _ _ at hr
  rw [hr]
  rw [complexAt, hp _]
  simp [target, Matrix.map, Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
    apply_ite, ite_mul]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  apply Finset.sum_congr rfl
  intro u _
  rw [← FlatWalshKernel.packed_entry]
  push_cast
  rfl

end FlatWalshNode

end

end NearSquareRoot
end Computability
end OAI
