import OAI.Computability.NearSquareRoot.InterchangeRepairRun
import OAI.Computability.NearSquareRoot.InterchangePredictRun

/-!
# Packing extension-valued rows from ground-alphabet streams

A grouped row is a finite stripe of ground-field streams. Flattening or
reassembling many grouped rows reads their finite register indices using fixed
scans. The same charged program on the flat bank therefore serves callers with
any ordering of grouped rows.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

noncomputable section
namespace Interchange.RepairRun

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip
  IntegerMultiplication.Loom InterchangeBank SwapRepair

variable {I Y K E D A B S U L T : Type} {X : I → Type} {r : Regime I}
  {N l : I → ℕ} {job : Job Y} {zone : I → Y → Prop} {cell : Cell X K}


/-- A physical scalar stream has one contiguous payload for every record. -/
def payloadCell {X V : I → Type} (records : (i : I) → Series (X i)) (payload : (i : I) → Series (V i))
    (symbol : K → Tree) : Cell (fun i => X i × V i) K :=
  fun i v => stripe (records i) fun k => stripe (payload i) fun d => symbol (v (k,d))

def groupCell (coord : E ≃ (D → K)) (basis : Series D) (cell : Cell X K) : Cell X E :=
  fun i x => stripe basis (fun d => cell i (fun k => coord (x k) d))

def lanesAt (coord : E ≃ (D → K)) (index : S → A × D) (x : Values X A E) :
    Values X S K := fun i s k => coord (x i (index s).1 k) (index s).2

variable (store : Store r N l cell) (coord : E ≃ (D → K)) (basis : Series D)

include store in
theorem liveGroup (x : (i : I) → X i → E) :
    Alive r N l (fun i => groupCell coord basis cell i (x i)) :=
  Fatigue.entire basis _ store.positive (fun d => store.live (fun i k => coord (x i k) d))

include store in
theorem flattenGroup (a : Series A) (s : Series S) (index : S → A × D) (x : Values X A E) :
    Rip r N l (render (groupCell coord basis cell) a x) (render cell s (lanesAt coord index x)) := by
  have live := Fatigue.entire a _ store.positive (fun t => liveGroup store coord basis (fun i => x i t))
  apply Fatigue.dry s _ live
  intro t
  exact Fatigue.drill basis _ (Fatigue.drill a _ live (index t).1) (index t).2

include store in
theorem gatherGroup (a : Series A) (s : Series S) (index : S ≃ A × D) (x : Values X A E) :
    Rip r N l (render cell s (lanesAt coord index x)) (render (groupCell coord basis cell) a x) := by
  have live := liveBank store s (lanesAt coord index x)
  apply Fatigue.dry a _ live
  intro t
  apply Fatigue.dry basis _ live
  intro d
  have h := Fatigue.drill s (fun i t => cell i (lanesAt coord index x i t)) live (index.symm (t,d))
  have read (i : I) : lanesAt coord index x i (index.symm (t,d)) = fun k => coord (x i t k) d := by
    funext k
    dsimp only [lanesAt]
    rw [index.apply_symm_apply]
  simpa only [read] using h

include store in
theorem groupRuns {p : ℕ} (s : Series S) (u : Series U)
    (input : S ≃ A × D) (output : U ≃ B × D) (x : Values X A E) (y : Values X B E)
    (h : Hopto job r N l zone p (together r.header (render cell s (lanesAt coord input x)))
      (render cell u (lanesAt coord output y))) :
    Runs job r N l zone (groupCell coord basis cell) p x y := by
  intro sa sb
  exact (h.preceded ((flattenGroup store coord basis sa s input x).right (Drive.started store.positive))).afterTask
    (gatherGroup store coord basis sb u output y)

include store in
theorem groupTagged [Fintype A] [Fintype B] [Fintype D]
    (tag : (i : I) → X i → T)
    (exec : ∀ (sa : Series (A × D)) (sb : Series (B × D))
      (x : Values X (A × D) K) (f : T → (A × D → K) → B × D → K),
      Drive r N l (render cell sa x) (render cell sb (fun i b k => f (tag i k) (fun a => x i a k) b)))
    (sa : Series A) (sb : Series B) (x : Values X A E) (f : T → (A → E) → B → E) :
    Drive r N l (render (groupCell coord basis cell) sa x)
      (render (groupCell coord basis cell) sb (fun i b k => f (tag i k) (fun a => x i a k) b)) := by
  let y : Values X B E := fun i b k => f (tag i k) (fun a => x i a k) b
  let table (t : T) (v : A × D → K) (b : B × D) :=
    coord (f t (fun a => coord.symm (fun d => v (a,d))) b.1) b.2
  have done := exec (sa.cart basis) (sb.cart basis) (lanesAt coord id x) table
  have hy :
      (fun i b k => table (tag i k) (fun a => lanesAt coord id x i a k) b) = lanesAt coord id y := by
    funext i b k
    simp only [table, lanesAt, id_eq, Equiv.symm_apply_apply, y]
  rw [hy] at done
  exact (((flattenGroup store coord basis sa (sa.cart basis) id x).right (Drive.started store.positive)).chain
    done).chain (gatherGroup store coord basis sb (sb.cart basis) (Equiv.refl _) y)

include store in
theorem groupStore [Fintype D] [Nonempty D] : Store r N l (groupCell coord basis cell) where
  positive := store.positive
  live := liveGroup store coord basis
  table sa sb x f :=
    groupTagged store coord basis (fun _ _ => ()) (fun a b z g => store.table a b z (g ()))
      sa sb x (fun _ => f)

include store in
theorem groupStep [Fintype D] {p : ℕ} (x y : (i : I) → X i → E)
    (step : ∀ d, Hopto job r N l zone p
      (together r.header (fun i => cell i (fun k => coord (x i k) d)))
      (fun i => cell i (fun k => coord (y i k) d))) :
    Hopto job r N l zone ((Fintype.card D * p : ℕ) : ℤ)
      (together r.header (fun i => groupCell coord basis cell i (x i)))
      (fun i => groupCell coord basis cell i (y i)) := by
  have h := collect store.positive basis basis (fun i d => cell i (fun k => coord (x i k) d))
    (fun i d => cell i (fun k => coord (y i k) d)) id (fun _ => p)
    (fun d => store.live (fun i k => coord (x i k) d))
    (fun d => store.live (fun i k => coord (y i k) d)) step
  change Hopto job r N l zone _ (together r.header
    (stackRun (fun _ => basis) (fun i d => cell i (fun k => coord (x i k) d))))
    (stackRun (fun _ => basis) (fun i d => cell i (fun k => coord (y i k) d)))
  simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.cast_mul] using h


include store in
/-- A physical single-row certificate may present its basis streams as a flat
bank indexed by a dummy register and its component. -/
theorem oneGroupStep {p : ℕ} (s : Series (Unit × D)) (x y : (i : I) → X i → E)
    (h : Hopto job r N l zone p
      (together r.header (render cell s (fun i t k => coord (x i k) t.2)))
      (render cell s (fun i t k => coord (y i k) t.2))) :
    Hopto job r N l zone p (together r.header (fun i => groupCell coord basis cell i (x i)))
      (fun i => groupCell coord basis cell i (y i)) := by
  have source := liveGroup store coord basis x
  have get : Rip r N l (fun i => groupCell coord basis cell i (x i))
      (render cell s (fun i t k => coord (x i k) t.2)) := by
    apply Fatigue.dry s _ source
    intro t
    exact Fatigue.drill basis _ source t.2
  have out := liveBank store s (fun i (t : Unit × D) k => coord (y i k) t.2)
  have put : Rip r N l (render cell s (fun i t k => coord (y i k) t.2))
      (fun i => groupCell coord basis cell i (y i)) := by
    apply Fatigue.dry basis _ out
    intro d
    exact Fatigue.drill s _ out ((), d)
  exact (h.preceded (get.right (Drive.started store.positive))).afterTask put

/-- The predictor places register and basis first, followed by the label. -/
def predictorIndex (L : Type) (s m : ℕ) :
    (Fin s × BasisIndex m) × L ≃ (L × Fin s) × BasisIndex m where
  toFun t := ((t.2,t.1.1),t.1.2)
  invFun t := ((t.1.2,t.2),t.1.1)
  left_inv _ := rfl
  right_inv _ := rfl

include store in
theorem predictorRuns [Field K] {s m p : ℕ}
    (basis : Series (BasisIndex m)) (flat : Series ((Fin s × BasisIndex m) × L))
    (x y : (i : I) → RepairSchedule.Data K L (X i) s m)
    (h : Hopto job r N l zone p
      (together r.header (render cell flat (RepairSchedule.streams x)))
      (render cell flat (RepairSchedule.streams y))) :
    Runs job r N l zone (groupCell (components K m).toEquiv basis cell) p
      (fun i (t : L × Fin s) => x i t.1 t.2) (fun i (t : L × Fin s) => y i t.1 t.2) :=
  groupRuns store (components K m).toEquiv basis flat flat (predictorIndex L s m) (predictorIndex L s m)
    (fun i (t : L × Fin s) => x i t.1 t.2) (fun i (t : L × Fin s) => y i t.1 t.2) h


include store in
/-- Return a grouped computation to the original independent scalar streams. -/
theorem ungroupRuns [Field K] {s m p : ℕ}
    (basis : Series (BasisIndex m)) (group : Series (L × Fin s))
    (flat : Series ((Fin s × BasisIndex m) × L))
    (x y : (i : I) → RepairSchedule.Data K L (X i) s m)
    (h : Runs job r N l zone (groupCell (components K m).toEquiv basis cell) p
      (fun i (t : L × Fin s) => x i t.1 t.2) (fun i (t : L × Fin s) => y i t.1 t.2)) :
    Hopto job r N l zone p (together r.header (render cell flat (RepairSchedule.streams x)))
      (render cell flat (RepairSchedule.streams y)) := by
  have get := gatherGroup store (components K m).toEquiv basis group flat (predictorIndex L s m)
    (fun i (t : L × Fin s) => x i t.1 t.2)
  have put := flattenGroup store (components K m).toEquiv basis group flat (predictorIndex L s m)
    (fun i (t : L × Fin s) => y i t.1 t.2)
  exact ((h group group).preceded (get.right (Drive.started store.positive))).afterTask put

end Interchange.RepairRun

end

end NearSquareRoot
end Computability
end OAI
