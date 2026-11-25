import OAI.Computability.NearSquareRoot.InterchangeROMRepairPhysical
import OAI.Computability.NearSquareRoot.InterchangeROMProgram

/-! # The shared finite bank script for selected ground-field repair

An instruction parks its first `k` rows and applies a leaf to the remaining bank.
A parked predictor or check row is read again at its original address. Only the
active suffix participates in a rectangle move or a spectral sweep.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeROMRepair.Physical

open Matrix

inductive Leaf
  | duplicate | stage | extract | forward | correct | backward | restore | copyCube | finish
  deriving DecidableEq, Repr

abbrev Step := ℕ × Leaf

/-- The nonzero prefix counts refer to saved data rows. Label is the outer
index and the ground coefficient lane is the inner index within each bank. -/
def steps (n d : ℕ) : List Step :=
  [(0,.duplicate)] ++ List.replicate d (n,.stage) ++
  [(0,.extract),(n,.forward),(n,.correct),(n,.backward),(0,.restore)] ++
  List.replicate d (2*n,.stage) ++ [(0,.copyCube)] ++
  List.replicate (2*d) (3*n,.stage) ++ [(0,.finish)]

def applyStep {E : Type} (leaf : Leaf → List E → List E) (bank : List E) (s : Step) : List E :=
  bank.take s.1 ++ leaf s.2 (bank.drop s.1)

def runSteps {E : Type} (leaf : Leaf → List E → List E) (s : List Step) (bank : List E) : List E :=
  s.foldl (applyStep leaf) bank

theorem run_append {E : Type} (leaf : Leaf → List E → List E) (a b : List Step) (bank : List E) :
    runSteps leaf (a++b) bank = runSteps leaf b (runSteps leaf a bank) :=
  List.foldl_append

theorem active_step {E : Type} (leaf : Leaf → List E → List E) (b : Leaf) (ys xs : List E) :
    applyStep leaf (ys ++ xs) (ys.length,b) = ys ++ leaf b xs := by
  simp [applyStep]

theorem active_iterate {E A : Type} (leaf : Leaf → List E → List E) (b : Leaf) (enc : A → List E)
    (f : A → A) (h : ∀ x, leaf b (enc x) = enc (f x))
    (ys : List E) (k : ℕ) (x : A) :
    runSteps leaf (List.replicate k (ys.length,b)) (ys ++ enc x) = ys ++ enc (f^[k] x) := by
  induction k generalizing x with
  | zero => simp [runSteps]
  | succ k ih =>
    rw [List.replicate_succ]
    change runSteps leaf _ (applyStep leaf _ _) = _
    rw [active_step,h,ih,Function.iterate_succ_apply]

/-- The physical functions realized by a fixed set of leaves on a single
layout and payload. The row encoder includes the entire row at all addresses. -/
structure LeafSemantics {E R V U L X : Type} [Field R] [Fintype V] [Fintype U] {m : ℕ}
    (leaf : Leaf → List E → List E) (t : Spec R V U m) (half : R)
    (tag : X → Fin m → Bool) (fw bw : (X → R) → X → R)
    (advance : Bank R L X V → Bank R L X V)
    (wide : Bank R L X V → List E) (short : Bank R L X U → List E) : Prop where
  duplicate x : leaf .duplicate (wide x) = wide x ++ wide x
  stage x : leaf .stage (wide x) = wide (advance x)
  extract x y : leaf .extract (wide x ++ wide y) =
    wide y ++ (short (gather t.extract y) ++ short (gather t.extract x))
  forward a b : leaf .forward (short a ++ short b) = short (sweep fw a) ++ short (sweep fw b)
  correct a b : leaf .correct (short a ++ short b) =
    short (applyTag t tag false a b) ++ short (applyTag t tag true a b)
  backward a b : leaf .backward (short a ++ short b) = short (sweep bw a) ++ short (sweep bw b)
  restore u v w : leaf .restore (wide u ++ (short v ++ short w)) =
    (wide u ++ wide (gather t.restore w)) ++ wide (gather t.restore v)
  copyCube u v w : leaf .copyCube ((wide u ++ wide v) ++ wide w) =
    ((wide u ++ wide v) ++ wide w) ++ wide u
  finish u v w c : leaf .finish (((wide u ++ wide v) ++ wide w) ++ wide c) =
    wide (u - half • (c-u) - w + v)

variable {E R V U L X : Type} [Field R] [Fintype V] [Fintype U] {m : ℕ}
    {leaf : Leaf → List E → List E} {t : Spec R V U m} {half : R}
    {tag : X → Fin m → Bool} {fw bw : (X → R) → X → R}
    {advance : Bank R L X V → Bank R L X V}
    {wide : Bank R L X V → List E} {short : Bank R L X U → List E}

/-- The schedule reuses the first predictor for both the check projection and
the cubic term, then invokes the fourth predictor on the first restored block. -/
theorem run_steps (h : LeafSemantics leaf t half tag fw bw advance wide short)
    (n : ℕ) (hw : ∀ x, (wide x).length = n) (d : ℕ) (x : Bank R L X V) :
    runSteps leaf (steps n d) (wide x) =
      wide (schedule t half tag fw bw (advance^[d]) x) := by
  have rep {n' : ℕ} (u : List E) (l : u.length = n') (k : ℕ) (v : Bank R L X V) :
      (List.replicate k (n',.stage)).foldl (applyStep leaf) (u ++ wide v) = u ++ wide (advance^[k] v) := by
    subst n'
    exact active_iterate leaf .stage wide advance h.stage u k v
  have two (y z : Bank R L X V) : (wide y ++ wide z).length = 2*n := by simp [hw]; omega
  have three (y z w : Bank R L X V) : ((wide y ++ wide z) ++ wide w).length = 3*n := by simp [hw]; omega
  have bare (b : Leaf) (v : List E) : applyStep leaf v (0,b) = leaf b v := by simp [applyStep]
  have kept (b : Leaf) (y : Bank R L X V) (v : List E) :
      applyStep leaf (wide y ++ v) (n,b) = wide y ++ leaf b v := by
    rw [← hw y]; apply active_step
  simp only [steps,run_append]
  simp only [runSteps,List.foldl_cons,List.foldl_nil,bare,h.duplicate]
  rw [rep _ (hw x)]
  simp only [h.extract,kept,h.forward,h.correct,h.backward,h.restore]
  rw [rep _ (two _ _),h.copyCube,rep _ (three _ _ _),h.finish]
  simp only [schedule,two_mul,Function.iterate_add_apply]

/-- Local tables have zero recursive charge. Each conversion traverses the
two check banks, with one selected-field call per lane and field. -/
def price (stage checks m : ℕ) (s : Step) : ℕ :=
  match s.2 with
  | .stage => stage
  | .forward | .backward => 2 * checks * m
  | _ => 0

theorem total_price (n d stage checks m : ℕ) :
    ((steps n d).map (price stage checks m)).sum = 4*d*stage + 4*checks*m := by
  simp [steps,price,List.sum_replicate]
  ring

end InterchangeROMRepair.Physical

end NearSquareRoot
end Computability
end OAI
