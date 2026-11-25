import OAI.Computability.NearSquareRoot.InterchangeRepairProgram
import OAI.Computability.NearSquareRoot.InterchangeBankRun
import OAI.Computability.NearSquareRoot.InterchangePayloadBank

/-!
# Charged bank execution of the interchange repair

Fixed finite banks can be retained across a paid operation and combined by
ordinary aligned scans. This permits reuse of the first prediction and of both
outputs of the check-row table throughout the Hermite correction.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

noncomputable section

namespace Interchange.RepairRun

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip
  IntegerMultiplication.Loom InterchangeBank RepairSchedule SwapRepair
  OAI.LinearAlgebra.FiniteFourier Matrix

variable {I Y E A B C : Type} {X : I → Type} {r : Regime I}
  {N l : I → ℕ} {job : Job Y} {zone : I → Y → Prop}

abbrev Values (X : I → Type) (A E : Type) := (i : I) → A → X i → E
abbrev Cell (X : I → Type) (E : Type) := (i : I) → (X i → E) → Tree

def render (cell : Cell X E) (bank : Series A) (x : Values X A E) (i : I) : Tree :=
  stripe bank (fun a => cell i (x i a))

/-- Requirements on individual rows and aligned finite tables. -/
structure Store (r : Regime I) (N l : I → ℕ) (cell : Cell X E) : Prop where
  positive : ∀ i, 1 ≤ N i
  live (x : (i : I) → X i → E) : Alive r N l (fun i => cell i (x i))
  table {A B : Type} [Fintype A] [Fintype B] [Nonempty A] (a : Series A) (b : Series B)
      (x : Values X A E) (f : (A → E) → B → E) :
    Drive r N l (render cell a x) (render cell b (fun i t k => f (fun j => x i j k) t))

theorem scalarStore [Finite E] (points : (i : I) → Series (X i)) (st : Station r points)
    (symbol : E → Tree) (hs : Function.Injective symbol) :
    Store r (fun i => (points i).count) l (fun i v => stripe (points i) (symbol ∘ v)) where
  positive := st.1
  live x := (finite_manifest symbol x).lives st
  table a b x f := InterchangeBank.table points st a b symbol symbol hs x f

/-- A complete variable-length payload stays together in each physical
record. An occupied source row supplies all payload boundaries for the table. -/
theorem payloadStore [Finite E] {D : I → Type} (points : (i : I) → Series (X i))
    (st : Station r points) (payload : (i : I) → Series (D i))
    (bound : ∀ i, (payload i).count ≤ l i) (symbol : E → Tree) (hs : Function.Injective symbol) :
    Store r (fun i => (points i).count) l (X := fun i => X i × D i)
      (fun i v => stripe (points i) fun x => stripe (payload i) fun d => symbol (v (x,d))) where
  positive := st.1
  live x := (InterchangePayloadBank.manifest payload symbol x bound).lives st
  table a b x f := InterchangePayloadBank.table_nonempty points st payload bound a b symbol symbol hs x f

variable {cell : Cell X E}
variable (store : Store r N l cell)
include store in
theorem liveBank (sa : Series A) (x : Values X A E) : Alive r N l (render cell sa x) :=
  Fatigue.entire sa _ store.positive (fun a => store.live (fun i => x i a))

/-- The caller chooses the order of both banks independently. -/
def Runs (job : Job Y) (r : Regime I) (N l : I → ℕ) (zone : I → Y → Prop)
    (cell : Cell X E) (k : ℕ) (x : Values X A E) (y : Values X B E) : Prop :=
  ∀ sa : Series A, ∀ sb : Series B,
    Hopto job r N l zone k (together r.header (render cell sa x)) (render cell sb y)

private def order (A : Type) [Fintype A] : Series A :=
  ⟨Finset.univ.toList, Finset.nodup_toList _, by simp⟩

variable {x : Values X A E} {y : Values X B E} {z : Values X C E} {p q : ℕ}

include store

theorem runs_table [Fintype A] [Fintype B] [Nonempty A] (x : Values X A E) (f : (A → E) → B → E) :
    Runs job r N l zone cell 0 x (fun i t k => f (fun j => x i j k) t) :=
  fun sa sb => Hopto.tarry (store.table sa sb x f)

theorem Runs.seq [Fintype B] (h : Runs job r N l zone cell p x y)
    (g : Runs job r N l zone cell q y z) :
    Runs job r N l zone cell (p+q) x z := by
  intro sa sc
  simpa only [Nat.cast_add] using sequence store.positive (liveBank store sa x)
    (liveBank store (order B) y) (h sa (order B)) (g (order B) sc)

omit store in
def both (x : Values X A E) (y : Values X B E) : Values X (A ⊕ B) E :=
  fun i => Sum.elim (x i) (y i)

private theorem merge (sa : Series A) (sb : Series B) (sc : Series (A ⊕ B))
    (x : Values X A E) (y : Values X B E) :
    Rip r N l (together (render cell sa x) (render cell sb y)) (render cell sc (both x y)) := by
  have live := Rip.alivePair (liveBank store sa x) (liveBank store sb y)
  apply Fatigue.dry sc _ live
  intro t
  cases t with
  | inl a => exact Fatigue.drill sa _ (Rip.split live).1 a
  | inr b => exact Fatigue.drill sb _ (Rip.split live).2 b

theorem Runs.fork [Fintype B] [Fintype C] (h : Runs job r N l zone cell p x y)
    (g : Runs job r N l zone cell q x z) :
    Runs job r N l zone cell (p+q) x (both y z) := by
  intro sa sbc
  have l₀ := liveBank store sa x
  have l₁ := liveBank store (order B) y
  have l₂ := liveBank store (order C) z
  have h' := (h sa (order B)).doubleg (g sa (order C))
    (Rip.alivePair (Drive.started store.positive) l₀) l₁ l₂
  simpa only [Nat.cast_add] using h'.afterTask (merge store (order B) (order C) sbc y z)

theorem empty_target [IsEmpty B] (x : Values X A E) (y : Values X B E) :
    Runs job r N l zone cell 0 x y := by
  intro sa sb
  apply Hopto.tarry
  exact Fatigue.dry sb _ (Rip.alivePair (Drive.started store.positive) (liveBank store sa x))
    (fun b => isEmptyElim b)

theorem Runs.keep [Fintype A] [Fintype B] (h : Runs job r N l zone cell p x y) :
    Runs job r N l zone cell p x (both x y) := by
  have id' : Runs job r N l zone cell 0 x x := by
    by_cases hA : Nonempty A
    · exact runs_table store x (fun u a => u a)
    · have : IsEmpty A := not_nonempty_iff.mp hA
      exact empty_target store x x
  simpa only [Nat.zero_add] using id'.fork store h

theorem runs_rows [Fintype A] (F : (i : I) → (X i → E) → X i → E) (x : Values X A E)
    (step : ∀ v : (i : I) → X i → E, Hopto job r N l zone p
      (together r.header (fun i => cell i (v i))) (fun i => cell i (F i (v i)))) :
    Runs job r N l zone cell (Fintype.card A * p) x (fun i a => F i (x i a)) := by
  intro sa sb
  have h := collect store.positive sa sb (fun i a => cell i (x i a))
    (fun i a => cell i (F i (x i a))) id (fun _ => p)
    (fun a => store.live (fun i => x i a)) (fun a => store.live (fun i => F i (x i a)))
    (fun a => step (fun i => x i a))
  change Hopto job r N l zone _ (together r.header (stackRun (fun _ => sa) (fun i a => cell i (x i a))))
    (stackRun (fun _ => sb) (fun i a => cell i (F i (x i a))))
  simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.cast_mul] using h

omit store

variable {K L : Type} [Field K] [Fintype L] {m : ℕ}
variable {enc : Cell X (Coeff K m)} (machine : Store r N l enc)

abbrev Rows (L : Type) (n : ℕ) := L × Fin n

/-- The physical register for row number `k` of label `w` is the pair `(w,k)`. -/
def flatten {n : ℕ} (x : (i : I) → Data K L (X i) n m) : Values X (Rows L n) (Coeff K m) :=
  fun i t => x i t.1 t.2

include machine

/-- The shared check table is an ordinary finite lookup controlled by the
computed mask at that address. -/
def Tagged (job : Job Y) (r : Regime I) (N l : I → ℕ) (zone : I → Y → Prop)
    (enc : Cell X (Coeff K m)) (tag : (i : I) → X i → Pattern m) : Prop :=
  ∀ {S U : Type} [Fintype S] [Fintype U] [Nonempty S] (v : Values X S (Coeff K m))
    (f : Pattern m → (S → Coeff K m) → U → Coeff K m),
    Runs job r N l zone enc 0 v (fun i t a => f (tag i a) (fun k => v i k a) t)


omit machine in
private theorem bank_rules {E : Type} {cell : RepairRun.Cell X E} (s : RepairRun.Store r N l cell) :
    RepairProgram.Rules (X:=X) (E:=E) (fun {_A _B} price x y => Runs job r N l zone cell price x y) where
  table x f := runs_table s x f
  seq h g := Runs.seq s h g
  fork h g := Runs.fork s h g
  keep h := Runs.keep s h
  empty x y := empty_target s x y

/-- Execute the four predictors and the four check-row sweeps, retaining each
intermediate exactly where its later use requires it. `paid` is the cost of
one complete conversion of one extension row, including its basis components. -/
theorem execute [Nonempty L] (e : Environment K m) (T : Table K m)
    (tag : (i : I) → X i → Pattern m) (mask : Tagged job r N l zone enc tag)
    (F G : (i : I) → (X i → Coeff K m) → X i → Coeff K m)
    (P : (i : I) → Data K L (X i) (width m) m → Data K L (X i) (width m) m)
    (pred paid : ℕ)
    (hp : ∀ x, Runs job r N l zone enc pred (flatten x) (flatten fun i => P i (x i)))
    (hf : ∀ v : (i : I) → X i → Coeff K m, Hopto job r N l zone paid
      (together r.header (fun i => enc i (v i))) (fun i => enc i (F i (v i))))
    (hg : ∀ v : (i : I) → X i → Coeff K m, Hopto job r N l zone paid
      (together r.header (fun i => enc i (v i))) (fun i => enc i (G i (v i))))
    (x : (i : I) → Data K L (X i) (width m) m) :
    Runs job r N l zone enc (4 * pred + 4 * Fintype.card L * checks m * paid)
      (flatten x) (flatten (fun i => schedule e T (tag i) (F i) (G i) (P i) (x i))) := by
  exact RepairProgram.execute (bank_rules machine) e T tag mask F G P pred paid hp
    (fun x => runs_rows machine F x hf) (fun x => runs_rows machine G x hg) x

end Interchange.RepairRun

end

end NearSquareRoot
end Computability
end OAI
