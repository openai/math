import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fin.Tuple.Basic
import OAI.LinearAlgebra.MatrixExponent.Sphere.Control.Depth
import OAI.LinearAlgebra.MatrixExponent.Sphere.Surface.Accounting
import OAI.LinearAlgebra.MatrixExponent.Sphere.Surface.Cardinality

/-!
# Recording a sequence with few interruptions

It suffices to name the first entry and the position and value just
after each interruption of the deterministic successor rule.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Control
open Finset
open scoped Classical
variable {α : Type} {n k : ℕ} (next : α → α)

def Sparse (f : Fin n → α) (k : ℕ) : Prop :=
  ∃ s : Finset (Fin n), s.card ≤ k ∧
    ∀ i j : Fin n, i.val + 1 = j.val → i ∉ s → f j = next (f i)

private abbrev Log (α : Type) (n k : ℕ) := Fin (k + 1) → Option (Fin n × α)

private def Encodes (a : Log α n k) (f : Fin n → α) : Prop :=
  (∀ s i v, a s = some (i, v) → f i = v) ∧
    ∀ i : Fin n, (∃ s v, a s = some (i, v)) ∨
      ∃ j : Fin n, j.val + 1 = i.val ∧ f i = next (f j)

private theorem Encodes.unique {a : Log α n k} {f g : Fin n → α}
    (h : Encodes next a f) (e : Encodes next a g) : f = g := by
  funext i
  induction hn : i.val using Nat.strong_induction_on generalizing i with
  | h n ih =>
    by_cases named : ∃ s v, a s = some (i, v)
    · obtain ⟨s, v, hv⟩ := named
      exact (h.1 s i v hv).trans (e.1 s i v hv).symm
    obtain ⟨j, hj, hu⟩ := (h.2 i).resolve_left named
    obtain ⟨l, hl, hv⟩ := (e.2 i).resolve_left named
    rw [hu, hv, show l = j from Fin.ext (by omega), ih j.val (by omega) j rfl]

private theorem Sparse.encodes {f : Fin n → α} (h : Sparse next f k) :
    ∃ a : Log α n k, Encodes next a f := by
  obtain ⟨s, hk, h⟩ := h
  let e := s.equivFin
  let pos (i : Fin n) := if hi : i.val + 1 < n then (⟨i.val + 1, hi⟩ : Fin n) else i
  let first := if hn : 0 < n then some (⟨0, hn⟩ : Fin n) else none
  let rest (i : Fin k) :=
    if hi : i.val < s.card then some (pos (e.symm ⟨i.val, hi⟩).val) else none
  let p : Fin (k + 1) → Option (Fin n) := Fin.cons first rest
  refine ⟨fun i => (p i).map (fun j => (j, f j)), ?_, ?_⟩
  · intro a i v ha
    obtain ⟨j, _, h⟩ := Option.map_eq_some_iff.mp ha
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    rfl
  intro i
  have named (j) (hj : p j = some i) :
      ∃ s v, (p s).map (fun j => (j, f j)) = some (i, v) := ⟨j, f i, by simp [hj]⟩
  by_cases hi : i.val = 0
  · apply Or.inl (named 0 ?_)
    simp only [p, Fin.cons_zero, first, dite_eq_left (by omega : 0 < n)]
    exact congrArg some (Fin.ext hi.symm)
  let j : Fin n := ⟨i.val - 1, by omega⟩
  have hj : j.val + 1 = i.val := by dsimp [j]; omega
  by_cases hs : j ∈ s
  · let q := e ⟨j, hs⟩
    refine .inl (named (Fin.castLE hk q).succ ?_)
    have he : pos j = i := by simp [pos, hj]
    simp [p, rest, q, he]
  · exact .inr ⟨j, hj, h j i hj hs⟩

theorem card_sparse [Fintype α] (n k : ℕ) :
    Fintype.card {f : Fin n → α // Sparse next f k} ≤ (n * Fintype.card α + 1) ^ (k + 1) := by
  choose g hg using fun f : {f : Fin n → α // Sparse next f k} => Sparse.encodes next f.property
  have hh : Function.Injective g := by
    intro i j h
    exact Subtype.ext (Encodes.unique next (h ▸ hg i) (hg j))
  simpa [Log] using Fintype.card_le_of_injective g hh

end OAI.LinearAlgebra.MatrixExponent.Sphere.Control
end

/-!
# A uniform local script

The index set and coefficient of each branch are chosen from a region
record. They must work in every larger graph realizing that record.
The domain of hidden-state indices can differ among those graphs.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Surface.Local

open Finset
open scoped Classical
variable {F T V E X J L K N : Type} {r t P g H U M D : ℕ}

def pending (s : Stage F r t T V E X) : Set (V × F) :=
  {q | ∃ u ∈ (s.scene.cell q.1).stations, u.pos = q.2 ∧ ∃ n, u.label.role = .active n}

def Calm (s : Stage F r t T V E X) : Prop :=
  ∀ v u, u ∈ (s.scene.cell v).stations → u.label.role.clock = 0

/-- Every seam traversable within the crossing allowance has its
other endpoint in the region. -/
def Covers (ports : J → List (L × F)) (v : J) : ℕ → Prop
  | 0 => True
  | n + 1 => ∀ p ∈ ports v, ∃ w y, w ≠ v ∧ (p.1, y) ∈ ports w ∧ Covers ports w n

structure Script (F : Type) (r t : ℕ) (J L K N : Type) where
  I : Type
  [finite : Fintype I]
  weight : I → F
  result : I → Record F r t J L K N
  fresh : I → List (K × ℕ)

attribute [instance] Script.finite

def Script.Ordered (h : Script F r t J L K N) (ν : ℕ → K) (n U : ℕ) :=
  ∀ i, n + (h.fresh i).length ≤ U ∧ ∀ j : Fin (h.fresh i).length, ((h.fresh i).get j).1 = ν (n + j.val)

variable [Field F]

structure Update (P g H U : ℕ) (R : Reference J L N V E T X) (β β' : V ⊕ ℕ → K)
    (s q : Stage F r t T V E X) (a : Record F r t J L K N) (fresh : List (K × ℕ)) : Prop where
  reach : s.Reach P g H U q
  valid : q.Valid U
  match' : Matches R β' q a
  outside : Outside (Set.range R.vertex) (Set.range R.edge) R.key s q β β' fresh

def Script.Executes [Fintype V] [Fintype E] (script : Script F r t J L K N) (P g H U : ℕ)
    (R : Reference J L N V E T X) (β : V ⊕ ℕ → K) (s : Stage F r t T V E X)
    (allowed : Set (V × F)) (f : X → F) : Prop :=
  ∃ (q : script.I → Stage F r t T V E X) (γ : script.I → V ⊕ ℕ → K),
    (∀ i, Update P g H U R β (γ i) s (q i) (script.result i) (script.fresh i) ∧
      Calm (q i) ∧ pending (q i) ⊆ allowed) ∧
    ∀ x, f x = ∑ i, script.weight i * (q i).value P x

def Script.Runs (script : Script F r t J L K N) (a : Record F r t J L K N)
    (P g H U M D : ℕ) (v : J) (z : F) : Prop :=
  ∀ {V E T X : Type} [Fintype V] [Fintype E] (R : Reference J L N V E T X)
    (β : V ⊕ ℕ → K) (s : Stage F r t T V E X) (src dst : E → V),
    Matches R β s a → s.Layout src dst g → s.Valid U →
    (∀ y, s.Reach P g H U y → y.Room M D) → Calm s →
    script.Executes P g H U R β s (pending s \ {(R.vertex v, z)}) (s.value P)

end OAI.LinearAlgebra.MatrixExponent.Sphere.Surface.Local
end

/-! # Composition of uniform region scripts -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Surface.Local

open Finset
open scoped Classical
variable {F T V E X J L K N : Type} [Field F] [Fintype E] [Fintype V]
  {r t P g H U M D : ℕ}
variable {R : Reference J L N V E T X} {β β' : V ⊕ ℕ → K}
  {s q : Stage F r t T V E X} {a : Record F r t J L K N}
  {f : X → F} {A : Set (V × F)} {ν : ℕ → K} {n : ℕ}

omit [Fintype V] [Fintype E] in
theorem Update.refl (h : Matches R β s a) (hv : s.Valid U) : Update P g H U R β β s s a [] :=
  ⟨.refl, hv, h, .refl⟩

namespace Script

def pure (a : Record F r t J L K N) : Script F r t J L K N :=
  ⟨Unit, fun _ => 1, fun _ => a, fun _ => []⟩

theorem ordered_pure (a : Record F r t J L K N) (h : n ≤ U) : (pure a).Ordered ν n U :=
  fun _ => ⟨h, fun i => i.elim0⟩

theorem executes_pure (h : Update P g H U R β β' s q a []) (hc : Calm q) (hp : pending q ⊆ A) :
    (pure a).Executes P g H U R β s A (q.value P) :=
  ⟨fun _ => q, fun _ => β', fun _ => ⟨h, hc, hp⟩, fun x => by change _ = ∑ _ : Unit, (1 : F) * q.value P x; simp⟩

variable {w : Script F r t J L K N}

def times (w : Script F r t J L K N) (k : F) := {w with weight := fun i => k * w.weight i}

theorem Executes.times (h : w.Executes P g H U R β s A f) (k : F) :
    (w.times k).Executes P g H U R β s A (fun x => k * f x) := by
  obtain ⟨q, γ, hg, he⟩ := h
  refine ⟨q, γ, hg, fun x => ?_⟩
  change k * f x = ∑ i, (k * w.weight i) * (q i).value P x
  rw [he, mul_sum]
  simp only [mul_assoc]

def prepend (s : Script F r t J L K N) (v : List (K × ℕ)) :=
  {s with fresh := fun i => v ++ s.fresh i}

omit [Field F] in
theorem Ordered.emit (h : w.Ordered ν (n + 1) U) (m : ℕ) :
    (w.prepend [(ν n, m)]).Ordered ν n U := by
  intro i
  obtain ⟨h, he⟩ := h i
  change n + ((ν n, m) :: w.fresh i).length ≤ U ∧ _
  refine ⟨by simp only [List.length_cons]; omega, ?_⟩
  change ∀ j : Fin ((w.fresh i).length + 1), (( (ν n, m) :: w.fresh i).get j).1 = ν (n + j.val)
  intro j
  refine Fin.cases rfl (fun j => ?_) j
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using he j

theorem Executes.before {l} (h : w.Executes P g H U R β' q A f)
    (step : Update P g H U R β β' s q a l) :
    (w.prepend l).Executes P g H U R β s A f := by
  obtain ⟨z, γ, hg, he⟩ := h
  refine ⟨z, γ, fun i => ?_, he⟩
  obtain ⟨hr, hc, hp⟩ := hg i
  exact ⟨⟨step.reach.trans hr.reach, hr.valid, hr.match', step.outside.trans hr.outside⟩, hc, hp⟩

theorem Executes.prior (h : w.Executes P g H U R β' q A f)
    (step : Update P g H U R β β' s q a []) : w.Executes P g H U R β s A f :=
  h.before step

variable {I : Type} [Fintype I] (k : I → F) (u : I → Script F r t J L K N)

def sum : Script F r t J L K N where
  I := Σ i, (u i).I
  weight i := k i.1 * (u i.1).weight i.2
  result i := (u i.1).result i.2
  fresh i := (u i.1).fresh i.2

theorem ordered_sum (h : ∀ i, (u i).Ordered ν n U) : (sum k u).Ordered ν n U :=
  fun i => h i.1 i.2

theorem executes_sum (f : I → X → F) (h : ∀ i, (u i).Executes P g H U R β s A (f i)) :
    (sum k u).Executes P g H U R β s A (fun x => ∑ i, k i * f i x) := by
  unfold Executes at h
  choose q γ hq he using h
  refine ⟨fun i => q i.1 i.2, fun i => γ i.1 i.2, fun i => hq i.1 i.2, fun x => ?_⟩
  change _ = ∑ i : Σ i, (u i).I, _
  simp only [he, mul_sum, Fintype.sum_sigma, sum, mul_assoc]

end Script
end OAI.LinearAlgebra.MatrixExponent.Sphere.Surface.Local
end

/-! # Running one mover uniformly in all ambient graphs -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Surface.Local

open Finset
open scoped Classical

structure Params where
  P : ℕ
  g : ℕ
  H : ℕ
  U : ℕ
  M : ℕ
  D : ℕ

structure Job (F : Type) (r t : ℕ) (J L K N : Type) where
  a : Record F r t J L K N
  v : J
  x : Entry F r t K N
  tail : List (Entry F r t K N)
  n : ℕ
  row : a.rows v = x :: tail
  active : x.role = .active n

variable {F T V E X J L K N : Type} {r t : ℕ}

def idle (A : Set (V × F)) (v : V) (u : Station F r t (Tag V T) X) :=
  u.label.role.clock = 0 ∧ (∀ n, u.label.role = .active n → (v, u.pos) ∈ A)

theorem idle_done {s : Stage F r t T V E X} {A : Set (V × F)}
    (h : ∀ v u, u ∈ (s.scene.cell v).stations → idle A v u) :
    Calm s ∧ pending s ⊆ A := by
  refine ⟨fun v u hu => (h v u hu).1, ?_⟩
  rintro ⟨v, z⟩ ⟨u, hu, he, n, hn⟩
  change u.pos = z at he
  exact he ▸ (h v u hu).2 n hn

variable [Field F]

/-- An ambient graph and arbitrary input functions interpreting a
given region record. Moving outside the region is excluded by Covers. -/
structure World (p : Params) (a : Record F r t J L K N) where
  T : Type
  X : Type
  V : Type
  E : Type
  [fv : Fintype V]
  [fe : Fintype E]
  R : Reference J L N V E T X
  β : V ⊕ ℕ → K
  s : Stage F r t T V E X
  src : E → V
  dst : E → V
  allowed : Set (V × F)
  match' : Matches R β s a
  layout : s.Layout src dst p.g
  valid : s.Valid p.U
  room : ∀ y, s.Reach p.P p.g p.H p.U y → y.Room p.M p.D

attribute [instance] World.fv World.fe
variable {p : Params} {a a' : Record F r t J L K N}

def World.next (w : World p a) {q γ h} (u : Update p.P p.g p.H p.U w.R w.β γ w.s q a' h) :
    World p a' where
  T := w.T
  X := w.X
  V := w.V
  E := w.E
  R := w.R
  β := γ
  s := q
  src := w.src
  dst := w.dst
  allowed := w.allowed
  match' := u.match'
  layout := by
    have layout {q} (h : w.s.Reach p.P p.g p.H p.U q) : q.Layout w.src w.dst p.g := by
      induction h with
      | refl => exact w.layout
      | tail _ h ih => exact h.layout ih
    exact layout u.reach
  valid := u.valid
  room _ h := w.room _ (u.reach.trans h)

variable (m : Job F r t J L K N)

structure Task (p : Params) extends World p m.a where
  rest : s.Ct
  raw : s.St
  located : s.scene.cell (R.vertex m.v) = rest.insert raw
  others : ∀ u ∈ rest.stations, idle allowed (R.vertex m.v) u
  away : ∀ k, k ≠ R.vertex m.v → ∀ u ∈ (s.scene.cell k).stations, idle allowed k u

namespace Task
variable {m} (q : Task m p)

private theorem aligned : Represents q.R q.β q.s.hidden q.raw m.x ∧
    List.Forall₂ (Represents q.R q.β q.s.hidden) q.rest.stations m.tail := by
  have e := q.match'.rows m.v
  rw [q.located, m.row] at e
  exact List.forall₂_cons.mp e

private def recast (u : Station F r t T X) (x : F) (a b : ℕ) (h : u.a = a) (g : u.b = b) :
    Station F r t T X :=
  ⟨x, a, b, u.label, fun x i j => u.table x (h.symm ▸ i) (g.symm ▸ j)⟩

omit [Field F] in
private theorem recast_eq (u : Station F r t T X) (x : F) (a b : ℕ)
    (h : u.a = a) (g : u.b = b) (e : u.pos = x) : recast u x a b h g = u := by
  subst_vars
  rfl

/-- Present the ambient station with the dimensions of the intrinsic record. -/
def mover := recast q.raw m.x.pos m.x.a m.x.b q.aligned.1.left q.aligned.1.right

theorem mover_eq : q.mover = q.raw := recast_eq _ _ _ _ _ _ q.aligned.1.pos

theorem here : q.s.scene.cell (q.R.vertex m.v) = q.rest.insert q.mover := by
  rw [mover_eq, q.located]

theorem rows : Represents q.R q.β q.s.hidden q.mover m.x ∧
    List.Forall₂ (Represents q.R q.β q.s.hidden) q.rest.stations m.tail := by
  rw [mover_eq]
  exact q.aligned

def move : Move q.s :=
  ⟨q.R.vertex m.v, q.rest, q.mover, m.n, q.here, q.rows.1.role.trans m.active,
    fun u h => (q.others u h).1, fun v h u h' => (q.away v h u h').1⟩

def executes (x : Script F r t J L K N) (f : q.X → F) :=
  x.Executes p.P p.g p.H p.U q.R q.β q.s q.allowed f

end Task

def Job.fuel (p : Params) := (p.U - m.n) * (p.M + 1) + m.tail.length

def Params.limit (p : Params) (F : Type) := breadth p.P p.g p.H p.M p.D (Nat.card F + 1)

def Params.fan (p : Params) (F : Type) := width p.P p.g p.H p.D (Nat.card F + 1)

omit [Field F] in
theorem Params.limit_pos (p : Params) (F : Type) : 0 < p.limit F := by
  unfold limit breadth window; positivity

omit [Field F] in
theorem Params.fan_pos (p : Params) (F : Type) : 0 < p.fan F := by
  unfold fan width window; positivity

def Job.Bounded (p : Params) (ν : ℕ → K) (b : ℕ) (f : ∀ q : Task m p, q.X → F) :=
  ∃ s : Script F r t J L K N, s.Ordered ν m.n p.U ∧
    Fintype.card s.I ≤ b ∧ ∀ q : Task m p, q.executes s (f q)

def Job.Solvable (p : Params) (ν : ℕ → K) :=
  m.Bounded p ν (p.fan F * p.limit F ^ (m.fuel p - 1))

def Job.Solves (p : Params) (ν : ℕ → K) :=
  m.Bounded p ν (p.limit F ^ m.fuel p) (fun q => q.s.value p.P)

def Job.Subtasks (p : Params) (ν : ℕ → K) :=
  ∀ l : Job F r t J L K N, l.fuel p < m.fuel p → l.n ≤ p.U →
    Covers l.a.ports l.v (p.U - l.n) → l.Solves p ν

end OAI.LinearAlgebra.MatrixExponent.Sphere.Surface.Local
end

/-! # Intrinsic energies, marks and order signs -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Surface.Local

open Finset
open scoped Classical
variable {F J L K N T E V X : Type} {r t : ℕ}

theorem split_match {A B : Type} {R : A → B → Prop} {xs : List A}
    {p q : List B} {x : B} (h : List.Forall₂ R xs (p ++ x :: q)) :
    ∃ a b u, xs = a ++ u :: b ∧ List.Forall₂ R a p ∧ R u x ∧ List.Forall₂ R b q := by
  induction p generalizing xs with
  | nil =>
    cases h with
    | cons hu hx => exact ⟨[], _, _, rfl, .nil, hu, hx⟩
  | cons y p ih =>
    cases h with
    | @cons i _ _ _ hu he =>
      obtain ⟨a, b, u, eq, hp, hq, hz⟩ := ih he
      exact ⟨i::a, b, u, congrArg (i :: ·) eq, .cons hu hp, hq, hz⟩

theorem image_match {A B C : Type} {R : A → B → Prop} {xs : List A} {ys : List B}
    {f : A → C} {g : B → C} (h : List.Forall₂ R xs ys) (he : ∀ a b, R a b → f a = g b) :
    xs.map f = ys.map g := by
  induction h with
  | nil => rfl
  | cons h _ ih => simp only [List.map_cons, he _ _ h, ih]

def eA (us : List (Entry F r t K N)) := (us.map Entry.a).sum
def eB (us : List (Entry F r t K N)) := (us.map Entry.b).sum

variable {R : Reference J L N V E T X} {β : V ⊕ ℕ → K} {ns : List ℕ}
  {xs : List (Station F r t (Tag V T) (Stack X t ns))} {ys : List (Entry F r t K N)}

theorem match_a (h : List.Forall₂ (Represents R β ns) xs ys) : sumA xs = eA ys :=
  congrArg List.sum (image_match h fun _ _ h => h.left)

theorem match_b (h : List.Forall₂ (Represents R β ns) xs ys) : sumB xs = eB ys :=
  congrArg List.sum (image_match h fun _ _ h => h.right)

theorem match_pos (h : List.Forall₂ (Represents R β ns) xs ys) :
    xs.map Station.pos = ys.map Entry.pos := image_match h fun _ _ h => h.pos

theorem match_role (h : List.Forall₂ (Represents R β ns) xs ys) :
    xs.map (fun u => (u.pos, u.label.role)) = ys.map (fun u => (u.pos, u.role)) :=
  image_match h fun _ _ h => Prod.ext h.pos h.role

variable {s : Stage F r t T V E X} {a : Record F r t J L K N}

theorem Matches.portWeight (h : Matches R β s a) (l : List (L × F)) :
    Surface.portWeight s.scene.level (l.map (Prod.map R.edge id)) = Surface.portWeight a.level l := by
  simp [Surface.portWeight, Function.comp_def, h.level]

def Record.sites (a : Record F r t J L K N) (v : J) :=
  ((a.rows v).map Entry.pos ++ (a.ports v).map Prod.snd).toFinset

theorem Matches.sites (h : Matches R β s a) (i : J) : (s.scene.cell (R.vertex i)).sites = a.sites i := by
  simp [Cell.sites, Cell.positions, Record.sites, match_pos (h.rows i), h.ports, Function.comp_def]

namespace Job

variable (m : Job F r t J L K N)

def B := (m.tail.map Entry.pos).toFinset
def seams := ((m.a.ports m.v).map Prod.snd).toFinset
def A := m.B ∪ m.seams
def d := (m.x.a + eA m.tail + portWeight m.a.level (m.a.ports m.v)) / 2
def e := (m.x.b + eB m.tail) / 2
def order (P : ℕ) := Motion.poleOrder P m.d m.e m.B
def threshold (p : Params) := p.P * m.x.a + m.x.b + 2 * p.P * p.H

end Job

namespace Task

variable [Field F] {p : Params} {m : Job F r t J L K N} (q : Task m p)

theorem ports : q.rest.ports = (m.a.ports m.v).map (Prod.map q.R.edge id) := by
  have h := q.match'.ports m.v
  rw [q.here] at h
  exact h

theorem inserts : q.rest.inserts = m.B := congrArg List.toFinset (match_pos q.rows.2)

theorem seams : q.rest.seams = m.seams := by simp [Cell.seams, Job.seams, q.ports, Function.comp_def]

theorem sites : q.rest.sites = m.A := by rw [Cell.sites_eq, q.inserts, q.seams]; rfl

theorem orderA : (q.s.scene.cell (q.R.vertex m.v)).orderA q.s.scene.level = m.d := by
  rw [q.here]
  change (m.x.a + sumA q.rest.stations + portWeight q.s.scene.level q.rest.ports) / 2 = _
  rw [match_a q.rows.2, q.ports, q.match'.portWeight]
  rfl

theorem orderB : (q.s.scene.cell (q.R.vertex m.v)).orderB = m.e := by
  rw [q.here]
  change (m.x.b + sumB q.rest.stations) / 2 = _
  rw [match_b q.rows.2]; rfl

end Task
end OAI.LinearAlgebra.MatrixExponent.Sphere.Surface.Local
end

/-! # Uniform scalar combinations and expiration -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Surface.Local

open Finset Function
open scoped Classical
variable {F J L K N : Type} [Field F] {r t : ℕ} {p : Params}
  {m : Job F r t J L K N} {ν : ℕ → K}

theorem Script.card_pure (a : Record F r t J L K N) : Fintype.card (Script.pure a).I = 1 :=
  Fintype.card_unit

theorem Script.card_sum {I : Type} [Fintype I] (w : I → F) (f : I → Script F r t J L K N)
    {k : ℕ} (h : ∀ i, Fintype.card (f i).I ≤ k) :
    Fintype.card (Script.sum w f).I ≤ Fintype.card I * k := by
  change Fintype.card (Σ i, (f i).I) ≤ _
  rw [Fintype.card_sigma]
  simpa using sum_le_sum (s := univ) (fun i _ => h i)

theorem Job.vacuous {b : ℕ} (hb : 0 < b) (hn : m.n ≤ p.U) (h : ¬ Nonempty (Task m p)) (f) :
    m.Bounded p ν b f :=
  ⟨Script.pure m.a, Script.ordered_pure _ hn, by rw [Script.card_pure]; exact hb, fun q => (h ⟨q⟩).elim⟩

theorem Job.combine {I : Type} [Fintype I] (w : I → F) (f : I → ∀ q : Task m p, q.X → F)
    (h : ∀ i, m.Solvable p ν (f i)) (fuel : 0 < m.fuel p)
    (count : Fintype.card I ≤ p.M * window p.P p.g p.H p.D) :
    m.Bounded p ν (p.limit F ^ m.fuel p) (fun q x => ∑ i, w i * f i q x) := by
  unfold Solvable Bounded at h
  choose s hs hc he using h
  refine ⟨Script.sum w s, Script.ordered_sum w s hs, ?_, fun q => Script.executes_sum w s _ (fun i => he i q)⟩
  calc
    _ ≤ Fintype.card I * (p.fan F * p.limit F ^ (m.fuel p - 1)) := Script.card_sum w s hc
    _ ≤ (p.M + 1) * window p.P p.g p.H p.D * (p.fan F * p.limit F ^ (m.fuel p - 1)) :=
      Nat.mul_le_mul_right _ (count.trans (Nat.mul_le_mul_right _ (Nat.le_succ _)))
    _ = p.limit F * p.limit F ^ (m.fuel p - 1) := by
      rw [← mul_assoc]
      congr 1
      unfold Params.limit Params.fan breadth width; ring
    _ = _ := by rw [← pow_succ', Nat.sub_add_cancel fuel]

theorem Task.finished (q : Task m p) (c : q.s.Ct) (n : ℕ)
    (hc : ∀ a ∈ c.stations, idle q.allowed (q.R.vertex m.v) a) :
    let s := {q.s.put (q.R.vertex m.v) c with expired := n}
    Calm s ∧ pending s ⊆ q.allowed := by
  apply idle_done
  intro v a ha
  change a ∈ (update q.s.scene.cell (q.R.vertex m.v) c v).stations at ha
  by_cases hv : v = q.R.vertex m.v
  · subst v; rw [update_self] at ha; exact hc a ha
  · rw [update_of_ne hv] at ha; exact q.away v hv a ha

theorem Job.expire (he : m.n = p.U) : m.Solves p ν := by
  let r := m.a.edit m.v (m.x.freeze :: m.tail)
  refine ⟨Script.pure r, Script.ordered_pure r he.le, by rw [Script.card_pure]; exact pow_pos (p.limit_pos F) _, fun q => ?_⟩
  let v := q.R.vertex m.v
  let u := {q.mover with label := {q.mover.label with role := Role.collector}}
  let c := q.rest.insert u
  let s := q.s.freeze v q.rest q.mover
  have hstep : q.s.Step p.P p.g p.H p.U s :=
    .expire _ _ _ _ q.here (q.rows.1.role.trans (m.active.trans (congrArg Role.active he))) q.move.ready
  have hu : Update p.P p.g p.H p.U q.R q.β q.β q.s s r [] :=
    ⟨.single hstep, q.valid.freeze _ _ _ q.here q.move.ready,
      q.match'.edit m.v c _ (by rw [q.here]; rfl) (.cons q.rows.1.freeze q.rows.2) _,
      Outside.edit v (Set.mem_range_self m.v) c _⟩
  obtain ⟨hc, hp⟩ := q.finished c (q.s.expired + 1) (by
    intro a ha
    rcases List.mem_cons.mp ha with rfl|ha
    · simp [idle, u, Role.clock]
    · exact q.others _ ha)
  change q.executes (Script.pure r) (q.s.value p.P)
  rw [Stage.freeze_value _ _ _ q.here]
  exact Script.executes_pure hu hc hp

end OAI.LinearAlgebra.MatrixExponent.Sphere.Surface.Local
end

/-! # Two locally identified seam sockets -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Surface.Local

open Finset Motion Stage
open scoped Classical
variable {F J L K N : Type} {r t : ℕ} {p : Params} {m : Job F r t J L K N}

structure Gate (m : Job F r t J L K N) where
  i : L
  w : J
  z : F
  y : F
  left₁ : List (L × F)
  left₂ : List (L × F)
  right₁ : List (L × F)
  right₂ : List (L × F)
  ne : m.v ≠ w
  left : m.a.ports m.v = left₁ ++ (i, z) :: left₂
  right : m.a.ports w = right₁ ++ (i, y) :: right₂

namespace Gate

variable (G : Gate m)

theorem of_cover (hc : Covers m.a.ports m.v (p.U - m.n)) (hn : m.n < p.U) {z : F}
    (hz : z ∈ m.seams) : ∃ G : Gate m, G.z = z ∧ Covers m.a.ports G.w (p.U - (m.n + 1)) := by
  obtain ⟨⟨i, y⟩, hi, hy⟩ := List.mem_map.mp (List.mem_toFinset.mp hz)
  change y = z at hy
  subst y
  rw [show p.U - m.n = (p.U - (m.n + 1)) + 1 by omega] at hc
  obtain ⟨w, y, ne, hw, ht⟩ := hc (i, z) hi
  obtain ⟨l, k, hl⟩ := List.append_of_mem hi
  obtain ⟨a, b, hr⟩ := List.append_of_mem hw
  exact ⟨⟨i, w, z, y, l, k, a, b, ne.symm, hl, hr⟩, rfl, ht⟩

def level := m.a.level G.i
def na := eA m.tail + portWeight m.a.level (G.left₁ ++ G.left₂)
def nb (_ : Gate m) := eB m.tail
def fa := eA (m.a.rows G.w) + portWeight m.a.level (G.right₁ ++ G.right₂)
def C := m.a.sites G.w

variable [Field F] (q : Task m p)

def near : q.s.Sock := ⟨G.left₁.map (Prod.map q.R.edge id), G.left₂.map (Prod.map q.R.edge id),
  q.rest.stations⟩
def far : q.s.Sock := ⟨G.right₁.map (Prod.map q.R.edge id), G.right₂.map (Prod.map q.R.edge id),
  (q.s.scene.cell (q.R.vertex G.w)).stations⟩

theorem near_eq : (G.near q).plug (q.R.edge G.i) G.z = q.rest := by
  have h := q.ports
  rw [G.left, List.map_append, List.map_cons] at h
  change (⟨_, q.rest.stations⟩ : q.s.Ct) = _
  rw [show (G.near q).before ++ (q.R.edge G.i, G.z) :: (G.near q).after = q.rest.ports from h.symm]

theorem far_eq : (G.far q).plug (q.R.edge G.i) G.y = q.s.scene.cell (q.R.vertex G.w) := by
  have h := q.match'.ports G.w
  rw [G.right, List.map_append, List.map_cons] at h
  change (⟨_, (q.s.scene.cell (q.R.vertex G.w)).stations⟩ : q.s.Ct) = _
  rw [show (G.far q).before ++ (q.R.edge G.i, G.y) :: (G.far q).after = _ from h.symm]

theorem nearA : (G.near q).base.bigA q.s.scene.level = G.na := by
  unfold na near Socket.base Cell.bigA
  dsimp only
  rw [match_a q.rows.2, ← List.map_append, q.match'.portWeight]

theorem nearB : sumB (G.near q).stations = G.nb := match_b q.rows.2

theorem farA : (G.far q).base.bigA q.s.scene.level = G.fa := by
  unfold fa far Socket.base Cell.bigA
  dsimp only
  rw [match_a (q.match'.rows G.w), ← List.map_append, q.match'.portWeight]

theorem available_ports :
    Unused (q.R.edge G.i) (G.near q).base.ports ∧ Unused (q.R.edge G.i) (G.far q).base.ports ∧
    ∀ k, k ≠ q.R.vertex m.v → k ≠ q.R.vertex G.w → Unused (q.R.edge G.i) (q.s.ports k) := by
  let v := q.R.vertex m.v
  let w := q.R.vertex G.w
  let i := q.R.edge G.i
  have l : ((G.near q).plug i G.z).ports = q.s.ports v := by
    unfold Stage.ports; rw [q.here, G.near_eq]; rfl
  have r : ((G.far q).plug i G.y).ports = q.s.ports w := congrArg Cell.ports (G.far_eq q)
  refine ⟨(G.near q).unused i G.z (by rw [l]; exact q.layout.unique _),
    (G.far q).unused i G.y (by rw [r]; exact q.layout.unique _), fun k hv hw a ha e => ?_⟩
  have hl := (q.layout.incident v i).mp (List.mem_map.mpr ⟨_, l ▸ (G.near q).mem i G.z, rfl⟩)
  have hr := (q.layout.incident w i).mp (List.mem_map.mpr ⟨_, r ▸ (G.far q).mem i G.y, rfl⟩)
  have ht := (q.layout.incident k i).mp (List.mem_map.mpr ⟨a, ha, e⟩)
  have ne : v ≠ w := q.R.vertex.injective.ne G.ne
  grind

include q in
theorem room :
    m.A.card ≤ p.M ∧ G.C.card ≤ p.M ∧
    m.x.a + m.x.b + (G.level + G.na) + G.nb ≤ p.D ∧ G.level + G.fa ≤ p.D ∧
    (m.a.rows G.w).length ≤ p.M := by
  have h := q.room _ .refl
  obtain ⟨h₁, h₂⟩ := q.move.room h
  change q.rest.sites.card ≤ _ at h₁
  rw [q.sites] at h₁
  change m.x.a + m.x.b + q.rest.bigA _ + sumB q.rest.stations ≤ _ at h₂
  have e : q.rest.bigA q.s.scene.level = G.level + G.na := by
    rw [← G.near_eq q, Socket.bigA, q.match'.level, G.nearA]; rfl
  rw [e, match_b q.rows.2] at h₂
  obtain ⟨h₃, h₄⟩ := h (q.R.vertex G.w)
  have size := (q.s.scene.cell (q.R.vertex G.w)).sizes h₃
  rw [q.match'.sites] at size
  have ee := (q.match'.rows G.w).length_eq
  simp only [Cell.positions, List.length_append, List.length_map] at h₃
  rw [← G.far_eq q, Socket.bigA, q.match'.level, G.farA] at h₄
  exact ⟨h₁, size, h₂, (Nat.le_add_right _ _).trans h₄, by omega⟩

end Gate
end OAI.LinearAlgebra.MatrixExponent.Sphere.Surface.Local
end

/-! # Choosing the same seam expansion in every ambient graph -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Surface.Local.Gate

open Finset Motion Stage
open scoped Classical
variable {F J L K N : Type} [Field F] [Fintype F] {r t : ℕ} {p : Params} {m : Job F r t J L K N}

variable (G : Gate m)

def nearSet (_ : Gate m) := fresh m.A
def farSet (P : ℕ) := powered P (fresh G.C)

def root (P : ℕ) (i : G.farSet P) : F := (mem_image.mp i.property).choose

abbrev indices (P : ℕ) (j : ℤ) := Hop P ((G.level + m.x.a + G.na) / 2) G.level m.x.a j G.nearSet (G.farSet P)

variable (d l : ℕ) [ExpChar F d] (hP : p.P = d ^ l) (hF : p.M * (2 * p.D + 1) < Fintype.card F)
  (j : ℤ) (hj : m.threshold p ≤ -j)

def path (q : Task m p) : Passage p.P q.mover where
  z := G.z
  y := G.y
  A := powered p.P m.A
  B := m.B
  C := powered p.P G.C
  U := G.nearSet
  V := G.farSet p.P
  root := G.root p.P
  hroot i := (mem_image.mp i.property).choose_spec.2
  hz := mem_image_of_mem _ (by rw [← q.sites, ← G.near_eq q, Socket.sites]; exact mem_insert_self ..)
  hy := mem_image_of_mem _ (by unfold C; rw [← q.match'.sites, ← G.far_eq q, Socket.sites]; exact mem_insert_self ..)
  hb := by
    rw [← q.inserts]
    exact disjoint_right.mp (q.rest.disjoint (q.move.distinct q.valid).1)
      (q.rest.mem_seams (G.near_eq q ▸ (G.near q).mem (q.R.edge G.i) G.z))
  hu := by rw [hP, powered_iff, ← q.sites]; exact (q.move.distinct q.valid).2
  hu' := by rw [← q.inserts]; exact fun e => (q.move.distinct q.valid).2 (q.rest.inserts_sub e)
  hU := disjoint_left.mpr (fun _ h e => (mem_sdiff.mp h).2 (mem_union_left _ e))
  hV := disjoint_left.mpr (by
    intro x hx he
    obtain ⟨y, hy, rfl⟩ := mem_image.mp hx
    rw [hP, powered_iff] at he
    exact (mem_sdiff.mp hy).2 he)
  e := G.level
  a := G.na
  b := G.nb
  c := G.fa
  sizeU := by
    obtain ⟨hA, _, h, _, _⟩ := G.room q
    have hB := (card_le_card (show m.B ⊆ m.A from subset_union_left)).trans hA
    exact (Nat.mul_le_mul hB (by change (m.x.b + G.nb) / 2 ≤ _; omega)).trans_lt (fresh_size hA hF)
  sizeV := by
    obtain ⟨_, hC, h, h', _⟩ := G.room q
    have hs : (G.farSet p.P).card = (fresh G.C).card := by
      rw [farSet, powered, hP, card_image_of_injective _ (power_injective d l)]
    rw [hs]
    refine (Nat.mul_le_mul (card_image_le.trans hC) ?_).trans_lt (fresh_size hC hF)
    change (G.level + m.x.a + G.fa) / 2 ≤ _
    omega
  H := p.H
  j := j
  low := hj

theorem fits (q : Task m p) :
    (G.path d l hP hF j hj q).Fits (G.near q).base (G.far q).base q.s.scene.level := by
  refine ⟨?_, ⟨(G.far q).base.inserts, ?_⟩, G.nearA q, G.nearB q, G.farA q⟩
  · have he := G.near_eq q
    have hs : m.A = insert G.z (G.near q).base.sites := by rw [← q.sites, ← he, Socket.sites]
    have hn := (G.near q).avoids _ _ (by rw [he]; exact (q.move.distinct q.valid).1)
    change Cell.Fixed p.P _ ((powered p.P m.A).erase (G.z ^ p.P)) m.B
    rw [hP]
    exact (G.near q).base.fixed_erase d l _ hn _ _ (by rw [hs]; exact subset_insert ..)
      (by rw [← q.inserts, ← he]; rfl)
  · have he := G.far_eq q
    have hs : G.C = insert G.y (G.far q).base.sites := by unfold C; rw [← q.match'.sites, ← he, Socket.sites]
    have hn := (G.far q).avoids _ _ (he.symm ▸ q.valid.distinct (q.R.vertex G.w))
    change Cell.Fixed p.P _ ((powered p.P G.C).erase (G.y ^ p.P)) _
    rw [hP]
    exact (G.far q).base.fixed_erase d l _ hn _ _ (by rw [hs]; exact subset_insert ..) Subset.rfl

theorem uniform (q v : Task m p) (i : G.indices p.P j) :
    (G.path d l hP hF j hj q).signed q.s.scene.level (G.near q) (G.far q) d l hP i =
      (G.path d l hP hF j hj v).signed v.s.scene.level (G.near v) (G.far v) d l hP i := by
  have left (q : Task m p) (e k : ℕ) : (G.near q).sign q.s.scene.level e k =
      (-1 : F) ^ ((k + eA m.tail + portWeight m.a.level G.left₁) * e) := by
    simp only [Socket.sign, near, match_a q.rows.2, q.match'.portWeight]
  have right (q : Task m p) (e k : ℕ) : (G.far q).sign q.s.scene.level e k =
      (-1 : F) ^ ((k + eA (m.a.rows G.w) + portWeight m.a.level G.right₁) * e) := by
    simp only [Socket.sign, far, match_a (q.match'.rows G.w), q.match'.portWeight]
  simp only [Passage.signed, left, right]
  rcases p with ⟨P, g, H, U, M, D⟩
  change P = d ^ l at hP
  subst P
  rfl

end OAI.LinearAlgebra.MatrixExponent.Sphere.Surface.Local.Gate
end

/-! # Rotating one recorded station to the front of a cell -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Surface.Local

open Finset Function Stage
open scoped Classical
variable {F J L K N V E T X : Type} [Field F] [Fintype V] [Fintype E] {r t : ℕ}
  {p : Params} {a : Record F r t J L K N} {s : Stage F r t T V E X}
  {R : Reference J L N V E T X} {β : V ⊕ ℕ → K}

def rotSign (ls : List (Entry F r t K N)) (u : Entry F r t K N) : F :=
  (-1) ^ (eA ls * u.a + eB ls * u.b)

theorem Matches.rotate (h : Matches R β s a) (valid : s.Valid p.U) (j : J)
    (l rest : List s.St) (u : s.St) (ls ts : List (Entry F r t K N)) (v : Entry F r t K N)
    (here : (s.scene.cell (R.vertex j)).stations = l ++ u :: rest)
    (hl : List.Forall₂ (Represents R β s.hidden) l ls)
    (ht : List.Forall₂ (Represents R β s.hidden) rest ts) (hu : Represents R β s.hidden u v) :
    let s' := s.reord (R.vertex j) l [u] rest
    Update p.P p.g p.H p.U R β β s s' (a.edit j (v :: (ls ++ ts))) [] ∧
      ∀ f : Test F r t, Signed f → s.observe p.P (R.vertex j) f =
        fun x => rotSign ls v * s'.observe p.P (R.vertex j) f x := by
  intro s'
  have perm : (s.scene.cell (R.vertex j)).stations.Perm ([u] ++ l ++ rest) := by
    rw [here]
    exact List.perm_middle
  refine ⟨⟨.single (.perm _ _ _ perm), valid.perm _ _ perm, ?_, Outside.put _ (Set.mem_range_self j) _⟩, ?_⟩
  · exact h.edit j ⟨(s.scene.cell (R.vertex j)).ports, u :: (l ++ rest)⟩ _ rfl (.cons hu (List.rel_append hl ht)) s.expired
  · intro f hf
    have e := s.scene.rotate (P := p.P) (R.vertex j) f hf l [u] rest (by simpa using here)
    have ha : sumA [u] = v.a := by simp [sumA, hu.left]
    have hb : sumB [u] = v.b := by simp [sumB, hu.right]
    rw [match_a hl, match_b hl, ha, hb] at e
    funext x
    unfold observe
    rw [funext e, trace_mul]
    rfl

end OAI.LinearAlgebra.MatrixExponent.Sphere.Surface.Local
end

/-! # Resuming a move or stopping at a collector -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Surface.Local
open scoped Classical
variable {F J L K N : Type} [Field F] {r t : ℕ} {m : Job F r t J L K N} {p : Params} {ν : ℕ → K}

def Script.Resumes (f : Script F r t J L K N) (p : Params) (a : Record F r t J L K N) (v : J) : Prop :=
  ∀ (w : World p a) (c : w.s.Ct) (u : w.s.St), w.s.scene.cell (w.R.vertex v) = c.insert u →
    (∀ z ∈ c.stations, idle w.allowed (w.R.vertex v) z) →
    (∀ k, k ≠ w.R.vertex v → ∀ z ∈ (w.s.scene.cell k).stations, idle w.allowed k z) →
    f.Executes p.P p.g p.H p.U w.R w.β w.s w.allowed (w.s.value p.P)

theorem Job.Subtasks.resume (rec : m.Subtasks p ν) (a : Record F r t J L K N) (v : J)
    (x : Entry F r t K N) (xs : List (Entry F r t K N)) (n : ℕ)
    (row : a.rows v = x::xs) (role : x.role = .active n ∨ x.role = .collector) (hn : n ≤ p.U)
    (safe : Covers a.ports v (p.U - n)) (decr : (p.U - n) * (p.M + 1) + xs.length < m.fuel p) :
    ∃ f : Script F r t J L K N, f.Ordered ν n p.U ∧
      Fintype.card f.I ≤ p.limit F ^ (m.fuel p - 1) ∧ f.Resumes p a v := by
  rcases role with ha|hc
  · let j : Job F r t J L K N := ⟨a, v, x, xs, n, row, ha⟩
    obtain ⟨f, hf, hc, he⟩ := rec j decr hn safe
    have hd : j.fuel p ≤ m.fuel p - 1 := Nat.le_pred_of_lt decr
    exact ⟨f, hf, hc.trans (Nat.pow_le_pow_right (p.limit_pos F) hd), fun w c u hv h₁ h₂ => he ⟨w, c, u, hv, h₁, h₂⟩⟩
  refine ⟨Script.pure a, Script.ordered_pure _ hn, by rw [Script.card_pure]; exact pow_pos (p.limit_pos F) _, fun w c u hv h₁ h₂ => ?_⟩
  have h := w.match'.rows v
  rw [hv, row] at h
  have hrole := (List.forall₂_cons.mp h).1.role.trans hc
  have closed : Calm w.s ∧ pending w.s ⊆ w.allowed := by
    apply idle_done
    intro i z hz
    by_cases e : i = w.R.vertex v
    · subst i; rw [hv] at hz
      rcases List.mem_cons.mp hz with rfl|hz
      · simp [idle, hrole, Role.clock]
      · exact h₁ z hz
    · exact h₂ i e z hz
  exact Script.executes_pure (.refl w.match' w.valid) closed.1 closed.2

end OAI.LinearAlgebra.MatrixExponent.Sphere.Surface.Local
end
