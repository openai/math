import Mathlib.Combinatorics.Quiver.Path.Vertices
import Mathlib.Combinatorics.Quiver.Path.Weight
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Finset.Max
import Mathlib.Data.Prod.Lex
import Mathlib.Data.List.MinMax
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Longest-walk potentials for the residual network of the balanced-prices market. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Market
namespace Potentials
open Quiver

variable {V : Type*} [Quiver V]
variable (w : ∀ {i j : V}, (i ⟶ j) → ℚ)

/-- On a simple circuit every vertex preceding the final return occurs once. -/
def NonpositiveSimpleCircuits : Prop :=
  ∀ {a b : V} (p : Path a b) (e : b ⟶ a), p.vertices.Nodup → (p.cons e).addWeight w ≤ 0

private theorem vertices_prefix {a b c : V} (p : Path a b) (q : Path b c) :
    p.vertices <+: (p.comp q).vertices := by
  induction q with
  | nil => exact ⟨[], by simp⟩
  | @cons _ d q e ih =>
    obtain ⟨s, hs⟩ := ih
    exact ⟨s ++ [d], by simp [Path.comp, ← hs, List.concat_eq_append]⟩

/-- Erasing a closed part never decreases the weight, and preserves both endpoints. -/
theorem exists_simple_ge (hc : NonpositiveSimpleCircuits w) {a b : V} (p : Path a b) :
    ∃ q : Path a b, q.vertices.Nodup ∧ p.addWeight w ≤ q.addWeight w := by
  classical
  induction p with
  | nil => exact ⟨.nil, by simp, le_rfl⟩
  | @cons b c p e ih =>
    obtain ⟨q, hq, hp⟩ := ih
    by_cases hv : c ∈ q.vertices
    · obtain ⟨q₁, q₂, rfl⟩ := q.exists_eq_comp_of_mem_vertices hv
      have h₁ := hq.sublist (vertices_prefix q₁ q₂).sublist
      have h₂ : q₂.vertices.Nodup := by
        rw [Path.vertices_comp] at hq
        exact (List.nodup_append.mp hq).2.1
      have hcycle := hc q₂ e h₂
      simp only [Path.addWeight_comp, Path.addWeight_cons] at hp hcycle ⊢
      exact ⟨q₁, h₁, by linarith⟩
    · exact ⟨q.cons e, List.Nodup.concat hv hq,
        by simpa using add_le_add_right hp (w e)⟩

/-- The simple-circuit hypothesis suffices for arbitrary closed walks. -/
theorem closed_nonpositive (hc : NonpositiveSimpleCircuits w) {a : V} (p : Path a a) :
    p.addWeight w ≤ 0 := by
  obtain ⟨q, hn, hle⟩ := exists_simple_ge w hc p
  cases q with
  | nil => simpa using hle
  | cons q e =>
    have ha := q.start_mem_vertices
    simp [List.concat_eq_append, List.nodup_append] at hn
    exact (hn.2 _ ha rfl).elim

section Finite

variable [Fintype V] [∀ i j : V, Fintype (i ⟶ j)]

/-- A candidate next step either terminates or takes an outgoing arc. -/
abbrev Choice (i : V) := Option (Σ j : V, i ⟶ j)

def score (terminal previous : V → ℚ) (i : V) : Choice i → ℚ
  | none => terminal i
  | some ⟨j, e⟩ => w e + previous j

/-- One Bellman relaxation, including the immediate stopping option. -/
def relax (terminal previous : V → ℚ) (i : V) : ℚ :=
  Finset.univ.sup' Finset.univ_nonempty (score w terminal previous i)

/-- Maximum of path weight plus terminal reward, allowing at most `k` arcs. -/
def value (terminal : V → ℚ) : ℕ → V → ℚ
  | 0 => terminal
  | k + 1 => relax w terminal (value terminal k)

theorem score_le_relax (r z : V → ℚ) (i : V) (o : Choice i) :
    score w r z i o ≤ relax w r z i :=
  Finset.le_sup' _ (Finset.mem_univ o)

theorem exists_score_eq_relax (r z : V → ℚ) (i : V) :
    ∃ o : Choice i, relax w r z i = score w r z i o := by
  obtain ⟨o, _, ho⟩ := Finset.exists_mem_eq_sup' (s := Finset.univ)
    Finset.univ_nonempty (score w r z i)
  exact ⟨o, ho⟩

theorem terminal_le_value (r : V → ℚ) (k : ℕ) (i : V) : r i ≤ value w r k i := by
  cases k with
  | zero => exact le_rfl
  | succ k => exact score_le_relax w r (value w r k) i none

/-- Every bounded-horizon value is attained by an actual walk. -/
theorem value_attained (r : V → ℚ) (k : ℕ) (i : V) :
    ∃ (j : V) (p : Path i j), p.length ≤ k ∧ value w r k i = p.addWeight w + r j := by
  induction k generalizing i with
  | zero => exact ⟨i, .nil, le_rfl, by simp [value]⟩
  | succ k ih =>
    obtain ⟨o, ho⟩ := exists_score_eq_relax w r (value w r k) i
    cases o with
    | none => exact ⟨i, .nil, by simp, by simpa [value, score] using ho⟩
    | some o =>
      obtain ⟨j, e⟩ := o
      obtain ⟨v, p, hp, hv⟩ := ih j
      refine ⟨v, e.toPath.comp p, ?_, ?_⟩
      · simpa [Nat.add_comm] using Nat.succ_le_succ hp
      · rw [value, ho]
        simp [score, hv, Quiver.Hom.toPath, add_assoc]

theorem walk_score_le_value (r : V → ℚ) (k : ℕ) {a b : V} (p : Path a b)
    (hk : p.length ≤ k) : p.addWeight w + r b ≤ value w r k a := by
  induction k generalizing a b with
  | zero =>
    obtain rfl := p.eq_of_length_zero (by omega)
    cases p with
    | nil => simp [value]
    | cons q e => simp at hk
  | succ k ih =>
    cases hh : p.length with
    | zero =>
      obtain rfl := p.eq_of_length_zero hh
      obtain rfl := (Path.length_eq_zero_iff p).mp hh
      simpa using terminal_le_value w r (k + 1) a
    | succ n =>
      obtain ⟨c, e, q, hq, rfl⟩ := p.eq_toPath_comp_of_length_eq_succ hh
      have hb := ih q (by omega)
      have he := score_le_relax w r (value w r k) a (some ⟨c, e⟩)
      simp only [Path.addWeight_comp, Quiver.Hom.toPath, Path.addWeight_cons, Path.addWeight_nil,
        zero_add, add_assoc]
      change w e + value w r k c ≤ value w r (k + 1) a at he
      linarith

/-- The terminal reward can be used to distinguish possible endpoints. -/
def potential (terminal : V → ℚ) (i : V) : ℚ :=
  value w terminal (Fintype.card V - 1) i

theorem walk_score_le_potential (r : V → ℚ) (hc : NonpositiveSimpleCircuits w)
    {a b : V} (p : Path a b) : p.addWeight w + r b ≤ potential w r a := by
  obtain ⟨q, hn, hq⟩ := exists_simple_ge w hc p
  have hcard := hn.length_le_card
  rw [Path.vertices_length] at hcard
  exact (add_le_add hq (le_refl (r b))).trans (walk_score_le_value w r (Fintype.card V - 1) q (by omega))

theorem arc_le_potential_sub (r : V → ℚ) (hc : NonpositiveSimpleCircuits w)
    {a b : V} (e : a ⟶ b) : w e ≤ potential w r a - potential w r b := by
  obtain ⟨c, p, _, hval⟩ := value_attained w r (Fintype.card V - 1) b
  have hh := walk_score_le_potential w r hc (e.toPath.comp p)
  simp only [Path.addWeight_comp, Quiver.Hom.toPath, Path.addWeight_cons, Path.addWeight_nil,
    zero_add] at hh
  change w e ≤ potential w r a - value w r _ b
  linarith

theorem potential_attained (r : V → ℚ) (hc : NonpositiveSimpleCircuits w) (a : V) :
    ∃ (b : V) (p : Path a b), p.vertices.Nodup ∧ potential w r a = p.addWeight w + r b := by
  obtain ⟨b, q, _, hq⟩ := value_attained w r (Fintype.card V - 1) a
  obtain ⟨p, hn, hp⟩ := exists_simple_ge w hc q
  refine ⟨b, p, hn, le_antisymm ?_ (walk_score_le_potential w r hc p)⟩
  rw [potential, hq]
  exact add_le_add hp le_rfl

omit [Fintype V] [∀ i j : V, Fintype (i ⟶ j)] in
/-- Integer multiples of a common unit remain so after adding arc weights. -/
theorem weight_denominator (D : ℕ) (hd : ∀ {a b : V} (e : a ⟶ b),
    ∃ z : ℤ, (D : ℚ) * w e = z) {a b : V} (p : Path a b) :
    ∃ z : ℤ, (D : ℚ) * p.addWeight w = z := by
  induction p with
  | nil => exact ⟨0, by simp⟩
  | cons p e ih =>
    obtain ⟨z, hz⟩ := ih
    obtain ⟨n, he⟩ := hd e
    exact ⟨z + n, by simp [mul_add, hz, he]⟩

omit [Fintype V] [∀ i j : V, Fintype (i ⟶ j)] in
theorem abs_weight_le (C : ℚ) (hb : ∀ {a b : V} (e : a ⟶ b), |w e| ≤ C)
    {a b : V} (p : Path a b) : |p.addWeight w| ≤ (p.length : ℚ) * C := by
  induction p with
  | nil => simp
  | cons p e ih =>
    simp only [Path.addWeight_cons, Path.length_cons, Nat.cast_add, Nat.cast_one, add_mul, one_mul]
    exact (abs_add_le (p.addWeight w) (w e)).trans (add_le_add ih (hb e))

theorem potential_abs_le (C : ℚ) (hC : 0 ≤ C)
    (hb : ∀ {a b : V} (e : a ⟶ b), |w e| ≤ C) (a : V) :
    |potential w 0 a| ≤ ((Fintype.card V - 1 : ℕ) : ℚ) * C := by
  obtain ⟨b, p, hp, h⟩ := value_attained w 0 (Fintype.card V - 1) a
  change |value w 0 (Fintype.card V - 1) a| ≤ _
  rw [h]
  simp only [Pi.zero_apply, add_zero]
  exact (abs_weight_le w C hb p).trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hp) hC)

theorem potential_denominator (D : ℕ) (hd : ∀ {a b : V} (e : a ⟶ b),
    ∃ z : ℤ, (D : ℚ) * w e = z) (a : V) : ∃ z : ℤ, (D : ℚ) * potential w 0 a = z := by
  obtain ⟨b, p, _, h⟩ := value_attained w 0 (Fintype.card V - 1) a
  simpa [potential, h] using weight_denominator w D hd p

/-- The dummy vertex fixes the additive constant in the prices. -/
def normalized (dummy v : V) : ℚ := potential w 0 v - potential w 0 dummy

theorem normalized_arc (hc : NonpositiveSimpleCircuits w) (dummy : V)
    {a b : V} (e : a ⟶ b) : w e ≤ normalized w dummy a - normalized w dummy b := by
  simpa [normalized] using arc_le_potential_sub w 0 hc e

theorem normalized_tight (hc : NonpositiveSimpleCircuits w) (dummy : V)
    {a b : V} (e : a ⟶ b) (back : b ⟶ a) (hback : w back = -w e) :
    w e = normalized w dummy a - normalized w dummy b := by
  have h₁ := normalized_arc w hc dummy e
  have h₂ := normalized_arc w hc dummy back
  linarith

theorem normalized_denominator (D : ℕ) (hd : ∀ {a b : V} (e : a ⟶ b),
    ∃ z : ℤ, (D : ℚ) * w e = z) (dummy a : V) :
    ∃ z : ℤ, (D : ℚ) * normalized w dummy a = z := by
  obtain ⟨z, hz⟩ := potential_denominator w D hd a
  obtain ⟨n, hn⟩ := potential_denominator w D hd dummy
  exact ⟨z - n, by simp [normalized, mul_sub, hz, hn]⟩

theorem normalized_abs_le (C : ℚ) (hC : 0 ≤ C)
    (hb : ∀ {a b : V} (e : a ⟶ b), |w e| ≤ C) (dummy a : V) :
    |normalized w dummy a| ≤ 2 * (Fintype.card V : ℚ) * C := by
  have hdim : ((Fintype.card V - 1 : ℕ) : ℚ) ≤ (Fintype.card V : ℚ) := by
    exact_mod_cast Nat.sub_le (Fintype.card V) 1
  have hs := mul_le_mul_of_nonneg_right hdim hC
  have h₁ := potential_abs_le w C hC hb a
  have h₂ := potential_abs_le w C hC hb dummy
  have h₃ := abs_sub (potential w 0 a) (potential w 0 dummy)
  unfold normalized
  linarith


/-- A feasible potential is sharp on a maximizing simple path to every reachable target.
A large reward on the target ensures that stopping elsewhere cannot win. -/
theorem exists_tight_path (hc : NonpositiveSimpleCircuits w) (C : ℚ) (hC : 0 ≤ C)
    (hb : ∀ {a b : V} (e : a ⟶ b), |w e| ≤ C) {s t : V} (route : Path s t) :
    ∃ (π : V → ℚ) (q : Path s t), q.vertices.Nodup ∧
      (∀ {a b : V} (e : a ⟶ b), w e ≤ π a - π b) ∧ q.addWeight w = π s - π t ∧
      ∀ p : Path s t, p.addWeight w ≤ q.addWeight w := by
  classical
  let B : ℚ := (Fintype.card V : ℚ) * C
  let bonus : ℚ := 2 * B + 1
  let r (v : V) : ℚ := if v = t then bonus else 0
  have hB : 0 ≤ B := mul_nonneg (Nat.cast_nonneg _) hC
  have hl : ∀ {a b : V} (p : Path a b), p.vertices.Nodup → |p.addWeight w| ≤ B := by
    intro a b p hp
    have h := hp.length_le_card
    rw [Path.vertices_length] at h
    apply (abs_weight_le w C hb p).trans
    apply mul_le_mul_of_nonneg_right _ hC
    exact_mod_cast (show p.length ≤ Fintype.card V by omega)
  have rootMax : ∀ {a : V} (_ : Path a t), ∃ p : Path a t,
      p.vertices.Nodup ∧ potential w r a = p.addWeight w + bonus := by
    intro a fromA
    obtain ⟨q, hq, _⟩ := exists_simple_ge w hc fromA
    have h₁ := (abs_le.mp (hl q hq)).1
    have h₂ := walk_score_le_potential w r hc q
    simp [r] at h₂
    obtain ⟨b, p, hp, heq⟩ := potential_attained w r hc a
    by_cases hbt : b = t
    · subst b
      exact ⟨p, hp, by simpa [r] using heq⟩
    · have hmm := (abs_le.mp (hl p hp)).2
      simp [r, hbt] at heq
      dsimp only [bonus] at h₂
      linarith
  obtain ⟨ps, hs, hps⟩ := rootMax route
  obtain ⟨pt, _, hpt⟩ := rootMax (Path.nil : Path t t)
  have hnt := closed_nonpositive w hc pt
  have hbonus : bonus ≤ potential w r t := by
    simpa [potential, r] using terminal_le_value w r (Fintype.card V - 1) t
  refine ⟨potential w r, ps, hs, fun e => arc_le_potential_sub w r hc e, by linarith, ?_⟩
  intro p
  have hh := walk_score_le_potential w r hc p
  simp [r] at hh
  linarith

/-- Tabulating the Bellman layers shares each previous entry across outgoing arcs. -/
def table {n : ℕ} [Quiver (Fin n)] [∀ i j : Fin n, Fintype (i ⟶ j)]
    (cost : ∀ {i j : Fin n}, (i ⟶ j) → ℚ) (r : Fin n → ℚ) : ℕ → Vector ℚ n
  | 0 => Vector.ofFn r
  | k + 1 =>
      let previous := table cost r k
      Vector.ofFn (relax cost r (fun i => previous[i.val]))

theorem table_correct {n : ℕ} [Quiver (Fin n)] [∀ i j : Fin n, Fintype (i ⟶ j)]
    (cost : ∀ {i j : Fin n}, (i ⟶ j) → ℚ) (r : Fin n → ℚ) (k : ℕ) (i : Fin n) :
    (table cost r k)[i.val] = value cost r k i := by
  induction k generalizing i with
  | zero => simp [table, value]
  | succ k ih =>
    simp only [table, Vector.getElem_ofFn, value]
    congr 1
    funext j
    exact ih j

end Finite

/-- A repeated vertex permits a strictly shorter walk to the same endpoint. -/
theorem exists_shorter_ge (hc : NonpositiveSimpleCircuits w) {a b : V} (p : Path a b)
    (hn : ¬p.vertices.Nodup) :
    ∃ q : Path a b, q.length < p.length ∧ p.addWeight w ≤ q.addWeight w := by
  classical
  induction p with
  | nil => simp at hn
  | @cons b c p e ih =>
    by_cases hp : p.vertices.Nodup
    · have hc' : c ∈ p.vertices := by
        by_contra h
        exact hn (List.Nodup.concat h hp)
      obtain ⟨q, tail, rfl⟩ := p.exists_eq_comp_of_mem_vertices hc'
      have ht : tail.vertices.Nodup := by
        rw [Path.vertices_comp] at hp
        exact (List.nodup_append.mp hp).2.1
      have hh := hc tail e ht
      refine ⟨q, ?_, ?_⟩
      · simp only [Path.length_cons, Path.length_comp]
        omega
      · simp only [Path.addWeight_comp, Path.addWeight_cons] at hh ⊢
        linarith
    · obtain ⟨q, hq, hw⟩ := ih hp
      exact ⟨q.cons e, by simpa using hq, by simpa using add_le_add hw (le_refl (w e))⟩

/-- The value and number of arcs are stored alongside the witness so comparisons need no path scan. -/
structure Plan (r : V → ℚ) (i : V) where
  finish : V
  path : Path i finish
  total : ℚ
  steps : ℕ
  total_spec : total = path.addWeight w + r finish
  steps_spec : steps = path.length

private def rank (total : ℚ) (steps : ℕ) : ℚ ×ₗ OrderDual ℕ := toLex (total, steps)

private theorem rank_le {x y : ℚ} {i j : ℕ} :
    rank x i ≤ rank y j ↔ x < y ∨ x = y ∧ j ≤ i := Prod.Lex.toLex_le_toLex

private theorem rank_add {x y : ℚ} {i j : ℕ} (hz : rank x i ≤ rank y j) (w' : ℚ) :
    rank (w' + x) (1 + i) ≤ rank (w' + y) (1 + j) := by
  rw [rank_le] at hz ⊢
  rcases hz with h | ⟨rfl, h⟩
  · exact Or.inl (by linarith)
  · exact Or.inr ⟨rfl, by omega⟩

namespace Plan

variable {w} {r : V → ℚ} {i j : V}

def stop (w : ∀ {i j : V}, (i ⟶ j) → ℚ) (r : V → ℚ) (i : V) : Plan w r i :=
  ⟨i, .nil, r i, 0, by simp, rfl⟩

def prepend (e : i ⟶ j) (p : Plan w r j) : Plan w r i where
  finish := p.finish
  path := e.toPath.comp p.path
  total := w e + p.total
  steps := 1 + p.steps
  total_spec := by simpa [Quiver.Hom.toPath, add_assoc] using p.total_spec
  steps_spec := by simpa using p.steps_spec

private def key (p : Plan w r i) := rank p.total p.steps

/-- A fixed input ordering resolves all remaining ties. -/
def pick (first : Plan w r i) (rest : List (Plan w r i)) : Plan w r i :=
  ((first :: rest).argmax key).getD first

private theorem pick_argmax (first : Plan w r i) (rest : List (Plan w r i)) :
    pick first rest ∈ (first :: rest).argmax key := by
  cases h : (first :: rest).argmax key with
  | none => simp at h
  | some x => simp [pick, h]

private theorem le_pick {first x : Plan w r i} {rest : List (Plan w r i)}
    (hx : x ∈ first :: rest) : key x ≤ key (pick first rest) :=
  List.le_of_mem_argmax hx (pick_argmax first rest)


/-- Instrument the scan of a nonempty list. Its second component counts lexicographic comparisons. -/
def scan (first : Plan w r i) : List (Plan w r i) → Plan w r i × ℕ
  | [] => (first, 0)
  | next :: rest =>
    let ⟨best, checks⟩ := scan next rest
    (if first.key < best.key then best else first, checks + 1)

theorem scan_eq (first : Plan w r i) (rest : List (Plan w r i)) :
    scan first rest = (pick first rest, rest.length) := by
  induction rest generalizing first with
  | nil => simp [scan, pick]
  | cons next rest ih =>
    have hm : (next :: rest).argmax key = some (pick next rest) := pick_argmax next rest
    have hchoose : pick first (next :: rest) =
        (if first.key < (pick next rest).key then pick next rest else first) := by
      change ((first :: next :: rest).argmax key).getD first = _
      rw [List.argmax_cons, hm]
      by_cases h : first.key < (pick next rest).key <;> simp [h]
    simp [scan, ih, hchoose]

end Plan

/-- A cached layer indexed by vertices with the dependent path origin preserved. -/
structure Layer {n : ℕ} (T : Fin n → Type*) where
  entries : Vector (Σ i, T i) n
  origin : ∀ i : Fin n, entries[i.val].1 = i

def Layer.ofFn {n : ℕ} {T : Fin n → Type*} (f : (i : Fin n) → T i) : Layer T where
  entries := Vector.ofFn (fun i => ⟨i, f i⟩)
  origin i := by simp

def Layer.get {n : ℕ} {T : Fin n → Type*} (t : Layer T) (i : Fin n) : T i :=
  (t.origin i) ▸ t.entries[i.val].2

@[simp] theorem Layer.get_ofFn {n : ℕ} {T : Fin n → Type*} (f : (i : Fin n) → T i)
    (i : Fin n) : (Layer.ofFn f).get i = f i := by
  have getSnd {pair : Σ j, T j} {x : T i} (hp : pair = ⟨i, x⟩) (hi : pair.1 = i) :
      hi ▸ pair.2 = x := by subst pair; rfl
  exact getSnd (by simp [Layer.ofFn]) ((Layer.ofFn f).origin i)

/-- Use an explicit numbering to tabulate dependent rows on an arbitrary finite vertex type. -/
def Layer.tabulate {V : Type*} {n : ℕ} (index : V ≃ Fin n) {T : V → Type*}
    (f : (i : V) → T i) : Layer (fun j => T (index.symm j)) :=
  Layer.ofFn fun j => f (index.symm j)

def Layer.lookup {V : Type*} {n : ℕ} (index : V ≃ Fin n) {T : V → Type*}
    (layer : Layer (fun j => T (index.symm j))) (i : V) : T i :=
  (index.symm_apply_apply i) ▸ layer.get (index i)

@[simp] theorem Layer.lookup_tabulate {V : Type*} {n : ℕ} (index : V ≃ Fin n)
    {T : V → Type*} (f : (i : V) → T i) (i : V) :
    Layer.lookup index (Layer.tabulate index f) i = f i := by
  have cast_eq {a b : V} (hab : a = b) : hab ▸ f a = f b := by subst b; rfl
  simp only [Layer.lookup, Layer.tabulate, Layer.get_ofFn]
  exact cast_eq _

section Reconstruction

variable {n : ℕ} (index : V ≃ Fin n)
variable (cost : ∀ {i j : V}, (i ⟶ j) → ℚ) (r : V → ℚ)
variable (out : (i : V) → List (Σ j : V, i ⟶ j))

/-- The witness DP stores one row per vertex. A row selects the best of stopping and taking
one listed arc followed by the previously computed row at its head. -/
def plans : ℕ → Layer (fun j => Plan cost r (index.symm j))
  | 0 => Layer.tabulate index (Plan.stop cost r)
  | k + 1 =>
    let previous := plans k
    Layer.tabulate index fun i => Plan.pick (Plan.stop cost r i)
      ((out i).map (fun je => Plan.prepend je.2 (Layer.lookup index previous je.1)))

theorem plans_steps_le (k : ℕ) (i : V) :
    (Layer.lookup index (plans index cost r out k) i).steps ≤ k := by
  induction k generalizing i with
  | zero => simp [plans, Plan.stop]
  | succ k ih =>
    simp only [plans, Layer.lookup_tabulate]
    let moves := (out i).map (fun je => Plan.prepend je.2 (Layer.lookup index (plans index cost r out k) je.1))
    have h := List.argmax_mem (Plan.pick_argmax (Plan.stop cost r i) moves)
    rcases List.mem_cons.mp h with hs | hs
    · rw [hs]
      simp [Plan.stop]
    · obtain ⟨⟨j, e⟩, _, he⟩ := List.mem_map.mp hs
      rw [← he]
      change 1 + (Layer.lookup index (plans index cost r out k) j).steps ≤ k + 1
      have := ih j
      omega

theorem plans_optimal
    (hout : ∀ {i j : V} (e : i ⟶ j), (⟨j, e⟩ : Σ z : V, i ⟶ z) ∈ out i)
    (k : ℕ) {a b : V} (p : Path a b) (hk : p.length ≤ k) :
    rank (p.addWeight cost + r b) p.length ≤ Plan.key (Layer.lookup index (plans index cost r out k) a) := by
  induction k generalizing a b with
  | zero =>
    obtain rfl := p.eq_of_length_zero (by omega)
    obtain rfl := (Path.length_eq_zero_iff p).mp (by omega)
    simp [plans, Plan.key, Plan.stop]
  | succ k ih =>
    simp only [plans, Layer.lookup_tabulate]
    cases hh : p.length with
    | zero =>
      obtain rfl := p.eq_of_length_zero hh
      obtain rfl := (Path.length_eq_zero_iff p).mp hh
      let moves := (out a).map (fun je => Plan.prepend je.2 (Layer.lookup index (plans index cost r out k) je.1))
      have h := Plan.le_pick (first := Plan.stop cost r a) (rest := moves) List.mem_cons_self
      simpa [Plan.key, Plan.stop, moves] using h
    | succ l =>
      obtain ⟨j, e, q, hq, rfl⟩ := p.eq_toPath_comp_of_length_eq_succ hh
      have hchild := ih q (by omega)
      have h₁ := rank_add hchild (cost e)
      have hm : Plan.prepend e (Layer.lookup index (plans index cost r out k) j) ∈
          Plan.stop cost r a :: ((out a).map (fun je => Plan.prepend je.2 (Layer.lookup index (plans index cost r out k) je.1))) :=
        List.mem_cons_of_mem _ (List.mem_map.mpr ⟨⟨j, e⟩, hout e, rfl⟩)
      apply le_trans _ (Plan.le_pick hm)
      simpa [Plan.key, Plan.prepend, Quiver.Hom.toPath, add_assoc, hq, Nat.add_comm] using h₁


/-- The tie rule selects a simple route even when nonpositive circuits of weight zero exist. -/
theorem plans_simple
    (hout : ∀ {i j : V} (e : i ⟶ j), (⟨j, e⟩ : Σ z : V, i ⟶ z) ∈ out i)
    (hc : NonpositiveSimpleCircuits cost) (k : ℕ) (a : V) :
    (Layer.lookup index (plans index cost r out k) a).path.vertices.Nodup := by
  let chosen := Layer.lookup index (plans index cost r out k) a
  change chosen.path.vertices.Nodup
  by_contra hn
  obtain ⟨q, hlen, hw⟩ := exists_shorter_ge cost hc chosen.path hn
  have hbudget : chosen.path.length ≤ k := chosen.steps_spec ▸ plans_steps_le index cost r out k a
  have h := plans_optimal index cost r out hout k q (hlen.le.trans hbudget)
  change rank (q.addWeight cost + r chosen.finish) q.length ≤ rank chosen.total chosen.steps at h
  rw [rank_le, chosen.steps_spec, chosen.total_spec] at h
  rcases h with h | ⟨_, h⟩
  · linarith
  · omega

/-- The internally stored rational is exactly the bounded-horizon Bellman value. -/
theorem plans_total_eq_value [Fintype V] [∀ i j : V, Fintype (i ⟶ j)]
    (hout : ∀ {i j : V} (e : i ⟶ j), (⟨j, e⟩ : Σ z : V, i ⟶ z) ∈ out i)
    (k : ℕ) (a : V) :
    (Layer.lookup index (plans index cost r out k) a).total = value cost r k a := by
  let chosen := Layer.lookup index (plans index cost r out k) a
  change chosen.total = _
  have hbudget : chosen.path.length ≤ k := chosen.steps_spec ▸ plans_steps_le index cost r out k a
  refine le_antisymm (chosen.total_spec ▸ walk_score_le_value cost r k chosen.path hbudget) ?_
  obtain ⟨b, q, hq, hval⟩ := value_attained cost r k a
  have h := plans_optimal index cost r out hout k q hq
  change rank (q.addWeight cost + r b) q.length ≤ rank chosen.total chosen.steps at h
  rw [rank_le, ← hval] at h
  exact h.elim LT.lt.le (fun z => z.1.le)


/-- Each row examines the immediate stop and the listed outgoing arcs once. The comparison
count is one per arc, including a repeated arc if the input explicitly lists it twice. -/
theorem row_scan_checks (k : ℕ) (i : V) :
    (Plan.scan (Plan.stop cost r i) ((out i).map (fun je =>
      Plan.prepend je.2 (Layer.lookup index (plans index cost r out k) je.1)))).2 = (out i).length := by
  simp [Plan.scan_eq]

/-- All scores stored in layer `k` use the common denominator of costs and terminal rewards. -/
theorem plans_denominator (D : ℕ)
    (hedge : ∀ {i j : V} (e : i ⟶ j), ∃ z : ℤ, (D : ℚ) * cost e = z)
    (hend : ∀ i, ∃ z : ℤ, (D : ℚ) * r i = z) (k : ℕ) (a : V) :
    ∃ z : ℤ, (D : ℚ) * (Layer.lookup index (plans index cost r out k) a).total = z := by
  let p := Layer.lookup index (plans index cost r out k) a
  obtain ⟨z, hz⟩ := weight_denominator cost D hedge p.path
  obtain ⟨c, hc⟩ := hend p.finish
  exact ⟨z + c, by rw [show (Layer.lookup index (plans index cost r out k) a).total = _ from
    p.total_spec, mul_add, hz, hc, Int.cast_add]⟩

theorem plans_abs_total_le (C R : ℚ) (hC : 0 ≤ C)
    (hedge : ∀ {i j : V} (e : i ⟶ j), |cost e| ≤ C) (hend : ∀ i, |r i| ≤ R)
    (k : ℕ) (a : V) : |(Layer.lookup index (plans index cost r out k) a).total| ≤ (k : ℚ) * C + R := by
  let p := Layer.lookup index (plans index cost r out k) a
  have hlen : p.path.length ≤ k := p.steps_spec ▸ plans_steps_le index cost r out k a
  have hbudget : (p.path.length : ℚ) * C ≤ (k : ℚ) * C :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hlen) hC
  change |p.total| ≤ _
  rw [p.total_spec]
  exact (abs_add_le _ _).trans (add_le_add ((abs_weight_le cost C hedge p.path).trans hbudget) (hend _))

end Reconstruction

end Potentials
end Market
end PriceGame
end LinearProgramming
end Optimization
end OAI
