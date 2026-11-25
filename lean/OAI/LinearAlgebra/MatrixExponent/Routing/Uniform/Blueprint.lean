import OAI.LinearAlgebra.MatrixExponent.Routing.Uniform.Colours
import OAI.LinearAlgebra.MatrixExponent.Routing.Uniform.Meter
import OAI.LinearAlgebra.MatrixExponent.Routing.Uniform.Tables
import OAI.LinearAlgebra.MatrixExponent.Routing.Algorithm.Computability
import OAI.LinearAlgebra.MatrixExponent.Routing.Algorithm.Spec

section
/-!
# Materializing the numeric tables

Each site query runs once while filling a vector. Subsequent reads
index this vector. The charge includes the metered steps, a fixed
allowance per slot and setup for the digit tables and array length.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Routing.Uniform.Materialize
open Coloring (B)
variable {M : ℕ}

private def scalar (q : Index.Query M) (h : ℕ) : Work ℕ :=
  let e := q.code
  let z := e.run h 0 0 0
  ⟨z.val, 16 * (e.width + h + 3) + z.steps⟩

private theorem scalar_eq (q : Index.Query M) (h : ℕ) :
    (scalar q h).value = q.code.eval h 0 0 0 := q.code.run_val h 0 0 0

def count (M h : ℕ) : Work ℕ := scalar (.total (M := M)) h

theorem count_eq (hM : 1 < M) (h : ℕ) : (count M h).value = Uniform.count M h :=
  (scalar_eq _ _).trans (Index.eval_total _ _ _ _ hM)

private def table {A : Type} (q : Index.Query M) (h b : ℕ)
    (f : (x : B (h + 1)) → (v : ℕ) → v = q.code.eval h b x.val 0 → A) :
    Work (B (h + 1) → A) :=
  let e := q.code
  let a : Work (B (h + 1) → A) := Work.tab fun x =>
    let z := e.run h b x.val 0
    ⟨f x z.val (e.run_val h b x.val 0), z.steps⟩
  ⟨a.value, 16 * (e.width + h + 3) + a.steps⟩

private theorem table_eq {A : Type} (q : Index.Query M) (h b : ℕ)
    (f : (x : B (h + 1)) → (v : ℕ) → v = q.code.eval h b x.val 0 → A) (x : B (h + 1)) :
    (table q h b f).value x = f x (q.code.eval h b x.val 0) rfl := by
  simp only [table, Work.tab_value, Index.run_val]

private def address (q : Index.Query M) (h : ℕ) (s : B (h + 1) → B (h + 1))
    (he : ∀ x, q.code.eval h 0 x.val 0 = (s x).val) : Work (B (h + 1) → B (h + 1)) :=
  table q h 0 (fun x v hv => ⟨v, (hv.trans (he x)).trans_lt (s x).isLt⟩)

private theorem address_eq (q : Index.Query M) (h : ℕ) (s : B (h + 1) → B (h + 1))
    (he : ∀ x, q.code.eval h 0 x.val 0 = (s x).val) : (address q h s he).value = s := by
  funext x
  rw [address, table_eq]
  exact Fin.ext (he x)

def digit (π : Equiv.Perm (Fin M)) (hM : 1 < M) (h : ℕ) : Work (B (h + 1) → B (h + 1)) :=
  address (.digit π) h (Uniform.packDigit hM π h) (fun x => Index.eval_packDigit hM h 0 π x 0)

theorem digit_eq (π : Equiv.Perm (Fin M)) (hM : 1 < M) (h : ℕ) :
    (digit π hM h).value = Uniform.packDigit hM π h := address_eq _ _ _ _

variable (p : ProductChart M) (hM : 1 < M) (h : ℕ)

def group (b : ℕ) : Work (B (h + 1) → ℕ) := table (.group p) h b (fun _ v _ => v)

include hM in
theorem group_eq (b : ℕ) (hb : b ≤ h + 2) :
    (group p h b).value = fun x => p.position h x / 2 ^ b := by
  funext x
  rw [group, table_eq]
  exact Index.eval_group p hM h b hb x 0

private def assignment :=
  address (.assign p) h (fun x => (reservation hM p h).assign x.val)
    (fun x => Index.eval_assign p hM h 0 x.val 0)

private def extend (a : B (h + 1) → B (h + 1)) : ℕ → B (h + 1) :=
  let n := 2 ^ (h + 1)
  fun x => if hx : x < n then a ⟨x, hx⟩ else 0

private theorem extend_eq : extend h (assignment p hM h).value = (reservation hM p h).assign := by
  have he : (assignment p hM h).value = fun x => (reservation hM p h).assign x.val :=
    address_eq (.assign p) h _ (fun x => Index.eval_assign p hM h 0 x.val 0)
  rw [he]
  funext x
  by_cases hx : x < 2 ^ (h + 1)
  · simp only [extend, dite_eq_left hx]
  · have hr : p.rows h ≤ 2 ^ (h + 1) := (Nat.le_mul_of_pos_right _ (p.degree_pos h hM)).trans
      ((p.area h).le.trans (count_bounds hM h).2.le)
    simp only [extend, dite_eq_right hx, reservation, dite_eq_right (show ¬ x < p.rows h by omega)]

private def support : Work (Reservation (h + 1)) :=
  let a := assignment p hM h
  let n := scalar (.rows p) h
  ⟨{ size := n.value
     assign := extend h a.value
     unique := by
       change Set.InjOn (extend h (assignment p hM h).value) (Set.Iio (scalar (.rows p) h).value)
       rw [extend_eq, scalar_eq]
       change Set.InjOn _ (Set.Iio ((Index.rows p).eval h 0 0 0))
       rw [Index.eval_rows hM]
       exact (reservation hM p h).unique }, a.steps + n.steps + 8⟩

private theorem support_eq : (support p hM h).value = reservation hM p h := by
  have ext (x y : Reservation (h + 1)) (hs : x.size = y.size) (ha : x.assign = y.assign) : x = y := by
    cases x; cases y; cases hs; cases ha; rfl
  exact ext _ _ ((scalar_eq _ _).trans (Index.eval_rows hM h 0 p 0 0)) (extend_eq p hM h)

private def base :=
  address (.base p) h (Uniform.chart hM p h).base (fun x => Index.eval_base p hM h 0 x 0)
private def location :=
  address (.location p) h (Uniform.chart hM p h).location (fun x => Index.eval_location p hM h 0 x 0)
private def mask (M h : ℕ) := table (.mask (M := M)) h 0 (fun _ v _ => decide (v = 1))

def chart : Work (Uniform.Chart (h + 1)) :=
  let a := base p hM h
  let c := location p hM h
  let m := mask M h
  let s := support p hM h
  let d := scalar (.columns p) h
  ⟨⟨a.value, c.value, m.value, s.value, d.value⟩, a.steps + c.steps + m.steps + s.steps + d.steps + 8⟩

theorem chart_eq : (chart p hM h).value = Uniform.chart hM p h := by
  have ext (x y : Uniform.Chart (h + 1)) (a : x.base = y.base) (b : x.location = y.location)
      (c : x.mask = y.mask) (d : x.support = y.support) (e : x.degree = y.degree) : x = y := by
    cases x; cases y; cases a; cases b; cases c; cases d; cases e; rfl
  refine ext _ _ (address_eq (.base p) h _ (fun x => Index.eval_base p hM h 0 x 0))
    (address_eq (.location p) h _ (fun x => Index.eval_location p hM h 0 x 0)) ?_ (support_eq p hM h)
    ((scalar_eq _ _).trans (Index.eval_columns hM h 0 p 0 0))
  funext x
  change (mask M h).value x = _
  rw [mask, table_eq]
  change decide ((Index.mask M).eval h 0 x.val 0 = 1) = _
  rw [Index.eval_mask p hM]
  cases (Uniform.chart hM p h).mask x <;> rfl

private theorem enlarge (h d : ℕ) :
    100 * (2 ^ (h + 1) * (100 + h) ^ d) ≤ 2 ^ (h + 1) * (100 + h) ^ (d + 1) := by
  rw [pow_succ (100 + h), ← mul_assoc (2 ^ (h + 1)), mul_comm 100]
  exact Nat.mul_le_mul_left _ (by omega)

private theorem charges (h d : ℕ) (q : Index.Query M)
    (hw : q.code.width ≤ d) (hc : q.code.cost h ≤ (100 + h) ^ d) :
    let n := 2 ^ (h + 1) * (100 + h) ^ (d + 2)
    (scalar q h).steps ≤ n ∧
      ∀ {A : Type} (b : ℕ) (f : (x : B (h + 1)) → (v : ℕ) → v = q.code.eval h b x.val 0 → A),
        (table q h b f).steps ≤ n := by
  let u := (100 + h) ^ (d + 1)
  let t := 2 ^ (h + 1) * u
  have hsmall : 100 + h ≤ u := Nat.le_self_pow (by omega) _
  have hpow : (100 + h) ^ d ≤ u := Nat.pow_le_pow_right (by omega) (by omega)
  have hwidth : q.code.width ≤ u := hw.trans
    (Nat.lt_two_pow_self.le.trans ((Nat.pow_le_pow_left (by omega) _).trans hpow))
  have work (b x) : (q.code.run h b x 0).steps ≤ u :=
    (q.code.run_steps h b x 0).trans (hc.trans hpow)
  have ht : u ≤ t := Nat.le_mul_of_pos_left _ (Nat.two_pow_pos _)
  have hn : 100 * t ≤ 2 ^ (h + 1) * (100 + h) ^ (d + 2) := enlarge h (d + 1)
  constructor
  · change 16 * (q.code.width + h + 3) + (q.code.run h 0 0 0).steps ≤ _
    have := work 0 0
    omega
  · intro A b f
    have he : (∑ x : B (h + 1), (64 + (q.code.run h b x.val 0).steps)) ≤ 2 * t := calc
      _ ≤ ∑ _x : B (h + 1), 2 * u := Finset.sum_le_sum (fun x _ => by have := work b x.val; omega)
      _ = _ := by simp [t, mul_left_comm]
    simp only [table, Work.tab_steps]
    omega

/-- The same exponent works at every height for every digit permutation
and every product chart over the fixed alphabet. -/
theorem bounds (M : ℕ) : ∃ d, ∀ (hM : 1 < M) (h : ℕ),
    let n := 2 ^ (h + 1) * (100 + h) ^ d
    (∀ π, (digit π hM h).steps ≤ n) ∧
    (∀ p, (chart p hM h).steps ≤ n) ∧
    (∀ (p : ProductChart M) b, (group p h b).steps ≤ n) ∧ (count M h).steps ≤ n := by
  obtain ⟨d, hd⟩ := Index.Query.bounds M
  refine ⟨d + 3, fun hM h => ?_⟩
  let t := 2 ^ (h + 1) * (100 + h) ^ (d + 2)
  have ht : 0 < t := by unfold t; positivity
  have hn : 100 * t ≤ 2 ^ (h + 1) * (100 + h) ^ (d + 3) := enlarge h (d + 2)
  have hc (q : Index.Query M) := charges h d q (hd q).1 ((hd q).2 h)
  have ha (q : Index.Query M) (s : B (h + 1) → B (h + 1)) (hs) :
      (address q h s hs).steps ≤ t := (hc q).2 _ _
  have hb : t ≤ 2 ^ (h + 1) * (100 + h) ^ (d + 3) := by omega
  refine ⟨fun π => ?_, fun p => ?_, fun p b => ?_, ((hc .total).1).trans hb⟩
  · exact (ha (.digit π) _ (fun x => Index.eval_packDigit hM h 0 π x 0)).trans hb
  · have h₁ : (base p hM h).steps ≤ t := ha (.base p) _ (fun x => Index.eval_base p hM h 0 x 0)
    have h₂ : (location p hM h).steps ≤ t :=
      ha (.location p) _ (fun x => Index.eval_location p hM h 0 x 0)
    have h₃ : (mask M h).steps ≤ t := (hc .mask).2 _ _
    have h₄ : (assignment p hM h).steps ≤ t :=
      ha (.assign p) _ (fun x => Index.eval_assign p hM h 0 x.val 0)
    have h₅ : (scalar (.rows p) h).steps ≤ t := (hc (.rows p)).1
    have h₆ : (scalar (.columns p) h).steps ≤ t := (hc (.columns p)).1
    simp only [chart, support]
    omega
  · exact ((hc (.group p)).2 b _).trans hb

end OAI.LinearAlgebra.MatrixExponent.Routing.Uniform.Materialize
end

section
/-!
# Generating the program of a fixed permutation expression

The recursive compiler takes a height and an expression on fixed
digit alphabets. It materializes literal tables on those digits,
then emits the instructions for the permutation factors. Its result
implements the expression on *every* input, including invalid tags.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Routing.Uniform
open Algorithm Coloring
variable {w h M : ℕ}

namespace Builder

def pick {A : Type} (j : Fin 3) : Builder w (Recipe.pick (α := A) j) 2 := by
  unfold Recipe.pick
  by_cases h : j = 0
  · simp only [h, ite_true]
    exact Builder.fst.mono (by decide)
  · simp only [h, ite_false]
    by_cases g : j = 1
    · simp only [g, ite_true]
      exact Builder.snd.comp .fst
    · simp only [g, ite_false]
      exact Builder.snd.comp .snd

private def clean (hh : h + 1 ≤ w) (size : ℕ) (he : size = count M h) :
    Builder w (Recipe.clean M h) (2 ^ (h + 1) * 7) := by
  have p := mask_table hh (fun i => decide (i.val < size))
  rw [he] at p
  unfold Recipe.clean
  simpa only [decide_eq_true_eq] using p

end Builder

namespace Recipe
variable (hM : 1 < M)

def exponent : Recipe M → ℕ
  | .id | .target | .digit _ => 1
  | .inv r => max r.exponent 25 + 1
  | .mul r s => max r.exponent s.exponent + 1
  | .factor _ _ r => max r.exponent 110 + 1

private theorem combine (w h c d : ℕ) :
    2 ^ h * (100 + w) ^ c + 2 ^ h * (100 + w) ^ d + 10 * 2 ^ h ≤ 2 ^ h * (100 + w) ^ (max c d + 1) := by
  have := budget_mono h w (le_max_left c d)
  have := budget_mono h w (le_max_right c d)
  have := budget_base h w (max c d)
  have := budget_step h w (max c d)
  omega

/-- The outer counter charges traversal and construction of numeric tables.
The inner Builder charges instruction emission separately. -/
def generate (r : Recipe M) (h : ℕ) (hw : 3 * (h + 1) + 10 ≤ w) :
    Work (Builder w (r.eval hM h) (2 ^ (h + 1) * (100 + w) ^ r.exponent)) := by
  have hh : h + 1 ≤ w := by omega
  have hp : 0 < 2 ^ (h + 1) := Nat.two_pow_pos _
  have start : 2 ^ (h + 1) * 2 ≤ 2 ^ (h + 1) * (100 + w) ^ 1 := by
    rw [pow_one]; exact Nat.mul_le_mul_left _ (by omega)
  match r with
  | .id => exact ⟨(Builder.tableLits hh _root_.id).mono start, 64⟩
  | .target => exact ⟨Builder.id.mono ((by omega : 1 ≤ 2 ^ (h + 1) * 2).trans start), 64⟩
  | .digit p =>
    let a := Materialize.digit p hM h
    refine ⟨?_, 64 + a.steps⟩
    have v := Builder.tableLits (A := ArrayOf (h + 1)) hh a.value
    rw [show a.value = packDigit hM p h from Materialize.digit_eq p hM h] at v
    exact v.mono start
  | .inv r =>
    let ih := generate r h hw
    refine ⟨(ih.value.comp (Builder.inverse hh)).mono ?_, 64 + ih.steps⟩
    exact (Nat.le_add_right ..).trans (combine w (h + 1) r.exponent 25)
  | .mul r s =>
    let ih := generate r h hw
    let ih' := generate s h hw
    refine ⟨((ih.value.pair ih'.value).comp (Builder.gather hh hh)).mono ?_, 64 + ih.steps + ih'.steps⟩
    have := combine w (h + 1) r.exponent s.exponent
    simp only [exponent]; omega
  | .factor p j r =>
    let ih := generate r h hw
    let c := Materialize.chart p hM h
    let n := Materialize.count M h
    refine ⟨?_, 64 + ih.steps + c.steps + n.steps⟩
    have mid := Builder.chart_run hw c.value
    rw [show c.value = Uniform.chart hM p h from Materialize.chart_eq p hM h] at mid
    let mask := Builder.clean hh n.value (Materialize.count_eq hM h)
    refine (((ih.value.comp mid).comp (Builder.pick j)).comp mask).mono ?_
    have := combine w (h + 1) r.exponent 110
    simp only [exponent]; omega

abbrev compile (r : Recipe M) (h : ℕ) (hw : 3 * (h + 1) + 10 ≤ w) :
    Builder w (r.eval hM h) (2 ^ (h + 1) * (100 + w) ^ r.exponent) :=
  (r.generate hM h hw).value

private theorem extra (h d : ℕ) :
    64 + 3 * (2 ^ (h + 1) * (100 + h) ^ d) ≤ 2 ^ (h + 1) * (100 + h) ^ (d + 1) := by
  have := budget_step (h + 1) h d
  have : 0 < 2 ^ (h + 1) * (100 + h) ^ d := by positivity
  omega

/-- For a fixed recipe the cost of producing numeric data is bounded
uniformly in height and independently of the requested word width. -/
theorem steps (r : Recipe M) :
    ∃ d, ∀ h w (hw : 3 * (h + 1) + 10 ≤ w),
      (r.generate hM h hw).steps ≤ 2 ^ (h + 1) * (100 + h) ^ d := by
  obtain ⟨a, ha⟩ := Materialize.bounds M
  have leaf (h : ℕ) : 64 ≤ 2 ^ (h + 1) * (100 + h) ^ 1 :=
    (Nat.le_add_right ..).trans (extra h 0)
  induction r with
  | id => exact ⟨1, fun h _ _ => leaf h⟩
  | target => exact ⟨1, fun h _ _ => leaf h⟩
  | digit p =>
    refine ⟨a + 1, fun h w hw => ?_⟩
    change 64 + (Materialize.digit p hM h).steps ≤ _
    have := (ha hM h).1 p
    have := extra h a
    omega
  | inv r hr =>
    obtain ⟨d, hd⟩ := hr
    refine ⟨d + 1, fun h w hw => ?_⟩
    change 64 + (r.generate hM h hw).steps ≤ _
    have := hd h w hw
    have := extra h d
    omega
  | mul r s hr hs =>
    obtain ⟨c, hc⟩ := hr
    obtain ⟨d, hd⟩ := hs
    refine ⟨max c d + 1, fun h w hw => ?_⟩
    change 64 + (r.generate hM h hw).steps + (s.generate hM h hw).steps ≤ _
    have := (hc h w hw).trans (budget_mono _ _ (le_max_left c d))
    have := (hd h w hw).trans (budget_mono _ _ (le_max_right c d))
    have := extra h (max c d)
    omega
  | factor p j r hr =>
    obtain ⟨d, hd⟩ := hr
    refine ⟨max d a + 1, fun h w hw => ?_⟩
    change 64 + (r.generate hM h hw).steps + (Materialize.chart p hM h).steps+
      (Materialize.count M h).steps ≤ _
    have hm := budget_mono (h + 1) h (le_max_right d a)
    have := ((ha hM h).2.1 p).trans hm
    have := (ha hM h).2.2.2.trans hm
    have := (hd h w hw).trans (budget_mono _ _ (le_max_left d a))
    have := extra h (max d a)
    omega

end Recipe
end OAI.LinearAlgebra.MatrixExponent.Routing.Uniform
end

section
/-!
# Generating the local decision program from a fixed array

The table stores only bounded words, bits and vectors. Its size can
be large, but is independent of the height. At each width the same
scan builds a program for comparing observations and selecting plans.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Routing.Uniform
open Coloring
open Algorithm.RAM (Observation observe)

structure MenuEntry (t q l p : ℕ) where
  tests : Vector (Vector Bool (2 ^ t)) (2 ^ t)
  marks : Vector (B q) (2 ^ t)
  key : B l
  slots : Vector (Bool × Bool × B p × B p) (2 ^ p)

structure Menu (t q l p n : ℕ) where
  entries : Vector (MenuEntry t q l p) n

variable {t q l p n w : ℕ}

namespace MenuEntry

def input (e : MenuEntry t q l p) : Observation t q :=
  (fun i j => (e.tests[i.val])[j.val], fun i => e.marks[i.val])

def plan (e : MenuEntry t q l p) : Decor.Plan l p p :=
  (e.key, fun j => e.slots[j.val])

def store (x : Observation t q) (v : Decor.Plan l p p) : MenuEntry t q l p :=
  ⟨Vector.ofFn (fun i => Vector.ofFn (x.1 i)), Vector.ofFn x.2, v.1, Vector.ofFn v.2⟩

theorem input_store (x : Observation t q) (v : Decor.Plan l p p) :
    (store x v).input = x := by simp [store, input]

theorem plan_store (x : Observation t q) (v : Decor.Plan l p p) :
    (store x v).plan = v := by simp [store, plan]

end MenuEntry
namespace Menu

private def emptyPlan (l p : ℕ) : Decor.Plan l p p := (0, fun _ => (false, false, 0, 0))

private def scan : List (MenuEntry t q l p) → Observation t q → Decor.Plan l p p
  | [], _ => emptyPlan l p
  | e::es, x => if x = e.input then e.plan else scan es x

def lookup (v : Menu t q l p n) := scan v.entries.toList

private theorem scan_store (b : Observation t q → Decor.Plan l p p)
    (s : List (Observation t q)) (x : Observation t q) (hx : x ∈ s) :
    scan (s.map (fun y => MenuEntry.store y (b y))) x = b x := by
  induction s with
  | nil => simp at hx
  | cons y s ih =>
    simp only [List.map_cons, scan, MenuEntry.input_store, MenuEntry.plan_store]
    by_cases e : x = y
    · simp only [e, ite_true]
    · rw [ite_eq_right e]
      exact ih ((List.mem_cons.mp hx).resolve_left e)

end Menu

/-- The group elements and the single array of decisions are chosen once,
before fixing any height. -/
theorem menu_exists {G : Type} [Group G] {f : Decor G q → Decor.Plan l p p} (hf : Decor.Local f) :
    ∃ (t : ℕ) (g : B t → G) (n : ℕ) (v : Menu t q l p n),
      ∀ r, v.lookup (observe g r) = f r := by
  obtain ⟨t, g, b, _, _, _, hb⟩ := Algorithm.RAM.menu hf
  let s := (Finset.univ : Finset (Observation t q)).toList
  let a := s.map (fun y => MenuEntry.store y (b y))
  let v : Menu t q l p a.length := ⟨⟨a.toArray, by simp⟩⟩
  refine ⟨t, g, a.length, v, fun r => ?_⟩
  have ha : v.entries.toList = a := by simp [v]
  rw [Menu.lookup, ha]
  exact (Menu.scan_store b s (observe g r) (by simp [s])).trans (hb r)

private def arrayCost (t c : ℕ) := 1 + (c + 3) * 2 ^ t
private def inputCost (t : ℕ) := (1 + arrayCost t (arrayCost t 4)) + (1 + arrayCost t 4) + 1 + 1
private def planCost (p : ℕ) := 1 + 2 ^ p * 8 + 1
def menuCost (t p n : ℕ) := planCost p + (inputCost t + planCost p + 3) * n

namespace Builder
variable {A D : Type} {c d : ℕ}

private abbrev Test (w : ℕ) (A : Type) [DecidableEq A] (c : ℕ) :=
  ∀ a : A, Builder w (fun x : A => decide (x = a)) c

private def testBool : Test w Bool 4 := fun a =>
  (Builder.id.pair Builder.id).comp (.gate (fun x => decide (x.1 = a)))

private def testWord (hq : q ≤ w) : Test w (B q) 4 := fun a =>
  (Builder.id.pair (.lit hq a)).comp (.eq hq)

private def testProd [DecidableEq A] [DecidableEq D] (ha : Test w A c) (hd : Test w D d) :
    Test w (A × D) (1 + c + (1 + d) + 1 + 1) := by
  rintro ⟨a, b⟩
  have H := ((Builder.fst.comp (ha a)).pair (Builder.snd.comp (hd b))).comp (.gate (fun x => x.1 && x.2))
  convert H using 1
  funext x
  rw [Bool.eq_iff_iff]
  simp [Prod.ext_iff]

private def testArray [DecidableEq A] (ha : Test w A c) (ht : t ≤ w) :
    Test w (B t → A) (arrayCost t c) := by
  intro a
  have scan (k : ℕ) (hk : k ≤ 2 ^ t) :
      Builder w (fun x : B t → A => decide (∀ i : B t, i.val < k → x i = a i)) (1 + (c + 3) * k) := by
    induction k with
    | zero => simpa using (Builder.bit (w := w) (A := B t → A) true)
    | succ k ih =>
      let i : B t := ⟨k, hk⟩
      have H := (((Builder.at ht i).comp (ha (a i))).pair (ih (by omega))).comp
        (.gate (fun x => x.1 && x.2))
      convert H using 1
      · funext x
        rw [Bool.eq_iff_iff]
        simp only [Function.comp_apply, Bool.and_eq_true, decide_eq_true_eq]
        refine ⟨fun hy => ⟨hy i (by unfold i; simp), fun j hj => hy j (by omega)⟩, ?_⟩
        rintro ⟨hi, hx⟩ j hj
        by_cases h : j.val < k
        · exact hx j h
        · have he : j = i := Fin.ext (by change j.val = k; omega)
          rwa [he]
      · simp only [mul_add, mul_one]
        omega
  have H := scan (2 ^ t) le_rfl
  unfold arrayCost
  convert H using 1
  funext x
  rw [Bool.eq_iff_iff]
  simp [funext_iff]

private def testInput (ht : t ≤ w) (hq : q ≤ w) : Test w (Observation t q) (inputCost t) :=
  testProd (testArray (testArray testBool ht) ht) (testArray (testWord hq) ht)

private def planLits (hl : l ≤ w) (hp : p ≤ w) (v : Decor.Plan l p p) :
    Builder w (fun _ : A => v) (planCost p) := by
  have H : Builder w (fun _ : A => v.2) (2 ^ p * 8) :=
    .tab hp _ (fun i => (Builder.bit (v.2 i).1).pair ((Builder.bit (v.2 i).2.1).pair
      ((Builder.lit hp (v.2 i).2.2.1).pair (Builder.lit hp (v.2 i).2.2.2))))
  exact (Builder.lit hl v.1).pair H

/-- Read the fixed vector backwards, emitting one selection per entry.
The list in the specification is erased from the generator. -/
def menu (ht : t ≤ w) (hq : q ≤ w) (hl : l ≤ w) (hp : p ≤ w) (v : Menu t q l p n) :
    Builder w v.lookup (menuCost t p n) := by
  have scan (k : ℕ) (hk : k ≤ n) :
      Builder w (Menu.scan (v.entries.toList.drop (n - k))) (menuCost t p k) := by
    induction k with
    | zero =>
      have he : v.entries.toList.drop (n - 0) = [] := List.drop_eq_nil_of_le (by simp)
      rw [he]
      exact planLits hl hp (Menu.emptyPlan l p)
    | succ k ih =>
      let j := n - (k + 1)
      have hj : j < n := by unfold j; omega
      let e := v.entries[j]
      have he : v.entries.toList.drop j = e :: v.entries.toList.drop (n - k) := by
        rw [List.drop_eq_getElem_cons (by simpa using hj), Vector.getElem_toList,
          show j + 1 = n - k by unfold j; omega]
      have H := ((testInput ht hq e.input).pair ((planLits hl hp e.plan).pair
        (ih (by omega)))).comp Builder.select
      change Builder w (Menu.scan (v.entries.toList.drop j)) _
      rw [he]
      convert H using 1
      · funext x
        simp only [Menu.scan, Function.comp_apply, decide_eq_true_eq]
      · simp only [menuCost, mul_add, mul_one]
        omega
  simpa only [Menu.lookup, Nat.sub_self, List.drop_zero] using scan n le_rfl

end Builder
end OAI.LinearAlgebra.MatrixExponent.Routing.Uniform
end

section
/-! # Compiling a fixed menu and the reads of the selected remote addresses -/

namespace OAI.LinearAlgebra.MatrixExponent.Routing.Uniform
open Coloring Transport

variable {w h p q t l n : ℕ}

private abbrev Addresses (h t : ℕ) := B t → Site h → Site h
private abbrev Source (h t q : ℕ) := (B t → Site h) × (Site h → B q)
abbrev DispatchInput (h t p q : ℕ) := (Site h → B q) × Addresses h t × Addresses h p

private def view (x : Source h t q) : Algorithm.RAM.Observation t q :=
  (fun j k => decide (x.1 j = x.1 k), x.2 ∘ x.1)

def Menu.dispatch (v : Menu t q l p n) (x : DispatchInput h t p q) (i : Site h) :=
  Decor.resolve (v.lookup (view (fun j => x.2.1 j i, x.1))) (fun j => x.2.2 j i)

/-- Correctness for one site, assuming the two address tables agree
with the actions used to observe this site and to resolve its slots. -/
theorem Menu.dispatch_eq {G : Type} [Group G] (v : Menu t q l p n)
    (g : B t → G) (hop : B p → G) (f : Decor G q → Decor.Plan l p p)
    (hv : ∀ r, v.lookup (Algorithm.RAM.observe g r) = f r)
    (act : MulAction G (Site h)) (z : Site h → B q) (X : B t → Site h → Site h)
    (Y : B p → Site h → Site h) (i : Site h)
    (hx : ∀ j, X j i = act.smul (g j) i) (hy : ∀ j, Y j i = act.smul (hop j) i) :
    v.dispatch (z, X, Y) i = Decor.resolve (f ⟨@Root.mk _ _ _ act i, z⟩) (fun j => act.smul (hop j) i) := by
  let r : Decor G q := ⟨@Root.mk _ _ _ act i, z⟩
  have he : view (fun j => X j i, z) = Algorithm.RAM.observe g r := by
    apply Prod.ext
    · funext a b
      rw [Bool.eq_iff_iff]
      simp only [view, Algorithm.RAM.observe, Root.see, decide_eq_true_eq, hx]
      rfl
    · exact funext fun a => congrArg z (hx a)
  unfold Menu.dispatch
  rw [he, hv]
  exact congrArg _ (funext hy)

private def addresses_at (ht : t ≤ w) (hh : h + 1 ≤ w) (i : Site h) :
    Builder w (fun (x : Addresses h t) j => x j i) (2 ^ t * 3) :=
  .tab ht _ (fun j => (Builder.at ht j).comp (.at hh i))

private def viewCost (t : ℕ) := 2 ^ t * (2 ^ t * 7 + 1) + (3 + 2 ^ t * 6) + 1

private def viewBuilder (ht : t ≤ w) (hh : h + 1 ≤ w) :
    Builder w (view : Source h t q → _) (viewCost t) := by
  have e : Builder w (fun (x : Source h t q) j k => decide (x.1 j = x.1 k)) (2 ^ t * (2 ^ t * 7 + 1)) :=
    .tab ht _ (fun j => .tab ht _ (fun k =>
      ((Builder.fst.comp (.at ht j)).pair (Builder.fst.comp (.at ht k))).comp (.eq hh)))
  exact e.pair ((Builder.snd.pair Builder.fst).comp (Builder.gather hh ht))

private def resolveBuilder (hp : p ≤ w) :
    Builder w (fun x : Decor.Plan l p p × (B p → Site h) => Decor.resolve x.1 x.2)
      (2 + 2 ^ p * 28 + 1) := by
  let A := Decor.Plan l p p × (B p → Site h)
  have H : Builder w (fun x : A => (Decor.resolve x.1 x.2).2) (2 ^ p * 28) := by
    refine Builder.tab hp _ (m := 27) (fun j => ?_)
    have T : Builder w (fun x : A => x.1.2 j) 3 := (Builder.fst.comp Builder.snd).comp (.at hp j)
    have K := (T.comp Builder.snd).comp Builder.snd
    have a := (Builder.snd.pair (K.comp Builder.fst)).comp (.read hp)
    exact (T.comp Builder.fst).pair (((T.comp Builder.snd).comp Builder.fst).pair (a.pair (K.comp Builder.snd)))
  exact (Builder.fst.comp Builder.fst).pair H

private def rowCost (t p c : ℕ) := 20 + 3 * 2 ^ t + viewCost t + c + 31 * 2 ^ p

def dispatchCost (t p n : ℕ) := rowCost t p (menuCost t p n) + 1

def Builder.dispatch (v : Menu t q l p n) (ht : t ≤ w) (hq : q ≤ w) (hl : l ≤ w)
    (hp : p ≤ w) (hh : h + 1 ≤ w) :
    Builder w (v.dispatch (h := h)) (2 ^ (h + 1) * dispatchCost t p n) := by
  have hb := Builder.menu ht hq hl hp v
  unfold dispatchCost
  refine Builder.tab hh _ (fun i => ?_)
  have X : Builder w (fun (x : DispatchInput h t p q) j => x.2.1 j i) (2 + 2 ^ t * 3) :=
    (Builder.snd.comp Builder.fst).comp (addresses_at ht hh i)
  have Y : Builder w (fun (x : DispatchInput h t p q) j => x.2.2 j i) (2 + 2 ^ p * 3) :=
    (Builder.snd.comp Builder.snd).comp (addresses_at hp hh i)
  have H := ((X.pair Builder.fst).comp (viewBuilder ht hh)).comp hb
  exact ((H.pair Y).comp (resolveBuilder hp)).mono (by unfold rowCost; omega)

end OAI.LinearAlgebra.MatrixExponent.Routing.Uniform
end

section
/-!
# A height-independent description of the controller

The menu, its observations and the recipe for each slot are finite
data. The compiler takes the height as its only variable parameter.
At each height it generates the same program for all input tags,
selectors and payload widths.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Routing.Uniform
open Coloring Transport Algorithm
variable {w h M t p q l n : ℕ}

def Builder.inflate (hh : h + 1 ≤ w) : Builder w (Routing.inflate h) (2 ^ (h + 1) * 3) := by
  have lift : Builder w (⇑(lowerHalf h)) 1 := by
    have e : (⇑(lowerHalf h)) = fun x : B h => Fin.ofNat (2 ^ (h + 1)) x.val := by
      funext x
      apply Fin.ext
      change x.val = x.val % 2 ^ (h + 1)
      exact (Nat.mod_eq_of_lt (lowerHalf h x).isLt).symm
    rw [e]
    exact .resize (by omega) hh
  refine Builder.tab hh (fun i x => Routing.inflate h x i) (m := 2) (fun i => ?_)
  by_cases hi : i.val < 2 ^ h
  · simp only [Routing.inflate, dite_eq_left hi]
    exact (Builder.at (show h ≤ w by omega) ⟨i, hi⟩).comp lift
  · simp only [Routing.inflate, dite_eq_right hi]
    exact (Builder.lit hh i).mono (by decide)

namespace Recipe
variable (hM : 1 < M) (f : B t → Recipe M)

def rates := Finset.univ.sup (fun i => (f i).exponent)

def menuCost (h w : ℕ) := 2 ^ t * (2 ^ (h + 1) * (100 + w) ^ (rates f) + 1)

/-- Materialize each recipe before sharing its code and cost. -/
def menu (ht : t ≤ w) (hh : 3 * (h + 1) + 10 ≤ w) :
    Work (Builder w (fun x i => (f i).eval hM h x) (menuCost f h w)) :=
  let a := Work.dtab (fun i => (f i).generate hM h hh)
  let code := Builder.tab ht _ (fun i => (a.value i).mono
    (budget_mono (h + 1) w (Finset.le_sup (f := fun i => (f i).exponent) (Finset.mem_univ i))))
  ⟨code, 64 + a.steps⟩

end Recipe

structure Blueprint (M t p q l n : ℕ) where
  watch : B t → Recipe M
  hop : B p → Recipe M
  chart : B p → ProductChart M
  menu : Menu t q l p n

namespace Blueprint
variable (a : Blueprint M t p q l n) (hM : 1 < M)

abbrev bits (h : ℕ) := 3 * (h + 1) + 10
def limit (t p q l : ℕ) := max (max t p) (max q l)

def dispatch (h : ℕ) (x : (Input h q).obj) : (Controls h p (.addr l)).obj :=
  let y := Routing.inflate h x.1
  a.menu.dispatch (x.2, fun i => (a.watch i).eval hM h y, fun j => (a.hop j).eval hM h y)

def charge (h : ℕ) := 1 + (1 + 2 ^ (h + 1) * 3 + (Recipe.menuCost a.watch h (bits h) +
  Recipe.menuCost a.hop h (bits h) + 1)) + 1 + 2 ^ (h + 1) * dispatchCost t p n

def build (h : ℕ) (hh : limit t p q l ≤ h) :
    Work (Builder (bits h) (a.dispatch hM h) (a.charge h)) := by
  unfold limit at hh
  have ht : t ≤ bits h := by unfold bits; omega
  have hp : p ≤ bits h := by unfold bits; omega
  have hq : q ≤ bits h := by unfold bits; omega
  have hl : l ≤ bits h := by unfold bits; omega
  have hv : h + 1 ≤ bits h := by unfold bits; omega
  let x := Recipe.menu hM a.watch ht (h := h) le_rfl
  let y := Recipe.menu hM a.hop hp (h := h) le_rfl
  let paths := ((Builder.fst (D := Site h → B q)).comp (Builder.inflate hv)).comp (x.value.pair y.value)
  exact ⟨(Builder.snd.pair paths).comp (Builder.dispatch a.menu ht hq hl hp hv), 128 + x.steps + y.steps⟩

abbrev compile (h : ℕ) (hh : limit t p q l ≤ h) := (a.build hM h hh).value

def partition (h b : ℕ) (i : Port h p) :=
  Index.Query.groupValue (a.chart i.2) h b i.1

/-- Generate the instruction stream and the port list in one pass.
The two expenditure counters of the builder account for setup of
the numeral tables and emission of the instructions respectively. -/
def generate (h b : ℕ) (hh : limit t p q l ≤ h) : Work (Program h p q l × (Port h p → ℕ)) :=
  let x := a.build hM h hh
  let y := Work.tab (fun i => Materialize.group (a.chart i) h b)
  ⟨(x.value.code, fun i => y.value i.2 i.1), 64 + x.steps + x.value.made.steps + y.steps⟩

theorem production (h b : ℕ) (hh : limit t p q l ≤ h) (hb : b ≤ h + 2) :
    (a.generate hM h b hh).value = ((a.compile hM h hh).code, a.partition h b) := by
  refine Prod.ext ?_ ?_
  · rfl
  · funext i
    simp only [generate, Work.tab_value, partition, Materialize.group_eq _ hM _ _ hb,
      Index.Query.groupValue_eq _ hM _ _ hb]

end Blueprint
end OAI.LinearAlgebra.MatrixExponent.Routing.Uniform
end
