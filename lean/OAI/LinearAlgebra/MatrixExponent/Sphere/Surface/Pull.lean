import OAI.LinearAlgebra.MatrixExponent.Sphere.Seam
import OAI.LinearAlgebra.MatrixExponent.Sphere.Interpolation
import OAI.LinearAlgebra.MatrixExponent.Sphere.Private.Preparation
import Mathlib.Data.Fin.Tuple.Basic
import OAI.LinearAlgebra.MatrixExponent.Sphere.Private.Install

/-!
# Sewn pairs of sphere forms

An ordinary assignment is a parameter of the insertion tables. Only
the shared sphere states are summed here. The label can record which
ordinary bits a station reads and its role in the movement procedure.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Surface

open Finset
open scoped Classical

variable {F T X E V : Type} [Field F] {r t : ℕ}

structure Station (F : Type) (r t : ℕ) (T X : Type) where
  pos : F
  a : ℕ
  b : ℕ
  label : T
  table : X → Level r a → Level t b → F

structure Cell (F : Type) (r t : ℕ) (T E X : Type) where
  ports : List (E × F)
  stations : List (Station F r t T X)

def modes (z : F) (w : Wedge r) : List (Site F r) := w.val.map (z, ·)

def ends (P : ℕ) (h : E → Wedge r) (l : List (E × F)) : List (Site F r) :=
  l.flatMap (fun j => modes (j.2 ^ P) (h j.1))

abbrev Test (F : Type) (r t : ℕ) := List (Site F r) → List (Site F t) → F

def forms : Test F r t := fun a b => wick fieldKernel a * wick fieldKernel b

/-- Expand all insertion tables, passing the ordered sites to a test. -/
def batch (P : ℕ) (x : X) : List (Station F r t T X) → Test F r t → F
  | [], f => f [] []
  | u :: us, f => ∑ a, ∑ b, u.table x a b * batch P x us
      (fun l m => f (modes (u.pos ^ P) a.val ++ l) (modes u.pos b.val ++ m))

def Cell.eval (P : ℕ) (c : Cell F r t T E X) (x : X) (h : E → Wedge r) : F :=
  batch P x c.stations fun l m => forms (l ++ ends P h c.ports) m

/-- Contract every seam at a fixed energy by ordinary basis equality. -/
def eval [Fintype E] [Fintype V] (P : ℕ) (C : V → Cell F r t T E X)
    (d : E → ℕ) (x : X) : F :=
  ∑ a : ∀ e, Level r (d e), ∏ v, Cell.eval P (C v) x (fun e => (a e).val)

end OAI.LinearAlgebra.MatrixExponent.Sphere.Surface
end

/-! # Linear operations on insertion tables -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Surface

open Finset
open scoped Classical
variable {F T X E : Type} [Field F] {r t : ℕ} (P : ℕ) (x : X)
variable (u : List (Station F r t T X))

theorem batch_mul_left (c : F) (f : Test F r t) :
    batch P x u (fun p q => c * f p q) = c * batch P x u f := by
  induction u generalizing f with
  | nil => rfl
  | cons a l ih =>
    simp only [batch, mul_sum]
    refine sum_congr rfl fun j _ => sum_congr rfl fun k _ => ?_
    rw [ih, mul_left_comm]

theorem batch_mul_right (c : F) (f : Test F r t) :
    batch P x u (fun p q => f p q * c) = batch P x u f * c := by
  simpa only [mul_comm c] using batch_mul_left P x u c f

theorem batch_sum {I : Type*} (s : Finset I) (f : I → Test F r t) :
    batch P x u (fun p q => ∑ i ∈ s, f i p q) = ∑ i ∈ s, batch P x u (f i) := by
  induction u generalizing f with
  | nil => rfl
  | cons a l ih =>
    simp only [batch]
    rw [sum_comm (s := s)]
    refine sum_congr rfl fun j _ => ?_
    rw [sum_comm (s := s)]
    refine sum_congr rfl fun k _ => ?_
    rw [ih, mul_sum]

@[simp] theorem batch_zero : batch P x u (fun _ _ => 0) = 0 := by
  simpa only [zero_mul] using batch_mul_left P x u 0 (fun _ _ => 1)

def sumA := (u.map Station.a).sum
def sumB := (u.map Station.b).sum

omit [Field F] in
@[simp] theorem weight_modes (z : F) (a : Wedge r) : weight (modes z a) = energy a.val := by
  simp [weight, modes, Function.comp_def]

omit [Field F] in
@[simp] theorem weight_append (p q : List (Site F r)) :
    weight (p ++ q) = weight p + weight q := by simp [weight, energy]

/-- Only these pairs of words can occur in the given batch. -/
structure Within (p : List (Site F r)) (q : List (Site F t)) : Prop where
  left : ∀ y ∈ p, ∃ s ∈ u, y.1 = s.pos ^ P
  right : ∀ y ∈ q, ∃ s ∈ u, y.1 = s.pos
  wa : weight p = sumA u
  wb : weight q = sumB u

theorem batch_congr {f g : Test F r t} (h : ∀ p q, Within P u p q → f p q = g p q) :
    batch P x u f = batch P x u g := by
  induction u generalizing f g with
  | nil => exact h [] [] ⟨by simp, by simp, rfl, rfl⟩
  | cons s u ih =>
    simp only [batch]
    refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => congrArg (s.table x a b * ·) ?_
    apply ih
    intro p q hw
    apply h
    constructor
    · intro y hy
      rcases List.mem_append.mp hy with hy|hy
      · obtain ⟨_, _, rfl⟩ := List.mem_map.mp hy
        exact ⟨s, by simp, rfl⟩
      · obtain ⟨v, hv, he⟩ := hw.left y hy
        exact ⟨v, .tail _ hv, he⟩
    · intro y hy
      rcases List.mem_append.mp hy with hy|hy
      · obtain ⟨_, _, rfl⟩ := List.mem_map.mp hy
        exact ⟨s, by simp, rfl⟩
      · obtain ⟨v, hv, he⟩ := hw.right y hy
        exact ⟨v, .tail _ hv, he⟩
    · simp only [weight_append, weight_modes, a.property, hw.wa, sumA, List.map_cons, List.sum_cons]
    · simp only [weight_append, weight_modes, b.property, hw.wb, sumB, List.map_cons, List.sum_cons]

def portWeight (d : E → ℕ) (l : List (E × F)) := (l.map fun p => d p.1).sum

theorem weight_ends (d : E → ℕ) (h : E → Wedge r) (l : List (E × F))
    (hh : ∀ i ∈ l, energy (h i.1).val = d i.1) : weight (ends P h l) = portWeight d l := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    change weight (modes (i.2 ^ P) (h i.1) ++ ends P h l) = d i.1 + portWeight d l
    rw [weight_append, weight_modes, hh i (by simp), ih (fun j hj => hh j (.tail _ hj))]

theorem mem_ends (h : E → Wedge r) (l : List (E × F)) (y : Site F r)
    (hy : y ∈ ends P h l) : ∃ j ∈ l, y.1 = j.2 ^ P := by
  obtain ⟨j, hj, h⟩ := List.mem_flatMap.mp hy
  obtain ⟨_, _, rfl⟩ := List.mem_map.mp h
  exact ⟨j, hj, rfl⟩

def Cell.test (c : Cell F r t T E X) (h : E → Wedge r) (f : Test F r t) : F :=
  batch P x c.stations fun l m => f (l ++ ends P h c.ports) m

end OAI.LinearAlgebra.MatrixExponent.Sphere.Surface
end

/-! # Ordered sums of insertion tables -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Surface

open Finset
variable {F X T : Type} [Field F] {r t : ℕ} (P : ℕ) (x : X)

theorem batch_append (us vs : List (Station F r t T X)) (test : Test F r t) :
    batch P x (us ++ vs) test = batch P x us (fun a b =>
      batch P x vs (fun a' b' => test (a ++ a') (b ++ b'))) := by
  induction us generalizing test with
  | nil => rfl
  | cons u us ih =>
    simp only [List.cons_append, batch, ih, List.append_assoc]

private theorem sum_tail {n : ℕ} (Y : Fin (n + 1) → Type) [∀ i, Fintype (Y i)]
    (g : (∀ i, Y i) → F) :
    ∑ x, g x = ∑ y : Y 0, ∑ z : (i : Fin n) → Y i.succ, g (Fin.cons y z) := by
  rw [← (Fin.consEquiv Y).sum_comp, Fintype.sum_prod_type]
  rfl

theorem batch_ofFn {n : ℕ} (s : Fin n → Station F r t T X) (test : Test F r t) :
    batch P x (List.ofFn s) test =
      ∑ a : (i : Fin n) → Level r (s i).a, ∑ b : (i : Fin n) → Level t (s i).b,
        (∏ i, (s i).table x (a i) (b i)) *
          test ((List.finRange n).flatMap fun i => modes ((s i).pos ^ P) (a i).val)
            ((List.finRange n).flatMap fun i => modes (s i).pos (b i).val) := by
  induction n generalizing test with
  | zero => simp [batch]
  | succ n ih =>
    rw [List.ofFn_succ, batch, sum_tail]
    apply sum_congr rfl
    intro a _
    simp_rw [sum_tail (fun i => Level t (s i).b)]
    rw [sum_comm]
    apply sum_congr rfl
    intro b _
    rw [ih, mul_sum]
    simp only [mul_sum, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ,
      List.finRange_succ, List.flatMap_cons, List.flatMap_map, mul_assoc]

end OAI.LinearAlgebra.MatrixExponent.Sphere.Surface
end

/-!
# Replacing local forms in a closed contraction

Sum over all assignments away from the chosen seam first. The energy
of that seam may change in each summand of the local identity.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Surface
open Finset Function
open scoped Classical

variable {V E I F : Type} [Field F] [Fintype V] [Fintype E] [Fintype I] {r : ℕ}

def contractGraph (f : V → (E → Wedge r) → F) (d : E → ℕ) : F :=
  ∑ a : ∀ e, Level r (d e), ∏ v, f v (fun e => (a e).val)

theorem contractGraph_replace (f : V → (E → Wedge r) → F) (d : E → ℕ)
    (v : V) (W : I → F) (g : I → (E → Wedge r) → F)
    (step : ∀ h, (∀ e, energy (h e).val = d e) → f v h = ∑ i, W i * g i h) :
    contractGraph f d = ∑ i, W i * contractGraph (update f v (g i)) d := by
  unfold contractGraph
  simp_rw [mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun a _ => ?_
  let h := fun e => (a e).val
  change (∏ k, f k h) = ∑ i, W i * ∏ k, update f v (g i) k h
  rw [← mul_prod_erase _ _ (mem_univ v), step h (fun e => (a e).property), sum_mul]
  refine sum_congr rfl fun i _ => ?_
  rw [← mul_prod_erase _ _ (mem_univ v), update_self, mul_assoc]
  congr 2
  exact prod_congr rfl fun k hk => by rw [update_of_ne (ne_of_mem_erase hk)]

private abbrev Rest (r : ℕ) (d : E → ℕ) (e : E) :=
  (j : {j // j ≠ e}) → Level r (d j.val)

private def emptyState (r : ℕ) : Wedge r := ⟨[], by simp⟩

private def fill {d : E → ℕ} {e : E} (a : Rest r d e) (j : E) : Wedge r :=
  if hj : j = e then emptyState r else (a ⟨j, hj⟩).val

omit [Fintype E] in
private theorem fill_energy {d : E → ℕ} {e : E} (a : Rest r d e) (j : E) (hj : j ≠ e) :
    energy (fill a j).val = d j := by
  simpa only [fill, dite_eq_right hj] using (a ⟨j, hj⟩).property

private def assemble (d : E → ℕ) (e : E) (n : ℕ) :
    Rest r d e × Level r n ≃ ((j : E) → Level r (update d e n j)) where
  toFun a j := ⟨update (fill a.1) e a.2.val j, by
    by_cases he : j = e
    · subst j; simpa only [update_self] using a.2.property
    · rw [update_of_ne he, update_of_ne he]; exact fill_energy a.1 j he⟩
  invFun a := (fun j => ⟨(a j.val).val, by simpa [j.property] using (a j.val).property⟩,
    ⟨(a e).val, by simpa using (a e).property⟩)
  left_inv a := by
    apply Prod.ext
    · funext j
      apply Subtype.ext
      simp [fill, j.property]
    · apply Subtype.ext; simp
  right_inv a := by
    funext j
    apply Subtype.ext
    by_cases he : j = e
    · subst j; simp
    · simp [fill, he]

/-- Local identities on an internal edge can be inserted into the full
contraction. All other vertices must ignore that edge. -/
theorem contractGraph_seam (f : V → (E → Wedge r) → F) (d : E → ℕ)
    (u v : V) (huv : u ≠ v) (e : E)
    (other : ∀ z, z ≠ u → z ≠ v → ∀ h a, f z (update h e a) = f z h)
    (W : I → F) (d' : I → ℕ) (g k : I → (E → Wedge r) → F)
    (step : ∀ h, (∀ j, j ≠ e → energy (h j).val = d j) →
      (∑ a : Level r (d e), f u (update h e a.val) * f v (update h e a.val)) =
        ∑ i, W i * ∑ b : Level r (d' i), g i (update h e b.val) * k i (update h e b.val)) :
    contractGraph f d =
      ∑ i, W i * contractGraph (update (update f u (g i)) v (k i)) (update d e (d' i)) := by
  let rem (h : E → Wedge r) := ∏ z ∈ (univ.erase u).erase v, f z h
  have expand (p q : (E → Wedge r) → F) (n : ℕ) :
      contractGraph (update (update f u p) v q) (update d e n) =
        ∑ t : Rest r d e, rem (fill t) *
          ∑ a : Level r n, p (update (fill t) e a.val) * q (update (fill t) e a.val) := by
    rw [contractGraph, ← (assemble (r := r) d e n).sum_comp, Fintype.sum_prod_type]
    refine sum_congr rfl fun t _ => ?_
    rw [mul_sum]
    refine sum_congr rfl fun a _ => ?_
    let h := update (fill t) e a.val
    change (∏ z, update (update f u p) v q z h) = rem (fill t) * (p h * q h)
    rw [← prod_erase_mul _ _ (mem_univ u), ← prod_erase_mul _ _ (mem_erase.mpr ⟨huv.symm, mem_univ _⟩),
      update_of_ne huv, update_self, update_self, mul_assoc, mul_comm (q h)]
    congr 1
    refine prod_congr rfl fun z hz => ?_
    have hv := ne_of_mem_erase hz
    have hu := ne_of_mem_erase (mem_of_mem_erase hz)
    rw [update_of_ne hv, update_of_ne hu]
    exact other z hu hv _ _
  have first := expand (f u) (f v) (d e)
  simp only [update_eq_self] at first
  rw [first]
  simp_rw [expand, step _ (fill_energy _), mul_sum]
  rw [sum_comm]
  simp only [mul_left_comm]

end OAI.LinearAlgebra.MatrixExponent.Sphere.Surface
end

section
/-! # Renaming stations and pulling back their ordinary parameters -/

namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Surface

variable {F T L X Y E : Type} [Field F] {r t P : ℕ}

def Station.pull (u : Station F r t T X) (π : Y → X) (tag : T → L) : Station F r t L Y :=
  ⟨u.pos, u.a, u.b, tag u.label, fun y => u.table (π y)⟩

def Cell.pull (c : Cell F r t T E X) (π : Y → X) (tag : T → L) : Cell F r t L E Y :=
  ⟨c.ports, c.stations.map (Station.pull · π tag)⟩

theorem batch_pull (x : Y) (u : List (Station F r t T X)) (π : Y → X) (f : Test F r t)
    (tag : T → L) :
    batch P x (u.map (Station.pull · π tag)) f = batch P (π x) u f := by
  induction u generalizing f with
  | nil => rfl
  | cons a l ih => simp only [List.map_cons, batch, ih]; rfl

theorem Cell.test_pull (x : Y) (c : Cell F r t T E X) (h : E → Wedge r)
    (π : Y → X) (f : Test F r t) (tag : T → L) :
    (c.pull π tag).test P x h f = c.test P (π x) h f := batch_pull _ _ _ _ _

theorem Cell.eval_pull (x : Y) (c : Cell F r t T E X) (h : E → Wedge r)
    (π : Y → X) (tag : T → L) :
    (c.pull π tag).eval P x h = c.eval P (π x) h := batch_pull _ _ _ _ _

omit [Field F] in
theorem Cell.pull_id (c : Cell F r t T E X) : c.pull id id = c := by
  unfold pull
  rw [show (fun s : Station F r t T X => s.pull id id) = id from rfl, List.map_id]

end OAI.LinearAlgebra.MatrixExponent.Sphere.Surface
end

/-!
# Making all insertion states explicit

First-sphere labels include seams as well as station legs. Seam ends
can occur at different positions, but always read the same wedge.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Layout
open Finset Surface Classical

variable {F T X E V : Type} [Field F] [Fintype E] [Fintype V] {r t : ℕ}
  (C : V → Surface.Cell F r t T E X)

abbrev Place := Σ v, Fin (C v).stations.length

def item (i : Place C) := (C i.1).stations.get i.2

abbrev First := E ⊕ Place C
abbrev Marked := (E × F) ⊕ Place C

def source : Marked C → First C := Sum.elim (.inl ∘ Prod.fst) .inr

def firstEnergy (d : E → ℕ) : First C → ℕ := Sum.elim d (fun i => (item C i).a)
def secondEnergy (i : Place C) := (item C i).b

def secondPoint (i : Place C) := (item C i).pos
def firstPoint (P : ℕ) (i : Marked C) := Sum.elim Prod.snd (secondPoint C) i ^ P

def secondList (v : V) : List (Place C) :=
  (List.finRange (C v).stations.length).map (fun i => ⟨v, i⟩)
def firstList (v : V) : List (Marked C) :=
  (secondList C v).map .inr ++ (C v).ports.map .inl

abbrev Family (r : ℕ) {I : Type} (e : I → ℕ) := ∀ i, Level r (e i)

def read {I : Type} {r : ℕ} (z : I → F) (s : I → Wedge r) (l : List I) : F :=
  wick fieldKernel (l.flatMap fun i => modes (z i) (s i))

def factors (P : ℕ) (d : E → ℕ) (x : X)
    (a : Family r (firstEnergy C d)) (b : Family t (secondEnergy C)) : F :=
  (∏ i, (item C i).table x (a (.inr i)) (b i)) *
    (∏ v, read (firstPoint C P) (fun i => (a (source C i)).val) (firstList C v)) *
      ∏ v, read (secondPoint C) (fun i => (b i).val) (secondList C v)

private abbrev SA (v : V) := ∀ i, Level r ((C v).stations.get i).a
private abbrev SB (v : V) := ∀ i, Level t ((C v).stations.get i).b

private def term (P : ℕ) (x : X) (h : E → Wedge r) (v : V) (a : SA C v) (b : SB C v) :=
  (∏ i, ((C v).stations.get i).table x (a i) (b i)) *
    forms (((List.finRange _).flatMap fun i => modes (((C v).stations.get i).pos ^ P) (a i).val) ++
        ends P h (C v).ports)
      ((List.finRange _).flatMap fun i => modes ((C v).stations.get i).pos (b i).val)

omit [Fintype E] [Fintype V] in
private theorem expand_cell (P : ℕ) (x : X) (h : E → Wedge r) (v : V) :
    (C v).eval P x h = ∑ a : SA C v, ∑ b : SB C v, term C P x h v a b := by
  have he := batch_ofFn P x (C v).stations.get
    (fun l m => forms (l ++ ends P h (C v).ports) m)
  rw [List.ofFn_get] at he
  exact he

private def splitFirst (d : E → ℕ) : Family r (firstEnergy C d) ≃ Family r d × (∀ v, SA C v) :=
  (Equiv.sumPiEquivProdPi _).trans ((Equiv.refl _).prodCongr
    (Equiv.piCurry fun v i => Level r ((C v).stations.get i).a))

private def splitSecond : Family t (secondEnergy C) ≃ (∀ v, SB C v) :=
  Equiv.piCurry fun v i => Level t ((C v).stations.get i).b

omit [Fintype E] in
private theorem factors_eq (P : ℕ) (d : E → ℕ) (x : X)
    (a : Family r (firstEnergy C d)) (b : Family t (secondEnergy C)) :
    factors C P d x a b = ∏ v, term C P x (fun e => (a (.inl e)).val) v
      (fun i => a (.inr ⟨v, i⟩)) (fun i => b ⟨v, i⟩) := by
  unfold factors
  rw [Fintype.prod_sigma, mul_assoc, ← prod_mul_distrib, ← prod_mul_distrib]
  apply prod_congr rfl
  intro v _
  simp [term, read, firstPoint, firstList, secondPoint, secondList, source, item,
    Surface.ends, forms, List.flatMap_map, Function.comp_def]

theorem eval_factors (P : ℕ) (d : E → ℕ) (x : X) :
    Surface.eval P C d x = ∑ a, ∑ b, factors C P d x a b := by
  let f (p : Family r d × (∀ v, SA C v)) (b : ∀ v, SB C v) :=
    ∏ v, term C P x (fun e => (p.1 e).val) v (p.2 v) (b v)
  have he (a b) : factors C P d x a b = f (splitFirst C d a) (splitSecond C b) :=
    factors_eq C P d x a b
  simp only [he, (splitSecond C).sum_comp]
  rw [(splitFirst C d).sum_comp (fun p => ∑ b, f p b), Fintype.sum_prod_type]
  unfold Surface.eval f
  simp only [expand_cell, Fintype.prod_sum]

end OAI.LinearAlgebra.MatrixExponent.Sphere.Layout
end

/-! Outer branching on the energy of each chunk of every leg. -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Layout
open Finset Classical

abbrev Shapes (M : ℕ) {I : Type} (e : I → ℕ) := ∀ i, Chunk.Shape M (e i)
abbrev Block (d : ℕ) {I : Type} {M : ℕ} {e : I → ℕ} (p : Shapes M e) := ∀ i, Chunk.Cells d (p i)

def families {I : Type} (M d : ℕ) (e : I → ℕ) :
    (Σ p : Shapes M e, Block d p) ≃ Family (M * d) e :=
  (show (Σ p : Shapes M e, Block d p) ≃ (∀ i, Σ b : Chunk.Shape M (e i), Chunk.Cells d b) from
    { toFun := fun a i => ⟨a.1 i, a.2 i⟩
      invFun := fun x => ⟨fun i => (x i).1, fun i => (x i).2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }).trans (Equiv.piCongrRight fun i => Chunk.states M d (e i))

variable {F T X E V : Type} [Field F] [Fintype E] [Fintype V] {M r t : ℕ}
  (C : V → Surface.Cell F (M * r) (M * t) T E X) (d : E → ℕ)

abbrev Profile := Shapes M (firstEnergy C d) × Shapes M (secondEnergy C)

namespace Profile
variable {C d} (p : Profile C d)

abbrev AState := Block r p.1
abbrev BState := Block t p.2

def joinA (s : p.AState) : Family (M * r) (firstEnergy C d) := families M r _ ⟨p.1, s⟩
def joinB (s : p.BState) : Family (M * t) (secondEnergy C) := families M t _ ⟨p.2, s⟩

def value (P : ℕ) (x : X) :=
  ∑ s : p.AState, ∑ t : p.BState, factors C P d x (p.joinA s) (p.joinB t)

end Profile

theorem eval_shapes (P : ℕ) (x : X) : Surface.eval P C d x = ∑ p : Profile C d, p.value P x := by
  rw [eval_factors, Fintype.sum_prod_type, ← (families M r (firstEnergy C d)).sum_comp,
    Fintype.sum_sigma]
  apply sum_congr rfl
  intro p _
  simp_rw [← (families M t (secondEnergy C)).sum_comp, Fintype.sum_sigma]
  rw [sum_comm]
  rfl

end OAI.LinearAlgebra.MatrixExponent.Sphere.Layout
end

/-! # Number of public chunk-energy choices -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Layout
open Classical Finset

private theorem card_shapes {I : Type} [Fintype I] [DecidableEq I] (M L : ℕ)
    (e : I → ℕ) (he : ∀ i, e i ≤ L) :
    Fintype.card (Shapes M e) ≤ (L + 1) ^ (M * Fintype.card I) := by
  let f (p : Shapes M e) (i : I) (j : Fin M) : Fin (L + 1) :=
    Fin.castLE (Nat.succ_le_succ (he i)) ((p i).val j)
  have hinj : Function.Injective f := by
    intro p q h
    funext i
    apply Subtype.ext
    funext j
    apply Fin.ext
    exact congrArg (fun a => (a i j).val) h
  simpa [Fintype.card_fun, pow_mul] using Fintype.card_le_of_injective f hinj

variable {F T X E V : Type} [Field F] [Fintype E] [Fintype V] {M r t : ℕ}
  (C : V → Surface.Cell F (M * r) (M * t) T E X) (d : E → ℕ)

omit [Field F] in
theorem card_profile (L : ℕ) (hd : ∀ i, d i ≤ L)
    (ha : ∀ i, (item C i).a ≤ L) (hb : ∀ i, (item C i).b ≤ L) :
    Fintype.card (Profile C d) ≤ (L + 1) ^ (M * (Fintype.card E + 2 * Fintype.card (Place C))) := by
  have h₁ := card_shapes M L (firstEnergy C d) (by rintro (i|i); exact hd i; exact ha i)
  have h₂ := card_shapes M L (secondEnergy C) hb
  have he := Nat.mul_le_mul h₁ h₂
  rw [← pow_add, Fintype.card_sum] at he
  rw [Fintype.card_prod]
  convert he using 1
  congr 1
  ring

end OAI.LinearAlgebra.MatrixExponent.Sphere.Layout
end
