import Mathlib

/-! Linear network semantics. A step transitions all the labels (an edge on each role),
then executes one inclusive update y_w += sum_v coeff w v y_v. Wires absent from the
update have all coefficients zero. Gates and labels are fixed independent of R
(cf. the complex motif executes over a varying finite modulus). -/

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Net
open Finset
inductive Amount
| none
| unit (neg : Bool)
| half (neg : Bool)
deriving DecidableEq, Fintype

namespace Amount
def flip : Amount → Amount
| none => none
| unit b => unit (!b)
| half b => half (!b)

def read {R : Type} [Ring R] (halfElem : R) : Amount → R
| none => 0
| unit b => if b then -1 else 1
| half b => if b then -halfElem else halfElem

@[simp] theorem read_none {R : Type} [Ring R] (h : R) : read h none = 0 := rfl
@[simp] theorem read_flip {R : Type} [Ring R] (h : R) (a : Amount) :
    read h a.flip = -read h a := by
  cases a with
  | none => simp [flip, read]
  | unit b => cases b <;> simp [flip, read]
  | half b => cases b <;> simp [flip, read]

@[simp] theorem flip_flip (a : Amount) : a.flip.flip = a := by cases a <;> simp [flip]
@[simp] theorem flip_eq_none (a : Amount) : a.flip = none ↔ a = none := by cases a <;> simp [flip]
end Amount

structure Hop (W L : Type) where
  label : W → L
  coeff : W → W → Amount

namespace Hop
variable {W L R : Type}
def ok (a : Hop W L) : Prop :=
  ∀ w v, a.coeff w v ≠ Amount.none → a.label w = a.label v

-- inclusive add
variable [Fintype W] [Ring R]
def run (a : Hop W L) (h : R) (x : W → R) : W → R :=
  fun w => x w + ∑ v, Amount.read h (a.coeff w v) * x v

/-- Coefficientwise (on any address set) -/
def point {O : Type} (a : Hop W L) (h : R) (x : W → O → R) : W → O → R :=
  fun w o => a.run h (fun u => x u o) w

variable {O : Type}
-- representations are additive and respect amount-coefficients from R
structure Frames (L O R : Type) [Ring R] where
  act : L → (O → R) ≃ (O → R)
  add l f g : act l (f + g) = act l f + act l g
  scale l (a : R) f : act l (fun o => a * f o) = fun o => a * act l f o

namespace Frames
theorem zero (D : Frames L O R) (l : L) : D.act l 0 = 0 := by
  have q := D.scale l 0 (fun _ => 0)
  simpa [← Pi.zero_def] using q

theorem sum (D : Frames L O R) (l : L) {J : Type} (x : J → O → R) (s : Finset J) :
    D.act l (∑ j ∈ s, x j) = ∑ j ∈ s, D.act l (x j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using D.zero l
  | insert e s he ih => rw [Finset.sum_insert he, Finset.sum_insert he, D.add, ih]
end Frames

theorem point_asfun (a : Hop W L) (h : R) (x : W → O → R) (w : W) :
    a.point h x w =
    x w + ∑ v, (fun o => Amount.read h (a.coeff w v) * x v o) := by
  ext
  simp [point, run]

theorem framed (a : Hop W L) (ha : a.ok) (D : Frames L O R) (h : R) (x : W → O → R)
    (w : W) :
    a.point h (fun v => D.act (a.label v) (x v)) w =
    D.act (a.label w) (a.point h x w) := by
  rw [point_asfun, point_asfun, D.add, D.sum]
  congr 1
  refine Finset.sum_congr rfl ?_
  intro v _
  by_cases n : a.coeff w v = Amount.none
  · rw [n, D.scale]; simp
  rw [← ha _ _ n, D.scale]
end Hop

structure Circuit (W L : Type) where
  init : W → L
  ops : List (Hop W L)

namespace Circuit
variable {W L R : Type}
def ok (c : Circuit W L) := ∀ x ∈ c.ops, Hop.ok x

def sinkOf (i : W → L) (o : List (Hop W L)) : W → L :=
  o.foldl (fun _ e => e.label) i
def sink (c : Circuit W L) := sinkOf c.init c.ops
def costOf [AddMonoid R] (B : W → L → L → R) : (W → L) → List (Hop W L) → W → R
| _, [] => 0
| i, e::t => fun w => B w (i w) (e.label w) + costOf B e.label t w
def cost [AddMonoid R] (c : Circuit W L) (B : W → L → L → R) : W → R := costOf B c.init c.ops
theorem cost_append [AddMonoid R] (B : W → L → L → R) (i : W → L)
    (o p : List (Hop W L)) (w : W) :
    costOf B i (o++p) w = costOf B i o w + costOf B (sinkOf i o) p w := by
  induction o generalizing i with
  | nil => simp [costOf, sinkOf]
  | cons e t ih =>
    simpa [costOf, sinkOf, add_assoc] using (congrArg (B w (i w) (e.label w) + ·) (ih e.label))

variable [Fintype W] [Ring R] {O : Type}
def logical (c : Circuit W L) (h : R) (x : W → R) : W → R :=
  c.ops.foldl (fun b e => e.run h b) x

def edges (i j : W → L) (D : Hop.Frames L O R) (x : W → O → R) : W → O → R :=
  fun v => D.act (j v) ((D.act (i v)).symm (x v))

def thread (D : Hop.Frames L O R) (h : R) : (W → L) → List (Hop W L) →
    (W → O → R) → W → O → R
| _, [], x => x
| i, a::ops, x => thread D h a.label ops (a.point h (edges i a.label D x))

def physical (c : Circuit W L) (D : Hop.Frames L O R) (h : R) := thread D h c.init c.ops

-- common frame invariant
theorem telescope (D : Hop.Frames L O R) (h : R) (i : W → L) (as : List (Hop W L))
    (x : W → O → R) (hc : ∀ a ∈ as, Hop.ok a) :
    thread D h i as (fun v => D.act (i v) (x v)) =
    (fun v => D.act (sinkOf i as v)
      (fun y => as.foldl (fun b e => e.run h b) (fun w => x w y) v)) := by
  induction as generalizing i x with
  | nil => rfl
  | cons a as ih =>
    simp only [thread]
    have eq : a.point h (edges i a.label D (fun v => D.act (i v) (x v))) =
        (fun v => D.act (a.label v) (a.point h x v)) := by
      unfold edges
      simp only [Equiv.symm_apply_apply]
      exact funext (fun v => a.framed (hc _ (by simp)) D h x v)
    rw [eq, ih a.label (a.point h x) (fun u hu => hc u (by simp [hu]))]
    rfl

theorem endpoint (c : Circuit W L) (hc : c.ok) (D : Hop.Frames L O R) (h : R)
    (route : W ≃ W) (s : W → R)
    (hr : ∀ a w, c.logical h a (route w) = s w * a w)
    (x : W → O → R) (w : W) :
    c.physical D h x (route w) = (fun y => s w *
      D.act (c.sink (route w)) ((D.act (c.init w)).symm (x w)) y) := by
  let u := fun v => (D.act (c.init v)).symm (x v)
  have t := congrFun (telescope D h c.init c.ops u hc) (route w)
  simp only [u, Equiv.apply_symm_apply] at t
  change c.physical D h x (route w) = D.act (c.sink (route w))
    (fun y => c.logical h (fun v => u v y) (route w)) at t
  rw [t]
  simp_rw [hr]
  exact D.scale _ _ _
end Circuit
end Net

end IntegerMultiplication
end Computability
end OAI
