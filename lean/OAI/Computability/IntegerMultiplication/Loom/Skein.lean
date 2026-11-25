import OAI.Computability.IntegerMultiplication.Match
import OAI.Computability.IntegerMultiplication.Net.NetworkBasic

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Loom
open Code Strip
abbrev Bead := ZMod 2
noncomputable section
def notify : Bead ≃ Bool := Nonempty.some ((Fintype.card_eq.mp (show Fintype.card Bead= Fintype.card Bool from by simp)))
instance : Codec Bead := ⟨fun x => Tree.atom (notify x)⟩
instance : FiniteState Bead where
  identify := fun _ _ h => notify.injective (Tree.atom.inj h)
variable {I J W : Type} [Fintype W] {A T : I→Type} {r : Regime I} {n l : I→ℕ} {p : I→Tree}
variable (s : (i:I)→Series (A i)) (t : (i:I)→Series (T i))
variable (R : Series W) (v : (i:I)→W→A i→T i→Bead)
abbrev swatch := fun i : I => stripe R (fun w => cloth s t (fun i => v i w) i)

theorem paint (a : W→Bead)
    (q : Rip r n l p (swatch s t R v)) (d : W) :
    Rip r n l p (cloth s t (fun i x y => ∑ w:W,a w*v i w x y)) := by
  have cells := Fatigue.drill R (fun i w => cloth s t (fun i => v i w) i) q
  classical
  generalize (Finset.univ:Finset W)=S
  induction S using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using
      map_open s t (fun i => v i d) (fun _ => (0:Bead)) (Easy.const _) (cells _)
  | insert x S h ih =>
    simp only [Finset.sum_insert h]
    exact duo_open s t (fun i => v i x) _ (fun p => a x*p.1+p.2) (cells x) ih
      (Easy.finite _) (0:Bead) (0:Bead)
theorem pallet (a : W→W→Bead)
    (q : Rip r n l p (swatch s t R v)) :
    Rip r n l p (swatch s t R (fun i w x y => ∑ d:W,a w d*v i d x y)) :=
  Fatigue.dry R _ q.again fun w => paint s t R v (a w) q w

open Net
def coat {L O U : Type} (a : Hop W L) (v : W→O→U→Bead) : W→O→U→Bead :=
  fun w x u => a.point 0 (fun k o => v k o u) w x
theorem bright {L} (a : Hop W L)
    (q : Rip r n l p (swatch s t R v)) :
    Rip r n l p (swatch s t R (fun i => coat a (v i))) := by
  classical
  let m w k := Net.Amount.read (0:Bead) (a.coeff w k) + if k=w then 1 else 0
  have g := pallet s t R v m q
  have e : (fun i w x y => ∑ d:W,m w d*v i d x y) = fun i => coat a (v i) := by
    funext i w x z
    simp [m,coat,Hop.point,Hop.run,add_mul, Finset.sum_add_distrib,ite_mul,add_comm]
  simpa only [e] using g

variable (W)
-- payload layout fixed role tree but addressed flat, enabling continuous cost, no divisibility at each node.
def Frame (base : ℕ) : ℕ → Type
| 0 => Fin base
| k+1 => Frame base k × W

def skein (R : Series W) (base : ℕ) : (k:ℕ) → Series (Frame W base k)
| 0 => Series.natural base
| k+1 => (skein R base k).cart R

@[simp] theorem strands (R : Series W) (a k : ℕ) :
    (skein W R a k).count=a*Fintype.card W^k := by
  induction k with
  | zero => change (Series.natural a).count = _; simp
  | succ k ih => change (@Series.count (Frame W a k × W) ((skein W R a k).cart R)) = _; rw [Series.count_cart,ih,pow_succ,Series.total,mul_assoc]
-- estimates independent of d
variable {W}
theorem bulk (s : Series J) (f : J→Bead) :
    (strip s f).count ≤ 2*s.count+1 := by
  simpa [Nat.mul_comm] using stripe_size s _ 1
    (show ∀ i,(send (f i)).count≤1 from fun _ => Nat.le_refl 1)
theorem visible (v : (i:I)→A i→T i→Bead) (h : ∀ i,(t i).count≤l i) :
    Manifest A l (fun i a => strip (t i) (v i a)) := by
  refine ⟨3,fun i a => ?_⟩
  have q := bulk (t i) (v i a)
  specialize h i
  omega
theorem cloth_size (d : Station r s) (v : (i:I)→A i→T i→Bead) (h : ∀ i,(t i).count≤l i) :
    Alive r (fun i => (s i).count) l (cloth s t v) := (visible t v h).lives d -- s variable?
omit [Fintype W] in
theorem clear (d : Station r s) (h : ∀ i,(t i).count≤l i) :
    Alive r (fun i => (s i).count) l (swatch s t R v) :=
  Fatigue.entire R _ d.1 fun w => cloth_size s t d (fun i => v i w) h

end
end Loom

end IntegerMultiplication
end Computability
end OAI
