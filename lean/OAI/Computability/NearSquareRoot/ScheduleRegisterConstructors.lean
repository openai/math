import OAI.Computability.NearSquareRoot.ScheduleRegisterWitness

/-! # Common-register constructors for P192 commands -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace RegisterWitness
open IntegerMultiplication Code

namespace Timed
variable {X Y : Type*} {R : ℕ} {a b : X → ℕ} {p q s : X → Tree}

theorem on (h : Timed R a p q) (f : Y → X) :
    Timed R (a ∘ f) (p ∘ f) (q ∘ f) :=
  register_witness R from Task.on (forget h) f

theorem bound (h : Timed R a p q) (D : ℕ) (e : ∀ x, a x+1 ≤ D*(b x+1)) :
    Timed R b p q :=
  register_witness R from Task.bound (forget h) D e

theorem compose (h : Timed R a p q) (g : Timed R b q s) :
    Timed R (fun x => a x+b x) p s :=
  register_witness R from Task.compose (forget h) (forget g)

theorem conform (h : Timed R a p q) {p' q' : X → Tree}
    (e : ∀ x, a x=b x) (f : ∀ x, p x=p' x) (g : ∀ x, q x=q' x) : Timed R b p' q' := by
  simpa only [funext e, funext f, funext g] using h

end Timed

namespace Easy
variable {X Y Z : Type*} [Codec X] [Codec Y] [Codec Z] {R : ℕ}
variable {f : X → Y} {g : Y → Z}

theorem identity : Easy R (id (α := X)) :=
  register_witness R from (Code.Easy.identity (X := X))

theorem compose (h : Easy R f) (e : Easy R g) : Easy R (fun x => g (f x)) :=
  register_witness R from Code.Easy.compose (forget h) (forget e)

theorem fst (hR : 4 ≤ R) : Easy R (Prod.fst : X × Y → X) :=
  register_witness R from (Code.Easy.fst (X := X) (Y := Y))

theorem snd (hR : 1 ≤ R) : Easy R (Prod.snd : X × Y → Y) :=
  register_witness R from (Code.Easy.snd (X := X) (Y := Y))

theorem cons : Easy R (fun i : X × List X => i.1 :: i.2) :=
  register_witness R from (Code.Easy.cons (X := X))

theorem const (hR : 1 ≤ R) (y : Y) : Easy R (fun _ : X => y) :=
  register_witness R from (Code.Easy.const (X := X) y)

theorem left (hR : 1 ≤ R) (h : Easy R f) : Easy R (fun i : X × Z => (f i.1,i.2)) :=
  register_witness R from (Code.Easy.left (Z := Z) (forget h))

theorem right (hR : 3 ≤ R) (h : Easy R f) : Easy R (fun i : Z × X => (i.1,f i.2)) :=
  register_witness R from (Code.Easy.right (Z := Z) (forget h))

theorem clone (hR : 3 ≤ R) : Easy R (fun x : X => (x,x)) :=
  register_witness R from (Code.Easy.clone (X := X))

theorem pair (hR : 3 ≤ R) {j : X → Z} (h : Easy R f) (g : Easy R j) :
    Easy R (fun x => (f x,j x)) :=
  (clone hR |>.compose (left (by omega) h) |>.compose (right hR g))

end Easy

namespace Bounded
variable {X Y : Type*} {R : ℕ} {a b t s : X → ℕ} {p q m : X → Tree}

theorem of_time (h : Timed R a p q) :
    Bounded R a (fun x => (p x).count+a x) p q :=
  register_witness R from (Space.BoundedTask.of_time (forget h))

theorem on (h : Bounded R a b p q) (f : Y → X) :
    Bounded R (a ∘ f) (b ∘ f) (p ∘ f) (q ∘ f) :=
  register_witness R from Space.BoundedTask.on (forget h) f

theorem bound (h : Bounded R a b p q) (C D : ℕ)
    (hc : ∀ x, a x+1 ≤ C*(t x+1)) (hd : ∀ x, b x+1 ≤ D*(s x+1)) :
    Bounded R t s p q :=
  register_witness R from Space.BoundedTask.bound (forget h) C D hc hd

end Bounded
end RegisterWitness

end NearSquareRoot
end Computability
end OAI
