import OAI.Computability.IntegerMultiplication.Code.Product
import Mathlib.Algebra.Order.BigOperators.Group.List

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Code

section Sums
variable {X Y : Type*}

/-- No algebra typeclasses. -/
def costSum (t : X → ℕ) (l : List X) : ℕ := (l.map t).sum

@[simp]
theorem costSum_nil (t : X → ℕ) : costSum t [] = 0 := rfl
@[simp]
theorem costSum_cons (t : X → ℕ) (x l) : costSum t (x::l)=t x+costSum t l := rfl
@[simp]
theorem costSum_cat (t : X → ℕ) (l s : List X) :
    costSum t (l++s) = costSum t l+costSum t s := by simp [costSum]

theorem costSum_le {t u : X → ℕ} {s : List X} (h : ∀ i ∈ s, t i ≤ u i) :
    costSum t s ≤ costSum u s := by
  induction s with
  | nil => exact le_rfl
  | cons x s ih =>
    simp only [List.mem_cons] at h
    exact Nat.add_le_add (h _ (Or.inl rfl)) (ih (fun i hi => h _ (Or.inr hi)))

theorem costSum_mul (c : ℕ) (t : X → ℕ) (l : List X) :
    costSum (fun x => c*t x) l = c*costSum t l := by
  induction l with
  | nil => simp
  | cons x l ih => simp [ih,Nat.mul_add]

theorem costSum_le_length_size [Codec X] (l : List X) :
    l.length+costSum size l + 1 = size l := by
  induction l with
  | nil => simp
  | cons x l ih => simp; omega

@[simp]
theorem size_append_right [Codec X] (l s : List X) :
    size (l++s) + 1 = size l + size s := by
  simp [← costSum_le_length_size]; omega

end Sums

namespace Task
variable {X Y : Type*}

/-- list extension of encoders (no Codec needed) -/
def forest (f : X → Tree) (s : List X) : Tree :=
  s.foldr (fun x z => .fork (f x) z) (.atom false)

@[simp]
theorem forest_cons (f : X → Tree) (x s) :
    forest f (x::s) = .fork (f x) (forest f s) := rfl
@[simp]
theorem forest_nil (f : X → Tree) : forest f [] = .atom false := rfl
@[simp]
theorem forest_send [Codec X] (s : List X) : forest send s = send s := by
  induction s <;> simp_all

@[simp]
theorem forest_map (f : Y → Tree) (g : X → Y) (s : List X) :
    forest f (s.map g) = forest (fun x => f (g x)) s := by induction s <;> simp_all

@[simp]
theorem forest_count (f : X → Tree) (s : List X) :
    (forest f s).count = s.length + costSum (fun x => (f x).count) s + 1 := by
  induction s with
  | nil => simp [Tree.count]
  | cons x s ih => simp [Tree.count, ih]; omega

/-- Physical implementation of fold-right, general seed argument included. -/
def rightBody (base cmd : Cmd) : Cmd :=
  splitRoot 0 (fun _ => base)
    ((move 0 1 2).join (.join (.again 0) ((move 1 0 2).join ((pack 0).join cmd))))

/-- Budget function; callback depends on the current suffix. Plus transport overhead
on each head, linear in its size. -/
def foldCost (a : X → List X → ℕ) : List X → ℕ
  | [] => 1
  | x::s => a x s + 1 + foldCost a s

theorem foldCost_pos (a : X → List X → ℕ) (s : List X) : foldCost a s ≥ 1 := by cases s <;> simp [foldCost]; omega

-- Extend to *indexed* ghost spec: same seed-linked index can govern all representation
-- and timing of elements (e.g., record width varies). No consistency assumptions encoded.
-- Also allow limited l in a downward-closed set for invariants.
theorem foldRight {p : Y → X → Tree} {f : List X → Y → Tree} {seed : Y → Tree}
    {b : Y → ℕ} {a : X → List X → Y → ℕ} {D : List X → Y → Prop}
    (hclosure : ∀ x l y, D (x::l) y → D l y)
    (h₀ : Task (fun x : {y // D [] y} => b x.val) (fun x => seed x.val)
      (fun x => f [] x.val))
    (h : Task (fun i : {s : X × List X × Y // D (s.1::s.2.1) s.2.2} => a i.val.1 i.val.2.1 i.val.2.2)
      (fun i => .fork (p i.val.2.2 i.val.1) (f i.val.2.1 i.val.2.2))
      (fun i => f (i.val.1::i.val.2.1) i.val.2.2)) :
    Task (fun i : {s : List X × Y // D s.1 s.2} =>
      b i.val.2+foldCost (fun x l => a x l i.val.2+(p i.val.2 x).count) i.val.1)
      (fun i => .fork (forest (p i.val.2) i.val.1) (seed i.val.2))
      (fun i => f i.val.1 i.val.2) := by
  obtain ⟨c,C,hc⟩ := h₀
  obtain ⟨d,E,hd⟩ := h
  let K := C+E+128
  let m := rightBody c d
  refine ⟨splitRoot 0 (fun _ => .pass) (.tie m),K+5,fun ⟨⟨s,y⟩,hs⟩ G r => ?_⟩
  let W := fun x l => a x l y+(p y x).count
  let env := m::G
  suffices hh : ∀ (l : List X) r, D l y →
      Fits env m (pile 0 (forest (p y) l) (pile 0 (seed y) r)) (pile 0 (f l y) r)
        (K*(b y+foldCost W l)) by
    change Fits _ _ (pile 0 (.fork _ _) _) _ ((K+5)*(b y+foldCost W s+1))
    apply (fits_pair (Fits.tie (hh _ _ hs))).mono
    have e := foldCost_pos W s
    -- simp arithmetic products
    simp only [Nat.add_mul,Nat.mul_add,Nat.mul_one]
    omega
  intro l r
  induction l generalizing r with
  | nil =>
    intro h
    have hu := hc ⟨y,h⟩ env r
    refine (fits_bit (c := fun _ => c) hu).mono ?_
    dsimp only [foldCost,K]
    simp only [Nat.add_mul]
    omega
  | cons x s ih =>
    intro hxs
    have ha := fits_move (i := 0) (u := 2) (j := 1) (by decide) (by decide)
      (p y x) env (pile 0 (forest (p y) s) (pile 0 (seed y) r))
    have hb := Fits.again0 (ih (pile 1 (p y x) r) (hclosure _ _ _ hxs))
    rw [pile_comm 1 _ _ 0 _ (by decide), pile_comm 1 _ _ 0 _ (by decide)] at ha
    have hh := fits_move (i := 1) (u := 2) (j := 0) (by decide) (by decide)
      (p y x) env (pile 0 (f s y) r)
    rw [pile_comm 1 _ _ 0 _ (by decide)] at hh
    have he := hd ⟨(x,s,y),hxs⟩ env r
    refine (fits_pair (ha.join (hb.join (hh.join ((fits_pack _ _ _ _ _).join he))))).mono ?_
    simp only [foldCost,W,K,Nat.add_mul,Nat.mul_add,Nat.mul_one]
    omega

theorem foldCost_add (f : X → Tree) (b : X → ℕ) (s : List X) :
    foldCost (fun x _ => b x+(f x).count) s = costSum b s + (forest f s).count := by
  induction s with
  | nil => rfl
  | cons x l ih =>
    simp only [foldCost, costSum_cons, forest_cons, Tree.count, ih]
    omega

/-- Independent map calls on all elements; linear overhead in input tree. -/
theorem mapTask (Y : Type*) (p q : Y → X → Tree) {a : Y → X → ℕ}
    {B : Y → X → Prop}
    (h : Task (fun x : {x : Y × X // B x.1 x.2} => a x.val.1 x.val.2)
      (fun x => p x.val.1 x.val.2) (fun x => q x.val.1 x.val.2)) :
    Task (fun x : {x : Y × List X // ∀ i∈x.2, B x.1 i} =>
      costSum (a x.val.1) x.val.2 + (forest (p x.val.1) x.val.2).count)
      (fun x => forest (p x.val.1) x.val.2) (fun x => forest (q x.val.1) x.val.2) := by
  let nil : Y → Tree := fun _ => .atom false
  let D (l : List X) (y) := ∀ i∈l, B y i
  let f l y := forest (q y) l
  have hi := foldRight (p := p) (f := f) (seed := nil)
    (a := fun i _ y => a y i) (b := fun _ => 0) (D := D)
    (fun _ _ _ h i e => h i (List.mem_cons_of_mem _ e))
    (show Task (fun _ => _) (fun _ => _) (fun _ => _) from Task.self)
    -- instantation
    ((h.on (fun x : {s : X × List X × Y // D (s.1::s.2.1) s.2.2} =>
      ⟨(x.val.2.2,x.val.1), x.property _ List.mem_cons_self⟩)).left fun x => forest (q x.val.2.2) x.val.2.1)
  let J := {x : Y × List X // ∀ i∈x.2, B x.1 i}
  let sw : J → {x : List X × Y // D x.1 x.2} := fun i => ⟨i.val.swap,i.property⟩
  let u (x : J) := forest (p x.val.1) x.val.2
  have hseed := (Task.supply (.atom false) u).compose (Task.exchange (fun _ => .atom false) u)
  refine (hseed.compose (hi.on sw)).bound 3 ?_
  intro x
  dsimp only [sw,u,Prod.swap,nil]
  simp only [Tree.count, zero_add, foldCost_add]
  omega

end Task

theorem Computes.mapping {X Y : Type*} [Codec X] [Codec Y] {a : X → ℕ} {f : X → Y}
    (h : Computes a f) :
    Computes (fun x : List X => size x + costSum a x) (List.map f) := by
  have hu := Task.mapTask (X := X) Unit (fun _ => send) (fun _ x => send (f x)) (a := fun _ => a)
    (B := fun _ _ => True) (h.on fun i : {x : Unit × X // True} => i.val.2)
  refine (hu.on (fun l : List X => ⟨((),l), by simp⟩)).conform (fun x => ?_) (fun x => ?_) (fun x => ?_)
  · dsimp only [size]
    rw [Task.forest_send,add_comm]
  · exact Task.forest_send _
  · change Task.forest _ x = send (List.map f x)
    rw [← Task.forest_map send f, Task.forest_send]

theorem Easy.mapping {X Y : Type*} [Codec X] [Codec Y] {f : X → Y}
    (h : Easy f) : Easy (List.map f) :=
  Easy.of_bound (Computes.mapping h) 2 fun x => by
    simp only [← costSum_le_length_size]
    omega

end Code

end IntegerMultiplication
end Computability
end OAI
