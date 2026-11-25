import OAI.Computability.IntegerMultiplication.Code.FoldLeft

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Code

namespace Task
variable {X : Type*}

theorem append_at (p : X → Tree) :
    Task (fun x : List X × List X => (forest p x.1).count)
      (fun x => .fork (forest p x.1) (forest p x.2))
      (fun x => forest p (x.1++x.2)) := by
  let f (x i : List X) := forest p (x++i)
  have h := Task.foldRight (p := fun _ => p) (f := f)
    (b := fun _ => 0) (a := fun _ _ _ => 0)
    (seed := forest p) (D := fun _ _ => True)
    (fun _ _ _ _ => trivial)
    (show Task _ _ _ from Task.self)
    (show Task _ _ _ from Task.self)
  exact ((h.on fun x => ⟨x,trivial⟩).mono fun x => by
    dsimp only
    have e := Task.foldCost_add p (fun _ => 0) x.1
    rw [e]
    have z (s : List X) : costSum (fun (_ : X) => 0) s=0 := by induction s <;> simp_all
    simp [z])

theorem reversal (p : X → Tree) :
    Task (fun x : List X => (forest p x).count) (forest p)
      (fun x => forest p x.reverse) := by
  have h := foldLeft (Y := Unit) (fun _ => p) (fun _ => forest p)
    (fun _ s x => x::s) (fun _ _ => 0) (D := fun _ _ => True)
    (show Task _ _ _ from Task.self)
  have hs := h.on fun x : List X => ⟨(x,[],()),by simp⟩
  have he := (Task.supply (.atom false) (forest p)).compose (Task.exchange (fun _ => .atom false) (forest p))
  have hf : ∀ (x z : List X), x.foldl (fun l a => a::l) z = x.reverse ++ z := by
    intro x; induction x with
    | nil => simp
    | cons x l ih => intro z; simp [ih]
  have z (s : List X) : costSum (fun (_ : X) => 0) s=0 := by induction s <;> simp_all
  simp only [hf, List.append_nil, z, zero_add] at hs -- reduce function apps first
  refine (he.compose hs).bound 2 fun x => ?_
  simp only [Tree.count,zero_add]
  omega

theorem flatten (p : X → Tree) :
    Task (fun l : List (List X) => (forest (forest p) l).count)
      (forest (forest p))
      (fun l => forest p l.flatten) := by
  let f (l : List (List X)) (_ : Unit) := forest p l.flatten
  let pt := fun (_ : Unit) => forest p
  have h := foldRight (p := pt) (f := f) (b := fun _ => 0)
    (a := fun l _ _ => (forest p l).count) (seed := fun _ => .atom false) (D := fun _ _ => True)
    (fun _ _ _ _ => trivial)
    (show Task _ _ _ from Task.self)
    -- appending two forests
    ((append_at p).on (fun x : {s : List X × List (List X) × Unit // True} => (x.val.1,x.val.2.1.flatten)))
  have he := (Task.supply (.atom false) (forest (forest p))).compose (Task.exchange (fun _ => .atom false) (forest (forest p)))
  refine (he.compose (h.on (fun x => ⟨(x,()),trivial⟩))).bound 4 ?_
  intro l
  dsimp only [Tree.count,pt]
  rw [foldCost_add]
  simp only [forest_count]
  omega

theorem lenConst {b : ℕ} {e : X → Tree} (h : ∀ x, (e x).count ≤ b) :
    ∀ l : List X, (forest e l).count ≤ (b+1)*l.length+1 := by
  intro l; induction l with
  | nil => simp [Tree.count]
  | cons x l ih =>
    simp only [forest_cons, Tree.count, List.length_cons, Nat.mul_add, Nat.mul_one]
    specialize h x
    omega

end Task

section Easy
variable {X Y : Type*} [Codec X] [Codec Y]
open _root_.OAI.Computability.IntegerMultiplication.Code.Task

protected theorem Easy.reverse : Easy (fun x : List X => x.reverse) := by
  refine (reversal (send (X := X))).conform (by simp [size]) (by simp) (by simp)

-- also for sublinear in pair size:
protected theorem Computes.append :
    Computes (fun x : List X × List X => size x.1) (fun x => x.1 ++ x.2) := by
  refine (append_at (send (X := X))).conform (by simp [size]) (by simp) (by simp)

protected theorem Easy.append :
    Easy (fun x : List X × List X => x.1 ++ x.2) :=
  Computes.append.mono fun x => by simp; omega

protected theorem Easy.flatten :
    Easy (fun x : List (List X) => x.flatten) := by
  have h := Task.flatten (send (X := X))
  -- forest nesting
  have e : Task.forest (X := X) send = send := funext Task.forest_send
  rw [e] at h
  refine h.conform (by simp [size]) (by simp) (by simp)

-- Peeling or eliminating lists from the front of a larger structure, propagating tails.
protected theorem Task.byList (Y X : Type*) [Codec X]
    (f : List X → Y → Tree) (a : List X → Y → ℕ) {p : Y → Tree}
    {D : List X → Y → Prop}
    (b : Task (fun i : {y // D [] y} => a [] i.val)
        (fun i => p i.val) (fun i => f [] i.val))
    (c : Task (fun i : {i : X × List X × Y // D (i.1::i.2.1) i.2.2} => a (i.val.1::i.val.2.1) i.val.2.2)
        -- encoding of (x::xs,y) is already ((x,xs),p y); no modification needed
        (fun i => .fork (.fork (send i.val.1) (send i.val.2.1)) (p i.val.2.2))
        (fun i => f (i.val.1::i.val.2.1) i.val.2.2)) :
    Task (fun i : {i : List X × Y // D i.1 i.2} => a i.val.1 i.val.2)
      (fun i => .fork (send i.val.1) (p i.val.2))
      (fun i => f i.val.1 i.val.2) := by
  obtain ⟨nilCode,n,h⟩ := b
  obtain ⟨consCode,m,e⟩ := c
  refine ⟨splitRoot 0 (fun _ => .pass)
    (splitRoot 0 (fun _ => nilCode) (.join (pack 0) (.join (pack 0) consCode))),
    20+n+m,?_⟩
  intro ⟨⟨l,y⟩,g⟩ env r
  cases l with
  | nil =>
    have hs := h ⟨y,g⟩ env r
    refine (fits_pair (fits_bit (c := fun _ => nilCode) (b := false) hs)).mono ?_
    dsimp only
    simp only [Nat.add_mul]
    omega
  | cons v l =>
    have hs := e ⟨(v,l,y),g⟩ env r
    refine (fits_pair (fits_pair ((fits_pack _ _ _ _ _).join ((fits_pack _ _ _ _ _).join hs)))).mono ?_
    dsimp only
    simp only [Nat.add_mul]
    omega

protected theorem Easy.listCase {f : X × List X → Y} (d : Y) (h : Easy f) :
    Easy (List.casesOn (motive := fun _ : List X => Y) · d (fun a b => f (a,b))) := by
  obtain ⟨c,C,hc⟩ := h
  refine ⟨splitRoot 0 (fun _ => Task.prepare 0 (send d)) (.join (pack 0) c),C+5*(send d).count+7,fun x env r => ?_⟩
  cases x with
  | nil =>
    refine (fits_bit (b := false) (c := fun _ => Task.prepare 0 (send d)) (fits_prepare _ _ _ _)).mono ?_
    simp only [size_nil,Nat.add_mul]
    omega
  | cons a l =>
    have hh := hc (a,l) env r
    refine (fits_pair ((fits_pack _ _ _ _ _).join hh)).mono ?_
    simp only [Nat.add_mul,size_cons,size_prod]
    omega

end Easy
end Code

end IntegerMultiplication
end Computability
end OAI
