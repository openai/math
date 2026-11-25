import OAI.Computability.IntegerMultiplication.Code.Task
import Mathlib.Logic.Function.Iterate

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Code
open Prog

namespace Task
variable {X : Type*} {a d : X → ℕ} {f g h e : X → Tree}

private theorem runBound {A} {env c r n s} (hr : Prog.Run (A := A) env c r n s) (j : ℕ) :
    (s j).length ≤ (r j).length + n := by
  induction hr with
  | pass => omega
  | @push Γ i x r =>
    by_cases hj : j=i
    · subst j; simp
    · simp [Function.update_of_ne hj]
  | @pop Γ i r =>
    by_cases hj : j=i
    · subst j
      simp; omega
    · simp [Function.update_of_ne hj]
  | look _ ih => omega
  | join _ _ ih jh => omega
  | tie _ ih => omega
  | again _ _ ih => omega

/-- Every task comes with an automatic bound on output size. -/
theorem sizeBound (ha : Task a f g) :
    ∃ C : ℕ, ∀ x, (g x).count ≤ (f x).count + C*(a x+1) := by
  obtain ⟨c,C,hc⟩ := ha
  refine ⟨C,fun x => ?_⟩
  obtain ⟨t,e,g'⟩ := hc x [] (fun _ => [])
  have hh := runBound g' 0
  simp only [letters_here, List.length_append, Tree.spell_length] at hh
  omega

/-- The left component is first. Wrapping a subcall there requires no scan or
movement of either component. -/
theorem left (ha : Task a f g) (h : X → Tree) :
    Task a (fun x => .fork (f x) (h x)) (fun x => .fork (g x) (h x)) := by
  obtain ⟨c,C,hc⟩ := ha
  refine ⟨splitRoot 0 (fun _ => .pass) (.join c (pack 0)), C+7, fun x env r => ?_⟩
  apply (fits_pair ((hc x env (pile 0 (h x) r)).join (fits_pack _ _ _ _ _))).mono
  rw [Nat.add_mul]
  omega

/-- Crossing to the right component costs a linear scan of the left component only. -/
theorem right (ha : Task a f g) (h : X → Tree) :
    Task (fun x => (h x).count+a x) (fun x => .fork (h x) (f x)) (fun x => .fork (h x) (g x)) := by
  obtain ⟨c,C,hc⟩ := ha
  refine ⟨splitRoot 0 (fun _ => .pass)
    ((move 0 1 2).join (c.join ((move 1 0 2).join (pack 0)))), 91+C, fun x env r => ?_⟩
  have h₁ := fits_move (i := 0) (u := 2) (j := 1) (by decide) (by decide) (h x) env (pile 0 (f x) r)
  have h₂ := hc x env (pile 1 (h x) r)
  rw [pile_comm 1 _ r 0 _ (by decide)] at h₁
  have h₃ := fits_move (i := 1) (u := 2) (j := 0) (by decide) (by decide) (h x) env (pile 0 (g x) r)
  rw [pile_comm 1 _ r 0 _ (by decide)] at h₃
  have h₄ := fits_pack (h x) (g x) r 0 env
  refine (fits_pair (h₁.join (h₂.join (h₃.join h₄)))).mono ?_
  -- 2+2+2+1+4+84 <91*(count+1)
  have H : 11 ≤ 91 := by decide
  simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one]
  omega

theorem copy (f : X → Tree) :
    Task (fun x => (f x).count) f (fun x => .fork (f x) (f x)) := by
  refine ⟨(clone 0 1 2).join ((move 1 0 2).join (pack 0)), 100, fun x env r => ?_⟩
  have ha := fits_clone (i := 0) (j := 1) (u := 2) (by decide) (by decide) (by decide) (f x) env r
  rw [pile_comm 0 _ r 1 _ (by decide)] at ha
  have hb := fits_move (i := 1) (j := 0) (u := 2) (by decide) (by decide) (f x) env (pile 0 (f x) r)
  exact (ha.join (hb.join (fits_pack _ _ _ _ _))).mono (by beta_reduce; omega)

/-- Can keep everything following x untouched while discarding x. -/
theorem dropLeft (f g : X → Tree) :
    Task (fun x => (f x).count) (fun x => .fork (f x) (g x)) g := by
  refine ⟨splitRoot 0 (fun _ => .pass) (discard 0),22,fun x env r => ?_⟩
  exact (fits_pair (fits_discard 0 _ env _)).mono (by beta_reduce; omega)

/-- A common, but linear-time on both sides, adapter. -/
theorem exchange (f g : X → Tree) :
    Task (fun x => (f x).count+(g x).count) (fun x => .fork (f x) (g x)) (fun x => .fork (g x) (f x)) := by
  refine ⟨splitRoot 0 (fun _ => .pass)
    ((move 0 1 2).join ((move 0 3 2).join ((move 1 0 2).join ((move 3 0 2).join (pack 0))))),
    90, fun x env r => ?_⟩
  have h₁ := fits_move (i := 0) (u := 2) (j := 1) (by decide) (by decide) (f x) env (pile 0 (g x) r)
  have h₂ := fits_move (i := 0) (u := 2) (j := 3) (by decide) (by decide) (g x) env (pile 1 (f x) r)
  have h₃ := fits_move (i := 1) (u := 2) (j := 0) (by decide) (by decide) (f x) env (pile 3 (g x) r)
  have h₄ := fits_move (i := 3) (u := 2) (j := 0) (by decide) (by decide) (g x) env (pile 0 (f x) r)
  rw [pile_comm 1 _ _ 0 _ (by decide)] at h₁
  rw [pile_comm 3 _ _ 1 _ (by decide)] at h₂
  rw [pile_comm 0 _ _ 3 _ (by decide)] at h₃
  exact (fits_pair (h₁.join (h₂.join (h₃.join (h₄.join (fits_pack _ _ _ _ _)))))).mono (by beta_reduce; omega)

/-- Remove right component. This may cost linear time on the retained component too. -/
theorem dropRight (f g : X → Tree) :
    Task (fun x => (f x).count+(g x).count) (fun x => .fork (f x) (g x)) f :=
  ((exchange f g).compose (dropLeft g f)).bound 2 fun x => by omega

/-- A branch controlled by the root constructor plus its finite atom value. Costs a
constant number of instructions before the selected computation starts. -/
theorem control (b : X → Bool)
    -- tag b physically stored as left child atom
    (ha : Task (fun x : {x // b x=false} => a x) (fun x => f x) (fun x => g x))
    (hb : Task (fun x : {x // b x=true} => a x) (fun x => f x) (fun x => g x)) :
    Task a (fun x => .fork (.atom (b x)) (f x)) g := by
  obtain ⟨c,C,hc⟩ := ha
  obtain ⟨d,D,hd⟩ := hb
  refine ⟨splitRoot 0 (fun _ => .pass) (splitRoot 0 (fun i => bif i then d else c) .pass),
    C+D+8,fun x env r => ?_⟩
  cases e : b x
  · have h := hc ⟨x,e⟩ env r
    simp only [e]
    refine (fits_pair (fits_bit (b := false) (c := fun i => bif i then d else c) h)).mono ?_
    rw [Nat.add_mul,Nat.add_mul]
    dsimp only
    omega
  · have h := hd ⟨x,e⟩ env r
    simp only [e]
    refine (fits_pair (fits_bit (b := true) (c := fun i => bif i then d else c) h)).mono ?_
    rw [Nat.add_mul,Nat.add_mul]
    dsimp only
    omega

theorem tag (b : Bool) (f : X → Tree) :
    Task (fun _ => 0) f (fun x => .fork (.atom b) (f x)) :=
  ⟨.join (give 0 b) (pack 0),4,fun _x _env _r => (fits_give _ _ _ _).join (fits_pack _ _ _ _ _)⟩

/-- Synthesize a fixed tree independent of input. -/
def prepare : ℕ → Tree → Cmd
  | i, .atom b => give i b
  | i, .fork x y => .join (prepare i y) (.join (prepare i x) (pack i))

theorem fits_prepare (i) (x : Tree) (env : Env) (r : Deck) :
    Fits env (prepare i x) r (pile i x r) (5*x.count) := by
  induction x generalizing r with
  | atom => exact (fits_give _ r _ _).mono (by simp [Tree.count])
  | fork x y hx hy =>
    exact ((hy r).join ((hx _).join (fits_pack _ _ _ _ _))).mono (by simp [Tree.count]; omega)

theorem supply (x : Tree) (f : X → Tree) :
    Task (fun _ => 0) f (fun i => .fork x (f i)) := by
  refine ⟨.join (prepare 0 x) (pack 0), 5*x.count+3, fun i env r => ?_⟩
  simpa only [Nat.mul_one, Nat.zero_add, Nat.add_assoc] using
    (fits_prepare _ x env _).join (fits_pack _ _ _ _ _)

theorem const (x : Tree) (f : X → Tree) :
    Task (fun i => (f i).count) f (fun _ => x) := by
  refine ⟨.join (discard 0) (prepare 0 x),20+5*x.count,fun i env r =>
    ((fits_discard _ _ _ _).join (fits_prepare _ x _ _)).mono ?_⟩
  simp only [Nat.add_mul,Nat.mul_add,Nat.mul_one]
  omega

end Task

section Time
variable {X Y Z : Type*} [Codec X] [Codec Y] [Codec Z]
variable {a : X → ℕ} {b : Y → ℕ} {f : X → Y} {g : Y → Z}

/-- Convenient linear-time procedures. Composition is closed because the result size
of the first call is itself at most linear. -/
def Easy (f : X → Y) := Computes size f

namespace Easy
protected theorem of_bound (h : Computes a f) (C : ℕ) (ha : ∀ x, a x ≤ C*size x) :
    Easy f :=
  h.bound (C+1) fun x => by have hh := ha x; rw [Nat.add_mul,Nat.mul_add]; omega

theorem length (h : Easy f) :
    ∃ C : ℕ, ∀ x, size (f x) ≤ C * size x := by
  obtain ⟨c,hc⟩ := h.sizeBound
  refine ⟨1+2*c, fun x => ?_⟩
  specialize hc x
  have e : size x ≥ 1 := size_pos x
  change size _ ≤ size _ + _ at hc
  have hh : c * (size x + 1) ≤ c * (size x + size x) :=
    Nat.mul_le_mul_left _ (by omega)
  simp only [Nat.add_mul, Nat.one_mul, Nat.mul_assoc, Nat.mul_add] at *
  omega

theorem compose (h : Easy f) (e : Easy g) : Easy (fun x => g (f x)) := by
  obtain ⟨c,hc⟩ := h.length
  apply Easy.of_bound (Computes.comp e h) (1+c)
  intro x
  rw [Nat.add_mul, Nat.one_mul]
  exact Nat.add_le_add_left (hc x) _

theorem identity : Easy (id (α := X)) := Computes.id

theorem exchange : Easy (Prod.swap (α := X) (β := Y)) :=
  (Task.exchange (fun (x : X × Y) => send x.1) (fun x => send x.2)).mono fun x => by
    change size _+size _ ≤ size x; simp

theorem left (h : Easy f) :
    Easy (fun x : X × Z => (f x.1,x.2)) :=
  (((Task.on h (Prod.fst : X × Z → X)).left (fun (x : X × Z) => send x.2))).mono fun x => by simp; omega

theorem right (h : Easy f) :
    Easy (fun x : Z × X => (x.1,f x.2)) :=
  (((Task.on h (Prod.snd : Z × X → X)).right (fun (x : Z × X) => send x.1))).mono fun x => by
    change size _+size _≤size x; simp

theorem clone : Easy (fun x : X => (x,x)) :=
  Task.copy send

theorem fst : Easy (Prod.fst : X × Y → X) :=
  (Task.dropRight (fun (x : X × Y) => send x.1) (fun x => send x.2)).mono fun x => by
    change size _ + size _ ≤ size x; simp

theorem snd : Easy (Prod.snd : X × Y → Y) :=
  (Task.dropLeft (fun (x : X × Y) => send x.1) (fun x => send x.2)).mono fun x => by
    change size _ ≤ size x; simp; omega

/-- Combine algorithms ignoring variable reuse (linear penalty). -/
theorem pair (h : Easy f) {j : X → Z} (e : Easy j) :
    Easy (fun x : X => (f x,j x)) :=
  (Easy.clone.compose h.left).compose e.right

theorem const (y : Y) : Easy (fun _ : X => y) :=
  Task.const (send y) send

theorem fstCompose {j : Z → X × Y} (h : Easy j) : Easy (fun x => (j x).1) :=
  h.compose fst

theorem sndCompose {j : Z → X × Y} (h : Easy j) : Easy (fun x => (j x).2) :=
  h.compose snd

theorem ifst {f g : X → Y}
    (h : Easy f) (e : Easy g) :
    Easy (fun i : Bool × X => bif i.1 then g i.2 else f i.2) := by
  let r (i : Bool × X) := send (bif i.1 then g i.2 else f i.2)
  change Task size (fun i => .fork (.atom i.1) (send i.2)) r
  refine Task.control (f := fun i => send (i : Bool × X).2) _ ?_ ?_
  · refine Task.conform (p' := fun x => send (x.val : Bool × X).2) (q' := fun x => r x.val)
      ((h.on fun x : {i : Bool × X // i.1=false} => x.val.2).mono (b' := fun x => size x.val) ?_)
      (fun _ => rfl) (fun _ => rfl) (fun x => ?_)
    · intro x; simp; omega
    rcases x with ⟨i,hi⟩
    simp [r,hi]
  · refine Task.conform (p' := fun x => send (x.val : Bool × X).2) (q' := fun x => r x.val)
      ((e.on fun x : {i : Bool × X // i.1=true} => x.val.2).mono (b' := fun x => size x.val) ?_)
      (fun _ => rfl) (fun _ => rfl) (fun x => ?_)
    · intro x; simp; omega
    rcases x with ⟨i,hi⟩
    simp [r,hi]

/-- constructing lists is just pair and atom. -/
theorem cons : Easy (fun i : X × List X => i.1 :: i.2) :=
  Task.self (p := send)

theorem leftSum : Easy (Sum.inl : X → X ⊕ Y) :=
  (Task.tag false send).mono (by simp)

theorem rightSum : Easy (Sum.inr : Y → X ⊕ Y) :=
  (Task.tag true send).mono (by simp)

-- size lemmas for chain automation later.
end Easy
end Time
end Code

end IntegerMultiplication
end Computability
end OAI
