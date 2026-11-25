import OAI.Computability.IntegerMultiplication.Code.Move
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Tactic.GCongr

/-!
## Algorithms on prefix tree encodings

A Task quantifies over a ghost parameter; e.g. at all x in a mathematical specification
domain the program must run taking the tree query(x) to reply(x) with budget ∝ budget(x)+1.
Thus it specifies the procedure directly on encoded inputs; no computable promise
recognition is required. It must work on top of parked data on *all* stacks, and clean
up all auxiliary work. Different algorithms can compose without assumptions about the
number of stacks they privately use. The compile theorem automatically takes care of
finiteness.

A common example (`Easy` below) is when the parameter is the input itself and time is
allowed linear in its encoded size. We use the typeclass `Codec` for most examples;
for example, a pair always costs one more constructor than the concatenation of the
two top-level encodings. We don't need to require that a Codec is injective; we reason
directly about particular encodings and the final theorem will ask for exactly the
output letters. No decoding step is implicit between composing procedures.
-/

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Code
variable {X Y Z : Type*}

theorem Fits.value.swap {env c i z w n} (h : value env c i z w n) (π : Equiv.Perm ℕ)
    (r : Deck) :
    Fits (env.map (Prog.rename π)) (Prog.rename π c) (pile (π i) z r)
      (pile (π i) w r) n := by
  let r' : Deck := fun j => r (π j)
  obtain ⟨t,e,g⟩ := h r'
  have hh := Prog.Run.rename π.injective g (fun _ => [])
  have e' (v : Tree) :
      Prog.paint π (letters (pile i v r')) (fun _ => ([] : List Ltr)) = letters (pile (π i) v r) := by
    funext j; obtain ⟨j,rfl⟩ := π.surjective j
    rw [Prog.paint_at π.injective]
    by_cases hj : j=i
    · subst j; simp [r', letters]
    · have hk := π.injective.ne hj
      simp [r', letters, pile_else _ _ _ _ hj, pile_else _ _ _ _ hk]
  rw [e', e'] at hh
  exact ⟨t,e,hh⟩

-- avoid issue renamed env isn't arbitrary: run with original env = []; Run has weaken-outer lemma.
theorem append_scope {A : Type} (k : Scope A) {env : Scope A} {c r n t}
    (h : Prog.Run env c r n t) : Prog.Run (env++k) c r n t := by
  induction h with
  | pass => exact .pass
  | push => exact .push
  | pop => exact .pop
  | look _ ih => exact .look ih
  | join _ _ ih jh => exact .join ih jh
  | tie _ ih => exact .tie ih
  | @again G i b r n s e _ ih =>
    have hlen : i < G.length := by
      by_contra! hf
      simp [List.getElem?_eq_none (by omega : G.length ≤ i)] at e
    refine .again (i := i) (by rw [List.getElem?_append_left hlen, e]) ?_
    simpa [List.drop_append, Nat.sub_eq_zero_of_le (Nat.le_of_lt hlen)] using ih

theorem Fits.weaken {env c r t n} (h : Fits env c r t n) (d : Env) :
    Fits (env++d) c r t n := by
  obtain ⟨x,e,h⟩ := h
  exact ⟨x,e,append_scope d h⟩

theorem Fits.value.toPile {c x y n} (h : value [] c 0 x y n) (i : ℕ) (env : Env) :
    value env (Prog.rename (Equiv.swap 0 i) c) i x y n := by
  intro r
  simpa using ((Fits.value.swap h (Equiv.swap 0 i) r).weaken env)

def Task (budget : X → ℕ) (query reply : X → Tree) : Prop :=
  ∃ c : Cmd, ∃ C : ℕ, ∀ x env, Fits.value env c 0 (query x) (reply x) (C*(budget x+1))

namespace Task
variable {b b' : X → ℕ} {p q r : X → Tree}

theorem make (c : Cmd) (C : ℕ)
    (h : ∀ x, Fits.value [] c 0 (p x) (q x) (C*(b x+1))) : Task b p q :=
  ⟨c,C,fun x env r => by simpa using ((h x r).weaken env)⟩

theorem atRegister (h : Task b p q) :
    ∃ C : ℕ, ∀ i, ∃ c : Cmd, ∀ x env,
      Fits.value env c i (p x) (q x) (C*(b x+1)) := by
  obtain ⟨c,C,h⟩ := h
  exact ⟨C,fun i => ⟨_,fun x => (Fits.value.toPile (h x []) i)⟩⟩

theorem bound (h : Task b p q) (D : ℕ) (x : ∀ x, b x + 1 ≤ D*(b' x+1)) :
    Task b' p q := by
  obtain ⟨c,C,e⟩ := h
  refine ⟨c,C*D,fun i env r => (e i env r).mono ?_⟩
  simpa [Nat.mul_assoc] using Nat.mul_le_mul_left C (x i)

theorem mono (h : Task b p q) (e : ∀ x, b x ≤ b' x) :
    Task b' p q :=
  h.bound 1 fun x => by rw [one_mul]; specialize e x; omega

theorem on (h : Task b p q) (f : Y → X) :
    Task (fun x => b (f x)) (fun x => p (f x)) (fun x => q (f x)) := by
  obtain ⟨c,C,h⟩ := h
  exact ⟨c,C,fun x => h (f x)⟩

theorem self : Task b p p :=
  ⟨.pass,1,fun _ env r => (Fits.pass _).mono (by rw [one_mul]; omega)⟩

private theorem bc (a b x y : ℕ) :
    a*(x+1)+b*(y+1)+2 ≤ (a+b+2)*(x+y+1) := by
  rw [Nat.add_mul, Nat.add_mul a b]
  have hx : a*(x+1) ≤ a*(x+y+1) := Nat.mul_le_mul_left _ (by omega)
  have hy : b*(y+1) ≤ b*(x+y+1) := Nat.mul_le_mul_left _ (by omega)
  omega

theorem compose (h : Task b p q) (e : Task b' q r) :
    Task (fun x => b x + b' x) p r := by
  obtain ⟨c,C,hc⟩ := h
  obtain ⟨d,D,hd⟩ := e
  exact ⟨.join c d, C+D+2, fun x env y => ((hc x env y).join (hd x env y)).mono (bc _ _ _ _)⟩

-- congruence syntax nicety
theorem conform (h : Task b p q) {b' : X → ℕ} {p' q' : X → Tree}
    (hb : ∀ x, b x=b' x) (hp : ∀ x, p x=p' x) (hq : ∀ x, q x=q' x) :
    Task b' p' q' := by
  simp only [funext hb,funext hp,funext hq] at h; exact h

end Task

class Codec (X : Type*) where
  send : X → Tree

export Codec (send)

instance : Codec Bool := ⟨Tree.atom⟩
instance : Codec Tree := ⟨id⟩
instance : Codec Unit := ⟨fun _ => Tree.atom false⟩
instance [Codec X] [Codec Y] : Codec (X × Y) := ⟨fun p => .fork (send p.1) (send p.2)⟩
instance [Codec X] : Codec (Option X) := ⟨fun | none => .atom false | some x => .fork (.atom true) (send x)⟩
instance [Codec X] [Codec Y] : Codec (X ⊕ Y) := ⟨fun
  | .inl x => .fork (.atom false) (send x)
  | .inr y => .fork (.atom true) (send y)⟩

private def sendList [Codec X] : List X → Tree
  | [] => .atom false
  | x::s => .fork (send x) (sendList s)

instance [Codec X] : Codec (List X) := ⟨sendList⟩

variable [Codec X] [Codec Y] [Codec Z]

@[simp] theorem send_prod (x : X × Y) : send x = .fork (send x.1) (send x.2) := rfl
@[simp] theorem send_none : send (none : Option X) = .atom false := rfl
@[simp] theorem send_some (x : X) : send (some x) = .fork (.atom true) (send x) := rfl
@[simp] theorem send_inl (x : X) : send (Sum.inl (β := Y) x) = .fork (.atom false) (send x) := rfl
@[simp] theorem send_inr (y : Y) : send (Sum.inr (α := X) y) = .fork (.atom true) (send y) := rfl
@[simp] theorem send_nil : send ([] : List X) = .atom false := rfl
@[simp] theorem send_cons (x : X) (s : List X) : send (x::s) = .fork (send x) (send s) := rfl

/-- Symbols in our tree representation -/
def size (x : X) : ℕ := (send x).count

theorem size_pos (x : X) : 0 < size x := (send x).count_pos
@[simp] theorem size_bit (x : Bool) : size x=1 := rfl
@[simp] theorem size_prod (x : X × Y) : size x = size x.1 + size x.2 + 1 := rfl
@[simp] theorem size_some (x : X) : size (some x)=size x+2 := by simp [size, Tree.count]; omega
@[simp] theorem size_none : size (none : Option X)=1 := rfl
@[simp] theorem size_nil : size ([] : List X)=1 := rfl
@[simp] theorem size_cons (x : X) (s : List X) : size (x::s)=size x+size s+1 := rfl
@[simp] theorem size_inl (x : X) : size (Sum.inl (β := Y) x) = size x+2 := by simp [size,Tree.count]; omega
@[simp] theorem size_inr (y : Y) : size (Sum.inr (α := X) y) = size y+2 := by simp [size,Tree.count]; omega

/-- Functional relation with input encoding. -/
abbrev Computes (b : X → ℕ) (f : X → Y) := Task b send fun x => send (f x)

protected theorem Computes.id {b : X → ℕ} : Computes b id := Task.self

protected theorem Computes.comp {b : X → ℕ} {t : Y → ℕ} {f : X → Y} {g : Y → Z}
    (h : Computes t g) (e : Computes b f) :
    Computes (fun i => b i+t (f i)) (g ∘ f) :=
  e.compose (h.on f)

end Code

end IntegerMultiplication
end Computability
end OAI
