import OAI.Computability.IntegerMultiplication.Net.NetworkBasic

/-! Execute one list of plane sequences simultaneously on a reindexed collection
of roles. Idle labels passed through on each lifted hop. -/

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Net
open Finset
namespace Parallel
abbrev Row (P W G : Type) := (P×W) ⊕ G
variable {P W G B L : Type}
def join (a : P → W → L) (idle : G → L) : Row P W G → L
| .inl (p,w) => a p w
| .inr g => idle g
@[simp] theorem join_l (a : P → W → L) (b : G → L) (p : P) (w : W) :
    join a b (.inl (p,w)) = a p w := rfl
@[simp] theorem join_r (a : P → W → L) (b : G → L) (g : G) :
    join a b (.inr g) = b g := rfl

variable [DecidableEq P]
def upC (a : P → W → W → Amount) :
    Row P W G → Row P W G → Amount
| .inl (p,w), .inl (p',v) => if p=p' then a p w v else .none
| _, _ => .none

def hop (a : P → Hop W L) (idle : G → L) : Hop (Row P W G) L where
  label := join (fun p => (a p).label) idle
  coeff := upC fun p => (a p).coeff

theorem ok (a : P → Hop W L) (idle : G → L) (h : ∀ p, Hop.ok (a p)) :
    Hop.ok (hop a idle) := by
  rintro (⟨p,w⟩|_) (⟨p',w'⟩|_) n
  all_goals try contradiction
  by_cases e : p=p'
  · subst p'
    exact h p w w' (by simpa [hop, upC] using n)
  simp [hop, upC, e] at n

def shift (i : B ≃ W) (a : Hop W L) : Hop B L where
  label := a.label ∘ i
  coeff := fun b c => a.coeff (i b) (i c)

omit [DecidableEq P] in
theorem shift_ok (i : B ≃ W) (a : Hop W L) (h : a.ok) : (shift i a).ok :=
  fun _ _ n => h _ _ n

-- pd (plane descriptor)
structure Job (P W G L : Type) where
  start : P → W → L
  prog : List (P → Hop W L)
  idle : G → L

namespace Job
variable (j : Job P W G L)
def child (p : P) : Circuit W L where
  init := j.start p
  ops := j.prog.map (fun a => a p)
def weave (i : B ≃ Row P W G) : Circuit B L where
  init := join j.start j.idle ∘ i
  ops := j.prog.map fun a => shift i (hop a j.idle)
def ok := ∀ p : P, (j.child p).ok
theorem weave_ok (i : B ≃ Row P W G) (hj : j.ok) : (j.weave i).ok := by
  rintro x hx
  rcases List.mem_map.mp hx with ⟨a,ha,rfl⟩
  apply shift_ok
  exact Parallel.ok a j.idle (fun p => hj p (a p) (List.mem_map_of_mem ha))

variable {I : Type} [AddMonoid I]
-- weight ignores role arg
theorem sink_weave (i : B ≃ Row P W G) :
    (j.weave i).sink =
      join (fun p => (j.child p).sink) j.idle ∘ i := by
  change Circuit.sinkOf (join j.start j.idle ∘ i) (j.prog.map _) = _
  unfold child Circuit.sink
  dsimp only
  generalize j.start = l, j.prog = o
  induction o generalizing l with
  | nil => rfl
  | cons e t ih =>
    simp only [List.map_cons, Circuit.sinkOf, List.foldl_cons]
    exact ih (fun p => (e p).label)

theorem cost_weave (i : B ≃ Row P W G) (Bgt : L → L → I) (h : ∀ l, Bgt l l = 0) :
    (j.weave i).cost (fun _ => Bgt) =
      join (fun p => (j.child p).cost (fun _ => Bgt)) (fun _ => 0) ∘ i := by
  unfold Circuit.cost weave child
  dsimp only
  generalize j.start = l, j.prog = o
  induction o generalizing l with
  | nil =>
    funext w
    simp only [Function.comp_apply]
    cases i w with
    | inl p => cases p; rfl
    | inr p => rfl
  | cons e t ih =>
    funext w
    have ih := congrFun (ih (fun p => (e p).label)) w
    simp only [List.map_cons, Circuit.costOf, Function.comp_apply, shift, hop]
    simp only [Function.comp_apply, shift, hop] at ih
    rw [ih]
    rcases i w with ⟨_,_⟩ | _
    · rfl
    exact by simp [join, h]

end Job

variable {R : Type} [Ring R] [Fintype P] [Fintype W] [Fintype G] [Fintype B]
theorem shift_run (i : B ≃ W) (a : Hop W L) (h : R) (x : W → R) :
    (shift i a).run h (x ∘ i) = a.run h x ∘ i := by
  funext b
  simp only [Hop.run, shift, Function.comp_apply]
  congr 1
  exact Equiv.sum_comp i (fun w => Amount.read h (a.coeff (i b) w) * x w)

theorem hop_run (a : P → Hop W L) (h : R) (idle : G → L) (x : P → W → R) (g : G → R) :
    (hop a idle).run h (join x g) = join (fun p => (a p).run h (x p)) g := by
  funext w
  rcases w with ⟨p,w⟩ | s
  · simp only [Hop.run, join_l, Fintype.sum_sum_type, Fintype.sum_prod_type]
    simp only [hop, upC, Amount.read_none, zero_mul, sum_const_zero, add_zero]
    congr 1
    rw [Finset.sum_eq_single p]
    · simp
    · intro k _ hk
      simp [Ne.symm hk]
    simp
  simp [hop, upC, join, Hop.run]

namespace Job
theorem weave_run (j : Job P W G L) (h : R) (i : B ≃ Row P W G) (x : P → W → R) (g : G → R) :
    (j.weave i).logical h (join x g ∘ i) =
      join (fun p => (j.child p).logical h (x p)) g ∘ i := by
  unfold Circuit.logical weave child
  dsimp only
  generalize j.prog = o
  induction o generalizing x with
  | nil => rfl
  | cons b t ih =>
    simp_rw [List.map_cons, List.foldl_cons, shift_run, hop_run]
    exact ih _
end Job
end Parallel
end Net

end IntegerMultiplication
end Computability
end OAI
