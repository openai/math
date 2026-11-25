import OAI.Computability.IntegerMultiplication.Strip.Bearing
import OAI.Computability.IntegerMultiplication.Loom.Skein
import OAI.Computability.NearSquareRoot.ScheduleRegisterAlignEffectiveTask

/-! # A fixed physical command for concatenating the rows of a prefix pass -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Controlled.PrefixCommand

open IntegerMultiplication Code Strip Loom

/-- Concatenate a forest of rows represented by arbitrary serialized trees. -/
noncomputable def flattenCmd : Cmd := (Easy.flatten (X := Tree)).choose

/-- The same tape command flattens every rectangular block, including empty
row and column series. Its clock charges the size of the actual input forest. -/
theorem flatten_runs {I : Type} {P B : I → Type}
    (s : (i : I) → Series (P i)) (t : (i : I) → Series (B i))
    (v : (i : I) → P i × B i → Tree) :
    let input := stackRun s (fun i a => stripe (t i) (fun b => v i (a,b)))
    EffectiveTask.Runs flattenCmd (fun i => (input i).count) input
      (stackRun (fun i => (s i).cart (t i)) v) := by
  intro input
  let rows (i : I) := (s i).tab (fun a => (t i).tab (fun b => v i (a,b)))
  have encoded (i : I) : input i = send (rows i) := by
    change stripe (s i) _ = send (rows i)
    simp_rw [stripe_eq (t i)]
    exact stripe_eq' (s i) _
  obtain ⟨C,h⟩ := (Easy.flatten (X := Tree)).choose_spec
  refine ⟨C,fun i => ?_⟩
  change ∀ env, Fits.value env flattenCmd 0 (input i) (stripe ((s i).cart (t i)) (v i)) (C*((input i).count+1))
  rw [encoded,cart_eq]
  exact h (rows i)

private theorem rows_size (l : List (List Tree)) : size l = size l.flatten + 2*l.length := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    have add := size_append_right a l.flatten
    simp only [List.flatten_cons,List.length_cons,size_cons]
    omega

/-- Removing a row erases its list delimiter and its terminating atom. This
identity applies when each record has a different encoded size. -/
theorem nested_count {P B : Type} (s : Series P) (t : Series B) (v : P × B → Tree) :
    (stripe s (fun a => stripe t (fun b => v (a,b)))).count =
      (stripe (s.cart t) v).count + 2*s.count := by
  let l := s.tab (fun a => t.tab (fun b => v (a,b)))
  have e : stripe s (fun a => stripe t (fun b => v (a,b))) = send l := by
    simp_rw [stripe_eq t]
    exact stripe_eq' s _
  rw [e,cart_eq]
  simpa only [l,Series.card,size] using rows_size l

variable {P B U : Type} (s : Series P) (t : Series B) (u : Series U)
    (v : P × B → U → Bead)

/-- The flat forest stores each bit strip with a single list delimiter. -/
theorem flat_size : (stripe (s.cart t) (fun a => strip u (v a))).count ≤
    (s.count*t.count)*(2*u.count+2)+1 := by
  simpa only [Series.count_cart] using
    stripe_size (s.cart t) _ (2*u.count+1) (fun a => bulk u (v a))

/-- The forest before concatenation stores a delimiter and a terminal for each row. -/
theorem nested_size : (stripe s (fun a => stripe t (fun b => strip u (v (a,b))))).count ≤
    s.count*(t.count*(2*u.count+2)+2)+1 :=
  stripe_size s _ _ (fun a => stripe_size t _ (2*u.count+1) (fun b => bulk u (v (a,b))))

/-- Bound the full set of row packets when their local headers have a common size bound. -/
theorem packet_size (header : P → Tree) (h : ℕ) (size : ∀ a, (header a).count ≤ h) :
    (stripe s (fun a => .fork (header a) (stripe t (fun b => strip u (v (a,b)))))).count ≤
      s.count*(h+t.count*(2*u.count+2)+3)+1 := by
  apply stripe_size s _ (h+t.count*(2*u.count+2)+2)
  intro a
  have row := stripe_size t (fun b => strip u (v (a,b))) (2*u.count+1) (fun b => bulk u (v (a,b)))
  change _ ≤ t.count*(2*u.count+2)+1 at row
  have head := size a
  change (header a).count + _ + 1 ≤ _
  omega

end Controlled.PrefixCommand

end NearSquareRoot
end Computability
end OAI
