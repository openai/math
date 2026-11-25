import OAI.Computability.IntegerMultiplication.Code.Product

/-!
# Bounds on live stacks in a structured program

A run certificate carries a common absolute height for data registers and a
bound on the number of additional return addresses. A join pays for a return
address throughout its left child. Tail calls and the right child of a join
reuse the caller's return depth.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Space

open IntegerMultiplication

/-- Space-aware execution of P192 structured stack programs. A short segment
can be certified from its exact time when every stack has sufficient headroom. -/
inductive BoundedRun {A : Type} (cap : ℕ) :
    ℕ → Scope A → Prog A → Reg A → ℕ → Reg A → Prop
  | clock {depth Γ c r n s} (run : Prog.Run Γ c r n s)
      (data : ∀ i, (r i).length + n ≤ cap) (ret : n ≤ depth) :
      BoundedRun cap depth Γ c r n s
  | pass {depth Γ r} (data : ∀ j, (r j).length ≤ cap) :
      BoundedRun cap depth Γ .pass r 1 r
  | pop {depth Γ i r} (data : ∀ j, (r j).length ≤ cap) :
      BoundedRun cap depth Γ (.pop i) r 1 (Function.update r i (r i).tail)
  | push {depth Γ i x r} (data : ∀ j, ((Function.update r i (x :: r i)) j).length ≤ cap) :
      BoundedRun cap depth Γ (.push i x) r 1 (Function.update r i (x :: r i))
  | look {depth Γ i c r n s} (child : BoundedRun cap depth Γ (c (r i).head?) r n s) :
      BoundedRun cap depth Γ (.look i c) r (1 + n) s
  | join {depth leftDepth Γ c d r n s m t}
      (left : BoundedRun cap leftDepth Γ c r n s) (right : BoundedRun cap depth Γ d s m t)
      (reserve : leftDepth + 1 ≤ depth) :
      BoundedRun cap depth Γ (.join c d) r (1 + n + 1 + m) t
  | tie {depth Γ c r n s} (child : BoundedRun cap depth (c :: Γ) c r n s) :
      BoundedRun cap depth Γ (.tie c) r (1 + n) s
  | again {depth Γ i c r n s} (lookup : Γ[i]? = some c)
      (child : BoundedRun cap depth (Γ.drop i) c r n s) :
      BoundedRun cap depth Γ (.again i) r (1 + n) s

namespace BoundedRun

variable {A : Type} {cap depth cap' depth' : ℕ} {Γ : Scope A} {c : Prog A}
  {r s : Reg A} {n : ℕ}

theorem run (h : BoundedRun cap depth Γ c r n s) : Prog.Run Γ c r n s := by
  induction h with
  | clock run _ _ => exact run
  | pass _ => exact .pass
  | pop _ => exact .pop
  | push _ => exact .push
  | look _ ih => exact .look ih
  | join _ _ _ ih jh => exact .join ih jh
  | tie _ ih => exact .tie ih
  | again eq _ ih => exact .again eq ih

theorem start (h : BoundedRun cap depth Γ c r n s) (i : ℕ) : (r i).length ≤ cap := by
  induction h with
  | clock _ data _ => exact (Nat.le_add_right ..).trans (data i)
  | pass data => exact data i
  | pop data => exact data i
  | @push _ _ j x r data =>
    specialize data i
    by_cases hj : i = j
    · subst j
      simp only [Function.update_self, List.length_cons] at data
      omega
    · simpa [Function.update_of_ne hj] using data
  | look _ ih => exact ih
  | join _ _ _ ih _ => exact ih
  | tie _ ih => exact ih
  | again _ _ ih => exact ih

open private runBound from OAI.Computability.IntegerMultiplication.Code.Product

theorem finish (h : BoundedRun cap depth Γ c r n s) (i : ℕ) : (s i).length ≤ cap := by
  induction h with
  | clock run data _ => exact (runBound run i).trans (data i)
  | pass data => exact data i
  | push data => exact data i
  | @pop _ _ j r data =>
    by_cases hj : i = j
    · subst j
      simp only [Function.update_self, List.length_tail]
      exact (Nat.sub_le _ _).trans (data i)
    · simpa [Function.update_of_ne hj] using data i
  | look _ ih => exact ih
  | join _ _ _ _ ih => exact ih
  | tie _ ih => exact ih
  | again _ _ ih => exact ih

theorem mono (h : BoundedRun cap depth Γ c r n s) (hc : cap ≤ cap') (hd : depth ≤ depth') :
    BoundedRun cap' depth' Γ c r n s := by
  induction h generalizing depth' with
  | clock run data ret => exact .clock run (fun i => (data i).trans hc) (ret.trans hd)
  | pass data => exact .pass (fun j => (data j).trans hc)
  | push data => exact .push (fun j => (data j).trans hc)
  | pop data => exact .pop (fun j => (data j).trans hc)
  | look _ ih => exact .look (ih hd)
  | join _ _ reserve ih jh => exact .join (ih le_rfl) (jh hd) (reserve.trans hd)
  | tie _ ih => exact .tie (ih hd)
  | again lookup _ ih => exact .again lookup (ih hd)

end BoundedRun

open IntegerMultiplication.Code

/-- Time budget and absolute stack bounds for a computation on a deck of trees. -/
def BoundedFits (env : Env) (c : Cmd) (r s : Deck) (time cap depth : ℕ) : Prop :=
  ∃ n ≤ time, BoundedRun cap depth env c (letters r) n (letters s)

namespace BoundedFits

variable {env : Env} {c d : Cmd} {r s t : Deck} {n m cap depth leftDepth : ℕ}

theorem fits (h : BoundedFits env c r s n cap depth) : Fits env c r s n := by
  obtain ⟨t, ht, h⟩ := h
  exact ⟨t, ht, h.run⟩

theorem of_fits (h : Fits env c r s n) (data : ∀ i, (letters r i).length + n ≤ cap)
    (ret : n ≤ depth) : BoundedFits env c r s n cap depth := by
  obtain ⟨t, ht, run⟩ := h
  exact ⟨t, ht, .clock run (fun i => (Nat.add_le_add_left ht _).trans (data i)) (ht.trans ret)⟩

theorem mono {time' cap' depth' : ℕ} (h : BoundedFits env c r s n cap depth)
    (ht : n ≤ time') (hc : cap ≤ cap') (hd : depth ≤ depth') :
    BoundedFits env c r s time' cap' depth' := by
  obtain ⟨t, bound, run⟩ := h
  exact ⟨t, bound.trans ht, run.mono hc hd⟩

theorem join (h : BoundedFits env c r s n cap leftDepth) (g : BoundedFits env d s t m cap depth)
    (reserve : leftDepth + 1 ≤ depth) : BoundedFits env (.join c d) r t (n + m + 2) cap depth := by
  obtain ⟨a, ha, first⟩ := h
  obtain ⟨b, hb, second⟩ := g
  exact ⟨1 + a + 1 + b, by omega, .join first second reserve⟩

theorem tie (h : BoundedFits (c :: env) c r s n cap depth) :
    BoundedFits env (.tie c) r s (n + 1) cap depth := by
  obtain ⟨a, ha, child⟩ := h
  exact ⟨1 + a, by omega, .tie child⟩

theorem again0 (h : BoundedFits (c :: env) c r s n cap depth) :
    BoundedFits (c :: env) (.again 0) r s (n + 1) cap depth := by
  obtain ⟨a, ha, child⟩ := h
  exact ⟨1 + a, by omega, .again (c := c) (by simp) (by simpa using child)⟩

end BoundedFits

/-- One command and one absolute constant work for all instances and every
bounded parked deck. The parked deck's initial height is charged separately. -/
def BoundedTask {I : Type*} (time space : I → ℕ) (input output : I → Tree) : Prop :=
  ∃ c : Cmd, ∃ C : ℕ, ∀ i env r base, (∀ j, (letters r j).length ≤ base) →
    BoundedFits env c (pile 0 (input i) r) (pile 0 (output i) r)
      (C * (time i + 1)) (base + C * (space i + 1)) (C * (space i + 1))

namespace BoundedTask

variable {I J : Type*} {time space time' space' : I → ℕ} {input middle output : I → Tree}

/-- Restrict a single command to a reindexed family of inputs. -/
theorem on (h : BoundedTask time space input output) (f : J → I) :
    BoundedTask (fun j => time (f j)) (fun j => space (f j))
      (fun j => input (f j)) (fun j => output (f j)) := by
  obtain ⟨c, C, h⟩ := h
  exact ⟨c, C, fun j => h (f j)⟩

theorem conform {input' output' : I → Tree} (h : BoundedTask time space input output)
    (ht : ∀ i, time i = time' i) (hs : ∀ i, space i = space' i)
    (hin : ∀ i, input i = input' i) (hout : ∀ i, output i = output' i) :
    BoundedTask time' space' input' output' := by
  simpa only [funext ht, funext hs, funext hin, funext hout] using h

/-- Change both resource estimates by uniform constant factors. -/
theorem bound (h : BoundedTask time space input output) (T S : ℕ)
    (ht : ∀ i, time i + 1 ≤ T * (time' i + 1))
    (hs : ∀ i, space i + 1 ≤ S * (space' i + 1)) :
    BoundedTask time' space' input output := by
  obtain ⟨c, C, hc⟩ := h
  refine ⟨c, C * max T S, fun i env r base hr => ?_⟩
  have t := (Nat.mul_le_mul_left C (ht i)).trans (Nat.mul_le_mul_left C
    (Nat.mul_le_mul_right (time' i + 1) (le_max_left T S)))
  have s := (Nat.mul_le_mul_left C (hs i)).trans (Nat.mul_le_mul_left C
    (Nat.mul_le_mul_right (space' i + 1) (le_max_right T S)))
  rw [← Nat.mul_assoc] at t s
  exact (hc i env r base hr).mono t (Nat.add_le_add_left s _) s

theorem mono (h : BoundedTask time space input output)
    (ht : ∀ i, time i ≤ time' i) (hs : ∀ i, space i ≤ space' i) :
    BoundedTask time' space' input output :=
  h.bound 1 1 (fun i => by simpa using ht i) (fun i => by simpa using hs i)

/-- Sequential commands pay both times and reuse their decks. The left command
returns to the right one using a single additional saved return address. -/
theorem compose (h : BoundedTask time space input middle)
    (g : BoundedTask time' space' middle output) :
    BoundedTask (fun i => time i + time' i) (fun i => max (space i) (space' i)) input output := by
  obtain ⟨c, C, hc⟩ := h
  obtain ⟨d, D, hd⟩ := g
  refine ⟨c.join d, C + D + 2, fun i env r base hr => ?_⟩
  let maxSpace := max (space i) (space' i)
  have s1 : C * (space i + 1) + 1 ≤ (C + D + 2) * (maxSpace + 1) := by
    have u := Nat.mul_le_mul_left C (Nat.succ_le_succ (le_max_left (space i) (space' i)))
    change C * (space i + 1) ≤ C * (maxSpace + 1) at u
    simp only [Nat.add_mul, Nat.two_mul]
    omega
  have s2 : D * (space' i + 1) ≤ (C + D + 2) * (maxSpace + 1) := by
    have u := Nat.mul_le_mul_left D (Nat.succ_le_succ (le_max_right (space i) (space' i)))
    change D * (space' i + 1) ≤ D * (maxSpace + 1) at u
    simp only [Nat.add_mul]
    omega
  have first := (hc i env r base hr).mono le_rfl
    (Nat.add_le_add_left (Nat.le_of_lt s1) base) le_rfl
  have second := (hd i env r base hr).mono le_rfl (Nat.add_le_add_left s2 base) s2
  apply (first.join second s1).mono _ le_rfl le_rfl
  simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.two_mul]
  omega

/-- Both the initial input and a short command can be charged to its space.
The constant in the time bound is uniform over inputs. -/
theorem of_time {I : Type*} {time : I → ℕ} {input output : I → Tree}
    (h : Code.Task time input output) :
    BoundedTask time (fun i => (input i).count + time i) input output := by
  obtain ⟨c, C, hc⟩ := h
  refine ⟨c, C + 1, fun i env r base hr => ?_⟩
  have space : C * (time i + 1) + (input i).count ≤ (C + 1) * ((input i).count + time i + 1) := by
    simp only [Nat.succ_mul, Nat.mul_add, Nat.mul_one]
    omega
  have g := BoundedFits.of_fits (hc i env r)
    (cap := base + ((C + 1) * ((input i).count + time i + 1))) (depth := (C + 1) * ((input i).count + time i + 1))
    (fun j => by
      by_cases hj : j = 0
      · subst j
        rw [letters_here, List.length_append, Tree.spell_length]
        have := hr 0
        omega
      · rw [pile_far _ _ (Ne.symm hj)]
        have := hr j
        omega)
    (by omega)
  exact g.mono (Nat.mul_le_mul_right _ (by omega)) le_rfl le_rfl

end BoundedTask

end Space

end NearSquareRoot
end Computability
end OAI
