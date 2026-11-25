import OAI.Computability.NearSquareRoot.ShortWordSpace

/-!
# From distinct visited cells to fences for repeated attempts

Unit head movements force every intermediate address between the start and
current position to have been visited. A cardinal space bound thus gives fixed
intervals about the initial heads even when the individual visited sets differ
between attempts or input values.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Uniform

open IntegerMultiplication TM

variable {A Q I : Type}

/-- No execution prefix extends beyond a halting execution. -/
theorem before_halt {X : Type} {f : X → Option X} {x y z : X} {k t : ℕ}
    (run : Trace f x t y) (halt : f y = none) (sub : Trace f x k z) : k ≤ t := by
  induction run generalizing k z with
  | nil =>
    cases sub with
    | nil => rfl
    | cons hs => simp [halt] at hs
  | @cons x u y n step _ ih =>
    cases sub with
    | nil => exact Nat.zero_le _
    | @cons _ v _ j hs rest =>
      obtain rfl : v = u := Option.some.inj (hs.symm.trans step)
      exact Nat.add_le_add_left (ih halt rest) 1

/-- A unit head visits every address between its initial and final positions. -/
theorem crosses {m : Rule A Q I} {x y : Config A Q I} {t : ℕ}
    (run : Trace (advance m) x t y) (i : I) (p : ℤ)
    (left : min (x.tape i).pos (y.tape i).pos ≤ p)
    (right : p ≤ max (x.tape i).pos (y.tape i).pos) :
    ∃ j ≤ t, ∃ z, Trace (advance m) x j z ∧ (z.tape i).pos = p := by
  induction run with
  | nil x => exact ⟨0, le_rfl, x, .nil _, by simpa using le_antisymm left right⟩
  | @cons x u y n step _ ih =>
    by_cases he : (x.tape i).pos = p
    · exact ⟨0,Nat.zero_le _,x,.nil _,he⟩
    · have hd := head_excursion (Trace.single step) i
      simp only [Nat.cast_one] at hd
      obtain ⟨k,hk,z,sub,hp⟩ := ih (by omega) (by omega)
      exact ⟨1+k,by omega,z,.cons step sub,hp⟩

/-- If at most `space` cells were visited, then each individual tape head
is always within that distance of its initial position. -/
theorem radius_of_visits {m : Rule A Q I} {x y : Config A Q I} {t k space : ℕ}
    (budget : VisitsAtMost m x t space) (hk : k ≤ t) (run : Trace (advance m) x k y) (i : I) :
    (x.tape i).pos - space ≤ (y.tape i).pos ∧ (y.tape i).pos ≤ (x.tape i).pos + space := by
  classical
  obtain ⟨v,hv,cover⟩ := budget
  let a := (x.tape i).pos
  let b := (y.tape i).pos
  let e := Function.Embedding.sectR i ℤ
  have hsub : (Finset.Icc (min a b) (max a b)).map e ⊆ v := by
    intro z hz
    obtain ⟨p,hp,hpz⟩ := Finset.mem_map.mp hz
    obtain ⟨hlo,hhi⟩ := Finset.mem_Icc.mp hp
    obtain ⟨j,hj,c,hc,hpos⟩ := crosses run i p hlo hhi
    subst z
    exact hpos ▸ cover j (hj.trans hk) c hc i
  have hc := (Finset.card_le_card hsub).trans hv
  rw [Finset.card_map, Int.card_Icc] at hc
  change a - space ≤ b ∧ b ≤ a + space
  omega

private theorem frame {m : Rule A Q I} {x y : Config A Q I} {t : ℕ}
    (run : Trace (advance m) x t y) (i : I) (p : ℤ)
    (outside : ∀ {j c}, j ≤ t → Trace (advance m) x j c → p ≠ (c.tape i).pos) :
    (y.tape i).absolute p = (x.tape i).absolute p := by
  induction run with
  | nil => rfl
  | @cons x u y n step _ ih =>
    rw [ih (fun hj hs => outside (by omega) (.cons step hs))]
    have hne := outside (Nat.zero_le _) (.nil x)
    unfold advance at step
    cases hop : m x.pc (fun z => (x.tape z).view 0) with
    | none => simp [hop] at step
    | some data =>
      obtain ⟨q,o⟩ := data
      simp only [hop, Option.map_some, Option.some.injEq] at step
      subst u
      exact (Tape.absolute_apply _ _ _).trans (ite_eq_right hne)

/-- Every location whose symbol changed lies inside the radius supplied by the
physical space bound. This applies to written endpoint marks as well as payload. -/
theorem changed_in_radius {m : Rule A Q I} {x y : Config A Q I} {t space : ℕ}
    (budget : VisitsAtMost m x t space) (run : Trace (advance m) x t y) (i : I) (p : ℤ)
    (changed : (y.tape i).absolute p ≠ (x.tape i).absolute p) :
    (x.tape i).pos - space ≤ p ∧ p ≤ (x.tape i).pos + space := by
  by_contra not_mem
  apply changed
  apply frame run i p
  intro j c hj tr he
  exact not_mem (he ▸ radius_of_visits budget hj tr i)

/-- A changed symbol lies at most as many cells from the initial head as
there have been transitions. -/
theorem changed_in_time {m : Rule A Q I} {x y : Config A Q I} {t : ℕ}
    (run : Trace (advance m) x t y) (i : I) (p : ℤ)
    (changed : (y.tape i).absolute p ≠ (x.tape i).absolute p) :
    (x.tape i).pos - t ≤ p ∧ p ≤ (x.tape i).pos + t := by
  by_contra h
  apply changed
  apply frame run i p
  intro j c hj sub he
  have hh := head_excursion sub i
  omega

/-- A string of nonblank digits on an initially empty output has its last
digit within the clock radius. This charges final publication to the trial. -/
theorem literal_length {m : Rule A Q I} {x y : Config A Q I} {t : ℕ} (i : I)
    (run : Trace (advance m) x t y) (origin : (x.tape i).pos = 0)
    (blank : A) (bit : Bool → A) (nonblank : ∀ b, bit b ≠ blank)
    (init : (x.tape i).absolute = fun _ => blank) (z : List Bool)
    (out : whole blank (z.map bit) (y.tape i)) : z.length ≤ t+1 := by
  by_cases hz : z.length = 0
  · omega
  let j := z.length - 1
  have hj : j < z.length := by dsimp [j]; omega
  have he : (y.tape i).absolute (j:ℤ) = bit z[j] := by
    rw [show (y.tape i).absolute = _ from out]
    simp [Tape.absolute,Tape.loaded,List.getElem?_eq_getElem hj]
  have changed : (y.tape i).absolute (j:ℤ) ≠ (x.tape i).absolute j := by
    rw [he,init]
    exact nonblank _
  have H := (changed_in_time run i _ changed).2
  dsimp only [j] at H
  rw [origin] at H
  omega

end Uniform

end NearSquareRoot
end Computability
end OAI
