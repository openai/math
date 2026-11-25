import OAI.Computability.NearSquareRoot.NamedPackedRate
import OAI.Computability.NearSquareRoot.CRTControlledPrefixClock
import OAI.Computability.NearSquareRoot.CRTControlledPrefixFlatten
import OAI.Computability.NearSquareRoot.ScheduleNamedLiftoff

/-! # Charged execution of a specified command on every row of a Cartesian forest -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Controlled.PrefixCommand

open IntegerMultiplication Code Strip NamedPacked

variable {X : Type} {a b : X → ℝ} {c : Cmd} {q v : X → Tree}

private theorem ceilCarry (h : EffectiveTask.Runs c (fun i => ⌈a i⌉₊) q v) (hn : ∀ i,1 ≤ a i)
    (hvol : Volume a q) : CarriesAt c a q v := by
  refine ⟨hn,⟨_,h,3,fun i => ?_⟩,hvol⟩
  have hi := Nat.ceil_lt_add_one (zero_le_one.trans (hn i))
  have := hn i
  norm_num; linarith

theorem reprice (h : CarriesAt c a q v) (C : ℕ) (hb : ∀ i,1 ≤ b i) (ht : ∀ i,a i ≤ C*b i) :
    CarriesAt c b q v := ceilCarry (price C h.release ht) hb (h.forget.times hb C ht).small

/-- Row mapping followed by concatenation has a fixed syntactic form for all
Cartesian geometries, row payload types, and reached arrays. -/
theorem rowPass {A B : X → Type} (s : (i : X) → Series (A i)) (t : (i : X) → Series (B i))
    (r : Regime X) (width : X → ℕ) (rate : X → ℝ) (hs : ∀i,1≤(s i).count) (ht : ∀i,1≤(t i).count)
    (hr : ∀ i,1≤rate i) (header : X → Tree) (v out : (i : X) → A i × B i → Tree) {inner : Cmd}
    (h : BreezeAt inner (fun z : Sigma A => rate z.1) (r.pull Sigma.fst)
      (fun z => (t z.1).count) (fun z => width z.1)
      (fun z => .fork (header z.1) (stripe (t z.1) (fun b => v z.1 (z.2,b))))
      (fun z => stripe (t z.1) (fun b => out z.1 (z.2,b)))) :
    BreezeAt ((NamedLiftoff.rowMap inner).join flattenCmd) rate r (fun i => ((s i).cart (t i)).count) width
      (stackRun s (fun i a => .fork (header i) (stripe (t i) (fun b => v i (a,b)))))
      (stackRun (fun i => (s i).cart (t i)) out) := by
  obtain ⟨_,d,step⟩ := h
  let src i (a : A i) := Tree.fork (header i) (stripe (t i) (fun b => v i (a,b)))
  let dst i (a : A i) := stripe (t i) (fun b => out i (a,b))
  let localRate := runrate rate r (fun i => (t i).count) width d
  let G := runrate rate r (fun i => ((s i).cart (t i)).count) width d
  have pos i : 1 ≤ localRate i := one_le_mul_of_one_le_of_one_le (unit_mass ht d i) (hr i)
  have entire i : 1 ≤ G i := one_le_mul_of_one_le_of_one_le
    (unit_mass (fun i => by rw [Series.count_cart]; exact Nat.mul_pos (hs i) (ht i)) d i) (hr i)
  have rateEq i : (s i).count*localRate i = G i := by
    simp only [G,localRate,runrate,mass,Series.count_cart,Nat.cast_mul]; ring
  have lift := NamedLiftoff.runs s src dst localRate pos step.small step.release
  have vol := stripe_volume s src localRate step.small pos
  have mapped := ceilCarry lift (fun i => by rw [rateEq]; have := entire i; linarith : ∀ i, 1 ≤ ((s i).count:ℝ)*localRate i+1) vol
  have first : CarriesAt (NamedLiftoff.rowMap inner) G (stackRun s src) (stackRun s dst) :=
    reprice mapped 2 entire (fun i => by rw [rateEq]; have := entire i; norm_num; linarith)
  have enough := first.forget.out
  obtain ⟨C,hC⟩ := enough
  have concat := flatten_runs s t out
  have finish : CarriesAt flattenCmd G (stackRun s dst) (stackRun (fun i => (s i).cart (t i)) out) :=
    ⟨entire,⟨_,concat,C+1,fun i => by have := hC i; have := entire i; push_cast; linarith⟩,C,hC⟩
  exact ⟨hr,d,first.next finish⟩

end Controlled.PrefixCommand

end NearSquareRoot
end Computability
end OAI
