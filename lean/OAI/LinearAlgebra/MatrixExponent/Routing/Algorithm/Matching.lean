import OAI.LinearAlgebra.MatrixExponent.Routing.Algorithm.Computability
import OAI.LinearAlgebra.MatrixExponent.Routing.Algorithm.Split
import OAI.LinearAlgebra.MatrixExponent.Coloring.Edges

/-!
# Matching a regular graph by repeated halving

The dummy labels and the initial multiplicities are input-independent.
The current counter at each edge fits in the same word throughout.
Materializing the chosen side and the cycle colors before updating the
counters avoids recomputing a global quantity for each edge.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Routing.Algorithm
open Coloring
open scoped Classical

abbrev Graph (h k : ℕ) := (B h → B k) × (B h → B k) × (B h → Bool)

namespace RAM
variable {w h k r m : ℕ}

theorem iterate {A : Type} {f : A → A} (hf : RAM w f m) (t : ℕ) :
    RAM w (f^[t]) (1 + t * m) := by
  induction t with
  | zero => simpa using (RAM.id : RAM w (_root_.id : A → A) 1)
  | succ t ih => rw [Function.iterate_succ', Nat.succ_mul, ← Nat.add_assoc]; exact ih.comp hf

private abbrev State (h k r : ℕ) := (B h → B k) × (B h → B k) × (B h → B r)
private abbrev View (h k r : ℕ) := State h k r × ((B h → Bool) × Bool)

private def odds (x : State h k r) := fun i => Coloring.odd (x.2.2 i)
private def color (x : State h k r) := Coloring.split x.1 x.2.1 (odds x)

private def update (x : View h k r) (i : B h) :=
  let v := x.1.2.2 i
  if Coloring.odd v && (x.2.1 i == x.2.2) then Coloring.half v + 1 else Coloring.half v

private def step (δ : B h → Bool) (x : State h k r) : State h k r :=
  (x.1, x.2.1, update (x, color x, Coloring.minority δ (odds x) (color x)))

private theorem step_val (δ : B h → Bool) (x : State h k r) :
    Fin.val ∘ (step δ x).2.2 = Coloring.halve x.1 x.2.1 δ (Fin.val ∘ x.2.2) := by
  funext i
  let v := x.2.2 i
  let bit := Coloring.odd v && (color x i == Coloring.minority δ (odds x) (color x))
  change (if bit then Coloring.half v + 1 else Coloring.half v).val =
    v.val / 2 + if bit then 1 else 0
  split_ifs with hb
  · have ho : v.val % 2 = 1 := of_decide_eq_true (Bool.and_eq_true_iff.mp hb).1
    have := v.isLt
    change (v.val / 2 + 1 % 2 ^ r) % 2 ^ r = _
    rw [Nat.add_mod_mod, Nat.mod_eq_of_lt (by omega)]
  · rfl

private theorem steps (δ : B h → Bool) (x : State h k r) (n : ℕ) :
    ((step δ)^[n] x).1 = x.1 ∧ ((step δ)^[n] x).2.1 = x.2.1 ∧
      Fin.val ∘ ((step δ)^[n] x).2.2 = (Coloring.halve x.1 x.2.1 δ)^[n] (Fin.val ∘ x.2.2) := by
  induction n with
  | zero => exact ⟨rfl, rfl, rfl⟩
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    exact ⟨ih.1, ih.2.1, by rw [step_val, ih.1, ih.2.1, ih.2.2]⟩

private theorem update_code (hh : h ≤ w) (hr : r ≤ w) (i : B h) :
    RAM w (fun x : View h k r => update x i) 50 := by
  have v : RAM w (fun x : View h k r => x.1.2.2 i) 4 :=
    ((RAM.fst.comp .snd).comp .snd).comp (.at hh i)
  have col : RAM w (fun x : View h k r => x.2.1 i) 3 := (RAM.snd.comp .fst).comp (.at hh i)
  have pick := (col.pair (RAM.snd.comp RAM.snd)).comp (.gate (fun x => x.1 == x.2))
  have tag := ((v.comp (.odd hr)).pair pick).comp (.gate (fun x => x.1 && x.2))
  have down := v.comp (.halve hr)
  have plus := (down.pair (.lit hr 1)).comp (.add hr)
  exact ((tag.pair (plus.pair down)).comp .select).mono (by decide)

private theorem step_code (hh : h + 1 ≤ w) (hk : k ≤ w) (hr : r ≤ w) (δ : B h → Bool) :
    RAM w (step (k := k) (r := r) δ) (2 ^ h * (100 + w) ^ 42) := by
  have hv : h ≤ w := by omega
  have mask : RAM w (odds (h := h) (k := k) (r := r)) (2 ^ h * 5) :=
    .tab hv _ (fun i => ((RAM.snd.comp .snd).comp (.at hv i)).comp (.odd hr))
  have row := (RAM.fst.pair ((RAM.snd.comp RAM.fst).pair mask)).comp (RAM.split hv hk)
  have side := (mask.pair row).comp (RAM.minority hh δ)
  have upd := ((row.pair side).keep).comp (RAM.tab hv _ (update_code (k := k) hv hr))
  refine (RAM.fst.pair ((RAM.snd.comp RAM.fst).pair upd)).mono ?_
  have := budget_mono h w (by decide : 10 ≤ 40)
  have := budget_base h w 40
  have := Nat.two_pow_pos h
  have h₁ := budget_step h w 40
  have h₂ := budget_step h w 41
  simp only [Nat.reduceAdd] at h₁ h₂
  omega

private def init (S : Finset (B k)) (d : ℕ) (x : Graph h k) : State (h + 1) k (h + 2) :=
  (join x.1 (dummyLabel S), join x.2.1 (dummyLabel S),
    fun i => Fin.ofNat (2 ^ (h + 2)) (weights S d x.2.2 i))

private theorem init_eq (S : Finset (B k)) (d : ℕ) (x : Graph h k) :
    Fin.val ∘ (init S d x).2.2 = weights S d x.2.2 := by
  funext t
  apply Nat.mod_eq_of_lt
  have hp : 2 ^ (h + 1) < 2 ^ (h + 2) := Nat.pow_lt_pow_right (by decide) (by omega)
  obtain ⟨i|i, rfl⟩ := (halves h).surjective t
  · simp only [weights, join, Function.comp_apply, Equiv.symm_apply_apply, Sum.elim_inl]
    split <;> first | exact (Nat.div_le_self ..).trans_lt hp | positivity
  · simp only [weights, join, Function.comp_apply, Equiv.symm_apply_apply, Sum.elim_inr]
    split <;> first | exact (Nat.mod_le ..).trans_lt hp | positivity

private theorem init_code (hh : h + 2 ≤ w) (hk : k ≤ w) (S : Finset (B k)) (d : ℕ) :
    RAM w (init (h := h) S d) (2 ^ h * 100) := by
  have hv : h + 1 ≤ w := by omega
  have ht : h ≤ w := by omega
  have ext : RAM w (fun p : B h → B k => join p (dummyLabel S)) (2 ^ (h + 1) * 2) := by
    apply RAM.tab (m := 1) hv
    intro t
    obtain ⟨i|i, rfl⟩ := (halves h).surjective t
    · simpa [join] using (RAM.at (A := B k) ht i)
    · simpa [join] using (RAM.lit (A := B h → B k) hk (dummyLabel S i))
  have cnt : RAM w (fun x : B h → Bool => fun t => Fin.ofNat (2 ^ (h + 2)) (weights S d x t))
      (2 ^ (h + 1) * 7) := by
    apply RAM.tab (m := 6) hv
    intro t
    obtain ⟨i|i, rfl⟩ := (halves h).surjective t
    · have he := ((RAM.at (A := Bool) ht i).pair
        ((RAM.lit hh (Fin.ofNat (2 ^ (h + 2)) (2 ^ (h + 1) / d))).pair (RAM.lit hh 0))).comp .select
      simp only [weights, join, Function.comp_apply, Equiv.symm_apply_apply, Sum.elim_inl]
      convert he using 1
      funext x
      by_cases h : x i = true <;> simp [h]
    · simp only [weights, join, Function.comp_apply, Equiv.symm_apply_apply, Sum.elim_inr]
      exact (RAM.lit hh _).mono (by decide)
  refine ((RAM.fst.comp ext).pair (((RAM.snd.comp RAM.fst).comp ext).pair
    ((RAM.snd.comp RAM.snd).comp cnt))).mono ?_
  rw [pow_succ]
  have := Nat.two_pow_pos h
  omega

private def out (a : State (h + 1) k (h + 2)) (i : B h) := decide (a.2.2 (halves h (.inl i)) = 1)

private theorem out_code (hh : h + 2 ≤ w) :
    RAM w (out (h := h) (k := k)) (2 ^ h * 7) := by
  apply RAM.tab (m := 6) (by omega)
  intro i
  exact ((((RAM.snd.comp .snd).comp (RAM.at (by omega) (halves h (.inl i)))).pair (.lit hh 1)).comp (.eq hh))

private theorem out_eq (S : Finset (B k)) (d : ℕ) (x : Graph h k) :
    out ((step (dummy h))^[h + 1] (init S d x)) = matching S d x.1 x.2.1 x.2.2 := by
  have he := (steps (dummy h) (init S d x) (h + 1)).2.2
  rw [init_eq] at he
  funext i
  have hv := congrFun he (halves h (.inl i))
  have hs : (1 : B (h + 2)).val = 1 := Nat.mod_eq_of_lt (Nat.one_lt_pow (by omega) (by decide))
  simp only [out, Fin.ext_iff, hs, Coloring.matching]
  exact congrArg (fun n => decide (n = 1)) hv

theorem matching (hh : h + 2 ≤ w) (hk : k ≤ w) (S : Finset (B k)) (d : ℕ) :
    RAM w (fun x : Graph h k => Coloring.matching S d x.1 x.2.1 x.2.2) (2 ^ h * (100 + w) ^ 46) := by
  have run := ((init_code hh hk S d).comp ((step_code (h := h + 1) hh hk hh (dummy h)).iterate (h + 1))).comp (out_code hh)
  have val : out ∘ (step (dummy h))^[h + 1] ∘ init S d =
      (fun x : Graph h k => Coloring.matching S d x.1 x.2.1 x.2.2) := funext (out_eq S d)
  rw [val] at run
  refine run.mono ?_
  have hi : (h + 1) * (2 ^ (h + 1) * (100 + w) ^ 42) ≤ 2 * (2 ^ h * (100 + w) ^ 43) := by
    calc
      _ ≤ (100 + w) * (2 ^ (h + 1) * (100 + w) ^ 42) := Nat.mul_le_mul_right _ (by omega)
      _ = _ := by
        have eqn (a b c : ℕ) : c * (a * 2 * b) = 2 * (a * (b * c)) := by ring
        rw [pow_succ 2 h, pow_succ (100 + w) 42]
        exact eqn ..
  have := Nat.two_pow_pos h
  have := budget_base h w 43
  have ha := budget_step h w 43
  have hb := budget_step h w 44
  have hc := budget_step h w 45
  simp only [Nat.reduceAdd] at ha hb hc
  omega

end RAM
end OAI.LinearAlgebra.MatrixExponent.Routing.Algorithm
