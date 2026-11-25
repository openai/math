import OAI.LinearAlgebra.MatrixExponent.Routing.Algorithm.Hop
import OAI.LinearAlgebra.MatrixExponent.Routing.Algorithm.Computability
import OAI.LinearAlgebra.MatrixExponent.Routing.Algorithm.Padding

/-!
# Deterministic control of the local sorting protocol

The record width affects only the padding and local kernels. One
program per height computes every configuration and opposite endpoint,
from the valid tags and one bounded selector per site. The program
and the list of port groups are fixed before either input is given.
We charge for the complete program and the group list as advice.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Routing.Algorithm
open Coloring Transport
open scoped Classical

variable {F : Type} [Field F] {m : ℕ} (T : Layout F m) (s : Rig T.params) (P : Palette T s)

/-- Space to read the input words, write the commands, and list one
group number per slot, including pair and array headers. -/
def records (p h : ℕ) := 2 ^ (h + 1) * (64 + 32 * 2 ^ p)

structure SortingAt (c D h : ℕ) where
  code : Code (3 * (h + 1) + 10) ((Perm h).pair (Selectors T s h)).obj (Commands T s P h).obj
  group : Port h s.p → ℕ
  group_word : ∀ x, group x < 2 ^ (h + 2)
  capacity : ∀ i, (Finset.univ.filter (fun k => group k = i)).card ≤ 2 ^ (h / m + T.overhead + s.p)
  words : max (3 * (h + 1) + 10) (max P.l (max s.clock.bits s.p)) ≤ (2 * c + 10) * h
  time : code.time + records s.p h ≤ 2 ^ h * (100 + h) ^ c
  memory : code.advice + code.scratch + records s.p h ≤ 2 ^ h * (100 + h) ^ c
  addresses : 2 ^ h * (100 + h) ^ c ≤ 2 ^ ((2 * c + 10) * h)
  resolves : Resolves T s P code.eval
  widths : ∀ w ≥ h, ∃ j ≤ Nat.clog 2 w, w ≤ s.clock.width * 2 ^ j ∧ s.clock.width * 2 ^ j ≤ 2 * w ∧
    let S := (systemOf T s P code.eval group j).pad w
    S.Correct 9624 ∧ Install.Weight F S.localWeight (w * (100 + Nat.clog 2 w) ^ D)

theorem selector_bits (h : ℕ) : (Selectors T s h).width = 2 ^ (h + 1) * s.clock.bits := by
  simp [Selectors]

private theorem address_space (h c : ℕ) (hh : 100 ≤ h) :
    2 ^ h * (100 + h) ^ c ≤ 2 ^ ((2 * c + 10) * h) := by
  have hb : 100 + h ≤ 2 ^ (2 * h) := by
    have hn := Nat.lt_two_pow_self (n := h)
    have he : 100 + h ≤ (h + 1) ^ 2 := by nlinarith
    rw [mul_comm 2 h, pow_mul]
    exact he.trans (Nat.pow_le_pow_left hn 2)
  calc
    _ ≤ 2 ^ h * (2 ^ (2 * h)) ^ c := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hb _)
    _ = 2 ^ (h + 2 * h * c) := by rw [pow_add, pow_mul 2 (2 * h) c]
    _ ≤ _ := Nat.pow_le_pow_right (by decide) (by nlinarith)

private theorem time_bound (h c p : ℕ) (hh : 64 + 32 * 2 ^ p ≤ h) :
    32 * (2 ^ (h + 1) * (100 + h) ^ c) + records p h ≤ 2 ^ h * (100 + h) ^ (c + 2) := by
  have hr : records p h ≤ 2 * (2 ^ h * (100 + h) ^ (c + 1)) := by
    have hs : h ≤ (100 + h) ^ (c + 1) := (Nat.le_add_left ..).trans (Nat.le_self_pow (by omega) _)
    unfold records
    rw [pow_succ 2 h, mul_comm (2 ^ h) 2, mul_assoc]
    exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (hh.trans hs))
  have hs : 32 * (2 ^ (h + 1) * (100 + h) ^ c) ≤ 2 ^ h * (100 + h) ^ (c + 1) := by
    refine le_trans ?_ (budget_step h h c)
    rw [pow_succ 2 h]
    grind
  have hm : 100 * (2 ^ h * (100 + h) ^ (c + 1)) ≤ 2 ^ h * (100 + h) ^ (c + 2) := budget_step h h (c + 1)
  omega

/-- The fixed finite tests and deterministic permutation procedures suffice.
There is no upper bound on w in the control statement. -/
theorem Layout.sorting (hm : 2 ≤ m) (ht : T.Computes Computable) :
    ∃ (s : Rig T.params) (P : Palette T s) (c D : ℕ),
      ∀ᶠ h in Filter.atTop, Nonempty (SortingAt T s P c D h) := by
  obtain ⟨s, P, D, proto⟩ := T.protocol
  obtain ⟨c, hf⟩ := T.dispatch ht s P
  refine ⟨s, P, c + 2, padExponent (Format.addr P.l).width s.p D, ?_⟩
  filter_upwards [hf, Filter.eventually_ge_atTop (2 * T.overhead), Filter.eventually_ge_atTop 100,
    Filter.eventually_ge_atTop (64 + 32 * 2 ^ s.p), Filter.eventually_ge_atTop s.clock.width,
    Filter.eventually_ge_atTop (max P.l (max s.clock.bits s.p))] with h hf ho hh hh' hw hb
  obtain ⟨f, resolves, time⟩ := hf
  obtain ⟨C, he, hc, _⟩ := time.code
  have ratio : 2 * (h / m) ≤ h := (Nat.mul_le_mul_right _ hm).trans (Nat.mul_div_le h m)
  obtain ⟨group, bounds, cap, ok⟩ := proto h (h / m + T.overhead) le_rfl (by omega)
  have hr : Resolves T s P C.eval := by rw [he]; exact resolves
  have hs := (Nat.add_le_add_right hc (records s.p h)).trans (time_bound h c s.p hh')
  have bits : max (3 * (h + 1) + 10) (max P.l (max s.clock.bits s.p)) ≤ (2 * (c + 2) + 10) * h :=
    (show max _ _ ≤ 4 * h by omega).trans (Nat.mul_le_mul_right _ (by omega))
  refine ⟨⟨C, group, bounds, cap, bits, hs, (Nat.add_le_add_right C.advice_scratch _).trans hs,
    address_space _ _ hh, hr, ?_⟩⟩
  intro w hv
  have hW : 1 ≤ s.clock.width := (by decide : 1 ≤ 4).trans s.clock.wide
  obtain ⟨j, hj, hl, hu⟩ := padded_scale hW (hw.trans hv)
  obtain ⟨correct, small⟩ := ok _ hr j
  exact ⟨j, hj, hl, hu, System.pad_correct _ correct hl hu, System.pad_weight _ small hW hu hj⟩

end OAI.LinearAlgebra.MatrixExponent.Routing.Algorithm
