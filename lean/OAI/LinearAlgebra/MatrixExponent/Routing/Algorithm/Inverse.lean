import OAI.LinearAlgebra.MatrixExponent.Routing.Algorithm.Computability
import OAI.LinearAlgebra.MatrixExponent.Routing.Algorithm.Sort

/-! # Recovering inverse permutations by sorting the images -/

namespace OAI.LinearAlgebra.MatrixExponent.Routing.Algorithm.RAM
open Coloring

private theorem inverse_sorted {h : ℕ} (g : Equiv.Perm (B h)) :
    Coloring.permutation g (fun _ => true) = g.symm := by
  let key (i : B h) := toLex (false, toLex (g i, i))
  have hs : StrictMono (key ∘ g.symm) := by
    intro i j hij
    simp only [Function.comp_apply, key, Equiv.apply_symm_apply, Prod.Lex.toLex_lt_toLex]
    exact .inr ⟨trivial, .inl hij⟩
  change Tuple.sort key = g.symm
  symm
  exact Tuple.eq_sort_iff.mpr ⟨hs.monotone, fun _ _ hij he => ((hs hij).ne he).elim⟩

theorem inverse {w h : ℕ} (hh : h ≤ w) :
    ∃ inv : Endo h, RAM w inv (2 ^ h * (100 + w) ^ 25) ∧
      ∀ g : Equiv.Perm (B h), inv g = ⇑g.symm := by
  have on : RAM w (fun (_ : B h → B h) (_ : B h) => true) (2 ^ h * 2) :=
    .tab hh _ (fun _ => .bit true)
  refine ⟨_, (on.keep.comp (RAM.permutation hh hh)).mono ?_, fun g => ?_⟩
  · have := Nat.two_pow_pos h
    have := budget_base h w 20
    have := (budget_step h w 20).trans (budget_mono h w (by decide : 21 ≤ 25))
    omega
  · change ⇑(Coloring.permutation g (fun _ => true)) = ⇑g.symm
    rw [inverse_sorted]

end OAI.LinearAlgebra.MatrixExponent.Routing.Algorithm.RAM
