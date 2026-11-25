import OAI.Computability.BorderVNP.DiagonalFlatReplay
import OAI.Computability.BorderVNP.PackedHistoryOuter

/-! # Independent private assignments on the public outer tree of site epochs -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal.CellEntries.Outer

open Crossing Shortening Adaptive Packing
open scoped BigOperators Classical

universe u

variable {D K b : ℕ} {P Team Param Gadget Hidden E : Type} [Fintype Team] [Fintype Param]
    [Fintype Hidden] [Field E] {bits : P → ℕ} {A : ℕ → Type u}
    (layout : ∀ n, A n → Network D (Port K P n) (width bits K n))
    (bottom : A 0) (epoch : ∀ n, (Fin K → A n) → ProfileSum (A (n+1)))

/-- Row-major enumeration of the original batches after these packing stages. -/
local instance {n : ℕ} : Fintype (Port K Team n) := Replay.batchFinite K Team n

/-- The local evaluator for one actual site epoch, with a separate
conditioned tagged table for every child. `SiteReplay.term` supplies this
map on the geometric execution and its attained profile index. -/
abbrev Advance :=
  ∀ n (child : Fin K → A n),
    (∀ i, Tracked (Port K Team n) Param Gadget b (layout n (child i))) →
    (q : (epoch n child).Index) →
      Tracked (Port K Team (n+1)) Param Gadget b (layout (n+1) ((epoch n child).term q))

variable (base : Hidden → Tracked Team Param Gadget b (layout 0 bottom))
    (advance : Advance (Team := Team) (Param := Param) (Gadget := Gadget) (b := b) layout epoch)

/-- Replay the very same public epoch index used by the packing procedure.
The independently supplied bottom private strings are indexed row-major. -/
noncomputable def term : (n : ℕ) → (Fin (K^n) → Hidden) →
    (q : (packHistory bottom epoch n).Index) →
      Tracked (Port K Team n) Param Gadget b (layout n ((packHistory bottom epoch n).term q))
  | 0, z, _ => base (z 0)
  | n+1, z, q =>
    let h := packHistory bottom epoch n
    let child := fun i : Fin K => h.term (q.1 i)
    let tagged := fun i : Fin K => term n (fun j => z (copyIndex K n (i,j))) (q.1 i)
    advance n child tagged q.2

omit [Fintype Hidden] in
/-- The product over the conditioned inputs is the sum over exactly the
public profile histories returned by the recursive outer packing procedure. -/
theorem sum_terms (values : Gadget → E) (top : ℕ)
    (exact : ∀ n, n < top → ∀ child tagged x, (∏ i, ((tagged i).valued values).tensor (fun p => x (i,p))) =
      ∑ q, ((advance n child tagged q).valued values).tensor x)
    (n : ℕ) (hn : n ≤ top) (z : Fin (K^n) → Hidden) (x : Ports (fun q : Fin (K^n) × P => bits q.2)) :
    (∏ i, ((base (z i)).valued values).tensor (fun p => x (i,p))) =
      ∑ q, ((term layout bottom epoch base advance n z q).valued values).tensor
        (nestedPorts bits K n x) := by
  induction n with
  | zero =>
    exact (Fintype.prod_unique (fun i : Fin 1 => ((base (z i)).valued values).tensor (fun p => x (i,p)))).trans
      (Fintype.sum_unique (fun _ : PUnit => ((base (z 0)).valued values).tensor (fun p => x (0,p)))).symm
  | succ n ih =>
    let h := packHistory bottom epoch n
    let val := fun i : Fin (K^(n+1)) => ((base (z i)).valued values).tensor (fun p => x (i,p))
    have flat := (copyIndex K n).prod_comp val
    rw [Fintype.prod_prod_type] at flat
    refine flat.symm.trans ?_
    let z' := fun (i : Fin K) (j : Fin (K^n)) => z (copyIndex K n (i,j))
    let x' := fun (i : Fin K) (p : Fin (K^n) × P) => x (copyIndex K n (i,p.1),p.2)
    trans ∏ i : Fin K, ∑ q : h.Index,
      ((term layout bottom epoch base advance n (z' i) q).valued values).tensor (nestedPorts bits K n (x' i))
    · exact Finset.prod_congr rfl fun i _ => ih (by omega) (z' i) (x' i)
    rw [Fintype.prod_sum]
    change _ = ∑ q : Σ c : Fin K → h.Index, (epoch n (fun i => h.term (c i))).Index, _
    rw [Fintype.sum_sigma]
    apply Finset.sum_congr rfl
    intro c _
    exact exact n (by omega) (fun i => h.term (c i))
      (fun i => term layout bottom epoch base advance n (z' i) (c i)) (nestedPorts bits K (n+1) x)

/-- Sum over all fine inputs as well, commuting the finite hidden choices
past the public profile enumeration. This order matches a processor that
chooses the common public history before reading private cell factors. -/
theorem sum_private_and_public (values : Gadget → E) (top : ℕ)
    (exact : ∀ n, n < top → ∀ child tagged x, (∏ i, ((tagged i).valued values).tensor (fun p => x (i,p))) =
      ∑ q, ((advance n child tagged q).valued values).tensor x)
    (n : ℕ) (hn : n ≤ top) (x : Ports (fun q : Fin (K^n) × P => bits q.2)) :
    (∏ i, ∑ z : Hidden, ((base z).valued values).tensor (fun p => x (i,p))) =
      ∑ q, ∑ z : Fin (K^n) → Hidden, ((term layout bottom epoch base advance n z q).valued values).tensor
        (nestedPorts bits K n x) := by
  rw [Fintype.prod_sum, Finset.sum_comm]
  exact Finset.sum_congr rfl fun z _ => sum_terms layout bottom epoch base advance values top exact n hn z x

end Diagonal.CellEntries.Outer

end BorderVNP
end Computability
end OAI
