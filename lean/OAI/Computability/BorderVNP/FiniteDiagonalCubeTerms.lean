import OAI.Computability.BorderVNP.CubeGlobalExpansion

/-! # The scalar field sum of all genuine cube packet assignments

The independent selectors name one finite cube network per packet. Its internal
edge words and its two external endpoint words are separate indices before the
sum. The antipodal identity collapses them to one common word for each pair.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FiniteDiagonal

open Cube Crossing MvPolynomial
open scoped BigOperators Classical
open private commonEnds sum_ends from OAI.Computability.BorderVNP.CubeGlobalExpansion

/-- One full cube expansion term in Section 8.3, retaining the shared singleton
bits, both endpoint words, the selector of each packet and its genuine cable words. -/
abbrev CubeTerm (I Sing : Type*) (n b h K s D : ℕ) :=
  (Sing → Bool) × (I → Ends n → Fin (h*b) → Bool) ×
    ((u : I → Selector n K h) × ∀ i, (packetNetwork D b s (u i)).Assignment)

variable {I Sing F : Type*} [Fintype I] [CommRing F] {n b h K s D : ℕ}

/-- The assigned host factor times the actual cube table entry at each packet vertex. -/
noncomputable def cubeTermWeight (table : I → TableEntry n b h K s → F)
    (host : (Sing → Bool) → (I → Ends n → Fin (h*b) → Bool) → F) (a : CubeTerm I Sing n b h K s D) : F :=
  host a.1 a.2.1 * ∏ i, ∏ v : (packetNetwork D b s (a.2.2.1 i)).Site,
    (packetNetwork D b s (a.2.2.1 i)).read (packetTables (table i) D (a.2.2.1 i))
      (a.2.2.2 i) (a.2.1 i) v

/-- Summation over the entire unfiltered scalar term type gives exactly the host
sum with each antipodal pair using a single common word. -/
theorem sum_cubeTermWeight [Fintype Sing] (table : I → TableEntry n b h K s → F)
    (valid : ∀ i, ValidTables (table i))
    (host : (Sing → Bool) → (I → Ends n → Fin (h*b) → Bool) → F) (D : ℕ) :
    (∑ a : CubeTerm I Sing n b h K s D, cubeTermWeight table host a) =
      ∑ w : Sing → Bool, ∑ y : I → Vertex n → Fin (h*b) → Bool, host w (fun i e => y i e.1) := by
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro w _
  rw [Fintype.sum_prod_type]
  let row (x : I → Ends n → Fin (h*b) → Bool) (i : I) (u : Selector n K h)
      (z : (packetNetwork D b s u).Assignment) : F :=
    ∏ v : (packetNetwork D b s u).Site, (packetNetwork D b s u).read (packetTables (table i) D u) z (x i) v
  have contract (x : I → Ends n → Fin (h*b) → Bool) :
      (∑ q : (u : I → Selector n K h) × ∀ i, (packetNetwork D b s (u i)).Assignment,
        cubeTermWeight table host (w,x,q)) = host w x * ∏ i, ∏ e : Vertex n,
          if x i (e,false) = x i (e,true) then 1 else 0 := by
    rw [Fintype.sum_sigma]
    change (∑ u : I → Selector n K h, ∑ z : ∀ i, (packetNetwork D b s (u i)).Assignment, host w x * ∏ i, row x i (u i) (z i)) = _
    simp_rw [← Finset.mul_sum]
    congr 1
    calc
      _ = ∑ u : I → Selector n K h, ∏ i, ∑ z, row x i (u i) z :=
        Finset.sum_congr rfl fun u _ => (Fintype.prod_sum fun i z => row x i (u i) z).symm
      _ = ∏ i, ∑ u, ∑ z, row x i u z := (Fintype.prod_sum fun i u => ∑ z, row x i u z).symm
      _ = _ := Finset.prod_congr rfl fun i _ => packet_sum (table i) (valid i) D (x i)
  simp_rw [contract]
  have common := sum_ends (I := I) (n := n) (b := b) (h := h) (Param := Unit) (fun x => C (host w x))
  have result := congrArg (eval (fun _ : Unit => (0:F))) common
  simp only [map_sum,map_mul,map_prod,eval_C,apply_ite,map_one,map_zero] at result
  exact result

end FiniteDiagonal

end BorderVNP
end Computability
end OAI
