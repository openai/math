import OAI.Computability.BorderVNP.DiagonalCubeNetwork

/-! # Simultaneous replacement of antipodal packets

Each packet receives its own selector and internal cube cable words. Summing
over these choices enforces equality of its two original endpoint words.
All singleton bits and the tagged host factors are retained throughout.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube

open Crossing Diagonal.CellEntries MvPolynomial
open scoped BigOperators Classical

variable {I Sing Param Gadget E : Type*} {n b h K s : ℕ}

private abbrev EndpointWords (I : Type*) (n w : ℕ) := I → Ports (fun _ : Ends n => w)

private def commonEnds (y : I → Vertex n → Fin (h*b) → Bool) : EndpointWords I n (h*b) :=
  fun i p => y i p.1

/-- The tagged global product records the host and the multiplicities of every
gadget position selected by every packet. A failed host check propagates zero. -/
noncomputable def globalEntry [Fintype I] (pos : I → TableEntry n b h K s → Gadget) (D : ℕ)
    (host : (Sing → Bool) → (I → Ports (fun _ : Ends n => h*b)) → Entry Param Gadget)
    (w : Sing → Bool) (x : I → Ports (fun _ : Ends n => h*b)) (u : I → Selector n K h)
    (z : ∀ i, (packetNetwork D b s (u i)).Assignment) : Entry Param Gadget :=
  host w x * ∏ i, assignmentEntry (packetNetwork D b s (u i))
    (packetTables (fun p => gadget (Param := Param) (pos i p)) D (u i)) (z i) (x i)

variable [Fintype I] [CommRing E]

private theorem sum_internal (pos : I → TableEntry n b h K s → Gadget) (values : Gadget → E)
    (ht : ∀ i, ValidTables (values ∘ pos i)) (D : ℕ)
    (host : (Sing → Bool) → EndpointWords I n (h*b) → Entry Param Gadget)
    (w : Sing → Bool) (x : EndpointWords I n (h*b)) :
    (∑ u : I → Selector n K h, ∑ z : ∀ i, (packetNetwork D b s (u i)).Assignment,
      interpret values (globalEntry pos D host w x u z)) =
      interpret values (host w x) * ∏ i, ∏ e : Vertex n, if x i (e,false) = x i (e,true) then 1 else 0 := by
  let f (i : I) (u : Selector n K h) (z : (packetNetwork D b s u).Assignment) :=
    interpret values (assignmentEntry (packetNetwork D b s u)
      (packetTables (fun p => gadget (Param := Param) (pos i p)) D u) z (x i))
  simp only [globalEntry, map_mul, map_prod]
  change (∑ u : I → Selector n K h, ∑ z : ∀ i, (packetNetwork D b s (u i)).Assignment,
    interpret values (host w x) * ∏ i, f i (u i) (z i)) = _
  simp_rw [← Finset.mul_sum]
  congr 1
  calc
    _ = ∑ u : I → Selector n K h, ∏ i, ∑ z, f i (u i) z :=
      Finset.sum_congr rfl fun u _ => (Fintype.prod_sum (fun i z => f i (u i) z)).symm
    _ = ∏ i, ∑ u, ∑ z, f i u z := (Fintype.prod_sum (fun i u => ∑ z, f i u z)).symm
    _ = _ := Finset.prod_congr rfl fun i _ => packet_sum_tagged (pos i) values (ht i) D (x i)

private theorem sum_ends (host : EndpointWords I n (h*b) → MvPolynomial Param E) :
    (∑ x, host x * ∏ i, ∏ e : Vertex n, if x i (e,false) = x i (e,true) then 1 else 0) =
    ∑ y : I → Vertex n → Fin (h*b) → Bool, host (commonEnds y) := by
  symm
  apply Fintype.sum_of_injective commonEnds
  · intro a b hab
    funext i e
    exact congrFun (congrFun hab i) (e, false)
  · intro x hx
    have hd : ¬∀ i e, x i (e,false) = x i (e,true) := by
      intro hh
      apply hx
      refine ⟨fun i e => x i (e,false), ?_⟩
      funext i ⟨e,j⟩
      cases j with
      | false => rfl
      | true => exact hh i e
    push Not at hd
    obtain ⟨i,e,he⟩ := hd
    apply mul_eq_zero_of_right
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    apply Finset.prod_eq_zero (Finset.mem_univ e)
    simp [he]
  · intro y
    simp [commonEnds]

variable [Fintype Sing]

/-- The full sum over all packet selectors, internal cube assignments and
independent endpoint words equals the old sum with a single word per wire. -/
theorem packet_global_expansion (pos : I → TableEntry n b h K s → Gadget) (values : Gadget → E)
    (ht : ∀ i, ValidTables (values ∘ pos i)) (D : ℕ)
    (host : (Sing → Bool) → (I → Ports (fun _ : Ends n => h*b)) → Entry Param Gadget) :
    (∑ w, ∑ x, ∑ u : I → Selector n K h, ∑ z : ∀ i, (packetNetwork D b s (u i)).Assignment,
      interpret values (globalEntry pos D host w x u z)) =
    ∑ w, ∑ y : I → Vertex n → Fin (h*b) → Bool, interpret values (host w (fun i p => y i p.1)) := by
  apply Finset.sum_congr rfl
  intro w _
  simp_rw [sum_internal pos values ht D host w]
  exact sum_ends (fun x => interpret values (host w x))

/-- Reject failing global records before interpretation. Passing records whose
scalar values happen to vanish remain in the sum with their gadget counts. -/
theorem packet_global_expansion_passing (pos : I → TableEntry n b h K s → Gadget) (values : Gadget → E)
    (ht : ∀ i, ValidTables (values ∘ pos i)) (D : ℕ)
    (host : (Sing → Bool) → (I → Ports (fun _ : Ends n => h*b)) → Entry Param Gadget) :
    (∑ w, ∑ x, ∑ u : I → Selector n K h,
      ∑ z ∈ Finset.univ.filter (fun z => globalEntry pos D host w x u z ≠ 0),
        interpret values (globalEntry pos D host w x u z)) =
    ∑ w, ∑ y : I → Vertex n → Fin (h*b) → Bool, interpret values (host w (fun i p => y i p.1)) := by
  rw [← packet_global_expansion pos values ht D host]
  refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun u _ => ?_
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro z _ hz
  have h : globalEntry pos D host w x u z = 0 := by simpa using hz
  rw [h, map_zero]

end Cube

end BorderVNP
end Computability
end OAI
