import OAI.Computability.VPVNP.MotifPayloadIdentity

/-!
# The repeated motif identity as an ordinary sum over total widths

After copying a fixed base identity, choices of its summands form selector
lists. The supply edge payloads are grouped by their total width vector.
The selector and validity checks in the local maps count each admissible
list exactly once, as required by Theorem 6.1.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace MotifSelector

open WireTensor

variable {J E S R : Type*} [Fintype J] [Nonempty J] [Fintype E] [Fintype S] [CommSemiring R]
variable {C : J → Type*} (G : Supply J E) (w : S → E → ℕ)
variable (L : ∀ s j, C j → Half G (fun e => Word (w s e)) j → R)
variable {u bits : ℕ} (code : S ↪ Word bits)

open scoped Classical in
/-- The contribution of one selected base map after contracting its supply wires. -/
noncomputable def baseTerm (s : S) (d : ∀ j, C j) : R :=
  ∑ y : ∀ e, Word (w s e), ∏ j, L s j (d j) (edgeAssignment G.src G.dst y j)

open scoped Classical in
private theorem sum_decoded_tags (v : E → ℕ) (c : ∀ j, Fin u → C j) :
    (∑ t : Fin u → Word bits, ∑ y : ∀ e, Word (v e),
        ∏ j, evalIndices L j (tagIndices G w code v t j (c j) (edgeAssignment G.src G.dst y j))) =
      ∑ θ : Fin u → S, ∑ y : ∀ e, Word (v e),
        ∏ j, evalIndices L j (payloadIndices G w v θ j (c j) (edgeAssignment G.src G.dst y j)) := by
  classical
  let e := sequenceCode code u
  let F (θ : Fin u → S) := ∑ y : ∀ i, Word (v i),
    ∏ j, evalIndices L j (payloadIndices G w v θ j (c j) (edgeAssignment G.src G.dst y j))
  let T (t : Fin u → Word bits) := ∑ y : ∀ i, Word (v i),
    ∏ j, evalIndices L j (tagIndices G w code v t j (c j) (edgeAssignment G.src G.dst y j))
  have valid (θ : Fin u → S) : T (e θ) = F θ := by
    simp [T, F, tagIndices, e]
  have invalid (t : Fin u → Word bits) (h : t ∉ Set.range e) : T t = 0 := by
    change ¬ ∃ θ, sequenceCode code u θ = t at h
    simp [T, tagIndices, h, evalIndices]
  change ∑ t, T t = ∑ θ, F θ
  symm
  apply Finset.sum_bij_ne_zero (fun θ _ _ => e θ) (fun _ _ _ => Finset.mem_univ _)
    (fun _ _ _ _ _ _ h => e.injective h) _ (fun θ _ _ => (valid θ).symm)
  intro t _ ht
  obtain ⟨θ, rfl⟩ : t ∈ Set.range e := by
    by_contra h
    exact ht (invalid t h)
  exact ⟨θ, Finset.mem_univ _, (valid θ) ▸ ht, rfl⟩

open scoped Classical in
private theorem sum_grouped_fields (v : E → ℕ) (c : ∀ j, Fin u → C j) :
    (∑ x : ∀ e, Word (v e + u * bits),
      ∏ j, groupedMap G w L code v j (c j) (edgeAssignment G.src G.dst x j)) =
      ∑ θ : Fin u → S, ∑ y : ∀ e, Word (v e),
        ∏ j, evalIndices L j (payloadIndices G w v θ j (c j) (edgeAssignment G.src G.dst y j)) := by
  classical
  let F (t : Fin u → Word bits) (j : J) (d : Fin u → C j) (y : Half G (fun e => Word (v e)) j) :=
    evalIndices L j (tagIndices G w code v t j d y)
  let eqv := Equiv.piCongrRight (fun e => wireFields u bits (v e))
  have eqterm (z : ∀ e, (Fin u → Word bits) × Word (v e)) (j : J) :
      groupedMap G w L code v j (c j) (edgeAssignment G.src G.dst (eqv.symm z) j) =
        selectedMap G F j (c j) (edgeAssignment G.src G.dst z j) := by
    have he : (fun e => wireFields u bits (v e) (eqv.symm z e)) = z := eqv.apply_symm_apply z
    simp only [groupedMap, groupedIndices, mapHalf_edgeAssignment, he, selectedMap]
    split <;> rfl
  rw [← eqv.symm.sum_comp,
    Fintype.sum_congr _ _ (fun z => Finset.prod_congr rfl (fun j _ => eqterm z j))]
  have h := congrFun (applyLocal_selectedMap G F) c
  rw [Finset.sum_apply] at h
  erw [applyLocal_wireNetwork G.src G.dst _ (selectedMap G F) c] at h
  have he (t : Fin u → Word bits) := applyLocal_wireNetwork G.src G.dst _ (F t) c
  simp_rw [he] at h
  exact h.trans (sum_decoded_tags G w L code v c)

open scoped Classical in
/-- Each compressed term counts precisely the lists with its total width vector. -/
theorem groupedMap_contraction (v : E → ℕ) (c : ∀ j, Fin u → C j) :
    applyLocal (B := (wireNetwork (k := R) G.src G.dst (fun e => Word (v e + u*bits))).Basis)
      (groupedMap G w L code v) (wireNetwork G.src G.dst (fun e => Word (v e + u*bits))).coeff c =
      ∑ θ : Fin u → S, if v = totalWidth w θ then
        ∏ i, baseTerm G w L (θ i) (fun j => c j i) else 0 := by
  classical
  erw [applyLocal_wireNetwork G.src G.dst _ (groupedMap G w L code v) c]
  rw [sum_grouped_fields G w L code v c]
  exact Finset.sum_congr rfl fun θ _ => sum_payload_indices G w L v θ c

open scoped Classical in
/-- The repeated ordinary sum, grouped by admitted total payload widths.
Every successful selector list has exactly one outer index. -/
theorem power_expansion (admitted : Finset (E → ℕ))
    (cover : ∀ θ : Fin u → S, totalWidth w θ ∈ admitted)
    (c : ∀ j, Fin u → C j) :
    (∏ i, ∑ s, baseTerm G w L s (fun j => c j i)) =
      ∑ v ∈ admitted, applyLocal
        (B := (wireNetwork (k := R) G.src G.dst (fun e => Word (v e + u*bits))).Basis)
        (groupedMap G w L code v)
        (wireNetwork G.src G.dst (fun e => Word (v e + u*bits))).coeff c := by
  classical
  simp_rw [groupedMap_contraction G w L code _ c]
  rw [Fintype.prod_sum, Finset.sum_comm]
  exact Finset.sum_congr rfl fun θ _ => by simp [cover θ]

end MotifSelector

end VPVNP
end Computability
end OAI
