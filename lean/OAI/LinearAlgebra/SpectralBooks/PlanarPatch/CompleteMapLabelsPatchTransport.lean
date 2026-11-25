import OAI.LinearAlgebra.SpectralBooks.PlanarPatch.PlanarPatchCertificates

/-! # Round priorities under injective vertex naming -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace PlanarPatch

variable {V : Type*} [DecidableEq V] (key : V ↪ ℕ)

omit [DecidableEq V] in
theorem nameList_map (P : Finset V) :
    nameList (Function.Embedding.refl ℕ) (P.map key) = nameList key P := by
  simp [nameList]

omit [DecidableEq V] in
theorem leastName_map (P : Finset V) :
    leastName (Function.Embedding.refl ℕ) (P.map key) = leastName key P := by
  classical
  by_cases h : P.Nonempty
  · simp [leastName,h,h.map]
  · simp [Finset.not_nonempty_iff_eq_empty.mp h, leastName]

theorem mem_selected_map_iff {C : Finset (Finset V)} {P : Finset V} :
    P.map key ∈ selected (Function.Embedding.refl ℕ) (C.image (Finset.map key)) ↔
      P ∈ selected key C := by
  have hmem {Q : Finset V} : Q.map key ∈ C.image (Finset.map key) ↔ Q ∈ C := by
    rw [Finset.mem_image]
    exact ⟨fun ⟨w,hw,h⟩ => Finset.map_injective key h ▸ hw, fun h => ⟨_,h,rfl⟩⟩
  rw [mem_selected,mem_selected,hmem]
  apply and_congr_right
  intro _
  constructor
  · intro h Q hQ hd
    simpa only [nameList_map] using h (Q.map key) (hmem.mpr hQ)
      (fun hd' => hd ((Finset.disjoint_map key).mp hd'))
  · intro h Q hQ hd
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hQ
    simpa only [nameList_map] using h q hq (fun hd' => hd ((Finset.disjoint_map key).mpr hd'))

end PlanarPatch

end SpectralBooks
end LinearAlgebra
end OAI
