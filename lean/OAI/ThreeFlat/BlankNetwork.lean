import OAI.ThreeFlat.RAM.ContractionMemory

namespace OAI
/-! # Seed memory outside the cell records -/

namespace ThreeFlat.BitNetwork

open Computability.VPVNP.BurstRAM
open RAM RAM.BitLayout

variable {F : Type*} {w p : ℕ}

/-- A seed with the same number of pins, hidden bits, and output rows as
the desired network. Its rows require no template or private data. -/
def blankNetwork [Zero F] (pins hidden count : ℕ) : BitNetwork F pins where
  internal := hidden
  cells := count
  source _ _ := .constant false
  table _ _ := 0

/-- Every address below the cell region stores a literal, pin bit or hidden bit. -/
theorem source_covers {k p h : ℕ} (hk : k < cellsBase p h) :
    ∃ s : BitSource h p, sourceAddress s = k := by
  by_cases lit : k < 2
  · rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl
    · exact ⟨.constant false, rfl⟩
    · exact ⟨.constant true, rfl⟩
  by_cases pin : k < hiddenBase p
  · unfold hiddenBase at pin
    exact ⟨.pin ⟨k-2, by omega⟩, by change 2 + (k-2) = k; omega⟩
  · unfold cellsBase at hk
    exact ⟨.hidden ⟨k-hiddenBase p, by omega⟩, by change hiddenBase p + (k-hiddenBase p) = k; omega⟩

/-- The initial network and desired network have identical bounded memory
outside the cell array when supplied with the same pin and hidden bits. -/
theorem blankNetwork_read [Fintype F] [Semiring F] (N : BitNetwork F p)
    (code : FieldCode F w) (pin : Fin p → Bool) (hidden : Fin N.internal → Bool)
    (k : ℕ) (hk : k < footprint N)
    (away : k < cellsBase p N.internal ∨ mulBase p N.internal N.cells ≤ k) :
    memory (blankNetwork p N.internal N.cells) code pin hidden k = memory N code pin hidden k := by
  rcases away with before | past
  · obtain ⟨s,rfl⟩ := source_covers before
    exact (read_source (blankNetwork p N.internal N.cells) code pin hidden s).trans
      (read_source N code pin hidden s).symm
  · let b := mulBase p N.internal N.cells
    let f := Fintype.equivFin F
    have lo : b ≤ k := past
    have hi : k < b+Fintype.card F*Fintype.card F := hk
    let z : Fin (Fintype.card F*Fintype.card F) := ⟨k-b, by omega⟩
    let ij := finProdFinEquiv.symm z
    have idx : ij.2.val + Fintype.card F*ij.1.val = k-b :=
      congrArg Fin.val (finProdFinEquiv.apply_symm_apply z)
    have addr : b+Fintype.card F*(f (f.symm ij.1)).val+(f (f.symm ij.2)).val = k := by
      simp only [Equiv.apply_symm_apply]
      omega
    rw [← addr]
    exact (read_product (blankNetwork p N.internal N.cells) code pin hidden (f.symm ij.1) (f.symm ij.2)).trans
      (read_product N code pin hidden (f.symm ij.1) (f.symm ij.2)).symm

end ThreeFlat.BitNetwork

end OAI
