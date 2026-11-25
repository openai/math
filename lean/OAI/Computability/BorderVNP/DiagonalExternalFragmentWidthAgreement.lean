import OAI.Computability.BorderVNP.DiagonalExternalFragmentCommonRows

/-! # The same native pair-width column at every original team -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.NativeIntervals

open Crossing Physical
open private pairCode_eq from OAI.Computability.BorderVNP.CubeDirectedIntervalPhysical

/-- Each numeric word of the full native width rectangle is the address
of a true pair of product labels, including the zero-width bins. -/
theorem product_pair_exists {dim d z k : ℕ} (hz : d^(dim+1)=z) (hk : k<z^2) :
    ∃ u, pairCode (productCode dim d z hz) u = k := by
  let key : Fin (z*z) := ⟨k,by rwa [←pow_two]⟩
  let p : Fin z × Fin z := finProdFinEquiv.symm key
  let code : Label (dim+1) d ≃ Fin z := finFunctionFinEquiv.trans (finCongr hz)
  refine ⟨(code.symm p.1, code.symm p.2),?_⟩
  rw [pairCode_eq]
  change (finProdFinEquiv (code (code.symm p.1),code (code.symm p.2))).val = k
  rw [Equiv.apply_symm_apply,Equiv.apply_symm_apply]
  exact congrArg Fin.val (finProdFinEquiv.apply_symm_apply key)

/-- Two native scans with the same physical edge ranks and labels agree
throughout the complete numeric width array, even when their intermediate
memories and sparse row directories differ. -/
theorem PhysicalRows.same_widths {D M dim d : ℕ} {P : Type*} {bits : P → ℕ} {Cell : Type}
    {N : Network D P bits} {cell : N.Site → Cell} {l : Layout} {ord : N.CrossingEdge cell ≃ Fin M}
    {r s : Fin M ↪o Fin l.count} {ca cb : Cell ↪ ℕ} {label : Cell → Label (dim+1) d}
    {hz : d^(dim+1)=l.alphabet} {before before' after after' : ℕ → ℕ}
    (a : PhysicalRows N cell l before ord r ca label (productCode dim d l.alphabet hz))
    (b : PhysicalRows N cell l before' ord s cb label (productCode dim d l.alphabet hz))
    (im : l.Image before l.count after) (im' : l.Image before' l.count after')
    (k : ℕ) (hk : k<l.alphabet^2) : after (l.widths+k) = after' (l.widths+k) := by
  obtain ⟨u,rfl⟩ := product_pair_exists hz hk
  exact (a.image_load im u).trans (b.image_load im' u).symm

end Cube.NativeIntervals

end BorderVNP
end Computability
end OAI
