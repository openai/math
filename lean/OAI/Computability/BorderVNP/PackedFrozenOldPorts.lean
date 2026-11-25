import OAI.Computability.BorderVNP.PackedInheritedWorkPortPath

/-! # Grouped port pointers on the actual parallel source, before shortening -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.WorkWords

open Cover Crossing Shortening Shortening.PublicParallel PackedHistoryCircuit.Normalized
open scoped Classical

variable {D k V np lev w : ℕ} {P I K : Type} [Fintype I] {bits : P → ℕ}
    (children : Fin k → PlacedPack D P bits K I lev) (sites : ∀ j,(children j).pack.layout.Site ↪ Fin V)
    (port : P ↪ Fin np) (header : Ports np)

/-- Every original argument occupies its fixed parallel port slot. Its physical
host is the child's host displaced by the full child site rectangle. -/
theorem Ports.raw_parallel (old : ∀ j,header.Reads (children j).pack.layout (sites j) port)
    (width : (PortTable.mk np port header).Widths bits w) :
    (header.parallel k V).Reads (raw children).layout (parallelName sites) (Parallel.portRows k port) := by
  have full := width.parallel k V
  refine ⟨?_,full.live,full.holes⟩
  rintro ⟨j,p⟩
  change (finProdFinEquiv.symm (finProdFinEquiv (j,port p))).1.val*V+
    header.host (finProdFinEquiv.symm (finProdFinEquiv (j,port p))).2 =
      (parallelName sites ⟨j,(children j).pack.layout.attach p⟩).val
  rw [finProdFinEquiv.symm_apply_apply,(old j).attach]
  change _+_ = _+V*j.val
  ac_rfl

end Packing.Inherited.WorkWords

end BorderVNP
end Computability
end OAI
