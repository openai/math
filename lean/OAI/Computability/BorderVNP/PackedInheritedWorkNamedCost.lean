import OAI.Computability.BorderVNP.PackedInheritedWorkNamedKernel
import OAI.Computability.BorderVNP.PackedInheritedWorkNodeCost

/-! # Sparse work overhead on the named compiler's canonical histogram pins -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.SourcePath.NamedRun

open Crossing Cover Epoch Epoch.Round Shortening Shortening.Adaptive Shortening.StaticRows Shortening.PublicParallel
open Shortening.PublicEndpoints Packing Packing.Inherited Packing.Inherited.WorkWords InheritedBank NamedKernel Physical
open VPVNP.VerifierNetwork
open scoped Classical BorderVNP.Epoch.Cube
attribute [local instance] portFintype
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

universe u
variable {D m b k np : ℕ} [NeZero D] {K P : Type} [Field K] [Fintype P] {bits : P → ℕ}
variable {e : PaidIdentity K D m} {h H ν : ℝ} {src : SourcePath b e h H ν} {last high : ℕ}
variable {V E : ℕ → ℕ} {w : ℕ} {cap : ℕ → ℕ} {Extra : ℕ → Type u}
variable {keep : ∀ j, src.NamedAt last high V E w P bits k Extra j → Prop} {hk : 0<k}
variable {nodes : ∀ i : Fin b, src.Node last high V E w k i}
variable (r : src.NamedRun last high V E w cap keep hk nodes)

local notation3 "Seeds" i => Shortening.PublicDenseReceipt.Seed (src.pattern i).bins (src.asPath.depth last high (Fin.val i+1))
local notation3 "Words" j => WithWidths (src.StatePins last high V E w j) (V j) w
local notation3 "Pins" => Pin (Cube D) (fun i => (src.pattern i).bins.Bin) (src.asPath.depth last high) e.count (fun _ => w)
local notation3 "At" j => NamedState.Admissible (src.NamedGood last high V E w cap keep) j
variable (header : WorkWords.Ports np) (leaf : P ↪ Fin np)
variable (rect : ∀ i : Fin b, V (i.val+1) = siteCapacity e (k*V i.val) (Fintype.card
    (Shortening.PublicDenseReceipt.Seed (src.pattern i).bins (src.asPath.depth last high (i.val+1)))))
variable (fits : ∀ i : Fin b, V (i.val+1) ≤ 2^w)

/-- The actual scheduled geometry is shared. All additional gates are charged
to its live-capacity rectangle, the grouped ports and the seed population. -/
theorem widthSteps_cubic (i : Fin b) {R W : ℕ}
    (rows : 1+CellAddressCircuit.count (V (i.val+1)) (E (i.val+1)) (k*Parallel.nestedCapacity k np i.val) (V (i.val+1)) ≤ R)
    (seeds : Fintype.card (Seeds i) ≤ R) (width : w ≤ W) (depth : Nat.clog 2 R ≤ W) :
    (r.widthSteps header rect fits i.val i.isLt).size ≤ (nodes i).size +
      (4100+100*(2*e.count+1+birthNodes e))*R*(W+1)^3 := by
  have size : (r.widthSteps header rect fits i.val i.isLt).size = (r.widthNode header rect fits i).size :=
    scheduled_size ..
  rw [size]
  exact jointAt_cubic e (r.widthSeed i).toEmbedding (header.nested k V i.val) (rect i) (fits i)
    (nodes i) rows seeds width depth

end PackedHistoryCircuit.Normalized.SourcePath.NamedRun

end BorderVNP
end Computability
end OAI
