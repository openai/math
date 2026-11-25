import OAI.Computability.BorderVNP.DiagonalSpecializedDenseSiteEpoch
import OAI.Computability.BorderVNP.DiagonalFactoryReplay
import OAI.Computability.BorderVNP.PackedDenseFactory

/-! # Replay over all outer epochs of the sorted physical factory

The dense programs and their reference-field geometry are fixed before the scalar
specialization. Local expansions use the stored sorted cable order. The outer replay
then sums precisely the factory's public histories and the independent hidden
choices of all its bottom bundles.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal.CellEntries.DenseTerminal

open Crossing Shortening Adaptive Packing Packing.PhysicalEpochs Epoch Epoch.Round Cover
open scoped BigOperators Classical BorderVNP.Epoch.Cube
attribute [local instance] portFintype

variable {D m exp : ℕ} [NeZero D] {K E P Team Param Gadget Hidden : Type}
  [Field K] [Field E] [Fintype P] [Fintype Team] [Fintype Param]
  {bits : P → ℕ} {e : PaidIdentity K D m} {S : PackedHistoryCircuit.Normalized.SiteSchedule e}
  (program : Factory.Dense.Programs S)


variable {start T : ℕ} (deep : (Factory.ofDenseSchedule program).floor+1+(Factory.ofDenseSchedule program).drop*T ≤ start)

/-- The particular dense site execution underlying this active factory node. -/
noncomputable abbrev execution {t : ℕ} (ht : t < T) (child : Fin (Factory.ofDenseSchedule program).fan → (Factory.ofDenseSchedule program).State bits start t) :=
  program.run ((Factory.ofDenseSchedule program).depth start (t+1)-1) ((Factory.ofDenseSchedule program).levels deep ht).1
    (Port (Factory.ofDenseSchedule program).fan P t) (width bits (Factory.ofDenseSchedule program).fan t) (fun i => (child i).pack)
    (fun i => reindexRoutes ((Factory.ofDenseSchedule program).levels deep ht).2.2.symm (child i).route)

/-- Enumerate the team ports at epoch `n` by child indices and then by the original team. -/
noncomputable local instance {n : ℕ} : Fintype (Port (Factory.ofDenseSchedule program).fan Team n) := Replay.batchFinite (Factory.ofDenseSchedule program).fan Team n

variable (y : e.Entry → E)
    (hy : ∀ f : MvPolynomial e.Entry ℤ, MvPolynomial.eval₂Hom (Int.castRingHom K) e.entry f = 0 →
      MvPolynomial.eval₂Hom (Int.castRingHom E) y f = 0)
    (pos : e.Entry → Gadget)

/-- The tagged summands are taken from the original factory node's finite output
ordinal, using the chosen dense saved rows for every internal shortening step. -/
noncomputable def emit (y : e.Entry → E)
    (hy : ∀ f : MvPolynomial e.Entry ℤ, MvPolynomial.eval₂Hom (Int.castRingHom K) e.entry f = 0 →
      MvPolynomial.eval₂Hom (Int.castRingHom E) y f = 0) (pos : e.Entry → Gadget) :
    FactoryReplay.Emit (Team := Team) (Param := Param) (Gadget := Gadget) (exp := exp) (bits := bits) (Factory.ofDenseSchedule program) deep :=
  by
    intro t ht child tagged j
    letI : Fintype (Port (Factory.ofDenseSchedule program).fan P t) := portFintype
    exact DenseSiteReplay.term (execution program deep ht child) y hy pos tagged j

/-- Local arithmetic replay on the same finite output indices as the factory's
width and site concentration estimates. -/
theorem correct (values : Gadget → E) (lookup : ∀ i, values (pos i) = y i)
    (t : ℕ) (ht : t < T) (child : Fin (Factory.ofDenseSchedule program).fan → (Factory.ofDenseSchedule program).State bits start t)
    (tagged : ∀ i, Tracked (Port (Factory.ofDenseSchedule program).fan Team t) Param Gadget exp (child i).pack.layout)
    (x : Ports (width bits (Factory.ofDenseSchedule program).fan (t+1))) :
    (∏ i, ((tagged i).valued values).tensor (fun p => x (i,p))) =
      ∑ j, ((emit program deep y hy pos t ht child tagged j).valued values).tensor x := by
  let : Fintype (Port (Factory.ofDenseSchedule program).fan P t) := portFintype
  exact DenseSiteReplay.sum_terms (execution program deep ht child) y hy pos tagged values lookup x

variable [Fintype Hidden] (bottom : (Factory.ofDenseSchedule program).State bits start 0)
    (base : Hidden → Tracked Team Param Gadget exp bottom.pack.layout)

/-- Conditioned parameter polynomial and unary positions on the complete actual
outer history, with its specified independent bottom assignments. -/
noncomputable def terminal (q : ((Factory.ofDenseSchedule program).histories deep bottom T).Index) (z : Fin ((Factory.ofDenseSchedule program).fan^T) → Hidden) :
    Tracked (Port (Factory.ofDenseSchedule program).fan Team T) Param Gadget exp (((Factory.ofDenseSchedule program).histories deep bottom T).term q).pack.layout :=
  FactoryReplay.terminal (Factory.ofDenseSchedule program) deep (emit program deep y hy pos) bottom base q z

/-- The product of the bottom polynomial sums is the full sum over the reference
factory's actual terminal histories and all independent bottom choices, interpreted
in the scalar field of this branch. -/
theorem terminal_sum (values : Gadget → E) (lookup : ∀ i, values (pos i) = y i)
    (x : Ports (fun q : Fin ((Factory.ofDenseSchedule program).fan^T) × P => bits q.2)) :
    (∏ i, ∑ z : Hidden, ((base z).valued values).tensor (fun p => x (i,p))) =
      ∑ q, ∑ z, ((terminal program deep y hy pos bottom base q z).flat.valued values).tensor x :=
  FactoryReplay.terminal_sum (Factory.ofDenseSchedule program) deep (emit program deep y hy pos) values
    (correct program deep y hy pos values lookup) bottom base x

end Diagonal.CellEntries.DenseTerminal

end BorderVNP
end Computability
end OAI
