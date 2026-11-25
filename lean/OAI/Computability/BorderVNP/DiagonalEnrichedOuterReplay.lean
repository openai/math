import OAI.Computability.BorderVNP.DiagonalEnrichedDenseSiteReplay
import OAI.Computability.BorderVNP.PackedHistoryNormalizedOuter

/-! # Tagged local replay on a full assigned outer geometry state -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal.CellEntries.EnrichedOuterReplay

open Crossing Shortening Cover Epoch Epoch.Round Adaptive Packing PackedHistoryCircuit
open PackedHistoryCircuit.Normalized PackedHistoryCircuit.Normalized.EnrichedOuter PublicCapacity
open scoped BigOperators Classical BorderVNP.Epoch.Cube
attribute [local instance] portFintype

universe u

variable {D m exp start T t : ℕ} [NeZero D] {K E Team Param Gadget P : Type}
  [Field K] [Field E] [Fintype Team] [Fintype Param] [Fintype P] {bits : P → ℕ}
  {e : PaidIdentity K D m} {S : Normalized.SiteSchedule e}
  {shape : ℕ → Shape} {W V : ℕ → Type} [∀ j, Fintype (W j)] [∀ j, Fintype (V j)]
  {w : ℕ → ℕ} {good : ∀ j, EnrichedOuter.State S start P bits shape W j → Prop}
  {deep : S.floor+1+S.drop*T ≤ start} {ht : t < T}
  (M : EnrichedOuter.Epoch.{u} deep ht good V w)

/-- Enumerate the nested row-major team labels in this public epoch. -/
noncomputable local instance {n : ℕ} : Fintype (Port (fan S) Team n) := Replay.batchFinite (fan S) Team n

variable (y : e.Entry → E)
  (hy : ∀ f : MvPolynomial e.Entry ℤ, MvPolynomial.eval₂Hom (Int.castRingHom K) e.entry f = 0 →
    MvPolynomial.eval₂Hom (Int.castRingHom E) y f = 0)
  (pos : e.Entry → Gadget)

/-- Attach specialized factors to the very branch whose pin array, record directory
and histogram the installed public circuit returns. -/
noncomputable def emit (c : Fin (fan S) → Admissible good t)
    (tags : ∀ i, Tracked (Port (fan S) Team t) Param Gadget exp (c i).val.pack.layout)
    (q : (M.choice c).Index) :
    Tracked (Port (fan S) Team (t+1)) Param Gadget exp ((M.choice c).term q).val.pack.layout := by
  letI : Fintype (Port (fan S) P t) := portFintype
  exact EnrichedSiteReplay.term (M.run c) M.saveNames y hy pos tags q

/-- The product identity for this genuine compiled epoch, on its complete input states
and the exact local output indices of the outer public system. -/
theorem correct (values : Gadget → E) (lookup : ∀ i, values (pos i) = y i)
    (c : Fin (fan S) → Admissible good t)
    (tags : ∀ i, Tracked (Port (fan S) Team t) Param Gadget exp (c i).val.pack.layout)
    (x : Ports (width bits (fan S) (t+1))) :
    (∏ i, ((tags i).valued values).tensor (fun p => x (i,p))) =
      ∑ q, ((emit M y hy pos c tags q).valued values).tensor x := by
  let : Fintype (Port (fan S) P t) := portFintype
  exact EnrichedSiteReplay.sum_terms (M.run c) M.saveNames y hy pos tags values lookup x

end Diagonal.CellEntries.EnrichedOuterReplay

end BorderVNP
end Computability
end OAI
