import OAI.Computability.BorderVNP.DiagonalEnrichedOuterReplay
import OAI.Computability.BorderVNP.DiagonalFactoryReplay
import OAI.Computability.BorderVNP.PackedHistoryNormalizedMachine

/-! # The complete cross-field tagged sum on the actual enriched geometry machine -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal.CellEntries.EnrichedOuterReplay

open Crossing Shortening Cover Epoch Epoch.Round Adaptive Packing PackedHistoryCircuit
open PackedHistoryCircuit.Normalized PackedHistoryCircuit.Normalized.EnrichedOuter PublicCapacity
open scoped BigOperators Classical BorderVNP.Epoch.Cube
open private move sum_move from OAI.Computability.BorderVNP.DiagonalFactoryReplay
attribute [local instance] portFintype

universe u

variable {D m exp start T : ℕ} [NeZero D] {K E Team Param Gadget Hidden P : Type}
  [Field K] [Field E] [Fintype Team] [Fintype Param] [Fintype P] {bits : P → ℕ}
  {e : PaidIdentity K D m} {S : Normalized.SiteSchedule e}
  {shape : ℕ → Shape} {W : ℕ → Type} [∀ j, Fintype (W j)] {V : ℕ → ℕ → Type} [∀ t j, Fintype (V t j)]
  {w : ℕ → ℕ → ℕ} {good : ∀ j, EnrichedOuter.State S start P bits shape W j → Prop}
  {deep : S.floor+1+S.drop*T ≤ start} (M : EnrichedOuter.Machine.{0,u} deep good V w)

/-- Enumerate the nested row-major team labels in this public epoch. -/
noncomputable local instance {n : ℕ} : Fintype (Port (fan S) Team n) := Replay.batchFinite (fan S) Team n

variable (y : e.Entry → E)
  (hy : ∀ f : MvPolynomial e.Entry ℤ, MvPolynomial.eval₂Hom (Int.castRingHom K) e.entry f = 0 →
    MvPolynomial.eval₂Hom (Int.castRingHom E) y f = 0)
  (pos : e.Entry → Gadget)

/-- Tag exactly the active full-state machine branches. The dormant levels use
the same empty choice type as the genuine physical geometry program. -/
noncomputable def advance (y : e.Entry → E)
    (hy : ∀ f : MvPolynomial e.Entry ℤ, MvPolynomial.eval₂Hom (Int.castRingHom K) e.entry f = 0 →
      MvPolynomial.eval₂Hom (Int.castRingHom E) y f = 0) (pos : e.Entry → Gadget) :
    Outer.Advance (Team := Team) (Param := Param) (Gadget := Gadget) (b := exp)
      (fun _ (a : Admissible good _) => a.val.pack.layout) M.epoch := by
  intro n c tagged
  let f := fun a : Admissible good (n+1) => Tracked (Port (fan S) Team (n+1)) Param Gadget exp a.val.pack.layout
  by_cases hn : n < T
  · exact move (V := f) (dite_eq_left hn : M.epoch n c = _).symm (emit (M n hn) y hy pos c tagged)
  · exact move (V := f) (dite_eq_right hn : M.epoch n c = _).symm (fun j : Empty => j.elim)

/-- Every active outer step expands the conditioned product on precisely its
actual attained inner program histograms and complete routed successor states. -/
theorem advance_sum (values : Gadget → E) (lookup : ∀ i, values (pos i) = y i) (n : ℕ) (hn : n < T)
    (c : Fin (fan S) → Admissible good n)
    (tagged : ∀ i, Tracked (Port (fan S) Team n) Param Gadget exp (c i).val.pack.layout)
    (x : Ports (width bits (fan S) (n+1))) :
    (∏ i, ((tagged i).valued values).tensor (fun p => x (i,p))) =
      ∑ q, ((advance M y hy pos n c tagged q).valued values).tensor x := by
  let f := fun a : Admissible good (n+1) => Tracked (Port (fan S) Team (n+1)) Param Gadget exp a.val.pack.layout
  let v := fun a (z : f a) => (z.valued values).tensor x
  refine (correct (M n hn) y hy pos values lookup c tagged x).trans ?_
  unfold advance
  rw [dite_eq_left hn]
  exact (sum_move (V := f) (dite_eq_left hn : M.epoch n c = _).symm (emit (M n hn) y hy pos c tagged) v).symm

variable [Fintype Hidden] (bottom : Admissible good 0)
    (base : Hidden → Tracked Team Param Gadget exp bottom.val.pack.layout)

/-- The tagged terminal for an actual accepted sequence of public histograms
and independent private inputs in the row-major physical bundle order. -/
noncomputable def terminal (q : (packHistory bottom M.epoch T).Index) (z : Fin ((fan S)^T) → Hidden) :
    Tracked (Port (fan S) Team T) Param Gadget exp ((packHistory bottom M.epoch T).term q).val.pack.layout :=
  Outer.term (fun _ (a : Admissible good _) => a.val.pack.layout) bottom M.epoch base (advance M y hy pos) T z q

/-- Sum of the actual returned conditioned tensors over the enriched geometry
histories and the hidden bundle assignments. The reference field and enriched
machine can be fixed before choosing the specialized field of this evaluation. -/
theorem terminal_sum (values : Gadget → E) (lookup : ∀ i, values (pos i) = y i)
    (x : Ports (fun q : Fin ((fan S)^T) × P => bits q.2)) :
    (∏ i, ∑ z : Hidden, ((base z).valued values).tensor (fun p => x (i,p))) =
      ∑ q, ∑ z, ((terminal M y hy pos bottom base q z).flat.valued values).tensor x :=
  Outer.sum_private_and_public (fun _ (a : Admissible good _) => a.val.pack.layout) bottom M.epoch base
    (advance M y hy pos) values T (advance_sum M y hy pos values lookup) T le_rfl x

end Diagonal.CellEntries.EnrichedOuterReplay

end BorderVNP
end Computability
end OAI
