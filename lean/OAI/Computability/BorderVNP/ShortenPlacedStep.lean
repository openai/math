import OAI.Computability.BorderVNP.ShortenPhysicalRows
import OAI.Computability.BorderVNP.PackedProfiles

/-!
# Placed packs and one physical node of an epoch

A node combines the concrete valued networks of its children. Its selector
histogram indexes the output and its measured coordinates are evaluated
from the same quotient placements and edge widths used to prove the two
shortening estimates. Input midpoints may be specified by the geodesic
subdivision, and new midpoints are chosen on the sewn quotient segments.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Shortening

open Cover Crossing Epoch Packing CombiningStep Finset
open scoped Classical

/-- A pack at a specified cover level with its actual quotient sites, public
charge mask, and midpoints for the tile population. -/
structure PlacedPack (D : ℕ) (P : Type) (bits : P → ℕ) (K : Type*) (I : Type) [Fintype I] (d : ℕ) where
  /-- The physical layout and its local coefficient tables. -/
  pack : Pack D P bits K
  /-- Quotient sites occupied by its vertices. -/
  site : pack.layout.Site → SurfaceHost I (d+1)
  /-- All designated charged edges, including coincident ones. -/
  charged : pack.layout.Edge → Bool
  /-- The chosen midpoint of each cable. -/
  midpoint : pack.layout.Edge → SurfaceHost I (d+1)

variable {D m d d' k : ℕ} {P : Type} {bits : P → ℕ} {K : Type*} {I : Type} [Fintype I]

namespace PlacedPack

variable (p : PlacedPack D P bits K I d)

/-- Unnormalized total charged length W. -/
noncomputable def length : ℝ := chargedLength p.pack.layout p.site p.charged

/-- Only positive-length charged edges contribute to the population of
the tile of their chosen midpoint. -/
def occupies (t : I → Deck (d+1)) (c : p.pack.layout.Edge) : Prop :=
  p.charged c = true ∧ p.site (p.pack.layout.src c) ≠ p.site (p.pack.layout.dst c) ∧
    productTileName d (p.midpoint c) = t

/-- The unnormalized intermediate concentration X of this pack. -/
noncomputable def concentration : ℝ := tileNorm fun t => testedWidth p.pack.layout.width (p.occupies t)

/-- Both measured quantities are nonnegative on every actual branch. -/
theorem nonneg : 0 ≤ p.length ∧ 0 ≤ p.concentration := by
  refine ⟨sum_nonneg fun c _ => ?_,mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)⟩
  split_ifs <;> positivity

end PlacedPack

variable [NeZero D] [Field K] {B : Type} [Fintype B]

/-- An actual combining operation on the disjoint union of the child packs.
Its data may depend on all the previously selected public histories. -/
structure PlacedStep (m : ℕ) (B : Type) [Fintype B] (d' : ℕ) (child : Fin k → PlacedPack D P bits K I d) where
  /-- Measured bin tag of each cable after moving the disjoint children. -/
  bin : (parallelPacks (fun i => (child i).pack)).layout.Edge → Option ((I → Deck (d'+1)) × B)
  /-- Signed direction permutations used by the pool allocation. -/
  perm : Fin D → Equiv.Perm ((I → Deck (d'+1)) × B)
  /-- The carried orientation of each cable in this union. -/
  positive : (parallelPacks (fun i => (child i).pack)).layout.Edge → Bool
  /-- Input placements after the chosen motions and the new seed charts. -/
  placed : Placement (m := m) (parallelPacks fun i => (child i).pack) bin perm I (SurfaceHost I (d'+1))

namespace PlacedStep

variable {child : Fin k → PlacedPack D P bits K I d} (s : PlacedStep m B d' child)
variable (e : PaidIdentity K D m)

/-- This operation's attained joint histogram indices. -/
abbrev Index := Counts e (parallelPacks fun i => (child i).pack) s.bin s.perm

/-- The measured pack of a public output histogram. -/
noncomputable def result (q : s.Index e) : PlacedPack D (Fin k × P) (fun z => bits z.2) K I d' where
  pack := output e _ s.bin s.perm s.positive (0,false) q
  site := s.placed.postSites _ s.bin s.perm e s.positive q
  charged := postMask _ s.bin s.perm e s.positive q
  midpoint := s.placed.outputMidpoint _ s.bin s.perm e s.positive q

/-- The measured length agrees with the first physical row's coordinate. -/
theorem length_result (q : s.Index e) : (s.result e q).length =
    s.placed.result e _ s.bin s.perm s.positive q := rfl

set_option maxHeartbeats 1200000 in
/-- The midpoint concentration agrees with the second physical row's coordinate. -/
theorem concentration_result (q : s.Index e) : (s.result e q).concentration =
    s.placed.outputConcentration _ s.bin s.perm e s.positive q := rfl

set_option maxHeartbeats 1200000 in
/-- Summing these very same measured output packs preserves the arbitrary
tensor of the disjoint input children, with arbitrary outside connections. -/
theorem tensor_sum (x : Ports fun z : Fin k × P => bits z.2) :
    (parallelPacks (fun i => (child i).pack)).tensor x =
      ∑ q : s.Index e, (s.result e q).pack.tensor x :=
  by
    refine (exact_sum e _ s.bin s.perm s.positive (0,false) x).trans ?_
    apply Finset.sum_congr _ (fun _ _ => rfl)
    ext q
    simp

/-- Geometric conservation for each oriented child cable. Motion may discard
a charge tag on a coincident cable, whose contribution to length is zero. -/
def KeepsLength : Prop :=
  ∀ i (c : (child i).pack.layout.Edge),
    (if (s.bin ⟨i,c⟩).isSome then
      dist (s.placed.old ⟨i,(child i).pack.layout.src c⟩) (s.placed.old ⟨i,(child i).pack.layout.dst c⟩)
    else 0) = (if (child i).charged c then dist ((child i).site ((child i).pack.layout.src c))
      ((child i).site ((child i).pack.layout.dst c)) else 0)

omit [Field K] in
/-- Cablewise preservation identifies the moved union's total W with
the sum of the lengths of the actual children. -/
theorem input_length (keeps : s.KeepsLength) :
    s.placed.input _ s.bin s.perm = ∑ i, (child i).length := by
  unfold Placement.input PlacedPack.length chargedLength
  let cost (c : Σ i, (child i).pack.layout.Edge) : ℝ :=
    if (s.bin c).isSome then ((child c.1).pack.layout.width c.2 : ℝ) *
      dist (s.placed.old ⟨c.1,(child c.1).pack.layout.src c.2⟩)
        (s.placed.old ⟨c.1,(child c.1).pack.layout.dst c.2⟩) else 0
  refine (Fintype.sum_sigma cost).trans ?_
  apply sum_congr rfl
  intro i _
  apply sum_congr rfl
  intro c _
  dsimp only [cost]
  simpa only [mul_ite, mul_zero] using congrArg (((child i).pack.layout.width c : ℝ) * ·) (keeps i c)

end PlacedStep
end Shortening

end BorderVNP
end Computability
end OAI
