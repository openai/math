import OAI.Computability.VPVNP.CompressionBoundedBind
import OAI.Computability.VPVNP.CompressionProcedure

/-!
# Local history bounds of exact compressor procedures

The bounds refer to the records attached to each term in the actual execution
tree. Sequential procedures retain both sets of records, including the records
of the continuation selected by each branch.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace Compression.Procedure

open NetworkKernel

variable {R : Type*} [CommSemiring R] {a b k κ : ℕ} {μ : ℝ}

/-- Uniform local record and branch length bounds for every execution of a procedure. -/
structure RecordBounds (P : Procedure R a b k κ μ) (C steps : ℕ) where
  /-- The local records for the whole execution tree of each input, used to bound each pass and
  the length of every selected branch. -/
  records : ∀ g n h X, (P.run g n h X).Records
  bounded : ∀ g n h X, (P.run g n h X).Bounded C (records g n h X)
  length_le : ∀ g n h X z, ((P.run g n h X).termChain (records g n h X) z).length ≤ steps

namespace RecordBounds

variable {P : Procedure R a b k κ μ} {C D m n : ℕ}

/-- Enlarge both bounds while keeping the same records. -/
def mono (B : P.RecordBounds C m) (hC : C ≤ D) (hm : m ≤ n) : P.RecordBounds D n where
  records := B.records
  bounded g l h X := (P.run g l h X).bounded_mono _ hC (B.bounded g l h X)
  length_le g l h X z := (B.length_le g l h X z).trans hm

/-- The empty schedule has an empty history and depth zero. -/
def id (R : Type*) [CommSemiring R] (a C : ℕ) : (Procedure.id R a).RecordBounds C 0 where
  records g l h X := by
    have hl : l = g := h.trans (Nat.zero_add g)
    subst g
    exact PUnit.unit
  bounded g l h X := by
    have hl : l = g := h.trans (Nat.zero_add g)
    subst g
    trivial
  length_le g l h X z := by
    have hl : l = g := h.trans (Nat.zero_add g)
    subst g
    exact Nat.zero_le 0

/-- Concatenate the two actual execution records. The largest elementary
bound applies throughout, and the two uniform branch lengths add. -/
def seq {d k' κ' : ℕ} {ν : ℝ} {Q : Procedure R b d k' κ' ν}
    (B : P.RecordBounds C m) (B' : Q.RecordBounds D n) :
    (P.seq Q).RecordBounds (max C D) (m + n) where
  records g l h X :=
    let E := P.run (k' + g) l (h.trans (Nat.add_assoc k k' g)) X
    E.bindRecords (fun z => Q.run g (k' + g) rfl (E.finalState z))
      (B.records _ _ _ X) (fun z => B'.records _ _ _ (E.finalState z))
  bounded g l h X := by
    let E := P.run (k' + g) l (h.trans (Nat.add_assoc k k' g)) X
    apply E.bounded_bindRecords
    · exact E.bounded_mono _ (le_max_left _ _) (B.bounded _ _ _ X)
    · intro z
      exact (Q.run _ _ _ (E.finalState z)).bounded_mono _ (le_max_right _ _)
        (B'.bounded _ _ _ (E.finalState z))
  length_le g l h X z := by
    let E := P.run (k' + g) l (h.trans (Nat.add_assoc k k' g)) X
    exact E.length_bindRecords_le _ _ _ (B.length_le _ _ _ X)
      (fun y => B'.length_le _ _ _ (E.finalState y)) z

section SinglePass

variable {A : ℝ} (hκ : 0 < κ) (hμ : 0 ≤ μ) (hA : 0 ≤ A)
  (f : ∀ g (X : State a (k + g)), StatePass R X b g)
  (hcount : ∀ g X (i : (f g X).step.Choice), X.positions = κ * ((f g X).next i).positions)
  (henergy : ∀ g X (i : (f g X).step.Choice),
    ((f g X).next i).energy ≤ μ * X.energy + A * (X.positions : ℝ) ^ 2)

/-- Every branch of a procedure created from one pass has depth exactly one. -/
theorem ofPass_length (g l : ℕ) (h : l = k + g) (X : State a l)
    (rec : ((Procedure.ofPass hκ hμ hA f hcount henergy).run g l h X).Records)
    (z : ((Procedure.ofPass hκ hμ hA f hcount henergy).run g l h X).Choices) :
    (((Procedure.ofPass hκ hμ hA f hcount henergy).run g l h X).termChain rec z).length = 1 := by
  subst l
  exact (StateExecution.length_more (f g X) (fun i => .done ((f g X).next i)) rec z)

/-- Lift the supplied records and elementary bound of a single pass to the
whole procedure. Each selected history contains exactly that pass. -/
def ofPass (rec : ∀ g X, (f g X).Records) (hrec : ∀ g X, (f g X).Bounded (rec g X) C) :
    (Procedure.ofPass hκ hμ hA f hcount henergy).RecordBounds C 1 where
  records g l h X := by
    subst l
    exact (rec g X, fun _ => PUnit.unit)
  bounded g l h X := by
    subst l
    exact ⟨hrec g X, fun _ => trivial⟩
  length_le g l h X z := (ofPass_length hκ hμ hA f hcount henergy g l h X _ z).le

end SinglePass
end RecordBounds
end Compression.Procedure

end VPVNP
end Computability
end OAI
