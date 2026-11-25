import OAI.Computability.BorderVNP.DiagonalNativeValue
import OAI.Computability.BorderVNP.DiagonalResidueRAMLeadSum
import OAI.Computability.BorderVNP.TransmissionPinsComplete
import OAI.Computability.BorderVNP.RoutingISABlockAppend

/-! # Signed path decomposition of the complete native evaluation branch

The first stage guesses the substituted index exactly once. Each such choice starts
the expansion, routing, cell and tally code in the actual resulting memory. The
physical last stage supplies the residue reader's multiplicity on the lead team.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator

open VPVNP.BurstRAM TeamContraction Pins DiagonalResidueRAM
open scoped BigOperators Classical

variable {w : ℕ} (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)

/-- Stages between the fresh index guess and the final residue reader, in execution order. -/
def expansionStages (epochs groups arguments occurrences : Code) : List Code :=
  [epochs, Packing.Directory.ISA.program, groups, route, arguments, callOwnedCells, occurrences,
    DiagonalTallyRAM.complete]

private theorem expand_iff (epochs groups arguments occurrences : Code) {s m es t mt} :
    Runs pub mac (evaluate epochs groups arguments occurrences) s m es t mt ↔
      Runs pub mac (.seq preparePins (.seq (.block (expansionStages epochs groups arguments occurrences)) leadEntry))
        s m es t mt := by
  change Runs _ _ (.seq preparePins (.block (expansionStages epochs groups arguments occurrences ++ [leadEntry]))) _ _ _ _ _ ↔ _
  simp only [Runs.seq_iff, Runs.block_append_iff (a := expansionStages epochs groups arguments occurrences)
    (b := [leadEntry]) (List.cons_ne_nil _ _) (List.cons_ne_nil _ _),Code.block]

/-- A physical residue-reader history has a unique final state and memory. Keeping that
state in a return preserves its trace and integer weight. -/
noncomputable def leadReturnEquiv (s : Bank w) (m : Memory w) : Returns leadEntry pub mac s m ≃ LeadReturns pub mac s m := by
  let f (z : Returns leadEntry pub mac s m) : LeadReturns pub mac s m := ⟨z.val.1,z.val.2.1,z.val.2.2,z.property⟩
  refine Equiv.ofBijective f ⟨?_,?_⟩
  · intro a b he
    have h : a.val.1 = b.val.1 := congrArg Subtype.val he
    obtain ⟨_,hr,hm⟩ := a.property.eq_of_shared_events b.property (congrArg (· ++ []) h)
    exact Subtype.ext (Prod.ext h (Prod.ext hr hm))
  · rintro ⟨es,z,mz,r⟩
    exact ⟨⟨(es,z,mz),r⟩,rfl⟩

/-- The matrix-entry multiplicity in the current, post-tally state. -/
noncomputable def leadMultiplicity (s : Bank w) (m : Memory w) : ℤ :=
  if m (pub 0).val = 0 then (Nat.card (StagedPaths pub mac (leadBank pub s m) m) : ℤ) else 1

/-- Sum of signs of all possible matrix-entry continuations. -/
theorem leadReturn_sum (s : Bank w) (m : Memory w) [Fintype (Returns leadEntry pub mac s m)] :
    (∑ z : Returns leadEntry pub mac s m, pathWeight z.val.1) = leadMultiplicity pub mac s m := by
  let := Fintype.ofEquiv (Returns leadEntry pub mac s m) (leadReturnEquiv pub mac s m)
  calc
    _ = ∑ z : LeadReturns pub mac s m, signedWeight z.val :=
      (leadReturnEquiv pub mac s m).sum_comp (fun z => signedWeight z.val)
    _ = _ := lead_signed pub mac s m

variable (epochs groups arguments occurrences : Code) (s : Bank w) (m : Memory w)

/-- The contiguous native table handling all expansion, cell and tally stages. -/
abbrev expansionBody := Code.block (expansionStages epochs groups arguments occurrences)

/-- Joining a genuine initial pin guess, all middle-stage returns and a real residue
continuation is a bijection preserving the entire chronological history. -/
noncomputable def evaluateReturnEquiv {k : ℕ} (pins : (Fin k → Bool) ≃ Pins.Return pub mac s m) :
    (Σ b : Fin k → Bool,
      Σ x : Returns (expansionBody epochs groups arguments occurrences) pub mac (pins b).val.2.1 (pins b).val.2.2,
      Returns leadEntry pub mac x.val.2.1 x.val.2.2) ≃
    Returns (evaluate epochs groups arguments occurrences) pub mac s m := by
  let mid := expansionBody epochs groups arguments occurrences
  let eqv : Returns (.seq preparePins (.seq mid leadEntry)) pub mac s m ≃
      Returns (evaluate epochs groups arguments occurrences) pub mac s m :=
    Equiv.subtypeEquivRight (fun _ => (expand_iff pub mac epochs groups arguments occurrences).symm)
  exact (Equiv.sigmaCongrRight fun b => seqReturnEquiv mid leadEntry pub mac (pins b).val.2.1 (pins b).val.2.2).trans
    ((Equiv.sigmaCongrLeft (β := fun z : Returns preparePins pub mac s m =>
      Returns (.seq mid leadEntry) pub mac z.val.2.1 z.val.2.2) pins).trans
    ((seqReturnEquiv preparePins (.seq mid leadEntry) pub mac s m).trans eqv))

/-- The event history preserves the fresh guess and all expansion and residue traces. -/
theorem evaluateReturnEquiv_events {k : ℕ} (pins : (Fin k → Bool) ≃ Pins.Return pub mac s m)
    (b : Fin k → Bool)
    (x : Returns (expansionBody epochs groups arguments occurrences) pub mac (pins b).val.2.1 (pins b).val.2.2)
    (y : Returns leadEntry pub mac x.val.2.1 x.val.2.2) :
    ((evaluateReturnEquiv pub mac epochs groups arguments occurrences s m pins) ⟨b,x,y⟩).val.1 =
      (pins b).val.1 ++ (x.val.1 ++ y.val.1) := rfl

/-- The full evaluation path sum, including arbitrary private outcomes in the middle
of the program, factors into one term per fresh index and one per expansion return.
The lead-team factor uses the actual staged residue memory at the end of that return. -/
theorem evaluate_sum {k : ℕ} (pins : (Fin k → Bool) ≃ Pins.Return pub mac s m)
    [Fintype (Returns (evaluate epochs groups arguments occurrences) pub mac s m)]
    [∀ b : Fin k → Bool, Fintype (Returns (expansionBody epochs groups arguments occurrences)
      pub mac (pins b).val.2.1 (pins b).val.2.2)]
    [∀ (b : Fin k → Bool) (x : Returns (expansionBody epochs groups arguments occurrences)
      pub mac (pins b).val.2.1 (pins b).val.2.2), Fintype (Returns leadEntry pub mac x.val.2.1 x.val.2.2)] :
    (∑ z : Returns (evaluate epochs groups arguments occurrences) pub mac s m, pathWeight z.val.1) =
      ∑ b : Fin k → Bool, ∑ x : Returns (expansionBody epochs groups arguments occurrences)
        pub mac (pins b).val.2.1 (pins b).val.2.2, pathWeight x.val.1 * leadMultiplicity pub mac x.val.2.1 x.val.2.2 := by
  let e := evaluateReturnEquiv pub mac epochs groups arguments occurrences s m pins
  rw [← e.sum_comp (fun z => pathWeight z.val.1),Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro b _
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro x _
  rw [← leadReturn_sum pub mac,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  have one : pathWeight (pins b).val.1 = 1 := by
    apply List.prod_eq_one
    intro n hn
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hn
    simp [(preparePins_positive (pins b).property) a ha,TeamRAM.Sign.value]
  change pathWeight ((evaluateReturnEquiv pub mac epochs groups arguments occurrences s m pins) ⟨b,x,y⟩).val.1 = _
  rw [evaluateReturnEquiv_events]
  simp only [pathWeight,List.map_append,List.prod_append] at one ⊢
  rw [one,one_mul]

end RoutingISA.Evaluator

end BorderVNP
end Computability
end OAI
