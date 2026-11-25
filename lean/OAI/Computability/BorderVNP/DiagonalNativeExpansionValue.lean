import OAI.Computability.BorderVNP.DiagonalNativeEvaluate
import OAI.Computability.BorderVNP.DiagonalNativeCellValue
import OAI.Computability.BorderVNP.RoutingISAStageLink

/-! # The native expansion as a sum of owned-cell products and checked residues

The pre-call code includes the real geometry reconstruction, public directories and
routing. Its returns determine the live private inputs. Each cell's independent
signed choices factor out of the actual post-call occurrence and tally continuation.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator

open VPVNP BurstRAM TeamContraction CellDispatch
open scoped BigOperators Classical

variable {w : ℕ}

/-- All stages that prepare the true cell-call arguments, including the complete route. -/
def prepareExpansion (epochs groups arguments : Code) : Code :=
  .block [epochs,Packing.Directory.ISA.program,groups,route,arguments]

/-- Populate the selected occurrence records and turn their checked subtotals into query bits. -/
def finishExpansion (occurrences : Code) : Code := .seq occurrences DiagonalTallyRAM.complete

private theorem expansion_split (epochs groups arguments occurrences : Code) {pub : Arg → Word w}
    {mac : TeamOpcode.Macros w 8} {s m es t mt} :
    Runs pub mac (expansionBody epochs groups arguments occurrences) s m es t mt ↔
      Runs pub mac (.seq (prepareExpansion epochs groups arguments) (.seq callOwnedCells (finishExpansion occurrences))) s m es t mt :=
  Runs.block_append_iff (a := [epochs,Packing.Directory.ISA.program,groups,route,arguments])
    (b := [callOwnedCells,occurrences,DiagonalTallyRAM.complete]) (List.cons_ne_nil _ _) (List.cons_ne_nil _ _)

variable (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8) (s : Bank w) (m : Memory w)
    (epochs groups arguments occurrences : Code)

/-- The exact dependent product of the real preparation, private call directory and
final tally paths. No extra machine choices are introduced by the equivalence. -/
noncomputable def expansionReturnEquiv :
    (Σ p : Returns (prepareExpansion epochs groups arguments) pub mac s m,
      Σ c : Returns callOwnedCells pub mac p.val.2.1 p.val.2.2,
      Returns (finishExpansion occurrences) pub mac c.val.2.1 c.val.2.2) ≃
    Returns (expansionBody epochs groups arguments occurrences) pub mac s m := by
  let prepare := prepareExpansion epochs groups arguments
  let finish := finishExpansion occurrences
  let e : Returns (.seq prepare (.seq callOwnedCells finish)) pub mac s m ≃
      Returns (expansionBody epochs groups arguments occurrences) pub mac s m :=
    Equiv.subtypeEquivRight (fun _ => (expansion_split epochs groups arguments occurrences).symm)
  exact (Equiv.sigmaCongrRight fun p : Returns prepare pub mac s m => seqReturnEquiv callOwnedCells finish pub mac p.val.2.1 p.val.2.2).trans
    ((seqReturnEquiv prepare (.seq callOwnedCells finish) pub mac s m).trans e)

/-- Event histories and final states under the expansion path correspondence. -/
theorem expansionReturnEquiv_val (p : Returns (prepareExpansion epochs groups arguments) pub mac s m)
    (c : Returns callOwnedCells pub mac p.val.2.1 p.val.2.2)
    (z : Returns (finishExpansion occurrences) pub mac c.val.2.1 c.val.2.2) :
    (expansionReturnEquiv pub mac s m epochs groups arguments occurrences ⟨p,c,z⟩).val =
      (p.val.1 ++ (c.val.1 ++ z.val.1),z.val.2) := rfl

private theorem finish_det (hd : occurrences.deterministic = true) :
    (finishExpansion occurrences).deterministic = true := by
  simp only [finishExpansion,Code.deterministic,hd,
    show DiagonalTallyRAM.complete.deterministic = true by decide,Bool.and_self]

private theorem finish_sub (hd : occurrences.deterministic = true) :
    Subsingleton (Returns (finishExpansion occurrences) pub mac s m) := by
  constructor
  intro a b
  obtain ⟨he,hs,hm⟩ := a.property.unique_of_deterministic (finish_det occurrences hd) b.property
  exact Subtype.ext (Prod.ext he (Prod.ext hs hm))

/-- The actual post-call tally-and-entry value. Deterministic tally code either rejects
or supplies a unique serialized query to the staged matrix reader. -/
noncomputable def tallyValue (hd : occurrences.deterministic = true) : ℤ :=
  have := finish_sub pub mac s m occurrences hd
  letI := Fintype.ofFinite (Returns (finishExpansion occurrences) pub mac s m)
  ∑ z : Returns (finishExpansion occurrences) pub mac s m,
    pathWeight z.val.1 * leadMultiplicity pub mac z.val.2.1 z.val.2.2

/-- A successful unsigned subtotal and occurrence scan contributes precisely the
entry determined by its true output registers and serialized memory. -/
theorem tallyValue_of_return (hd : occurrences.deterministic = true) (hu : occurrences.unsigned = true)
    {es t mt} (r : Runs pub mac (finishExpansion occurrences) s m es t mt) :
    tallyValue pub mac s m occurrences hd = leadMultiplicity pub mac t mt := by
  let z : Returns (finishExpansion occurrences) pub mac s m := ⟨(es,t,mt),r⟩
  have := finish_sub pub mac s m occurrences hd
  let := Fintype.ofFinite (Returns (finishExpansion occurrences) pub mac s m)
  change (∑ y : Returns _ _ _ _ _, pathWeight y.val.1 * leadMultiplicity pub mac y.val.2.1 y.val.2.2) = _
  rw [Fintype.sum_subsingleton _ z]
  have unsigned : (finishExpansion occurrences).unsigned = true := by
    simp only [finishExpansion,Code.unsigned,hu,show DiagonalTallyRAM.complete.unsigned = true by decide,Bool.and_self]
  have plus : pathWeight es = 1 := by
    apply List.prod_eq_one
    intro x hx
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hx
    simp [(r.unsigned_events unsigned a ha).2,TeamRAM.Sign.value]
  change pathWeight es * _ = _
  rw [plus,one_mul]

/-- Every preparation return selects the corresponding physically addressed finite cell
histories. Their signed sum multiplies one common post-call tally value. -/
theorem expansion_signed_sum (hd : occurrences.deterministic = true)
    (choices : List (Word w) → Finset Outcome) (spec : ∀ v o, o ∈ choices v ↔ mac 0 v o.1 = some o.2)
    (frameFit : (pub 0).val+15 < 2^w)
    (room : ∀ p : Returns (prepareExpansion epochs groups arguments) pub mac s m,
      let f := Frame.ofMemory pub p.val.2.2
      f.base+3*f.count ≤ 2^w)
    [Fintype (Returns (prepareExpansion epochs groups arguments) pub mac s m)]
    [Fintype (Returns (expansionBody epochs groups arguments occurrences) pub mac s m)] :
    (∑ z : Returns (expansionBody epochs groups arguments occurrences) pub mac s m,
      pathWeight z.val.1 * leadMultiplicity pub mac z.val.2.1 z.val.2.2) =
    ∑ p : Returns (prepareExpansion epochs groups arguments) pub mac s m,
      let f := Frame.ofMemory pub p.val.2.2
      pathWeight p.val.1 * ((∑ es ∈ f.histories pub p.val.2.2 choices, pathWeight es) *
        tallyValue pub mac (cellBank pub mac p.val.2.1 p.val.2.2) p.val.2.2 occurrences hd) := by
  let Prep := Returns (prepareExpansion epochs groups arguments) pub mac s m
  let Calls (p : Prep) := Returns callOwnedCells pub mac p.val.2.1 p.val.2.2
  let Tally (p : Prep) (c : Calls p) := Returns (finishExpansion occurrences) pub mac c.val.2.1 c.val.2.2
  let : ∀ p : Prep, Fintype (Calls p) := fun p =>
    Fintype.ofEquiv _ (cellHistoriesEquiv pub mac p.val.2.1 p.val.2.2 spec frameFit (room p)).symm
  let : ∀ (p : Prep) (c : Calls p), Fintype (Tally p c) := fun p c => by
    have := finish_sub pub mac c.val.2.1 c.val.2.2 occurrences hd
    exact Fintype.ofFinite _
  let e := expansionReturnEquiv pub mac s m epochs groups arguments occurrences
  rw [← e.sum_comp (fun z => pathWeight z.val.1 * leadMultiplicity pub mac z.val.2.1 z.val.2.2),Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro p _
  dsimp only
  rw [Fintype.sum_sigma,← cell_sum_with pub mac p.val.2.1 p.val.2.2 spec frameFit (room p)
    (fun t mt => tallyValue pub mac t mt occurrences hd),Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c _
  change (∑ z : Tally p c, pathWeight (p.val.1 ++ (c.val.1 ++ z.val.1)) *
    leadMultiplicity pub mac z.val.2.1 z.val.2.2) = pathWeight p.val.1 *
      (pathWeight c.val.1 * ∑ z : Tally p c, pathWeight z.val.1 * leadMultiplicity pub mac z.val.2.1 z.val.2.2)
  simp only [Finset.mul_sum,pathWeight,List.map_append,List.prod_append,mul_assoc]

end RoutingISA.Evaluator

end BorderVNP
end Computability
end OAI
