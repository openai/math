import OAI.Computability.BorderVNP.DiagonalTallyReportModel
import OAI.Computability.BorderVNP.DiagonalTallyCountChecked
import OAI.Computability.BorderVNP.CubePhysicalOperandLedger

/-! # The actual descriptor order of a processor's tally scanner

The writer emits each owned cell's reported counts before that cell's unary
positions, then emits its routed cube lookups. Moving the unary rows to the
front for the mathematical sum preserves the multiset of coordinate and value
pairs, even when many copies report the same parameter or a zero increment.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace DiagonalTallyCellReports

open VPVNP.TapeWord DiagonalTallyMaterialize

/-- The actual source parameter, exponent and use bit of one marked copy. -/
def ReportBundle.usePair (b : ReportBundle) (i : Fin b.useCount) : ℕ × ℕ :=
  ((b.source i).parameter,if b.uses i then 2^(b.source i).place else 0)

/-- The true ordered sequence of binary increments for all marked copies in a cell. -/
def ReportCell.usePairs {l : ReportLayout} (c : ReportCell l) : List (ℕ × ℕ) :=
  c.bundles.flatMap fun b => List.ofFn b.usePair

/-- The checked little-endian gadget count fields of the same cell. -/
def ReportCell.countPairs {l : ReportLayout} (c : ReportCell l) : List (ℕ × ℕ) :=
  List.ofFn fun g : Fin l.gadgets => (l.parameters+g.val,value (List.ofFn (c.counts g)))

/-- Indirect RAM pointers, which advance separately at each bundle, give the designated
binary increment for each actual chronological report. -/
theorem bundleOperands_pairs (bs : List ReportBundle) (q : ReportCursor) (a : ℕ) :
    (bundleOperands bs q a).map Operand.pair = bs.flatMap (fun b => List.ofFn b.usePair) := by
  induction bs generalizing q a with
  | nil => rfl
  | cons b bs ih =>
    simp only [bundleOperands,List.map_append,List.map_ofFn,List.flatMap_cons,ih]
    exact congrArg (· ++ _) (congrArg List.ofFn (funext fun i =>
      unaryOperand_pair _ _ _ _ _ _ (b.uses i)))

/-- Every count operand uses its physical absolute source addresses and decodes the
same little-endian bits the private directory checked. -/
theorem ReportCell.operand_pairs {l : ReportLayout} (c : ReportCell l) (q : ReportCursor) :
    (c.operands q).map Operand.pair = c.countPairs ++ c.usePairs := by
  rw [ReportCell.operands,List.map_append,List.map_ofFn,bundleOperands_pairs]
  exact congrArg (· ++ _) (congrArg List.ofFn (funext fun g => (c.countFrame q).count_pair g (c.counts g)))

/-- Reorder the emitted absolute-address descriptors of all owned cells, preserving
every repeated pair. The native writer itself still traverses the cells in order. -/
theorem cellOperands_pairs_perm {l : ReportLayout} (cs : List (ReportCell l)) (q : ReportCursor) :
    ((cellOperands cs q).map Operand.pair).Perm
      (cs.flatMap ReportCell.usePairs ++ cs.flatMap ReportCell.countPairs) := by
  induction cs generalizing q with
  | nil => rfl
  | cons c cs ih =>
    rw [cellOperands,List.map_append,ReportCell.operand_pairs]
    simp only [List.flatMap_cons,List.append_assoc]
    let swap : (c.countPairs ++ (c.usePairs ++ cs.flatMap ReportCell.usePairs)).Perm
        ((c.usePairs ++ cs.flatMap ReportCell.usePairs) ++ c.countPairs) := List.perm_append_comm
    have moved := swap.append_right (cs.flatMap ReportCell.countPairs)
    apply (List.Perm.append_left _ (List.Perm.append_left _ (ih (c.after q)))).trans
    simpa only [List.append_assoc] using moved

variable {l : ReportLayout} {Site : Type*} [Fintype Site]
    (c : ReportCell l) (cell : Cube.Physical.NativeLedger.CellRead Site l.gadgets)
    (fields : cell.directory.reportedCounts = countFields (c.privateWires+c.supplied) l.gadgets l.countWidth)
    (source : ∀ g j, c.counts g j = cell.bank (c.privateWires+c.supplied+g.val*l.countWidth+j.val))

include source fields in
/-- The physical scanner's absolute-address count row agrees with the relative private
directory's reported field, and therefore with the sum of this cell's original site IDs. -/
theorem countPair_siteSum (g : Fin l.gadgets) (q : ReportCursor) :
    ((c.countFrame q).countRow g (c.counts g)).pair =
      (l.parameters+g.val,∑ v : Site, ((cell.observed v).filterMap Prod.snd).count g.val) := by
  have valid : CellSparse.countsValid cell.bank cell.directory.reportedCounts
      ((List.ofFn cell.order).flatMap cell.observed) := by
    by_contra hn
    apply cell.pass
    simp [CellSparse.Directory.weight,cell.reads,hn]
  rw [show c.counts g = fun j => cell.bank (c.privateWires+c.supplied+g.val*l.countWidth+j.val)
    from funext (source g)]
  refine ((c.countFrame q).count_pair_checked g _ cell.bank cell.directory fields _ valid).trans ?_
  rw [CellSparse.count_site_ids,List.map_ofFn,List.sum_ofFn]
  exact congrArg (Prod.mk _) (cell.order.sum_comp (fun v => ((cell.observed v).filterMap Prod.snd).count g.val))

/-- Source ordinal of a physical unary report, distinguishing cells, bundle occurrences,
and every original position/copy pair even when the stored values agree. -/
abbrev UseOccurrence {l : ReportLayout} (cs : List (ReportCell l)) :=
  (i : Fin cs.length) × (j : Fin cs[i].bundles.length) × Fin cs[i].bundles[j].useCount

/-- The parameter and binary increment read at this genuine report position. -/
def occurrencePair {l : ReportLayout} (cs : List (ReportCell l)) (u : UseOccurrence cs) : ℕ × ℕ :=
  cs[u.1].bundles[u.2.1].usePair u.2.2

private theorem count_flatMap {α β : Type*} [BEq β] (xs : List α) (f : α → List β) (p : β) :
    (xs.flatMap f).count p = ∑ i : Fin xs.length, (f xs[i]).count p := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    change (List.flatMap f (x::xs)).count p = ∑ i : Fin (xs.length+1), (f (x::xs)[i]).count p
    rw [List.flatMap_cons,List.count_append,Fin.sum_univ_succ,ih]
    rfl

private theorem count_ofFn {α : Type*} [DecidableEq α] [BEq α] [LawfulBEq α] {n : ℕ} (f : Fin n → α) (x : α) :
    (List.ofFn f).count x = ∑ i, if f i = x then 1 else 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.ofFn_succ,Fin.sum_univ_succ,List.count_cons,ih]
    simp only [beq_iff_eq]
    by_cases h : f 0 = x
    · rw [h]; simp only [ite_true]; omega
    · simp only [h,ite_false,Nat.add_zero,Nat.zero_add]

/-- Exact resource charge of the physical sparse report stream. -/
theorem occurrence_card {l : ReportLayout} (cs : List (ReportCell l)) :
    Fintype.card (UseOccurrence cs) = ∑ i : Fin cs.length, ∑ j : Fin cs[i].bundles.length,
      cs[i].bundles[j].useCount := by
  simp only [UseOccurrence,Fintype.card_sigma,Fintype.card_fin]

/-- Moving actual report rows to any enumeration of their original power slots preserves
the exact coordinate/value pairs, including repeated and rejected-bit contributions. -/
theorem usePairs_perm {l : ReportLayout} {Slots : Type*} [Fintype Slots] {n : ℕ}
    (cs : List (ReportCell l)) (source : UseOccurrence cs ≃ Slots)
    (order : Fin n ≃ Slots) (read : Slots → ℕ × ℕ)
    (aligned : ∀ u, occurrencePair cs u = read (source u)) :
    (cs.flatMap ReportCell.usePairs).Perm (List.ofFn fun j => read (order j)) := by
  apply List.perm_iff_count.mpr
  intro p
  let term (u : Slots) : ℕ := if read u = p then 1 else 0
  have natural : (cs.flatMap ReportCell.usePairs).count p =
      ∑ u : UseOccurrence cs, if occurrencePair cs u = p then 1 else 0 := by
    simp only [count_flatMap,ReportCell.usePairs,count_ofFn,UseOccurrence,Fintype.sum_sigma,occurrencePair]
    congr 1
  rw [natural,count_ofFn]
  simp_rw [aligned]
  exact (source.sum_comp term).trans (order.sum_comp term).symm

/-- The same incidence identification gives a uniform upper bound on the number of
actual unary descriptor writes, without scanning every parameter at every cell. -/
theorem useCount_le {l : ReportLayout} {Slots : Type*} [Fintype Slots]
    (cs : List (ReportCell l)) (source : UseOccurrence cs ↪ Slots) :
    (∑ i : Fin cs.length, ∑ j : Fin cs[i].bundles.length, cs[i].bundles[j].useCount) ≤ Fintype.card Slots :=
  (occurrence_card cs).symm.le.trans (Fintype.card_le_of_injective _ source.injective)

end DiagonalTallyCellReports

end BorderVNP
end Computability
end OAI
