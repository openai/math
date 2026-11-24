import OAI.Computability.VPVNP.PairSimulationShrinkGatherSource
import OAI.Computability.VPVNP.PairTerminalFootprint

/-!
# Exact reads of the selected map route

The native route reads three words, at the resident ID, selected term and old
level layout. Its ordinal comparisons consume only local instruction ticks.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.ShrinkMapImage.Registers

open BurstRAM BurstRAM.PrivateRAM CompressorRecords CompressorRecords.SourceTransport
open Compression Compression.ShrinkMotif MotifGrid MotifBlocks MotifConversion MapResidentRows
open scoped Fin.CommRing
open private fetch from OAI.Computability.VPVNP.PairSimulationMapResidentInputs

variable {K : Type} [Field K] {factor : ℝ}
  {B : FixedBlock K demandSource demandTarget supply
    (realWidths demandMass) (realWidths supplyMass) (31 / 16) factor}
  {w a g : ℕ} (X : State a (packingLaneBits a g)) (sel : X.ShrinkSelection B)
  (side : Bool) (site : Site X) (m : Memory w) (level term : Word w)
  (R : MapRowSource X sel side m level term) (i : Fin (order X side site).length)

local notation "src" => rowCursor X sel side site m level term R i
local notation "motif" => Prod.fst (entry X side site i)
local notation "rank" => Fin.val (ordinal X (motif))
local notation "ev" => routeEvents X sel side site m level term R i

theorem rowCursor_fit : (src) < 2 ^ w := by
  have h := (directory_fit X R.first site R.fit).2
  have hi : i.val < capacity a := i.isLt.trans_eq (length_eq X side site)
  exact (Nat.add_lt_add_left hi _).trans h

private theorem termAddress_val : (MapResidentInputs.termAddr m ((src) : Word w) term 10).val =
    term.val + (rank) * 10 := by
  have fit := rowCursor_fit X sel side site m level term R i
  have digits := allocated_id X R.first R.fit R.rows site i
  change (m (src)).val = (rank) * 6 + (entry X side site i).2.val at digits
  let id := m (src)
  have rb := (ordinal X (motif)).isLt
  have room := R.termFit
  have h6 : 6 < 2 ^ w := by omega
  have hTerm : term.val + (rank) * 10 < 2 ^ w := by omega
  have q : (BinaryOp.div.eval id 6).val = (rank) := by
    change id.val / (6 : Word w).val % (2 ^ w) = _
    rw [show (6 : Word w).val = 6 from Nat.mod_eq_of_lt h6,
      Nat.mod_eq_of_lt ((Nat.div_le_self ..).trans_lt id.isLt)]
    change (m (src)).val / 6 = _
    rw [digits]
    have h := (entry X side site i).2.isLt
    omega
  have qWord : BinaryOp.div.eval id 6 = ((rank) : Word w) := by
    rw [← q]
    exact Fin.ext (Nat.mod_eq_of_lt (BinaryOp.div.eval id 6).isLt).symm
  change (term + BinaryOp.div.eval (m (((src) : Word w).val)) 6 * 10).val = _
  rw [show ((src) : Word w).val = (src) from Nat.mod_eq_of_lt fit, qWord,
    show term = (term.val : Word w) from Fin.ext (Nat.mod_eq_of_lt term.isLt).symm]
  change (((term.val : Word w) + ((rank) : Word w) * ((10 : ℕ) : Word w))).val = _
  rw [← Nat.cast_mul, ← Nat.cast_add]
  simpa only [Fin.val_natCast, Nat.mod_eq_of_lt term.isLt] using Nat.mod_eq_of_lt hTerm

/-- Three fitted addresses suffice for a read-footprint check of the entire
dispatcher and layout branch, for every stored map in the shrinking row. -/
theorem routeEvents_reads (allow : ℕ → Prop) (idSafe : allow (src))
    (termSafe : allow (term.val + (rank) * 10)) (layoutSafe : allow (level + 38).val) :
    Reads allow (ev) := by
  unfold routeEvents
  apply TerminalFootprint.reads_append
  · apply TerminalFootprint.reads_append
    · intro q val h
      simp only [MapResidentInputs.itemEvents, fetch, List.mem_cons, List.not_mem_nil,
        Event.read.injEq, reduceCtorEq, false_or, or_false] at h
      rcases h with h | h
      · rw [h.1, show ((src) : Word w).val = (src) from
          Nat.mod_eq_of_lt (rowCursor_fit X sel side site m level term R i)]
        exact idSafe
      · rw [h.1, termAddress_val X sel side site m level term R i]
        exact termSafe
    · exact TerminalFootprint.reads_ticks allow _
  · intro q val h
    simp only [ShrinkLayoutBranch.events, List.mem_cons, List.not_mem_nil, Event.read.injEq,
      reduceCtorEq, false_or, or_false] at h
    exact h.1 ▸ layoutSafe

/-- All external operations of the resident ID, term and layout route are reads. -/
theorem routeEvents_noWrites : Writes (fun _ ↦ False) (ev) := by
  intro q val h
  rcases List.mem_append.mp h with previous | layout
  · rcases List.mem_append.mp previous with item | tick
    · simp only [MapResidentInputs.itemEvents, fetch, List.mem_cons, List.not_mem_nil,
        reduceCtorEq, false_or] at item
    · cases List.eq_of_mem_replicate tick
  · simp only [ShrinkLayoutBranch.events, List.mem_cons, List.not_mem_nil, reduceCtorEq,
      false_or] at layout

theorem routeEvents_cost :
    countProbes (ev) = 3 ∧ choiceBits (ev) = [] := by
  have quiet (n) : countProbes (List.replicate n (.tick : Event w)) = 0 ∧
      choiceBits (List.replicate n (.tick : Event w)) = [] := by
    induction n with
    | zero => exact ⟨rfl, rfl⟩
    | succ n ih => simpa only [List.replicate_succ, countProbes, choiceBits] using ih
  have a := MapResidentInputs.itemCost m ((src) : Word w) term 10
  have b := ShrinkLayoutBranch.cost m level
  simp only [routeEvents, countProbes_append, PrimedInputRAM.Flow.choiceBits_append,
    a.2.1, a.2.2, b.2.1, b.2.2, (quiet _).1, (quiet _).2, List.nil_append, and_self]

end PairSimulation.ShrinkMapImage.Registers

end VPVNP
end Computability
end OAI
