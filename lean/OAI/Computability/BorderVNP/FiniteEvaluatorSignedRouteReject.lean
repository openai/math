import OAI.Computability.BorderVNP.FiniteEvaluatorOwnedProduct
import OAI.Computability.BorderVNP.FiniteEvaluatorSparseProgram
import OAI.Computability.BorderVNP.FiniteDiagonalReceivedTerms
import OAI.Computability.BorderVNP.CubeScatterReturnedOwnedFamily
import OAI.Computability.BorderVNP.FiniteEvaluatorCubeBanksNative

/-! # Zero field contribution when the shared routing words cannot be decoded

A shared route may return before any team runs the private owned-group
instructions. Every complete family of subsequent returns must reproduce
a genuine checked declaration and the exact received shared rows. If this
pair is absent, at least one team's sum over owned-group returns is empty.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FiniteEvaluator.OwnedContinuation

open VPVNP.BurstRAM RoutingISA TeamContraction BorderVNP.Cube
open scoped BigOperators Classical

variable {Team : Type*} [Fintype Team] {n b h K s w : ℕ} {F : Type*} [Field F] [Fintype F]
variable (table : TableEntry n b h K s → F) (length : ℕ) (codec : Cells.Codec) (prep : Code)
variable (pub : Team → Arg → Word w) (regs : Team → Bank w) (mem : Team → Memory w)
variable (ticks : Team → ℕ) (burst clock : ℕ)

local notation "lib" => Cells.library F codec
local notation "ret" => Cells.terminals F codec
local notation "fuel" => CompactMachine.nativeClock length
local notation "mac" => TeamSiteEvents.macros (w:=w) lib fuel
local notation "head" => CubeTriple.installGroups table
local notation "whole" => Code.seq (openCells table) (Code.seq prep privateReturns)

/-- If the actual private prefixes cannot all return, one of the local
bounded sums has no terms. This applies for every choice of residual clocks. -/
theorem zero_of_no_tuple (empty : ((u : Team) → Evaluator.Returns head (pub u) mac (regs u) (mem u)) → False) :
    (∏ u, boundedWeight (pub u) lib ret fuel whole (regs u) (mem u) (ticks u) burst clock) = 0 := by
  have miss : ¬ ∀ u, Nonempty (Evaluator.Returns head (pub u) mac (regs u) (mem u)) :=
    fun complete => empty (fun u => Classical.choice (complete u))
  obtain ⟨u,none⟩ := not_forall.mp miss
  apply Finset.prod_eq_zero (Finset.mem_univ u)
  rw [group_sum_stage table length codec prep (pub u) (regs u) (mem u) (ticks u) burst clock]
  exact Finset.sum_eq_zero (fun p _ => (none ⟨p.val⟩).elim)

end FiniteEvaluator.OwnedContinuation

namespace FiniteDiagonal.FieldRawLayout

open Crossing BorderVNP.Cube BorderVNP.Cube.Physical BorderVNP.Cube.Scatter
open TeamRows FiniteEvaluator RoutingISA TeamContraction VPVNP.BurstRAM
open scoped BigOperators Classical

variable {D w : ℕ} {P : Type} [Fintype P] {bits : P → ℕ} {N : Network D P bits}
variable {F : Type*} [Field F] [Fintype F] {T : N.Tables F} {L : FieldPacketPlan N F} {S : FieldSiteDirectory N T}
variable (V : FieldRawLayout L S) (R : ℕ) (header profile cells cables maxRows stride : ℕ)
local notation "ar" => planArena L R header profile cells cables maxRows stride
variable (decl : LengthDeclaration L.dimension L.alphabet) (group : Fin L.alphabet → Fin (R+1))
variable (shared : Symbols L.alphabet → List Bool)

omit [Fintype F] in
/-- The declaration and shared words read by a genuine complete joint family
belong to the exact finite received class of the selected field network. -/
theorem observed_received (family : TeamRows.Returns (Fin (R+1)) ar w)
    {q : NativeAssignments.Routed (b:=L.bitWidth) (s:=L.supply) (V.owners R)}
    (actual : ObservedOwned ar decl group family (V.owners R) shared q) :
    (decl,shared) ∈ Set.range (V.receivedWords R) := by
  let z := Assignment.Routed.wordsEquiv (V.owners R) L.bitWidth L.supply q
  have all := (Assignment.Routed.realizes_iff (V.owners R) Fin.valEmbedding (family.layout ar Fin.valEmbedding decl)
    (fun _ => (ar).header.packetBase) (fun _ => (ar).singleBank) (fun _ => rfl) (fun _ => rfl) q (family.observed ar decl shared)).mp actual.observed
  exact ⟨z,congrArg (fun z => (z.declaration,z.shared)) all⟩

variable (table : TableEntry L.dimension L.bitWidth L.copies L.alternatives L.supply → F)
variable (length : ℕ) (codec : Cells.Codec) (prep : Code)
variable (pub : Fin (R+1) → Arg → Word w) (regs : Fin (R+1) → Bank w) (mem : Fin (R+1) → Memory w)
variable (ticks : Fin (R+1) → ℕ) (burst clock : ℕ)
local notation "lib" => Cells.library F codec
local notation "ret" => Cells.terminals F codec
local notation "fuel" => CompactMachine.nativeClock length
local notation "mac" => TeamSiteEvents.macros (w:=w) lib fuel
local notation "head" => CubeTriple.installGroups table
local notation "whole" => Code.seq (openCells table) (Code.seq prep privateReturns)

/-- A fixed physical broadcast absent from the received public fibers has
zero weight. The reconstructed histories supply both their observed words
and their actual decoded assignments. -/
theorem invalid_received_zero
    (recover : ((u : Fin (R+1)) → Evaluator.Returns head (pub u) mac (regs u) (mem u)) →
      ∃ family : TeamRows.Returns (Fin (R+1)) ar w, ∃ q, ObservedOwned ar decl group family (V.owners R) shared q)
    (invalid : (decl,shared) ∉ Set.range (V.receivedWords R)) :
    (∏ u, boundedWeight (pub u) lib ret fuel whole (regs u) (mem u) (ticks u) burst clock)=0 := by
  apply OwnedContinuation.zero_of_no_tuple table length codec prep pub regs mem ticks burst clock
  intro paths
  obtain ⟨family,q,observed⟩ := recover paths
  exact invalid (V.observed_received R header profile cells cables maxRows stride decl group shared family observed)

end FiniteDiagonal.FieldRawLayout

end BorderVNP
end Computability
end OAI
