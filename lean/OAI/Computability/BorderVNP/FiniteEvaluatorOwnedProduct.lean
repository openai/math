import OAI.Computability.BorderVNP.FiniteEvaluatorOwnedFactors
import OAI.Computability.BorderVNP.FiniteEvaluatorCubeTripleBoot

/-! # All-team field value at the received routing words

The complete native installer and owned-group histories have weight one.
Reindexing their bounded chronological tuples by the distributed assignment
dictionary leaves the product of the actual continuations. Each continuation
starts at its own reached memory and spends its own remaining ticks.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FiniteEvaluator.OwnedContinuation

open VPVNP.BurstRAM RoutingISA TeamContraction BorderVNP.Cube
open scoped BigOperators Classical
open private owned_native from OAI.Computability.BorderVNP.DiagonalNativeSignedTags

variable {n b h K s w : ℕ} {F : Type*} [Field F] [Fintype F]
variable (table : TableEntry n b h K s → F) (N : ℕ)

local notation "lib" => Cells.library F
local notation "ret" => Cells.terminals F
local notation "fuel" => CompactMachine.nativeClock N
local notation "mac" => TeamSiteEvents.macros (w:=w) lib fuel
local notation "head" => CubeTriple.installGroups table
local notation "whole" => Code.seq (openCells table) (Code.seq prepareTasks privateReturns)

omit [Field F] in
/-- The constant deck installation and the actual owned-group scan contain
only ordinary native instructions, including the true local assignment guesses. -/
theorem installGroups_nativeOnly : (head).nativeOnly=true := by
  have fixed := (CubeDeck.install table).nativeOnly_of_unsigned (CubeConstants.install_unsigned (CubeDeck.entry table)).1
  exact Bool.and_eq_true_iff.mpr ⟨fixed,owned_native n b h K s⟩

section Codec

variable (codec : Cells.Codec)
local notation "clib" => Cells.library F codec
local notation "cret" => Cells.terminals F codec
local notation "cmac" => TeamSiteEvents.macros (w:=w) clib fuel

section Preparation

variable (prep : Code)
local notation "assembled" => Code.seq (openCells table) (Code.seq prep privateReturns)
local notation "continuation" => codeFor prep

/-- The local bounded word-program sum over genuine installer and group returns
with the residual native budget. -/
theorem group_sum_stage (pub : Arg → Word w) (bank : Bank w) (mem : Memory w) (ticks burst clock : ℕ) :
    letI := Fintype.ofFinite (Evaluator.BoundedReturns head pub cmac bank mem ticks burst clock)
    boundedWeight pub clib cret fuel assembled bank mem ticks burst clock =
      ∑ p : Evaluator.BoundedReturns head pub cmac bank mem ticks burst clock,
        boundedWeight pub clib cret fuel continuation p.val.val.2.1 p.val.val.2.2 (ticks-traceCost p.val.val.1) burst clock := by
  apply (at_owned_stage pub N bank mem codec prep table ticks burst clock).trans
  apply (reassociate_boundedWeight pub clib cret fuel [CubeDeck.install table] (TeamRows.ownedGroups n b h K s)
    continuation bank mem ticks burst clock).trans
  apply (boundedWeight_seq pub clib head continuation bank mem ticks burst clock cret fuel).trans
  apply Finset.sum_congr rfl
  intro x _
  rw [weight_native pub clib cret fuel x.val.property (installGroups_nativeOnly table),one_mul]

variable {Team I : Type*} [Fintype Team] [Fintype I]
variable (pub : Team → Arg → Word w) (bank : Team → Bank w) (mem : Team → Memory w)
variable (ticks : Team → ℕ) (burst clock : ℕ)

local notation "CodecHist" => (fun t => Evaluator.Returns head (pub t) cmac (bank t) (mem t))
local notation "CodecBounded" => (fun t => Evaluator.BoundedReturns head (pub t) cmac (bank t) (mem t) (ticks t) burst clock)

/-- The distributed private assignment dictionary exhausts the product of
native team histories at the actual received routing words. The cutoffs are
checked on every distributed assignment and retained on every continuation. -/
theorem routed_product_stage (dictionary : I ≃ ((t : Team) → CodecHist t))
    (time : ∀ i t, traceCost (dictionary i t).val.1 ≤ ticks t) (choose : 1 ≤ clock) :
    (∏ t, boundedWeight (pub t) clib cret fuel assembled (bank t) (mem t) (ticks t) burst clock) =
      ∑ i : I, ∏ t, let p := dictionary i t
        boundedWeight (pub t) clib cret fuel continuation p.val.2.1 p.val.2.2 (ticks t-traceCost p.val.1) burst clock := by
  let (t : Team) := Fintype.ofFinite (CodecBounded t)
  let checked (i : I) (t : Team) : CodecBounded t := ⟨dictionary i t,
    ((dictionary i t).property.nativeOnly_limits (installGroups_nativeOnly table)).mono (time i t) (Nat.zero_le _) choose⟩
  let E : I ≃ ((t : Team) → CodecBounded t) := Equiv.ofBijective checked (by
    constructor
    · intro i j h
      exact dictionary.injective (funext fun t => congrArg Subtype.val (congrFun h t))
    · intro x
      obtain ⟨i,hi⟩ := dictionary.surjective (fun t => (x t).val)
      exact ⟨i,funext fun t => Subtype.ext (congrFun hi t)⟩)
  let value (t : Team) (p : CodecBounded t) := boundedWeight (pub t) clib cret fuel continuation p.val.val.2.1 p.val.val.2.2
    (ticks t-traceCost p.val.val.1) burst clock
  calc
    _ = ∏ t, ∑ p : CodecBounded t, value t p := Finset.prod_congr rfl (fun t _ => group_sum_stage table N codec prep (pub t) (bank t) (mem t) (ticks t) burst clock)
    _ = ∑ z : (t : Team) → CodecBounded t, ∏ t, value t (z t) := Fintype.prod_sum value
    _ = _ := (E.sum_comp (fun z => ∏ t, value t (z t))).symm

end Preparation

/-- The local bounded word-program sum over genuine installer and group returns
with the residual native budget. -/
theorem group_sum_for (pub : Arg → Word w) (bank : Bank w) (mem : Memory w) (ticks burst clock : ℕ) :
    letI := Fintype.ofFinite (Evaluator.BoundedReturns head pub cmac bank mem ticks burst clock)
    boundedWeight pub clib cret fuel whole bank mem ticks burst clock =
      ∑ p : Evaluator.BoundedReturns head pub cmac bank mem ticks burst clock,
        boundedWeight pub clib cret fuel code p.val.val.2.1 p.val.val.2.2 (ticks-traceCost p.val.val.1) burst clock :=
  group_sum_stage table N codec prepareTasks pub bank mem ticks burst clock

variable {Team I : Type*} [Fintype Team] [Fintype I]
variable (pub : Team → Arg → Word w) (bank : Team → Bank w) (mem : Team → Memory w)
variable (ticks : Team → ℕ) (burst clock : ℕ)

local notation "CodecHist" => (fun t => Evaluator.Returns head (pub t) cmac (bank t) (mem t))
local notation "CodecBounded" => (fun t => Evaluator.BoundedReturns head (pub t) cmac (bank t) (mem t) (ticks t) burst clock)

/-- The distributed private assignment dictionary exhausts the product of
native team histories at the actual received routing words. The cutoffs are
checked on every distributed assignment and retained on every continuation. -/
theorem routed_product_for (dictionary : I ≃ ((t : Team) → CodecHist t))
    (time : ∀ i t, traceCost (dictionary i t).val.1 ≤ ticks t) (choose : 1 ≤ clock) :
    (∏ t, boundedWeight (pub t) clib cret fuel whole (bank t) (mem t) (ticks t) burst clock) =
      ∑ i : I, ∏ t, let p := dictionary i t
        boundedWeight (pub t) clib cret fuel code p.val.2.1 p.val.2.2 (ticks t-traceCost p.val.1) burst clock :=
  routed_product_stage table N codec prepareTasks pub bank mem ticks burst clock dictionary time choose

end Codec

/-- The local bounded word-program sum over genuine installer and group returns
with the residual native budget. -/
theorem group_sum (pub : Arg → Word w) (bank : Bank w) (mem : Memory w) (ticks burst clock : ℕ) :
    letI := Fintype.ofFinite (Evaluator.BoundedReturns head pub mac bank mem ticks burst clock)
    boundedWeight pub lib ret fuel whole bank mem ticks burst clock =
      ∑ p : Evaluator.BoundedReturns head pub mac bank mem ticks burst clock,
        boundedWeight pub lib ret fuel code p.val.val.2.1 p.val.val.2.2 (ticks-traceCost p.val.val.1) burst clock :=
  group_sum_for table N .dense pub bank mem ticks burst clock

variable {Team I : Type*} [Fintype Team] [Fintype I]
variable (pub : Team → Arg → Word w) (bank : Team → Bank w) (mem : Team → Memory w)
variable (ticks : Team → ℕ) (burst clock : ℕ)

local notation "Hist" => (fun t => Evaluator.Returns head (pub t) mac (bank t) (mem t))
local notation "Bounded" => (fun t => Evaluator.BoundedReturns head (pub t) mac (bank t) (mem t) (ticks t) burst clock)

/-- The distributed private assignment dictionary exhausts the product of
native team histories at the actual received routing words. The cutoffs are
checked on every distributed assignment and retained on every continuation. -/
theorem routed_product (dictionary : I ≃ ((t : Team) → Hist t))
    (time : ∀ i t, traceCost (dictionary i t).val.1 ≤ ticks t) (choose : 1 ≤ clock) :
    (∏ t, boundedWeight (pub t) lib ret fuel whole (bank t) (mem t) (ticks t) burst clock) =
      ∑ i : I, ∏ t, let p := dictionary i t
        boundedWeight (pub t) lib ret fuel code p.val.2.1 p.val.2.2 (ticks t-traceCost p.val.1) burst clock :=
  routed_product_for table N .dense pub bank mem ticks burst clock dictionary time choose

end FiniteEvaluator.OwnedContinuation

end BorderVNP
end Computability
end OAI
