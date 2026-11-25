import OAI.Hierarchy.TaggedWideFullGates
import OAI.Hierarchy.TaggedWideKeepBit

namespace OAI
/-! # The positive retention bit at the final installed paid memory address -/

noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.RAMMemory ProbeStage CoreBoard Tagged WideControlJoin
open ThreeFlat.RAM PhysicalProcedure
open ThreeFlat.Diagonal
open scoped Classical Fin.CommRing
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
  {κ A : ℝ} (x : WideParent κ A) (m ell short : ℕ) (u : ℝ→ℝ) (δ ξ : ℝ) (unitCost : ℕ)
local notation "h" => x.h
local notation "w" => x.w
local notation "W" => Native.wordBits x.h (2^v.W) Native.copies
local notation "g" => v.wideDated h w ell unitCost
local notation "l" => v.wideInstalledLayout x m ell short u δ ξ unitCost g
local notation "R" => v.wideInstalledRoot x
local notation "S" => v.wideInstalledSize x m ell unitCost g
local notation "U" => (l).pruneScratch+(l).pruneRows+1
local notation "C" => v.wideCorrectedSpillProgram h w ell unitCost v.maxBits R S ((g).romEnd R) ((g).workEnd S) U
local notation "fee" => v.wideCorrectedSpillTicks h w ell unitCost v.maxBits R S ((g).romEnd R) ((g).workEnd S) U
local notation "endPos" => v.wideCorrectedSpillEnd h w ell unitCost v.maxBits R S ((g).romEnd R) ((g).workEnd S) U
local notation "old" => v.widePrograms h w v.maxBits l
local notation "oldTicks" => v.wideProgramTicks h w v.maxBits l
variable (lim : v.FullGateRoom x m ell short u δ ξ unitCost)
local notation "G" => (v.wideFullGates x m ell short u δ ξ unitCost lim).2
local notation "addr" => (l).pruneScratch+(l).pruneRows
local notation "keepPin" => Gate.denseSeen addr
    ((Nat.lt_succ_self addr).trans_le (le_max_left U endPos)) (0 : Fin (W+1))
variable (E Qs D : Type) [Fintype E] [Fintype Qs] [Fintype D]

/-- One trivalent cell reads the observed low bit of the genuine
native membership word, after the suffix that publishes the spill turns. -/
def wideKeepNetwork : ThreeFlat.BitNetwork F
    (Fintype.card (SitePins E Qs D G)) :=
  KeepBit.network F (.inr (.inr (.inr keepPin)) : SitePins E Qs D G)

theorem wide_keep_cost :
    let n := v.wideKeepNetwork x m ell short u δ ξ unitCost lim E Qs D
    n.cells+n.internal=1 := rfl

/-- The word hypothesis is precisely the last conjunct of `formats_pruned`.
Every chronological assignment and numbering uses this same paid pin. -/
theorem wide_keep_flag (mid out : Memory W) (frame : ∀a,a<U→ out a=mid a) (keep : Prop)
    (stored : mid addr = if keep then 1 else 0) (ext : E→Bool) (sel : Qs→Bool)
    {J : Type} (ord : J≃D) (d : J→Bool) :
    ThreeFlat.Routing.TypedWiring.value
      (v.wideKeepNetwork x m ell short u δ ξ unitCost lim E Qs D)
      (Sum.elim ext (Sum.elim sel (Sum.elim (d ∘ ord.symm) ((G).terminal out)))) =
      if keep then 1 else 0 := by
  have bits : (mid addr).val=(decide keep).toNat := by
    have wpos := lim.original.word
    have two : 1<2^W := Nat.one_lt_two_pow (by omega)
    by_cases yes : keep
    · rw [stored,ite_eq_left yes]
      simpa [yes] using (show (1:Word W).val=1 by
        change 1 % 2^W=1
        exact Nat.mod_eq_of_lt two)
    · simp [stored,yes]
  have flag := v.wide_full_prior_flag x m ell short u δ ξ unitCost lim mid out frame
    addr (Nat.lt_succ_self _) (decide keep) bits
  unfold wideKeepNetwork
  rw [KeepBit.value]
  change (if (G).terminal out keepPin=true then (1:F) else 0)=_
  exact (congrArg (fun b : Bool => if b = true then (1 : F) else 0) flag).trans (by
    by_cases yes : keep <;> simp [yes])

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat

end
end OAI
