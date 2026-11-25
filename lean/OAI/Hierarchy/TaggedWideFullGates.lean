import OAI.Hierarchy.TaggedWideAppendedGates
import OAI.Hierarchy.TaggedWideInstalledLayout
import OAI.Hierarchy.ProbeFixedWideCorrectedSpill

namespace OAI
/-! # The two native parent gates, including the final dated spill turn controls -/
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
def wideFullPrograms := v.appendedPrograms h w v.maxBits l C
def wideFullTicks := v.appendedTimes h w v.maxBits l fee
def wideFullEnd := max U endPos
abbrev FullGateRoom := v.AppendedRoom h w v.maxBits l C fee endPos S

variable (lim : v.FullGateRoom x m ell short u δ ξ unitCost)
def wideFullGates := v.appendedGates h w v.maxBits l C fee endPos S lim
local notation "G" => v.wideFullGates x m ell short u δ ξ unitCost lim
local notation "endAll" => v.wideFullEnd x m ell short u δ ξ unitCost

theorem wide_full_first : (G).1=(v.wideGates h w v.maxBits l S lim.original).1 := rfl
theorem wide_full_end : U≤(G).2.u := le_max_left ..
theorem wide_full_addr (i : Fin endAll) : ((G).2.addr i).val=i.val := rfl

theorem wide_full_run (header : ℕ→Word W) (mid out : Memory W)
    (first : (old).2.Exec (initialMemory S header) mid (oldTicks).2) (last : (C).Exec mid out fee) :
    (G).2.Ran header out :=
  v.appended_paid_run h w v.maxBits l C fee endPos S lim header mid out first last

theorem wide_full_prior_word (mid out : Memory W) (frame : ∀a,a<U→ out a=mid a)
    (a : ℕ) (inside : a<U) (j : Fin W) :
    (G).2.terminal out (Gate.denseSeen a (inside.trans_le (le_max_left U endPos)) j.castSucc)=
      TraceWords.bits (mid a) j :=
  v.appended_prior_word h w v.maxBits l C fee endPos S lim mid out frame a inside j

theorem wide_full_prior_flag (mid out : Memory W) (frame : ∀a,a<U→ out a=mid a)
    (a : ℕ) (inside : a<U) (b : Bool) (has : (mid a).val=b.toNat) :
    (G).2.terminal out (Gate.denseSeen a (inside.trans_le (le_max_left U endPos)) 0)=b :=
  v.appended_prior_flag h w v.maxBits l C fee endPos S lim mid out frame a inside b has

theorem wide_full_prior_high (out : Memory W) (a : ℕ) (inside : a<U) :
    (G).2.terminal out (Gate.denseSeen a (inside.trans_le (le_max_left U endPos)) (Fin.last W))=false :=
  v.appended_prior_high h w v.maxBits l C fee endPos S lim out a inside

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
