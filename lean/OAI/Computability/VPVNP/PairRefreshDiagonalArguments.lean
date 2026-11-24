import OAI.Computability.VPVNP.PairRefreshDiagonal
import OAI.Computability.VPVNP.CompressorRefreshMapOperands

/-!
# The refresh diagonal checker on the actual node buffers

For each direction the child contributes its original slot at the promoted
port. The parent contributes the segment at the recorded offset in its
external slot. The checked bits are exactly the diagonal arguments of the
degree-refresh local kernel. Independent parent and child arguments suffice.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.RefreshDiagonal

open Compression Compression.Refresh Compression.DegreeRefresh CompressorRecords
open NodeArguments RefreshMapOperands NetworkKernel
open BurstRAM.PrivateRAM PrimedCounter.GuessWord
open scoped Fin.CommRing

variable {a b l dH w pcs regs params : ℕ}
variable (X : State a (a+l)) (v : (X.Base × BitWord l) × Fin (2^a))
variable (P : SlotGraph (Fin (2^a)) dH) (hD : 1 < 2^a) (hd : dH+1 ≤ 2^b)
variable (internal : X.Base × BitWord l → Fin (2^a) × Fin dH → ℕ)

local notation "G" => splitSlots X
local notation "widths" => groupedWidths (bitWordFinEquiv a) (splitWidths X)
local notation "matching" => oldPortMatching G (bitWordFinEquiv a)
local notation "Y" => newState X P hD hd internal

/-- Natural operand addresses reduced to native private RAM words. The
incoming segment uses the offset of its actual source in the old bundle. -/
noncomputable def argumentPointers (A : Arena) (child parent : ℕ) : Pointers w where
  oldOut := (A.fieldAddress X (oldSite X v) child false v.2 : ℕ)
  externalOut := (A.fieldAddress Y (promotedSites v) parent false (refreshSlots hd (.inl 0)) +
    (PortRefresh.outgoingRecord G (bitWordFinEquiv a) (splitWidths X) (v,v.2)).offset : ℕ)
  oldIn := (A.fieldAddress X (oldSite X v) child true v.2 : ℕ)
  externalIn := (A.fieldAddress Y (promotedSites v) parent true (refreshSlots hd (.inl 0)) +
    (PortRefresh.incomingRecord G (bitWordFinEquiv a) (splitWidths X) (v,v.2)).offset : ℕ)

private theorem encode_bit (u : Bool) : PrimedInputRAM.encodeBit w u = PrivateFields.bitValue w u := rfl

/-- Native execution on a selected refresh node's actual private half-buffers.
The branch taken agrees with the integer diagonal multiplier of the kernel. -/
theorem compare_arguments {M : Machine w pcs regs params} {pc first second : Fin 7 → Fin pcs}
    {reg : Fin 10 ↪ Fin regs} {yes no : Fin pcs} (link : Linked M pc first second reg yes no)
    (A : Arena) (child parent : ℕ) (x : X.network.Half (oldSite X v))
    (z : (Y).network.Half (promotedSites v)) (c : Config w pcs regs) (hc : c.pc = pc 0)
    (hx : NodeFields A child X _ x c.privateMem) (hz : NodeFields A parent Y _ z c.privateMem)
    (ready : (argumentPointers X v P hD hd internal A child parent).Ready reg c
      (widths (v,v.2)) (widths ((matching).symm (v,v.2))))
    (h₁ : widths (v,v.2) < 2^w) (h₂ : widths ((matching).symm (v,v.2)) < 2^w) :
    ∃ out, Prefix M c (List.replicate (7*(widths (v,v.2)+widths ((matching).symm (v,v.2)))+9)
      .tick) out ∧ out.pc = (if portDiagonal matching widths v.1 v.2 (oldHalf X v x)
        (segments X v P hD hd internal z) = (1 : ℤ) then yes else no) ∧
      out.privateMem = c.privateMem ∧ out.persistent = c.persistent ∧
      ∀ j, j ∉ Set.range reg → out.reg j = c.reg j := by
  let q := argumentPointers X v P hD hd internal A child parent (w := w)
  apply compare_portDiagonal matching widths v.1 v.2 (oldHalf X v x) (segments X v P hD hd internal z)
    q.oldOut q.externalOut q.oldIn q.externalIn link c hc ready.1 ready.2 _ _ h₁ h₂
  · constructor
    · intro j
      simpa only [q, argumentPointers, Nat.cast_add, encode_bit] using old_out_read X v A child x c.privateMem hx v.2 j
    · intro j
      simpa only [q, argumentPointers, Nat.cast_add, encode_bit] using
        external_out_read X v P hD hd internal A parent z c.privateMem hz v.2 j
  · constructor
    · intro j
      simpa only [q, argumentPointers, Nat.cast_add, encode_bit] using old_in_read X v A child x c.privateMem hx v.2 j
    · intro j
      simpa only [q, argumentPointers, Nat.cast_add, encode_bit] using
        external_in_read X v P hD hd internal A parent z c.privateMem hz v.2 j

end PairSimulation.RefreshDiagonal

end VPVNP
end Computability
end OAI
