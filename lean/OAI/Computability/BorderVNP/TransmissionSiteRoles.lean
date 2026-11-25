import OAI.Computability.BorderVNP.TransmissionSiteWiring
import OAI.Computability.BorderVNP.TeamSiteProcessorRoles

/-! # Real owner roles in the pinned processor literal and its wired interior stream -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction.ProcessorSlots

open VPVNP BurstRAM TeamTapeHandoff TeamSite.Processor

variable {r k reg w e a : ℕ}

/-- Physical endpoint flags from the processor ordinal. -/
def first (j : Fin r) : Bool := decide (j.val = 0)

/-- The right boundary of the real processor range. -/
def last (j : Fin r) : Bool := decide (j.val+1 = r)

/-- The first owner takes its incoming frame from its public literal. Other owners receive
the raw, unrestricted handoff from the preceding processor. -/
def ingress (start : Frame w reg) (int : Wires.Edge r reg w e (w+1) → Bool) (j : Fin r) : List Bool :=
  if j.val=0 then start.bits else Wires.frameInput (Wires.edgeEquiv int).1 true j

/-- Actual proposed outgoing frame, empty at the last processor. -/
def egress (int : Wires.Edge r reg w e (w+1) → Bool) (j : Fin r) : List Bool :=
  Wires.frameInput (Wires.edgeEquiv int).1 false j

/-- Remaining interior fields after both physical register messages have been consumed. -/
def sortTail (int : Wires.Edge r reg w e (w+1) → Bool) (j : Fin r) : List Bool :=
  TeamTapeInputRoute.ownerBits (Wires.edgeEquiv int).2 (Wires.primary j) (Wires.secondary j) ++
    List.replicate (Wires.innerWidth r reg w e (w+1) -
      (Wires.activeSlots j : List (Option (Wires.Edge r reg w e (w+1)))).length) false

/-- Each incoming frame has the true register bank width, regardless of the handoff bits. -/
theorem ingress_size (start : Frame w reg) (int : Wires.Edge r reg w e (w+1) → Bool) (j : Fin r) :
    (ingress start int j).length = TeamSite.Layout.frameSize reg w := by
  by_cases h : j.val = 0
  · simp [ingress,h,Frame.bits_length,TeamSite.Layout.frameSize]
  · simp [ingress,h,Wires.frameInput,Wires.frameIndex,show 0 < j.val by omega,
      TeamSite.Layout.frameSize,Wires.frameWidth]

/-- Every processor with a successor receives a full candidate outgoing frame. -/
theorem egress_size (int : Wires.Edge r reg w e (w+1) → Bool) (j : Fin r) (hl : last j = false) :
    (egress int j).length = TeamSite.Layout.frameSize reg w := by
  have h : j.val+1 < r := by
    have := j.isLt
    simp [last] at hl
    omega
  simp [egress,Wires.frameInput,Wires.frameIndex,h,TeamSite.Layout.frameSize,Wires.frameWidth]

/-- The final owner has no outgoing frame. -/
theorem egress_at_last (int : Wires.Edge r reg w e (w+1) → Bool) (j : Fin r) (hl : last j = true) :
    egress int j = [] := by
  have h : j.val+1 = r := of_decide_eq_true hl
  simp [egress,Wires.frameInput,Wires.frameIndex,h]

/-- The handoff decoder's role-dependent stream is exactly the wired contraction stream. -/
theorem ownerStream_roles (start : Frame w reg) (int : Wires.Edge r reg w e (w+1) → Bool) (j : Fin r) :
    ownerStream int j = incidentBytes (first j) (last j) (ingress start int j) (egress int j)
      (sortTail int j) := by
  by_cases hf : j.val = 0 <;> by_cases hl : j.val+1 = r <;>
    simp [ownerStream,incidentBytes,first,last,ingress,egress,sortTail,hf,hl,Wires.frameInput,
      Wires.frameIndex,List.append_assoc]
  all_goals rintro rfl; rfl

/-- The unconsumed literal after reading both endpoint flags and the optional first frame.
Its head carries the real metadata required by the owner sorter. -/
def metadataTail (pub : Fin k → Word w) (H limit burst : Word w) (start : Frame w reg)
    (j : Fin r) (e n : ℕ) (advice : Bool) (free : Fin a → Bool) : List Bool :=
  TeamTapeInputRoute.metadataBits n e (w+1) (Wires.primary j) (Wires.secondary j) ++
    List.replicate (prefixCapacity r k reg w n-(sitePrefix pub H limit burst start j e n).length) false ++
      [advice] ++ List.ofFn free

/-- The public loader and role decoder consume their actual contiguous bytes. -/
theorem payload_roles (pub : Fin k → Word w) (H limit burst : Word w) (start : Frame w reg)
    (j : Fin r) (e n : ℕ) (advice : Bool) (free : Fin a → Bool)
    (int : Wires.Edge r reg w e (w+1) → Bool) (tail : List Bool) :
    payload pub H limit burst start j e n advice free ++ tail =
      TeamPublicWords.bytes (TeamSite.Layout.parameters pub H limit burst) ++
        roleBytes (first j) (last j) (ingress start int j)
          (metadataTail pub H limit burst start j e n advice free ++ tail) := by
  by_cases h : j.val = 0 <;> simp [payload,sitePrefix,roleBytes,first,last,ingress,metadataTail,h,List.append_assoc]

end TeamContraction.ProcessorSlots

end BorderVNP
end Computability
end OAI
