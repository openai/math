import OAI.Computability.VPVNP.PairSimulationLeafScalarLoad
import OAI.Computability.VPVNP.PrimedCounterVirtualFuel

/-!
# Scalar sources for initializing the virtual verifier's private stacks

Every scalar stack is either a width-bounded binary word or a unary tally.
Only the incident bit vector needs the field-copy subroutine. Addresses,
caps and bucket endpoints are the words actually seen by the auxiliary
site verifier.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.LeafStartup

open BurstRAM RAMTape LeafScalarLoad

variable {d e w k : ℕ}

/-- The loading mode, bit count and source word for each scalar input field of a virtual site.
The incident port starts empty for the later half-wire copy. -/
def source (x : VirtualSite.Input d e w) (pub : Fin k → Word w) : Field k → Mode × ℕ × Word w
  | .blank | .incident => (.tally,0,1)
  | .zeroWord => (.binary,w,0)
  | .address => (.binary,d,x.addrWord)
  | .addressWidth => (.tally,d,1)
  | .width => (.tally,w,1)
  | .slots => (.tally,4*2^e,1)
  | .bucket => (.tally,2^e,1)
  | .fuel => (.tally,x.fuel,1)
  | .siteCredit => (.tally,2*2^e-1,1)
  | .choices => (.tally,choiceBound e w x.fuel,1)
  | .cap => (.binary,w,⟨2^d*2^e,x.hc⟩)
  | .lower => (.binary,w,SiteEndpoints.startWord e w x.v x.hcap)
  | .upper => (.binary,w,SiteEndpoints.endWord e w x.v x.hcap)
  | .initial => (.binary,w,x.initialWord)
  | .siteWord => (.binary,w,x.addrWord)
  | .header => (.binary,w,x.headerWord)
  | .operand i => (.binary,w,pub i)

theorem scalarSpec (x : VirtualSite.Input d e w) (pub : Fin k → Word w) (f : Field k)
    (hs : f ≠ .incident) :
    let v := source x pub f
    payload v.1 v.2.2 v.2.1 = (fieldBits x pub f).reverse := by
  have hw : 0 < w := (by decide : 0 < 2).trans_le x.hw
  cases f <;> first
    | rfl
    | contradiction
    | exact payload_word _ _ rfl
    | (simp only [source, fieldBits, payload_tally _ hw, List.reverse_replicate])

/-- The slot tally and choice-stream length fit in machine words when staging the site's scalar
fields. -/
structure SourceFit (x : VirtualSite.Input d e w) : Prop where
  slots : 4*2^e < 2^w
  choices : choiceBound e w x.fuel < 2^w

theorem SourceFit.length {x : VirtualSite.Input d e w} (h : SourceFit x)
    (pub : Fin k → Word w) (f : Field k) : (source x pub f).2.1 < 2^w := by
  have he := Nat.two_pow_pos e
  have hw := Nat.lt_two_pow_self (n := w)
  have hd := x.hcap
  have hslots := h.slots
  have hchoices := h.choices
  have hF : x.fuel ≤ choiceBound e w x.fuel :=
    (Nat.le_add_right x.fuel w).trans (Nat.le_mul_of_pos_left _ (by positivity))
  cases f <;> dsimp only [source] <;> omega

end PairSimulation.LeafStartup

end VPVNP
end Computability
end OAI
