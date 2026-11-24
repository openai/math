import OAI.Computability.VPVNP.RAMTapeVirtualSite
import OAI.Computability.VPVNP.RAMTapeSiteProcessorPorts
import OAI.Computability.VPVNP.CursorIncidentExtension
import OAI.Computability.VPVNP.CursorInitialCheck
import OAI.Computability.VPVNP.PrimedCounterData

/-!
# Input stacks of an auxiliary RAM validator in a compression history

The auxiliary RAM has an entire word of header data at each address, including
the nomination words. Each input of the successor reader is taken from the
four half-wire buffers at the current vertex. Only the selected local incident
vector is used. The sender array extending it serves in the correctness proof.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.LeafStartup

open BurstRAM CursorNetwork CursorRouting RAMLayout RAMTape LiveProgram
open RAMTape.SiteProcessorPorts

variable {d e w k r : ℕ}

/-- The constant-zero expression at each public index used to fix the type of the auxiliary
site processor's ports. -/
abbrev expr (k : ℕ) : Fin k → PublicExpr := fun _ => .lit 0
/-- The private stack ports of a site processor with `r` machine registers and `k` public
operand positions. -/
abbrev Port (r k : ℕ) := SiteProcessorPorts.Port r (expr k)

/-- Names of the finite collection of public fields copied into a leaf's
private stacks. A blank port gets length zero. -/
inductive Field (k : ℕ) where
  | blank | zeroWord | address | addressWidth | incident | width | slots | bucket
  | fuel | siteCredit | choices | cap | lower | upper | initial | siteWord | header
  | operand (i : Fin k)
  deriving DecidableEq

/-- Port assignments are fixed by the two linked stack machines. -/
def field : Port r k → Field k
  | .inl (.inl (.isa (.pub i))) => .operand i
  | .inl (.inl (.credit (.budget .globalLeft))) => .zeroWord
  | .inl (.inr (.inl (.inr .fuel))) => .fuel
  | .inl (.inr (.inl (.inr .callCredit))) => .siteCredit
  | .inl (.inr (.inl (.inr .choiceBudget))) => .choices
  | .inl (.inr (.inl (.inr .globalCap))) => .cap
  | .inl (.inr (.inl (.inr .startCost))) => .lower
  | .inl (.inr (.inl (.inr .endCost))) => .upper
  | .inl (.inr (.inl (.inr .initial))) => .initial
  | .inl (.inr (.inl (.inr .addressWord))) => .siteWord
  | .inl (.inr (.inl (.inr .headerWord))) => .header
  | .inl (.inr (.inl (.inl (.inr (.shape .word))))) => .width
  | .inl (.inr (.inl (.inl (.inr (.shape .blocks))))) => .slots
  | .inl (.inr (.inl (.inl (.inr .remaining)))) => .slots
  | .inl (.inr (.inl (.inl (.inr .zeros)))) => .zeroWord
  | .inl (.inr (.inl (.inl (.inl (.inl .address))))) => .address
  | .inl (.inr (.inl (.inl (.inl (.inl .incident))))) => .incident
  | .inl (.inr (.inl (.inl (.inl (.inr (.inl .bucket)))))) => .bucket
  | .inl (.inr (.inl (.inl (.inl (.inr (.inr .address)))))) => .addressWidth
  | _ => .blank

/-- Number of choice bits reserved for the site validator, twice its bucket size times the sum
of its fuel and word width. -/
def choiceBound (e w fuel : ℕ) := 2 * 2^e * (fuel+w)

/-- Encode one input field as its stack bits, using binary words, unary counts, the site's
incident vector or the selected public operand. -/
def fieldBits (x : VirtualSite.Input d e w) (pub : Fin k → Word w) : Field k → List Bool
  | .blank => []
  | .zeroWord => wordBits (0 : Word w)
  | .address => wordBits x.v
  | .addressWidth => List.replicate d true
  | .incident => List.ofFn (RAMLayout.incidentBits x.sends x.v)
  | .width => List.replicate w true
  | .slots => List.replicate (4*2^e) true
  | .bucket => List.replicate (2^e) true
  | .fuel => List.replicate x.fuel true
  | .siteCredit => List.replicate (2*2^e-1) true
  | .choices => List.replicate (choiceBound e w x.fuel) true
  | .cap => wordBits (⟨2^d*2^e,x.hc⟩ : Word w)
  | .lower => wordBits (SiteEndpoints.startWord e w x.v x.hcap)
  | .upper => wordBits (SiteEndpoints.endWord e w x.v x.hcap)
  | .initial => wordBits x.initialWord
  | .siteWord => wordBits x.addrWord
  | .header => wordBits x.headerWord
  | .operand i => wordBits (pub i)

/-- Assign each processor port the stack encoding of its input field for the specified site and
public operands. -/
def bank (r : ℕ) (x : VirtualSite.Input d e w) (pub : Fin k → Word w) : Stacks (Port r k) :=
  fieldBits x pub ∘ field

section Cursor

variable {L : PrimedInputRAM.Lengths} {n a H s : ℕ} {Q : PrimedInputRAM.Layout L n a H w}

/-- Local sender arrays from independently supplied half-wires. End clamps
come from the decoder at the two chain endpoints. -/
def sends (v : Position d) (buf : Buffers d (2^e) w) : SendArrays d (2^e) w :=
  localExtension v.2
    (fun s j => readBuffer buf ⟨.outgoing ((systemMask s).val.testBit v.1.val), s, j⟩)
    (fun s j => readBuffer buf ⟨.incoming ((systemMask s).val.testBit ((finRotate d).symm v.1).val), s, j⟩)

theorem sends_incident (v : Position d) (buf : Buffers d (2^e) w) :
    RAMLayout.incidentBits (sends v buf) v.2 = incidentBuffer v buf :=
  localExtension_incident v.2 _ _

/-- The auxiliary call graph receives its complete header word and the exact
private cutoff of the finite coefficient counter. -/
noncomputable def auxiliary (D : PrimedCounter.Data Q s) (hw : 2 ≤ w) (hc : 2^d*2^e < 2^w)
    (v : Position d) (buf : Buffers d (2^e) w) : VirtualSite.Input d e w where
  fuel := D.fuel
  v := v.2
  initialWord := 0
  headerWord := D.initial v.2
  sends := sends v buf
  hw := hw
  hc := hc

theorem auxiliary_incident (D : PrimedCounter.Data Q s) (hw : 2 ≤ w) (hc : 2^d*2^e < 2^w)
    (v : Position d) (buf : Buffers d (2^e) w) :
    fieldBits (auxiliary D hw hc v buf) D.pub .incident = List.ofFn (incidentBuffer v buf) :=
  congrArg List.ofFn (sends_incident v buf)

end Cursor
end PairSimulation.LeafStartup

end VPVNP
end Computability
end OAI
