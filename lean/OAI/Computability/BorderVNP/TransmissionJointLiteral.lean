import OAI.Computability.BorderVNP.TransmissionReferencePacket
import OAI.Computability.BorderVNP.TransmissionSiteStrings
import OAI.Computability.BorderVNP.GeometryAdviceLiteral

/-! # Joint placement of self-reading program, wide advice and private site descriptions

The processor's existing startup parser fixes every bit through the distributed advice
position. The remaining space up to the reserved half-tail carries two public stripes.
The half-tail contains only the concatenated original private site descriptions.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction.ProcessorSlots

open VPVNP BurstRAM UniversalMachine TeamTapeHandoff RoutingISA RoutingISA.Pins
open Packing.Directory

variable {pc reg k routines m g R r w a d : ℕ} {Q Γ : Type} [Fintype Q]
variable (P : TeamOpcode.Program pc reg k routines) (lib : Fin routines → TeamSite.Macro Q Γ m g)

/-- The start of the free part of a complete processor literal, immediately following
the single fixed advice bit. -/
noncomputable def freeStart (r w n : ℕ) := adviceOffset P lib r w n+1

/-- The fixed processor's prefix (including its code) consumes this many physical
positions before the free bits are assigned. -/
theorem freeStart_eq (n : ℕ) :
    freeStart P lib r w n =
      entryLiteral (TeamSite.Processor.machine P lib) (w+1) n (prefixCapacity r k reg w n+1) := by
  simp only [freeStart,adviceOffset,entryLiteral,Nat.add_assoc]

variable (S : SiteData R r reg k w a)

/-- The complete physical row presents exactly the fixed startup fields followed by
all free bits. The split uses the machine's program encoding and actual parser widths. -/
theorem literal_split (link n e : ℕ) (fit : Fits P lib r w a R link n e) (u : Fin (R+1)) (j : Fin r)
    (pin : Fin d → Bool) (ext : Exterior R r link → Bool) (ibase hbase starbase : ℕ) :
    let G := wiring P lib S d link n e fit
    let F := G.processorFields u pin ext ibase hbase starbase
    ∃ pref : List Bool, pref.length = freeStart P lib r w n ∧ F.literal j = pref ++ List.ofFn (S.free u j) := by
  intro G F
  let pr := TeamSite.Processor.machine P lib
  let stride := entryStride pr (w+1) n (prefixCapacity r k reg w n+1+a) R link
  let interior := Wires.innerWidth r reg w e (w+1)
  let control := sitePrefix (S.publicWords u) S.block S.limit S.burst (S.start P u) j e n
  let first := programPrefix pr ++ TeamTapeInput.parameters (TeamTapeInput.digits n stride)
    (TeamTapeInput.digits n interior) ++ TeamTapeInput.Entry.setupBits (w+1) n (j.val*stride) (2^e)
  let cap := prefixCapacity r k reg w n
  refine ⟨first ++ control ++ List.replicate (cap-control.length) false ++ [S.advice u j], ?_, ?_⟩
  · have hc : control.length ≤ cap := sitePrefix_length_le ..
    simp only [List.length_append,List.length_replicate,List.length_cons,List.length_nil,first,
      TeamTapeInput.length_parameters,length_setupBits,freeStart,adviceOffset]
    dsimp only [cap,pr] at *
    unfold cutWidth
    omega
  · change programPrefix pr ++ List.ofFn (cutTail n stride interior
      (entryTail (w+1) n (j.val*stride) (2^e) (S.siteBits P n e u j))) = _
    rw [ofFn_cutTail,ofFn_entryTail,SiteData.siteBits,ofFn_payloadBits]
    simp only [first,control,cap,payload,List.append_assoc]

/-- An absolute offset within the free suffix is read back from exactly that bit
of the source function in the processor's wired literal. -/
theorem literal_free_get (link n e : ℕ) (fit : Fits P lib r w a R link n e)
    (u : Fin (R+1)) (j : Fin r) (pin : Fin d → Bool) (ext : Exterior R r link → Bool)
    (ibase hbase starbase : ℕ) (z : Fin a) :
    let F := (wiring P lib S d link n e fit).processorFields u pin ext ibase hbase starbase
    (F.literal j)[freeStart P lib r w n+z.val]? = some (S.free u j z) := by
  intro F
  obtain ⟨pref,hl,eq⟩ := literal_split P lib S link n e fit u j pin ext ibase hbase starbase
  calc
    _ = (pref ++ List.ofFn (S.free u j))[freeStart P lib r w n+z.val]? :=
      congrArg (fun xs : List Bool => xs[freeStart P lib r w n+z.val]?) eq
    _ = _ := by
      rw [← hl, List.getElem?_append_right (by omega),Nat.add_sub_cancel_left]
      simp

/-- Optional boot stripe before the shared geometry stripe. Its entries and the geometry
payload are serialized in row-major processor order. Each stripe is zero-padded. -/
def jointHead (boot geom : GeometryAdvice.Stripe) (bootBits geomBits : List Bool)
    (proc addr : ℕ) : Bool :=
  let piece (s : GeometryAdvice.Stripe) (xs : List Bool) :=
    if s.offset ≤ addr ∧ addr < s.offset+s.width then xs[proc*s.width+(addr-s.offset)]?.getD false
    else false
  if addr < geom.offset then piece boot bootBits else piece geom geomBits

/-- Pin the two advice stripes, H*, and every original site description at once.
The supplied site control data fixes only the native startup arguments and registers.
The free and distributed advice bits of the result are determined by the packets. -/
def SiteData.joint (S : SiteData R r reg k w a) (D : Packing.Directory.Layout)
    (start : ℕ) (pack : Fin (R+1) → ReferencePacket w d) (boot geom : GeometryAdvice.Stripe)
    (bootBits geomBits : Fin (R+1) → List Bool) (strings : Fin D.entries → Fin D.description → Bool) :
    SiteData R r reg k w a :=
  { S.withPacket pack with
    free := fun u p z =>
      D.literalBit (fun _ => jointHead boot geom (bootBits u) (geomBits u)) strings u.val p.val (start+z.val) }

/-- Reads in the reserved tail do not depend on the head's public packet. -/
theorem literalBit_tail (D : Packing.Directory.Layout) (head other : ℕ → ℕ → ℕ → Bool)
    (strings : Fin D.entries → Fin D.description → Bool) (team proc addr : ℕ)
    (h : D.literal-D.literal/2 ≤ addr) :
    D.literalBit head strings team proc addr = D.literalBit other strings team proc addr := by
  simp only [Layout.literalBit,ite_eq_right (not_lt_of_ge h)]

end TeamContraction.ProcessorSlots

end BorderVNP
end Computability
end OAI
