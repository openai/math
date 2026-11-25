import OAI.Computability.BorderVNP.TeamSitePorts
import OAI.Computability.BorderVNP.TeamPublicStartup
import OAI.Computability.BorderVNP.TeamTapeInputRouteProcessor

/-! # Shared physical port layout of a signed processor

The raw input parser and the RAM callbacks use the same record buffer. Public words
are loaded directly into the ISA and meter destinations. Interior fields and the
first processor's public register frame are cut from their actual source streams.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamSite.Layout

open VPVNP BurstRAM RAMTape

variable {r k d w : ℕ}

/-- Physical port families of the entire processor, including both virtual sorting lanes. -/
inductive Port (r k d : ℕ) where
  | route (p : TeamTapeInputRoute.Verify.Port)
  | work (p : TeamSite.Port r k d)
  | incoming | outgoing | width | tag | pc | tmp | payload
  | frameWidth | unused
  deriving DecidableEq, Fintype

/-- Parser, initialization emitter and physical routing bank. -/
abbrev entry (p : TeamTapeInput.Entry.Port) : Port r k d := .route (.inr (.entry p))

/-- All initialized and runtime probe records share these exact stacks. -/
abbrev buffer (p : RecordBuffer.Port) : Port r k d := entry (.inr (.emit (.buffer p)))

/-- RAM simulation uses the input parser's buffer and separate registers everywhere else. -/
def site : TeamSite.Port r k d → Port r k d
  | .burst (.probe (.buffer p)) => buffer p
  | p => .work p

/-- Replacing the buffer by its physical alias preserves distinct work locations. -/
theorem site_injective : Function.Injective (site (r := r) (k := k) (d := d)) := by
  let back (p : Port r k d) : TeamSite.Port r k d := match p with
    | .route (.inr (.entry (.inr (.emit (.buffer i))))) => TeamSite.probe (.buffer i)
    | .work i => i
    | _ => .high
  apply Function.LeftInverse.injective (g := back)
  rintro (i|i|i|_|_|i) <;> first | rfl | (cases i <;> first | rfl | (rename_i j; cases j <;> rfl))

/-- The physical stream at the beginning of the local input tape. -/
abbrev input : Port r k d := entry (.inl (.cut .input))

/-- Remainder of the public literal before the exterior inputs and pin positions. -/
abbrev metadata : Port r k d := .route (.inr TeamTapeInputRoute.metadata)

/-- The unmodified team interior segment cut from the raw input. -/
abbrev incident : Port r k d := .route (.inr TeamTapeInputRoute.source)

/-- The eight words initialize the block and global caps, burst cap, persistent zero
registers, and the three literal meter registers. All belong to the pinned public prefix. -/
def headerWords (H limit max : Word w) : Fin 8 → Word w := ![H,limit,max,0,0,0,1,0]

/-- RAM parameters followed by the startup controller's public constants. -/
def parameters (pub : Fin k → Word w) (H limit max : Word w) : Fin (k+8) → Word w :=
  Fin.append pub (headerWords H limit max)

private def clockPort (p : TeamLocalClock.Port r k) : Port r k d := .work (.clock p)

private def headerPort : Fin 8 → Port r k d :=
  ![clockPort (.meter (.reg 0)),clockPort (.meter (.reg 1)),clockPort .maxBurst,
    clockPort (.isa .persistent),clockPort (.meter .persistent),clockPort (.meter (.reg 3)),
    clockPort (.meter (.reg 4)),clockPort (.meter (.reg 5))]

/-- Physical destinations of all the words read by the fixed startup routine. -/
def paramPort : Fin (k+8) → Port r k d :=
  Fin.append (fun i => clockPort (.isa (.pub i))) headerPort

/-- One physical installation of the literal-word decoder. -/
def publicPort : TeamPublicStartup.Port (k+8) → Port r k d
  | .inl p => entry p
  | .inr (.pub i) => paramPort i
  | .inr .input => .unused
  | .inr .width => .width
  | .inr .tmp => .tmp

private def backHeader (p : TeamLocalClock.Port r k) : Option (Fin (k+8)) :=
  match p with
  | .isa (.pub i) => some (i.castAdd 8)
  | .meter (.reg i) => some ((![0,1,0,5,6,7] i : Fin 8).natAdd k)
  | .maxBurst => some ((2 : Fin 8).natAdd k)
  | .isa .persistent => some ((3 : Fin 8).natAdd k)
  | .meter .persistent => some ((4 : Fin 8).natAdd k)
  | _ => none

/-- The physical decoder has exactly one destination per fixed public register. -/
theorem publicPort_injective : Function.Injective (publicPort (r := r) (k := k) (d := d)) := by
  let back (p : Port r k d) : TeamPublicStartup.Port (k+8) := match p with
    | .route (.inr (.entry q)) => .inl q
    | .width => .inr .width
    | .tmp => .inr .tmp
    | .work (.clock q) => (backHeader q).elim (.inr .input) (fun i => .inr (.pub i))
    | _ => .inr .input
  apply Function.LeftInverse.injective (g := back)
  rintro (p | p)
  · rfl
  · cases p with
    | pub i =>
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · simp [publicPort,paramPort,Fin.append,clockPort,back,backHeader]
      · fin_cases j <;> simp [publicPort,paramPort,Fin.append,headerPort,clockPort,back,backHeader]
    | _ => rfl

end TeamSite.Layout

end BorderVNP
end Computability
end OAI
