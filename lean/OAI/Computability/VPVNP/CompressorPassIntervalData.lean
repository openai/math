import OAI.Computability.VPVNP.CompressorPrefixFrames
import OAI.Computability.VPVNP.CompressorWorkspaceCore

/-! # Deterministic and selecting intervals on the physical block program -/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.ScheduledTrace

open BurstRAM BranchSegments SourceBankFrame BlockPlanner

variable {w : ℕ}

/-- A forced interval of actual workspace-framed calls, with the original
inner reports at their computational clock. -/
structure QuietInterval (A : Script) (pub : Fin 11 → Word w) (cap small : ℕ)
    (st : Option (Word w)) (m : Memory w) where
  /-- Executed workspace-framed segment for an interval whose source calls have empty choice
  tapes. -/
  segment : Segment (OnlineWorkspace.program A.plan pub) (cap+24) st m
  quiet : segment.bits = List.replicate segment.bits.length []
  stable : Stable ((pub 2).val+6) m segment.logs
  state : segment.state = some 0
  /-- Inner source execution at the smaller clock underlying the deterministic workspace-framed
  interval. -/
  source : OnlineWorkspace.Core A pub segment small

/-- One physical selector row, indexed by the mathematical term. -/
structure SelectorInterval (A : Script) (pub : Fin 11 → Word w) (cap small : ℕ)
    (st : Option (Word w)) (m : Memory w) (I : Type*) where
  /-- Branch cut whose indexed segments represent the alternatives of the native selector
  interval. -/
  cut : Cut (OnlineWorkspace.program A.plan pub) (cap+24) st m I
  frame : cut.PrefixFrame ((pub 2).val+6)
  state : ∀ i, (cut.part i).state = some 0
  /-- Inner source execution for each branch of the selector cut at the prescribed source
  clock. -/
  source : ∀ i, OnlineWorkspace.Core A pub (cut.part i) small

end CompressorRecords.ScheduledTrace

end VPVNP
end Computability
end OAI
