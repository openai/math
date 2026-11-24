import OAI.Computability.VPVNP.RAMTapeSiteTerminal
import OAI.Computability.VPVNP.RAMTapeSortStages

/-! # The shared bank for sorting and checking the predecessor records -/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.SitePost

open BurstRAM RAMBoundary Boundary

/-- Additional post-pass ports for the previous boundary record, sent boundary record, and
unary address width. -/
inductive Extra where | previous | sent | addressWidth deriving DecidableEq
instance : Fintype Extra := derive_fintype% _
/-- Combined bank for the sorting stages and the boundary-record checks. -/
abbrev Port := SortStages.Port ⊕ Extra

/-- Extend a sorting bank with serialized predecessor and sent records and the unary address
width. -/
def bank {w : ℕ} (d : ℕ) (prev sent : RawSlot w) (s : Stacks SortStages.Port) : Stacks Port :=
  Sum.elim s fun
    | .previous => recordBytes prev
    | .sent => recordBytes sent
    | .addressWidth => List.replicate d true

private def row (p : SortRow.Port) : Port := .inl (.inr (.inl (.inl (.inl p))))

/-- Port carrying the serialized block currently being sorted or checked. -/
def blockPort := row .current
/-- Unary word-width port shared by the sorting row and boundary scanner. -/
def widthPort := row .width
/-- Port holding the unary number of slots in the local sorting block. -/
def slotsPort : Port := .inl (.inr (.inr ()))
/-- Port collecting the validity flags produced during sorting. -/
def flagPort := row .flags
/-- Port holding the site address bits for the sorting pass. -/
def addressPort : Port := .inl (.inr (.inl (.inl (.inr .site))))
/-- Port carrying the remaining incident bits to the sorting row’s receive stream. -/
def incidentPort := row .crossReceive
/-- Unary site address width retained for initializing the sorting schedule. -/
def addressWidthPort : Port := .inr .addressWidth
/-- Port containing the serialized incoming predecessor record. -/
def previousPort : Port := .inr .previous
/-- Port containing the serialized record sent at the outgoing boundary. -/
def sentPort : Port := .inr .sent

/-- Connect the final boundary scanner to the sorted block, endpoint records, word width, saved
bits, and slot count. -/
def boundaryPorts : Boundary.Port → Port
  | .block => blockPort
  | .previous => previousPort
  | .sent => sentPort
  | .width => widthPort
  | .widthBack => row .widthBack
  | .saved => row .saved
  | .slots => slotsPort

private def scanTmp := row .lookup

/-- Run the final site-boundary decision and check the flags collected during sorting. -/
def terminal : FiniteRoutine Port := SiteTerminal.routine boundaryPorts addressPort scanTmp flagPort

variable {w h d : ℕ}

/-- Sorting and boundary bank at the initial schedule position, with the full incident tail
available. -/
def initialBank (v : Word d) (prev sent : RawSlot w) (x : SortReplay.State h w) (tail : List Bool) :=
  bank d prev sent (SortSchedule.bank (SortStages.data v x tail) (h+d) 0 0)

/-- Sorting and boundary bank at the final schedule position, with the incident tail exhausted. -/
def finalBank (v : Word d) (prev sent : RawSlot w) (x : SortReplay.State h w) :=
  bank d prev sent (SortSchedule.bank (SortStages.data v x []) 0 (h+d) 0)

private theorem boundaryPorts_inj : Function.Injective boundaryPorts := by decide
private theorem flags_disjoint : ∀ j, boundaryPorts j ≠ flagPort := by decide

theorem terminal_count (v : Word d) (prev sent : RawSlot w) (y : SortReplay.State h w)
    (c : ℕ → Stacks Port → ℕ) (extra : ℕ) :
    terminal.body.count c (extra+SiteTerminal.steps d w (2^h) v y.2) (finalBank v prev sent y) =
      (decision (decide (0<v.val)) (decide (v.val+1<2^d)) prev sent (List.ofFn y.1) && y.2.all id).toNat := by
  have ht := SiteTerminal.count boundaryPorts boundaryPorts_inj addressPort scanTmp flagPort
    (by decide) flags_disjoint prev sent (List.ofFn y.1) v (finalBank v prev sent y) rfl rfl
    (by intro j; cases j <;> first | rfl | simp [boundaryPorts, slotsPort, finalBank, bank,
        SortSchedule.bank, SortStages.data, SortOneStage.data, SortOneStage.bank, Boundary.store,
        SiteTerminal.inputs]) c extra
  simpa only [List.length_ofFn, show finalBank v prev sent y flagPort = y.2 from rfl, terminal] using ht

theorem terminal_total (v : Word d) (prev sent : RawSlot w) (y : SortReplay.State h w)
    (c : ℕ → Stacks Port → Prop) (extra : ℕ) :
    terminal.body.AllStops c (extra+SiteTerminal.steps d w (2^h) v y.2) (finalBank v prev sent y) := by
  have ht := SiteTerminal.total boundaryPorts boundaryPorts_inj addressPort scanTmp flagPort
    (by decide) flags_disjoint prev sent (List.ofFn y.1) v (finalBank v prev sent y) rfl rfl
    (by intro j; cases j <;> first | rfl | simp [boundaryPorts, slotsPort, finalBank, bank,
        SortSchedule.bank, SortStages.data, SortOneStage.data, SortOneStage.bank, Boundary.store,
        SiteTerminal.inputs]) c extra
  simpa only [List.length_ofFn, show finalBank v prev sent y flagPort = y.2 from rfl, terminal] using ht

end RAMTape.SitePost

end VPVNP
end Computability
end OAI
