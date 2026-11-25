import OAI.Computability.BorderVNP.DiagonalReturnedFinishWindow
import OAI.Computability.BorderVNP.RoutingISASignedReaderKeepActual
import OAI.Computability.BorderVNP.DiagonalNativeReaderClock

/-! # Uniform phase windows of actual local post-call receipts -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction.JointHeader.PositiveFields

open VPVNP.BurstRAM RoutingISA RoutingISA.Evaluator RoutingISA.Evaluator.ScheduleClock
open DiagonalTallyRAM DiagonalTallyMaterialize DiagonalTallyCellReports DiagonalResidueRAM
open TeamContraction.ProcessorSlots RoutingISA.SignedTaskArena

variable {teams dim subt w : ℕ} {team : Fin teams} {rows : Fin teams → Fin dim → ℕ}
    {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8} {pre : Bank w} {mem : Memory w} {claim : List (List Bool)}
    (h : FinishInput team rows subt pub mac pre mem claim)

/-- All returning nonlead teams read their original team guard from the actual
post-call directory. Only the six-instruction branch is traversed by the reader. -/
theorem FinishInput.nonleadTicks (l : SignedTaskArena.Layout) (A : StartupArena)
    (arena : h.post=l.after) (protect : ∀ k<l.after.start, k≠(pub 0).val+35 → h.selected k=mem k)
    (frame : (pub 0).val=A.frame) (placement : A.next≤l.cube.header.header)
    (teamWord : (mem (pub 0).val).val = team.val) (off : team.val≠0)
    (z : Returns (finishExpansion signedOccurrences) pub mac pre mem)
    (v : Returns leadEntry pub mac z.val.2.1 z.val.2.2) : traceCost v.val.1≤7 := by
  have alloc := h.allocation
  have cap := h.capacity
  rw [arena] at alloc cap
  have initial : ReaderKept A 0 0 mem mem mem := ⟨fun _ _ => rfl,fun _ _ => rfl,fun _ _ => rfl,fun _ _ => rfl⟩
  have kept := ReaderKept.after_finish A 0 0 l h.raw dim teams team.val subt pub mac pre h.bank mem mem mem
    h.selected h.earlier h.operands claim h.prepare protect alloc z.property frame (by simp) (Nat.zero_le _) placement cap initial
  have saved := kept.control 0 (by decide)
  rw [Nat.add_zero,←frame] at saved
  have other : z.val.2.2 (pub 0).val ≠ 0 := fun eqn => off (teamWord.symm.trans ((congrArg Fin.val saved).symm.trans (congrArg Fin.val eqn)))
  exact (lead_other_ticks other v.property).1 |>.le.trans (by decide)

/-- Convert the separately measured finish costs on an actual team to the
uniform physical phase. The complete rectangle shares the batch allowance
with the actual selected reader. -/
theorem uniform_finish_of_packet {batch R X P L fixed K F H units words powers rectangle cost : ℕ}
    (source : cost ≤ F*units+64*(words+powers+H*units)+rectangle)
    (global : words≤P) (localSize : powers≤L) (cube : units≤2*L) (bank : rectangle≤batch) :
    cost ≤ (uniformWindows batch R X P L K fixed F H).finish := by
  have paidF := Nat.mul_le_mul_left F cube
  have paidH := Nat.mul_le_mul_left H cube
  change cost ≤ 65*P+(64+2*F+128*H)*L+batch
  calc
    cost ≤ F*(2*L)+64*(P+L+H*(2*L))+batch :=
      source.trans (by gcongr)
    _ ≤ _ := by ring_nf; omega

end TeamContraction.JointHeader.PositiveFields

namespace RoutingISA.Evaluator.PinStart

open VPVNP.BurstRAM TeamContraction.JointHeader.PositiveFields
variable {w : ℕ}

/-- Local tagged rows and the true post-call accumulator at the end of a
returning team's fragment and typed private writer. The measured bound
uses this team's actual report cells, power slots and owned vertices. -/
structure PhysicalPost {teams d width : ℕ} (team : Fin teams) (l : SignedTaskArena.Layout)
    (P L F H : ℕ) (pub : Arg → Word w) (rt : TeamOpcode.Macros w 8)
    (pre : Bank w) (m : Memory w) (z : Returns (finishExpansion signedOccurrences) pub rt pre m) where
  /-- Bit fields of the shared subtotal claim presented to the tally suffix. -/
  claims : List (List Bool)
  /-- Natural subtotal in each team and coordinate, with the local row certified by `receipt`. -/
  rows : Fin teams → Fin d → ℕ
  /-- Inputs and execution witnessing the local operand counts and allocation for the tally suffix. -/
  receipt : FinishInput team rows width pub rt pre m claims
  location : receipt.post=l.after
  retained : ∀ k<l.after.start,k≠(pub 0).val+35 → receipt.selected k=m k
  /-- Allowance for the public gadget report fields in the finish cost. -/
  words : ℕ
  /-- Allowance for the weighted power slots in the team’s cell reports. -/
  powers : ℕ
  /-- Allowance for the cube work and the team’s owned vertex visits in the finish cost. -/
  units : ℕ
  occupied : words ≤ P
  slots : powers ≤ L
  localUnits : units ≤ 2*L
  measured : traceCost z.val.1 ≤ F*units+64*(words+powers+H*units)+512*(teams+1)*(d+1)*(w+1)

/-- Read the same local receipt at its canonical original team and coordinate
cardinalities. This changes indices only after proving both size identities. -/
def PhysicalPost.reindex {T T' d d' width P L F H : ℕ} {i : Fin T} {u : Fin T'}
    {l : SignedTaskArena.Layout} {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8}
    {pre : Bank w} {m : Memory w} {z : Returns (finishExpansion signedOccurrences) pub mac pre m}
    (data : PhysicalPost (d:=d) (width:=width) i l P L F H pub mac pre m z)
    (count : T=T') (dimension : d=d') (slot : i.val=u.val) :
    PhysicalPost (d:=d') (width:=width) u l P L F H pub mac pre m z := by
  subst T'
  subst d'
  obtain rfl : i=u := Fin.ext slot
  exact data

end RoutingISA.Evaluator.PinStart

end BorderVNP
end Computability
end OAI
