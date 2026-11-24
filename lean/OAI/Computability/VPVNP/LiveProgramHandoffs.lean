import OAI.Computability.VPVNP.LiveProgramRouting
import OAI.Computability.VPVNP.LiveHeaderUnique

/-!
# Exact transfers of the outer live router

At a jump, the continuation runs with cursor zero in the newly tagged
memory. An accepting router contributes exactly one path if its own report
fits the cap. These statements apply at a common group clock and keep every
report from the deterministic dispatch and flag test.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveProgram
open BurstRAM BurstRAM.PrivateRAM
open scoped Fin.CommRing

namespace Router

variable (r : Router) (c : Constants) (p : UniversalMachine.Program) (O : PairTable)
variable (g : Geometry) (lit : LiteralPrefix)

private theorem dispatch_le (addr : Word g.w) :
    (LiveStageLink.dispatchEvents addr r.stage).length ≤ 44 := by
  simp [LiveStageLink.dispatchEvents]; have := r.stage.isLt; omega

/-- Router report for a selected jump. It reads the flag, tests the indicated branch, writes
the destination tag, and returns cursor zero. -/
def jumpReport (i : Fin 3) (flag : Word g.w) (dest : Stage) : Report g.w :=
  let pub := r.data g lit
  ⟨[.tick,.read (pub 0) flag] ++ List.replicate (2*(i.val+1)) .tick ++
    [.tick,.tick,.write (pub 1) (LiveStageLink.tagWord g.w dest),.tick],some 0⟩

/-- Accepting router report consisting of the flag read and the tests through the selected
branch. -/
def haltReport (i : Fin 3) (flag : Word g.w) : Report g.w :=
  ⟨[.tick,.read ((r.data g lit) 0) flag] ++ List.replicate (2*(i.val+1)) .tick,none⟩

private theorem selected_jump (i : Fin 3) (dest : Stage) (flag : Word g.w)
    (h : r.target i = .jump (dest.castLE (by decide))) :
    Route.report (r.data g lit) flag i (r.target i) [] = some (r.jumpReport g lit i flag dest) := by rw [h]; rfl

private theorem selected_halt (i : Fin 3) (flag : Word g.w) (h : r.target i = .accept) :
    Route.report (r.data g lit) flag i (r.target i) [] = some (r.haltReport g lit i flag) := by rw [h]; rfl

/-- Wrap the router’s own report with the live stage linker’s dispatch and exit events at the
outer stage-tag address. -/
def outerReport (src : Report g.w) := LiveStageLink.linkedReport (next p)
  (Pieces.word g lit (.geometry Layout.stageTag)) r.stage src

/-- A jump costs one tag read in the linker and a read and write in the router. -/
theorem outer_jump_probes (i : Fin 3) (flag : Word g.w) (dest : Stage) :
    (r.outerReport p g lit (r.jumpReport g lit i flag dest)).probes = 3 := by
  rw [outerReport,LiveStageLink.linkedReport_probes]
  fin_cases i <;> rfl

/-- A terminal route reads the two tags and writes no word. -/
theorem outer_halt_probes (i : Fin 3) (flag : Word g.w) :
    (r.outerReport p g lit (r.haltReport g lit i flag)).probes = 2 := by
  cases r <;> fin_cases i <;> rfl

theorem outer_jump_clock (i : Fin 3) (flag : Word g.w) (dest : Stage) :
    (r.outerReport p g lit (r.jumpReport g lit i flag dest)).events.length < 57 := by
  cases r <;> fin_cases i <;> simp [outerReport,LiveStageLink.linkedReport,LiveStageLink.prependLog,LiveStageLink.dispatchEvents,
    LiveStageLink.exitReport,jumpReport,stage]

theorem after_jump (m : Memory g.w) (i : Fin 3) (flag : Word g.w) (dest : Stage) :
    after m (r.outerReport p g lit (r.jumpReport g lit i flag dest)).events =
      writeMemory m (Pieces.word g lit (.geometry Layout.stageTag)) (LiveStageLink.tagWord g.w dest) := by
  rw [outerReport, LiveStageLink.linkedReport_after]
  cases r <;> fin_cases i <;> rfl

private theorem result_jump (i : Fin 3) (flag : Word g.w) (dest : Stage) :
    (r.outerReport p g lit (r.jumpReport g lit i flag dest)).result = some 0 := rfl

/-- The actual choice-free jump at the group's common clock. -/
theorem jump_call (fit : 21 ≤ 2^g.w) (hw : 2 ≤ g.w) (clock : ℕ) (hclock : 57 ≤ clock)
    (st : Word g.w) (m : Memory g.w) (i : Fin 3)
    (hf : m ((r.data g lit) 0).val = (i.val : Word g.w))
    (ht : m (Pieces.word g lit (.geometry Layout.stageTag)).val = LiveStageLink.tagWord g.w r.stage)
    (dest : Stage) (h : r.target i = .jump (dest.castLE (by decide))) :
    let P := (machine c p O g lit).program
    BurstRAM.execute P clock (P.start st) m [] = some (r.outerReport p g lit (r.jumpReport g lit i (m ((r.data g lit) 0).val) dest)) := by
  let addr := Pieces.word g lit (.geometry Layout.stageTag)
  let f := clock-(13+(LiveStageLink.dispatchEvents addr r.stage).length)
  have hc : f+13+(LiveStageLink.dispatchEvents addr r.stage).length = clock := by
    have := dispatch_le r g addr; dsimp [f]; omega
  have he := r.execute c p O g lit hw fit st m i hf addr rfl ht [] f
  rw [hc,selected_jump r g lit i dest _ h] at he
  exact he

/-- Exact all-path transfer after a successful first-tail, last-tail, or pair
selection. The tag write is the only change in external memory. -/
noncomputable def jumpEquiv (fit : 21 ≤ 2^g.w) (hw : 2 ≤ g.w) (cap : List (Report g.w) → Prop)
    (clock : ℕ) (hclock : 57 ≤ clock) (st : Word g.w) (m : Memory g.w)
    (i : Fin 3) (hf : m ((r.data g lit) 0).val = (i.val : Word g.w))
    (ht : m (Pieces.word g lit (.geometry Layout.stageTag)).val = LiveStageLink.tagWord g.w r.stage)
    (dest : Stage) (h : r.target i = .jump (dest.castLE (by decide))) :
    let P := (machine c p O g lit).program
    let addr := Pieces.word g lit (.geometry Layout.stageTag)
    let rep := r.outerReport p g lit (r.jumpReport g lit i (m ((r.data g lit) 0).val) dest)
    ActualPaths P clock 0 (writeMemory m addr (LiveStageLink.tagWord g.w dest)) (fun rs => cap (rep::rs)) ≃
      ActualPaths P clock st m cap := by
  let addr := Pieces.word g lit (.geometry Layout.stageTag)
  let f := clock - (13+(LiveStageLink.dispatchEvents addr r.stage).length)
  have hc : f+13+(LiveStageLink.dispatchEvents addr r.stage).length = clock := by
    have := dispatch_le r g addr; dsimp [f]; omega
  have hsel := r.selected_jump g lit i dest (m ((r.data g lit) 0).val) h
  have e := r.pathEquiv c p O g lit hw fit st m i hf ht f _ hsel cap
  let clock' := f+13+(LiveStageLink.dispatchEvents addr r.stage).length
  change Continuations (machine c p O g lit).program clock' m (r.outerReport p g lit _) cap ≃
    ActualPaths (machine c p O g lit).program clock' st m cap at e
  have htClock : clock' = clock := hc
  rw [htClock] at e
  unfold Continuations at e
  rw [result_jump, after_jump r p g lit m i _ dest] at e
  exact e

/-- A checked unit-mode flag finishes the group at the router, with exactly
one possible choice stream consisting of a single empty call. -/
theorem unit_accept_iff (fit : 21 ≤ 2^g.w) (hw : 2 ≤ g.w) (cap : List (Report g.w) → Prop)
    (clock : ℕ) (hclock : 57 ≤ clock) (st : Word g.w) (m : Memory g.w)
    (hf : m ((Router.mode.data g lit) 0).val = 0)
    (ht : m (Pieces.word g lit (.geometry Layout.stageTag)).val = LiveStageLink.tagWord g.w Stage.mode)
    (bs : List (List Bool)) :
    let P := (machine c p O g lit).program
    let rep := Router.mode.outerReport p g lit (Router.mode.haltReport g lit 0 0)
    (∃ rs, runSegment P clock (some st) m bs = some rs ∧ endState (some st) rs = none ∧ cap rs) ↔
      bs = [[]] ∧ cap [rep] := by
  let P := (machine c p O g lit).program
  let rep := Router.mode.outerReport p g lit (Router.mode.haltReport g lit 0 0)
  let addr := Pieces.word g lit (.geometry Layout.stageTag)
  let f := clock-(13+(LiveStageLink.dispatchEvents addr Router.mode.stage).length)
  have hc : f+13+(LiveStageLink.dispatchEvents addr Router.mode.stage).length = clock := by
    have := dispatch_le Router.mode g addr; dsimp [f]; omega
  have he := Router.mode.execute c p O g lit hw fit st m 0 (by exact hf) addr rfl ht [] f
  rw [hc,hf,Router.mode.selected_halt g lit 0 0 rfl] at he
  change BurstRAM.execute P clock (P.start st) m [] = some rep at he
  have stop : rep.result = none := rfl
  have hrun : runSegment P clock (some st) m (List.replicate 1 []) = some [rep] := by simp [List.replicate_succ,runSegment,he]
  have halt : endState (some st) [rep] = none := stop
  change (∃ rs, runSegment P clock (some st) m bs = some rs ∧ endState (some st) rs = none ∧ cap rs) ↔ _
  constructor
  · rintro ⟨rs,hr,hh,hhc⟩
    obtain ⟨hx,rfl⟩ := BurstRAM.accepted_empty_unique hrun halt hr hh
    exact ⟨hx,hhc⟩
  · rintro ⟨rfl,h⟩; exact ⟨[rep],hrun,halt,h⟩

end Router
end LiveProgram

end VPVNP
end Computability
end OAI
