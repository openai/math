import OAI.ThreeFlat.RAM.TickGreedySetup
import OAI.ThreeFlat.RAM.TickGreedySchedule

namespace OAI
/-! # Fully initialized fixed-ROM greedy assignment for the history program -/

namespace ThreeFlat.RAM.TickGreedySetup

open Computability.VPVNP.BurstRAM PrivateRAM ContinuationLink Diagonal Diagonal.TickGreedyReplay
open TickGreedyNat TickGreedySweep LinearAlgebra.SpectralBooks.VNP
open scoped Fin.CommRing

variable {w p r k : ℕ} {α : Type*}

/-- The eighteen initialization labels lead directly to the thirty-label scheduler. -/
def bank (w : ℕ) (A : Layout) : Block w 48 17 0 := (block w A).seq (TickGreedySweep.block w)

/-- With arbitrary word charges the native bank realizes its full word recurrence,
including a zero item count or zero budgets. -/
theorem advance_replay (A : Layout) (W : ℕ) (items : List (Pair w))
    (M : Machine w p r k) (pc : Fin 48 ↪ Fin p) (R : Fin 17 ↪ Fin r) (pub : Fin 0 → Fin k)
    (exit : Fin p) (rom : (bank w A).Installed M pc R pub exit)
    (srcRoom : A.src+2*items.length < 2^w) (dstRoom : A.dst+2*items.length < 2^w)
    (safe : A.dst ≤ A.src ∨ A.src+2*items.length ≤ A.dst) (c : Config w p r) (mem : Memory w)
    (entry : c.pc=pc (bank w A).first) (stored : Stores mem A.src items)
    (countFit : A.countAddr < 2^w) (workFit : A.workAddr < 2^w)
    (cn : mem A.countAddr=(items.length : Word w)) (cw : mem A.workAddr=(W : Word w)) :
    let gc:=4*(W*A.B)
    let sc:=A.size/4
    let result:=(replay (data A.J W A.B gc sc) (encode ((0,gc),(0,sc))) items).2
    ∃ out, advance M.program (19+24*items.length) c mem = some (out,putPairs mem A.dst result) ∧
      out.pc=exit ∧ Stores (putPairs mem A.dst result) A.dst result := by
  dsimp only
  let P : Fin 18 ↪ Fin p := (Fin.castAddEmb 30).trans pc
  let Q : Fin 30 ↪ Fin p := (Fin.natAddEmb 18).trans pc
  obtain ⟨pre,sweep⟩ := ((block w A).seq_installed (TickGreedySweep.block w) M pc R pub exit).mp rom
  let d := initialized A mem R (guard Q) c
  have run : advance M.program 18 c mem = some (d,mem) :=
    advance_setup A M P R pub (guard Q) pre c mem entry
  have frame : Inputs A items.length W R d := initialized_inputs A mem R (guard Q) c items.length W
    countFit workFit cn cw
  have consts : params (itemReg R) d = data A.J W A.B (4*(W*A.B)) (A.size/4) := by
    change Params.mk (d.reg (R 6)) (d.reg (R 7)) (d.reg (R 8)) (d.reg (R 9)) (d.reg (R 10)) = _
    rw [frame.groups,frame.pairBudget,frame.work,frame.groupCap,frame.slotCap]; rfl
  have init : TickGreedyRow.state (itemReg R) d = encode ((0,4*(W*A.B)),(0,A.size/4)) := by
    change TickGreedyRow.State.mk (d.reg (R 2)) (d.reg (R 3)) (d.reg (R 4)) (d.reg (R 5)) = _
    rw [frame.group,frame.groupLeft,frame.slot,frame.slotLeft]; rfl
  obtain ⟨out,done,atExit,_⟩ := advance_sweep M Q R pub exit sweep items _ _ A.src A.dst srcRoom
    dstRoom safe d mem rfl stored frame.src frame.dst frame.stop consts init
  refine ⟨out,?_,atExit,stores_putPairs ..⟩
  rw [show 19+24*items.length=18+(1+24*items.length) by omega]
  exact advance_trans run done

/-- From arbitrary registers, the linked bank loads count and total work from the two
history metadata words and writes the natural greedy schedule for all input cells. -/
theorem advance_schedule (A : Layout) (teams W : ℕ) (work pairs : α → ℕ) (xs : List α)
    (jp : 0 < A.J) (wp : 0 < W) (bp : 0 < A.B)
    (gfit : 4*(W*A.B) < 2^w) (sfit : A.size/4 < 2^w)
    (pos : ∀ x ∈ xs, 0 < work x) (wt : Team.ticks work xs ≤ W) (pt : Team.ticks pairs xs ≤ A.B)
    (small : ∀ x ∈ xs, cellScore A.J W A.B work pairs x ≤ 2*(W*A.B))
    (sml : ∀ x ∈ xs, work x ≤ A.size/4)
    (covered : ∀ b ∈ schedule A.J W A.B work pairs xs, (Team.handoff work (A.size/4) teams b).2 = [])
    (M : Machine w p r k) (pc : Fin 48 ↪ Fin p) (R : Fin 17 ↪ Fin r) (pub : Fin 0 → Fin k)
    (exit : Fin p) (rom : (bank w A).Installed M pc R pub exit)
    (srcRoom : A.src+2*xs.length < 2^w) (dstRoom : A.dst+2*xs.length < 2^w)
    (safe : A.dst ≤ A.src ∨ A.src+2*xs.length ≤ A.dst) (c : Config w p r) (mem : Memory w)
    (entry : c.pc = pc (bank w A).first) (stored : Stores mem A.src (xs.map (weights work pairs)))
    (countFit : A.countAddr < 2^w) (workFit : A.workAddr < 2^w)
    (cn : mem A.countAddr = (xs.length : Word w)) (cw : mem A.workAddr = (W : Word w)) :
    let result := planned teams A.size A.J W A.B work pairs xs
    ∃ out, advance M.program (19+24*xs.length) c mem = some (out,putPairs mem A.dst result) ∧
      out.pc = exit ∧ Stores (putPairs mem A.dst result) A.dst result := by
  have run := advance_replay A W (xs.map (weights work pairs)) M pc R pub exit rom
    (by simpa using srcRoom) (by simpa using dstRoom) (by simpa using safe) c mem entry stored
    countFit workFit (by simpa using cn) cw
  dsimp only at run
  rw [replay_planned jp wp bp teams A.size work pairs xs gfit sfit pos wt pt small sml covered] at run
  simpa only [List.length_map] using run

end ThreeFlat.RAM.TickGreedySetup

end OAI
