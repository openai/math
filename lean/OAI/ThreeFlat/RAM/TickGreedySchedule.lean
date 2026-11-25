import OAI.ThreeFlat.RAM.TickGreedyNat
import OAI.ThreeFlat.RAM.TickGreedySweep

namespace OAI
/-! # Native array assignment to the diagonal's scheduled groups and slots -/

namespace ThreeFlat.RAM.TickGreedyNat

open Computability.VPVNP.BurstRAM PrivateRAM Diagonal Diagonal.TickGreedyReplay TickGreedySweep
open LinearAlgebra.SpectralBooks.VNP
open scoped Fin.CommRing
variable {w p r k : ℕ} {α : Type*}

def weights (work pairs : α → ℕ) (c : α) : Pair w := ((work c : Word w),(pairs c : Word w))
def owner (c : (ℕ × ℕ) × α) : Pair w := ((c.1.1 : Word w),(c.1.2 : Word w))

def data (J W B gc sc : ℕ) : Params w := ⟨J,B,W,gc,sc⟩

theorem replay_assign (xs : List α) (work pairs : α → ℕ) (J W B gc sc : ℕ) (g s : Cursor)
    (gcfit : gc < 2^w) (scfit : sc < 2^w) (gl : g.2 ≤ gc) (sl : s.2 ≤ sc)
    (small : ∀ x ∈ xs, cellScore J W B work pairs x ≤ gc)
    (fits : ∀ x ∈ xs, work x ≤ sc) :
    (replay (data (w:=w) J W B gc sc) (encode (g,s)) (xs.map (weights work pairs))).2 =
      (assignBoth (cellScore J W B work pairs) work gc sc g s xs).map owner := by
  induction xs generalizing g s with
  | nil => rfl
  | cons x xs ih =>
    let cost := cellScore J W B work pairs x
    let next := placeBoth gc sc g s cost (work x)
    have correct : (data (w:=w) J W B gc sc).step (encode (g,s)) (weights work pairs x) = encode next :=
      update_eq g s (work x) (pairs x) J B W gc sc gcfit scfit gl sl
        (small _ List.mem_cons_self) (fits _ List.mem_cons_self)
    have rem := remaining_le g s cost (work x) gc sc gl sl
    have tail := ih next.1 next.2 rem.1 rem.2
      (fun z hz => small z (List.mem_cons_of_mem _ hz)) (fun z hz => fits z (List.mem_cons_of_mem _ hz))
    simp only [List.map_cons,replay,assignBoth,correct]
    exact congrArg (List.cons ((encode (w:=w) next).group,(encode (w:=w) next).slot)) tail

/-- This is the exact natural schedule that is written, padded empty
groups and empty processor slots contributing no records. -/
def planned (teams m J W B : ℕ) (work pairs : α → ℕ) (xs : List α) : List (Pair w) :=
  (labelBoth (fun b => label 0 (Team.handoff work (m/4) teams b).1) 0 (schedule J W B work pairs xs)).map owner

theorem replay_planned {J W B : ℕ} (jp : 0 < J) (wp : 0 < W) (bp : 0 < B)
    (teams m : ℕ) (work pairs : α → ℕ) (xs : List α)
    (gfit : 4*(W*B) < 2^w) (sfit : m/4 < 2^w)
    (pos : ∀ x ∈ xs, 0 < work x) (wt : Team.ticks work xs ≤ W) (pt : Team.ticks pairs xs ≤ B)
    (small : ∀ x ∈ xs, cellScore J W B work pairs x ≤ 2*(W*B))
    (sml : ∀ x ∈ xs, work x ≤ m/4)
    (covered : ∀ b ∈ schedule J W B work pairs xs, (Team.handoff work (m/4) teams b).2 = []) :
    (replay (data (w:=w) J W B (4*(W*B)) (m/4)) (encode ((0,4*(W*B)),(0,m/4)))
      (xs.map (weights work pairs))).2 = planned teams m J W B work pairs xs := by
  rw [replay_assign xs work pairs J W B _ _ _ _ gfit sfit le_rfl le_rfl
    (fun x hx => by have := small x hx; omega) sml]
  rw [assignBoth_schedule jp wp bp m teams work pairs xs pos wt pt small sml covered]
  rfl

/-- Executing the bounded instruction table writes exactly the two designated
indices for every final cell, in its original order. -/
theorem advance_schedule {J W B : ℕ} (jp : 0 < J) (wp : 0 < W) (bp : 0 < B)
    (teams m : ℕ) (work pairs : α → ℕ) (xs : List α)
    (gfit : 4*(W*B) < 2^w) (sfit : m/4 < 2^w)
    (pos : ∀ x ∈ xs, 0 < work x) (wt : Team.ticks work xs ≤ W) (pt : Team.ticks pairs xs ≤ B)
    (small : ∀ x ∈ xs, cellScore J W B work pairs x ≤ 2*(W*B)) (sml : ∀ x ∈ xs, work x ≤ m/4)
    (covered : ∀ b ∈ schedule J W B work pairs xs, (Team.handoff work (m/4) teams b).2 = [])
    (M : Machine w p r k) (pc : Fin 30 ↪ Fin p) (reg : Fin 17 ↪ Fin r) (pub : Fin 0 → Fin k)
    (exit : Fin p) (rom : (TickGreedySweep.block w).Installed M pc reg pub exit)
    (src dst : ℕ) (srcRoom : src+2*xs.length < 2^w) (dstRoom : dst+2*xs.length < 2^w)
    (safe : dst ≤ src ∨ src+2*xs.length ≤ dst) (c : Config w p r) (mem : Memory w)
    (entry : c.pc = guard pc) (stored : Stores mem src (xs.map (weights work pairs)))
    (source : c.reg (itemReg reg 0) = (src : Word w))
    (target : c.reg (itemReg reg 1) = (dst : Word w))
    (endReg : c.reg (reg 16) = ((src+2*xs.length : ℕ) : Word w))
    (consts : params (itemReg reg) c = data J W B (4*(W*B)) (m/4))
    (init : TickGreedyRow.state (itemReg reg) c = encode ((0,4*(W*B)),(0,m/4))) :
    let result := planned teams m J W B work pairs xs
    ∃ out, advance M.program (1+24*xs.length) c mem = some (out,putPairs mem dst result) ∧
      out.pc = exit ∧ Stores (putPairs mem dst result) dst result := by
  obtain ⟨out,done,atExit,_⟩ := advance_sweep M pc reg pub exit rom _ _ _ src dst
    (by simpa using srcRoom) (by simpa using dstRoom) (by simpa using safe)
    c mem entry stored source target (by simpa using endReg) consts init
  have eq := replay_planned (w:=w) jp wp bp teams m work pairs xs gfit sfit pos wt pt small sml covered
  rw [eq,List.length_map] at done
  exact ⟨out,done,atExit,stores_putPairs ..⟩

end ThreeFlat.RAM.TickGreedyNat

end OAI
