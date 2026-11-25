import OAI.ThreeFlat.RAM.TickWeightedROM
import OAI.ThreeFlat.RAM.TickWeightedSlot
import OAI.ThreeFlat.RAM.HistoryFixed

namespace OAI
/-! # One native terminal bank for every padded group slot of common dimensions -/

noncomputable section
namespace ThreeFlat.RAM.TickWeightedBank

open Computability.VPVNP.BurstRAM PrivateRAM BitLayout Contraction HistoryFactors TickSeedTail
open BitNetwork Diagonal.TraceCircuit

open scoped Fin.CommRing

variable {F : Type*} [Field F] [Fintype F] {p H J w k pc r : ℕ}

attribute [local irreducible] HistoryFieldSeed.fieldExpr TickSeedTail.emit TickGenerateTable.emit
  TickGenerateTable.driver TickClearFrame.row HistoryFactors.interpreter

set_option maxHeartbeats 1600000 in
theorem mass_sized (M : Machine w pc r k) (fit : Fits (shape F p H J) w)
    («meta» lut : ℕ) (hm : footprint (shape F p H J) ≤ «meta») (hl : footprint (shape F p H J) ≤ lut)
    (N : BitNetwork F p) (lib : Library N) (hn : N.internal = H) (hc : N.cells = J)
    (bm : «meta»+4*J ≤ 2^w) (bl : lut+8*lib.count ≤ 2^w) (space : footprint (shape F p H J) < 2^w)
    (pin : Fin p → Bool) (input : Memory w) (c : Config w pc r)
    (stored : Stores N lib (codec (shape F p H J) fit) «meta» lut input)
    (frame : ∀ a < cellsBase p H, input a = TickMountedPins.memory pin a)
    (P : Fin (count (seed (k:=k) fit)) ↪ Fin pc)
    (genR : Fin (4+(seed (k:=k) fit).binds) ↪ Fin r) (R : Fin 36 ↪ Fin r) (K : Fin 7 → Fin k)
    (rom : ∀ i, M.code (P i) = emit fit «meta» lut P genR R K i)
    (par : ∀ i, M.publicData (K i) = (interpreter p H J «meta» lut (F:=F) fit).publicData i)
    (entry : c.pc = TickGenerateTable.driver (seed fit) (genPC _ P) 0) :
    let q := Fintype.card F
    ∃ t ≤ 53+(q*q)*(6*(q*q)+10)+5*H+550*J, ∀ extra,
      mass (codec (shape F p H J) fit) M.program (extra+t) c input = N.eval pin := by
  subst H J
  let e := seed (k:=k) fit
  let b := (mulBase p N.internal N.cells : Word w)
  let z := (footprint N : Word w)
  let native := interpreter p N.internal N.cells «meta» lut (F:=F) fit
  exact TickWeightedSlot.mass_slot M N fit lib «meta» lut hm hl bm bl space pin input c stored frame
    (genPC e P) genR (clearPC e P native.entry) (runPC e P) R K
    (gen_installed e b z native M P genR R K rom)
    (clear_installed e b z native M P genR R K rom)
    (TickSeedTail.clear_to_eval e native P)
    (interpreter_installed e b z native M P genR R K rom) par entry

end ThreeFlat.RAM.TickWeightedBank

end
end OAI
