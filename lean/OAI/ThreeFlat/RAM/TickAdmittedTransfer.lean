import OAI.ThreeFlat.RAM.TickExecutionInputs

namespace OAI
/-! # Running the physical active transfer on the actual admitted scratch arrays -/

noncomputable section
namespace ThreeFlat.RAM.TickActiveROM
open Computability.VPVNP.BurstRAM PrivateRAM ContinuationLink DescriptorScan TickFuel Diagonal.TickChronology
open Contraction BitLayout HistoryFactors
open scoped Fin.CommRing Classical

variable {F : Type*} [Field F] [Fintype F] {p H J w k n m nr mr r pc : ℕ}

def CellInput.tail {B : Layout} {clock : Clock} {fit : Fits (TickWeightedBank.shape F p H J) w}
    (x : CellInput B clock fit) (budget : ℕ) : ℕ :=
  let q := Fintype.card F
  (14+B.bits*5082)+(17+6*B.bits+max (30+20*x.intervals.length+4319*B.bits)
    (budget+(53+(q*q)*(6*(q*q)+10)+5*H+550*J)))

theorem admitted_transfer (B : Layout) (clock : Clock) (fit : Fits (TickWeightedBank.shape F p H J) w)
    (M : Machine w pc r k) (nav : Block w n nr k) (prep : Block w m mr k)
    (P : Labels (n:=n) (m:=m) (k:=k) B clock fit ↪ Fin pc)
    (R : Registers B clock fit nr mr r k) (K : Fin 7 → Fin k)
    (rom : ∀ i, M.code (P i) = emit B clock fit nav prep P R K i)
    (ph : Phase) (x : CellInput B clock fit) (oa na oc nc : Fin B.bits → Bool) (pin : Fin p → Bool)
    (space : WordBounds B fit) (data : ∀ i, M.publicData (K i) =
      (interpreter p H J B.metadata B.lut (F:=F) fit).publicData i)
    (slotInput : Memory w → Prop) (budget : ℕ)
    (program : TickStageSpec.Prepare prep M.publicData slotInput
      (fun _ m => TickWeightedBank.Ready fit x.net x.lib pin B.metadata B.lut m) budget)
    (out : Memory w) (navOut : NavOutput x ph oa na oc nc slotInput out)
    (cfg : Config w pc r) (here : cfg.pc = TickHistoryCore.resumeAux (B.aux w k)
      (inside P Label.control (fun _ _ h => by cases h; rfl))) :
    Returns (codec (TickWeightedBank.shape F p H J) fit) M.program (x.tail budget) cfg
      (boundsMemory B clock out) (x.weight ph oa na oc nc pin) := by
  have fitB := space.bounds
  have fitR := space.requests
  have ctrl := space.ctrl
  have clk := space.clk
  have low (i : ℕ) (h : i<B.bounds) := bounds_low B clock out i h (by omega)
  have oldAux := space.oldAux
  have newAux := space.newAux
  have before := space.oldChunk
  have after := space.newChunk
  refine active_transfer B clock fit M nav prep P R K rom ph x.aux cfg (boundsMemory B clock out)
    oa na oc nc here space.width space.requests space.safe_header
    (auxiliary_header B clock out ph x.count x.pairSpace (by omega) (by omega)
      navOut.phase navOut.marker navOut.count) ?_ ?_ ?_ ?_ (by omega) (by omega) ?_ ?_
    x.intervals x.lo x.group x.before x.after navOut.scanInputs x.net x.lib pin x.hidden x.cells
    space.metadata space.lut space.meta x.lutSpace space.low data slotInput budget program navOut.evalInputs
  · intro i
    rw [space.pinAddr _ oldAux i]
    have := i.isLt
    omega
  · intro i
    rw [space.pinAddr _ newAux i]
    have := i.isLt
    omega
  · intro i
    unfold ChunkRequests.bitAt
    rw [space.pinAddr _ oldAux i,low _ (by have := i.isLt; omega)]
    exact navOut.oldAux i
  · intro i
    unfold ChunkRequests.bitAt
    rw [space.pinAddr _ newAux i,low _ (by have := i.isLt; omega)]
    exact navOut.newAux i
  · intro i
    rw [low _ (by have := i.isLt; omega)]
    exact navOut.oldChunk i
  · intro i
    rw [low _ (by have := i.isLt; omega)]
    exact navOut.newChunk i


end ThreeFlat.RAM.TickActiveROM

end
end OAI
