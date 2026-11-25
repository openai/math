import OAI.ThreeFlat.RAM.TickWeightedBank
import OAI.ThreeFlat.RAM.TickStageSpec
import OAI.ThreeFlat.RAM.TickFuel

namespace OAI
/-! # Continuing a selected-cell replay into its weighted comparison slot -/

namespace ThreeFlat.RAM.TickWeightedBank

open Computability.VPVNP.BurstRAM PrivateRAM HistoryFactors Contraction BitLayout ContinuationLink TickFuel TickSeedTail

variable {F : Type*} [Field F] [Fintype F] {w p H J k pc r sz cells : ℕ}

/-- The work done for a single selected slot ends at the actual native weighted
interpreter. Its output is the network evaluation on the untouched exposed pins. -/
structure Ready (fit : Fits (shape F p H J) w) (N : BitNetwork F p) (lib : Library N)
    (pin : Fin p → Bool) («meta» lut : ℕ) (m : Memory w) : Prop where
  stored : Stores N lib (codec (shape F p H J) fit) «meta» lut m
  frame : ∀ a < cellsBase p H, m a = TickMountedPins.memory pin a

theorem after_prepare (M : Machine w pc r k) (fit : Fits (shape F p H J) w)
    («meta» lut : ℕ) (hm : footprint (shape F p H J) ≤ «meta») (hl : footprint (shape F p H J) ≤ lut)
    (N : BitNetwork F p) (lib : Library N) (nh : N.internal=H) (nc : N.cells=J)
    (mf : «meta»+4*J ≤ 2^w) (lf : lut+8*lib.count ≤ 2^w) (space : footprint (shape F p H J) < 2^w)
    (pin : Fin p → Bool) (P : Fin (count (seed (k:=k) fit)) ↪ Fin pc)
    (gen : Fin (4+(seed (k:=k) fit).binds) ↪ Fin r) (R : Fin 36 ↪ Fin r) (K : Fin 7 → Fin k)
    (rom : ∀ i, M.code (P i) = emit fit «meta» lut P gen R K i)
    (par : ∀ i, M.publicData (K i) = (interpreter p H J «meta» lut (F:=F) fit).publicData i)
    (prep : Block w sz cells k) (loc : Fin sz ↪ Fin pc) (frame : Fin cells ↪ Fin r)
    (pr : prep.Installed M loc frame id (TickGenerateTable.driver (seed fit) (genPC _ P) 0))
    (invariant : Memory w → Prop) (budget : ℕ)
    (prepared : TickStageSpec.Prepare prep M.publicData invariant
      (fun _ m => Ready fit N lib pin «meta» lut m) budget)
    (c : Config w pc r) (m : Memory w) (here : c.pc=loc prep.first) (init : invariant m) :
    let q := Fintype.card F
    Returns (codec (shape F p H J) fit) M.program
      (budget+(53+(q*q)*(6*(q*q)+10)+5*H+550*J)) c m (N.eval pin) := by
  obtain ⟨steps,first,b,output,bpc,ready,run⟩ :=
    prepared M loc frame id _ pr (fun _ => rfl) c m here init
  obtain ⟨s,second,value⟩ := mass_sized M fit «meta» lut hm hl N lib nh nc mf lf space pin output b
    ready.stored ready.frame P gen R K rom par bpc
  have terminal : Returns (codec (shape F p H J) fit) M.program s b output (N.eval pin) := value
  exact (terminal.prefix run).later (Nat.add_le_add first second)

end ThreeFlat.RAM.TickWeightedBank

end OAI
