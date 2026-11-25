import OAI.Computability.BorderVNP.CubeISAHeaderInstallExtension
import OAI.Computability.BorderVNP.CubeISAHeaderInstallModel
import OAI.Computability.BorderVNP.CubeISAOwnedPacketCount
import OAI.Computability.BorderVNP.CubeISAOwnedPacketRank

/-! # Physical cube-header inputs at the end of the booted geometry allocation -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.CubeHeaderInstall

open VPVNP.BurstRAM TeamContraction.JointHeader TeamContraction.ProcessorSlots

/-- Place the cube's secondary header after every geometry gate, gathered
output, deinterleaved bit, and packed program word. -/
def geometryInputs (fresh profile gates outputs width w d n blocks b h s : ℕ) : Inputs :=
  ⟨GeometryAdvice.Allocation.stop fresh profile gates outputs width w, d, n+1, blocks,
    profile, Cube.Physical.declarationCap n d blocks b h s⟩

/-- The loaded constructor state from the jointly placed 81-word extension. -/
theorem resident_inputs {w : ℕ} (pub : Arg → Word w) (m : Memory w)
    (old : Fin 81 → Word w) (fresh profile gates outputs width off ell d n blocks b h s : ℕ)
    (installed : ∀ j : Fin 81, m ((pub 0).val+31+j.val) =
      jointFields old fresh profile gates outputs width off ell d n blocks b h s j)
    {selectorBits : ℕ} (room : (geometryInputs fresh profile gates outputs width w d n blocks b h s).Fits
      w n selectorBits (pub 0).val)
    (profileFit : profile < 2^w) (blockFit : h*b < 2^w) :
    (geometryInputs fresh profile gates outputs width w d n blocks b h s).Loaded (readings pub) (readings m) ∧
    frameField (readings pub) (readings m) 61 = h*b := by
  let l := geometryInputs fresh profile gates outputs width w d n blocks b h s
  have h0 : l.header < 2^w := by have := room.bank; dsimp only [Inputs.packetBase] at this; exact (by dsimp [l]; omega)
  have hD : d < 2^w := by
    have hs : d*d < 2^w := room.square
    by_cases hd : d = 0
    · simp [hd]
    · exact (Nat.le_mul_of_pos_right d (Nat.zero_lt_of_ne_zero hd)).trans_lt hs
  have ha : n+1 < 2^w := by
    have ha := room.bank
    dsimp [Inputs.packetBase,geometryInputs] at ha
    omega
  have hb : blocks < 2^w := by
    have hh : 2*blocks*max 1 (d.choose 2^n) < 2^w := room.packets
    have := Nat.le_mul_of_pos_right (2*blocks) (show 0 < max 1 (d.choose 2^n) by omega)
    omega
  have hc : Cube.Physical.declarationCap n d blocks b h s < 2^w := Nat.lt_of_succ_lt room.cap
  have take (field value : ℕ) := resident_operand pub m old fresh profile gates outputs width off ell d n blocks b h s installed (field := field) (value := value)
  constructor
  · exact ⟨take 63 _ rfl h0, take 59 _ rfl hD,
      take 60 _ rfl ha,take 109 _ rfl hb,
      take 110 _ rfl profileFit,take 111 _ rfl hc⟩
  · exact take 61 _ rfl blockFit

/-- All six native constructor inputs, and the physical scalar-block width,
come from the actual pin-decoded processor extension. -/
theorem boot_inputs {w D : ℕ} {L : Pins.Layout} {F : Pins.ProcessorFields L}
    {f : BroadcastFrame} {A : AdviceLayout} {p : ReferencePacket w D}
    {pub : Arg → Word w} {bits : List Bool} {reg : Bank w} {m : Memory w}
    (boot : BootHeaderState F f A p pub bits reg m)
    (old : Fin 81 → Word w) (fresh profile gates outputs width off ell d n blocks b h s : ℕ)
    (pins : p.extension = jointFields old fresh profile gates outputs width off ell d n blocks b h s)
    {selectorBits : ℕ} (room : (geometryInputs fresh profile gates outputs width w d n blocks b h s).Fits
      w n selectorBits (pub 0).val)
    (profileFit : profile < 2^w) (blockFit : h*b < 2^w) :
    (geometryInputs fresh profile gates outputs width w d n blocks b h s).Loaded (readings pub) (readings m) ∧
    frameField (readings pub) (readings m) 61 = h*b := by
  exact resident_inputs pub m old fresh profile gates outputs width off ell d n blocks b h s
    (fun j => (boot.extension j).trans (congrFun pins j)) room profileFit blockFit

/-- The initialized shared-list prefix is the exact physical selector count
for a distinct symbol row. -/
theorem geometry_selector_length (fresh profile gates outputs width w d n blocks b h s K : ℕ)
    (i : Fin (n+1)) (pair : Cube.Symbols d) :
    (geometryInputs fresh profile gates outputs width w d n blocks b h s).volume n
      (VPVNP.MotifWidths.selectorBits K (Fintype.card (Cube.Edge (n+1))) h) =
    Cube.Physical.rowSelectorBits n d blocks K h i (Sym2.mk pair.val.1 pair.val.2) :=
  (Cube.Physical.Owned.strict_rowSelectorBits K h i pair).symm

/-- The full packet bank and its end sentinel lie beyond both square row
arrays and the directional totals. -/
def bankStop (l : Inputs) (n bankWidth : ℕ) : ℕ :=
  l.packetBase + (l.d*l.d)^(n+1)*2*l.blocks*bankWidth

/-- All global packet-bank blocks use addresses in this one fixed allocation. -/
theorem bankAt_room (l : Inputs) {n w bankWidth : ℕ} (i : Fin (n+1)) (pair : Cube.Symbols l.d)
    (t : Fin (Cube.Physical.Owned.packetTrials n l.d l.blocks)) (positive : 0 < bankWidth)
    (room : bankStop l n bankWidth ≤ 2^w) :
    l.packetBase + Cube.Physical.Owned.trialPacketIndex l.d ((l.d*l.d)^i.val) l.blocks
      pair.val.1.val pair.val.2.val t.val * bankWidth < 2^w :=
  Cube.Physical.Owned.trialPacketBase_lt i pair t positive room

end RoutingISA.CubeHeaderInstall

end BorderVNP
end Computability
end OAI
