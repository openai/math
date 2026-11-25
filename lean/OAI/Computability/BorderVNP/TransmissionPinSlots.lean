import OAI.Computability.BorderVNP.TeamContractionLayout
import OAI.Computability.BorderVNP.TransmissionExteriorSlots

/-! # The signed contraction's actual literal, exterior and pin memory -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction

open VPVNP BurstRAM Diagonal.Layout RoutingISA.Pins
open private exteriorBit pinBit from OAI.Computability.BorderVNP.TeamContractionLayout

variable {R r t d link inner n : ℕ} {Edge : Type} (G : Wiring R r t d link inner n Edge)

/-- Dimensions and scratch bases for the pin reader on one team of the signed contraction. -/
def Wiring.pinLayout (u : Fin (R+1)) (ibase hbase starbase : ℕ) : Layout :=
  ⟨u.val, R+1, r, G.program.length+t, link, d, ibase, hbase, starbase⟩

/-- Concrete data read by the processor-tape parser when its symbolic inputs are the
actual contraction slots. The routing stack follows these initialized RAM fields. -/
def Wiring.processorFields (u : Fin (R+1)) (pin : Fin d → Bool)
    (ext : Exterior R r link → Bool) (ibase hbase starbase : ℕ) :
    ProcessorFields (G.pinLayout u ibase hbase starbase) where
  literal j := G.program ++ List.ofFn (G.literal u j)
  exterior j := exteriorRows u j (assignments ext (fun _ (_ : Edge) => false))
  pins j := List.ofFn (fun a : Fin (G.program.length+t) => pinBit pin u j a)
  literal_length _ := by simp [Wiring.pinLayout]
  exterior_count _ := exteriorRows_count ..
  link_length i := exteriorRows_width u i _
  pins_length _ := List.length_ofFn

/-- Actual bit occupying position `x` of the flattened secondary fields. Only
the first `d` positions of team zero carry a live index bit. -/
def liveBit (u : Fin (R+1)) (pin : Fin d → Bool) (x : ℕ) : Bool :=
  if u = 0 then if h : x < d then pin ⟨x,h⟩ else false else false

/-- Flattening the per-processor pin fields produces exactly the specified live
index and its clamped padding, in the contraction's processor order. -/
theorem Wiring.processorFields_pins (u : Fin (R+1)) (pin : Fin d → Bool)
    (ext : Exterior R r link → Bool) (ibase hbase starbase : ℕ) :
    (G.processorFields u pin ext ibase hbase starbase).pinBits =
      List.ofFn fun x : Fin (r*(G.program.length+t)) => liveBit u pin x.val := by
  rw [List.ofFn_mul]
  simp only [ProcessorFields.pinBits, Wiring.processorFields, Wiring.pinLayout]
  congr 1
  apply congrArg List.ofFn
  funext i
  apply congrArg List.ofFn
  funext j
  simp only [pinBit, liveBit, finProdFinEquiv_apply_val, Nat.mul_comm (G.program.length+t),
    Nat.add_comm j.val]

/-- The complete signed input word splits into the actual parser initialization segment,
interior bits and canonical trailing zero padding. -/
theorem Wiring.word_processorFields (u : Fin (R+1)) (j : Fin r) (pin : Fin d → Bool)
    (ext : Exterior R r link → Bool) (int : Edge → Bool) (ibase hbase starbase : ℕ) :
    List.ofFn (G.word pin ext int u j) =
      (G.processorFields u pin ext ibase hbase starbase).row j ++
        List.ofFn (fun i => (G.interior j i).elim false int) ++
        List.replicate (n-(2*(G.program.length+t) + R*link + inner)) false := by
  calc
    _ = G.input pin ext int u j := G.read_bits pin ext (fun _ => int) u j
    _ = _ := ?_
  have he := flatten_exteriorRows u j (assignments ext (fun _ (_ : Edge) => false)) pin
  change (exteriorRows u j (assignments ext (fun _ (_ : Edge) => false))).flatten =
    List.ofFn (exteriorBit ext u j) at he
  simp only [Wiring.input, ProcessorFields.row, Wiring.processorFields, TeamTapeInput.inputData,
    List.append_assoc]
  rw [← he]
  rfl

/-- Reading the true secondary word returns its encoded contraction slot at each
position, both on team zero and on the teams with entirely clamped pin fields. -/
theorem Wiring.read_liveBit {w : ℕ} (u : Fin (R+1)) (pin : Fin d → Bool)
    (ext : Exterior R r link → Bool) (ibase hbase starbase : ℕ) (m : Memory w)
    (physical : (G.processorFields u pin ext ibase hbase starbase).ContainsInput m)
    (x : ℕ) (hx : x < r*(G.program.length+t)) :
    m (RoutingISA.livePinAddress (R+1) (G.program.length+t) link x) =
      TeamTapeInputEmit.word w (liveBit u pin x).toNat := by
  calc
    _ = TeamTapeInputEmit.headerWord w (G.processorFields u pin ext ibase hbase starbase).pinBits x :=
      physical.pin x hx
    _ = _ := by rw [G.processorFields_pins]; simp [TeamTapeInputEmit.headerWord, hx]

end TeamContraction

end BorderVNP
end Computability
end OAI
