import OAI.ThreeFlat.Diagonal.CompressorPostImage

namespace OAI
/-! # Key words retained by the native graph, key and width passes -/

namespace ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkStage
open Computability.VPVNP.Compression Computability.VPVNP.BurstRAM Computability.VPVNP.BurstRAM.PrivateRAM RAM RAM.DescriptorScan
open private seq_image from OAI.ThreeFlat.Diagonal.CompressorPostImage

namespace PostImage

/-- A key written by the key pass is still present after the width pass. -/
theorem retains_keys {w : ℕ} (C : SlotImage.Columns) (S : Graph.Stage)
    (current : Word w) (pub : Fin 1 → Word w) (m : Memory w) (keyBase lanes : ℕ)
    (graphFile keyFile widthFile : ℕ → Word w)
    (graph : FileSpec current pub (Template.graph S false) nextGraph graphWords
      m C.graph (6*C.rows) graphFile)
    (keyPass : FileSpec current pub (Template.graph S true) keys nextSlots
      (graphMem C m graphFile) keyBase C.rows keyFile)
    (widthPass : FileSpec current pub (Template.output S) nextWidths widthWords
      (keyMem C m keyBase graphFile keyFile) C.widths (C.rows*lanes) widthFile)
    (a : ℕ) (low : keyBase ≤ a) (high : a < keyBase+C.rows) (beforeWidths : a < C.widths) :
    ((post current S).execute current pub m).2 a = keyFile a := by
  let graphCode := Recipe.one (Template.graph S false) nextGraph graphWords
  let keyCode := Recipe.one (Template.graph S true) keys nextSlots
  let widthCode := Recipe.one (Template.output S) nextWidths widthWords
  let gm := graphMem C m graphFile
  let km := keyMem C m keyBase graphFile keyFile
  let wm := widthMem C m keyBase graphFile keyFile widthFile lanes
  have afterKeys : (((Recipe.seq keyCode widthCode).install current).execute current pub gm).2 = wm :=
    seq_image keyCode widthCode current pub gm km wm keyPass.image widthPass.image
  have reached : ((post current S).execute current pub m).2 = wm :=
    seq_image graphCode (.seq keyCode widthCode) current pub m gm wm graph.image afterKeys
  calc
    _ = wm a := congrFun reached a
    _ = km a := ite_eq_right (fun h => (Nat.not_le.mpr beforeWidths) h.1)
    _ = keyFile a := ite_eq_left ⟨low,high⟩


end PostImage
end ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkStage

end OAI
