import OAI.ThreeFlat.Diagonal.CompressorStageDimensions

namespace OAI
/-! # Stable offsets and lengths for local shrinking-site records -/
namespace ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkStage

def Dimensions.localCapacity (x : Dimensions) := 8*x.oldDegree^2*2^x.colorBits

/-- The kernel descriptors, active motifs, half headers and physical half rows
occupy adjacent arenas, beginning at word `base`. -/
def headerExtra (x : Dimensions) (base : ℕ) (i : ℕ) : ℕ :=
  let sites := x.outputSites
  let kernelLen := 5*sites
  let motifLen := 6*x.localCapacity*sites
  let headerLen := 2*sites
  let halfLen := 8*x.newDegree*sites
  match i with
  | 34 => base
  | 35 => kernelLen
  | 36 => base+kernelLen
  | 37 => motifLen
  | 38 => base+kernelLen+motifLen
  | 39 => headerLen
  | 40 => base+kernelLen+motifLen+headerLen
  | 41 => halfLen
  | 42 => base+kernelLen+motifLen+headerLen+halfLen
  | 43 => x.originalSites
  | 44 => base+kernelLen+motifLen+headerLen+halfLen+x.originalSites
  | 45 => x.originalSites
  | _ => 0

def extraEnd (x : Dimensions) (base : ℕ) := headerExtra x base 44 + headerExtra x base 45

theorem extra_extent (x : Dimensions) (base : ℕ) :
    extraEnd x base = base + (7 + 6*x.localCapacity + 8*x.newDegree)*x.outputSites + 2*x.originalSites := by
  change base+5*x.outputSites+6*x.localCapacity*x.outputSites+2*x.outputSites+
      8*x.newDegree*x.outputSites+x.originalSites+x.originalSites = _
  rw [two_mul x.originalSites]
  ring

end ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkStage

end OAI
