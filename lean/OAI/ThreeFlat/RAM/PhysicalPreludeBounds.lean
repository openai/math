import OAI.ThreeFlat.RAM.PhysicalImageData

namespace OAI
/-! # Address bounds for each stage of the H preprocessor -/

namespace ThreeFlat.RAM.PhysicalPrelude.Image

open BitLayout PhysicalInputRegions
variable {F : Type*} [Fintype F] [Field F] {w : ℕ} (I : Image F w)

structure Bounds : Prop where
  raw : I.sizes.rawCount<2^w
  scratch : I.sizes.scratch+I.sizes.rawCount<2^w
  packSafe : I.sizes.gateBase+I.sizes.packedWords ≤ I.sizes.scratch+I.sizes.rawTable
  packEnd : I.sizes.scratch+I.sizes.rawTable+w*I.sizes.packedWords<2^w
  parameterEnd : I.sizes.scratch+I.sizes.rawParams+I.parameters<2^w
  parameterSafe : I.sizes.parameterBase ≤ I.sizes.scratch+I.sizes.rawParams
  actualParameters : I.sizes.parameterBase+I.parameters<2^w
  traceEnd : I.sizes.templateBase+11*I.X.cells<2^w
  traceGate : I.sizes.gateBase+11*I.G.cells ≤ 2^w
  tracePorts : I.sizes.portBase+11*I.ports ≤ 2^w
  first : I.firstCell<2^w
  lowScratch : I.firstCell≤I.sizes.scratch
  footprint : BitLayout.footprint I.H<2^w
  rawInputs : I.sizes.scratch+2*I.endpointBits+I.advice<2^w

theorem bounds_of_limit (memory : I.sizes.limit < 2^w) : I.Bounds := by
  let s := I.sizes
  have hcap : s.scratch + s.rawCount < 2^w := memory
  have hraw : s.rawCount ≤ s.scratch := s.scratch_after_raw
  have hpack : s.packedEnd ≤ s.scratch := s.scratch_after_packed
  have g : s.gateBase+11*I.G.cells=s.portBase := rfl
  have q : s.portBase+11*I.ports=s.packedEnd := rfl
  have r : s.templateBase+11*I.X.cells=s.gateBase := rfl
  have ps : s.parameterBase+I.parameters=s.templateBase := rfl
  have p := s.packedEnd_eq
  have tail : s.scratch+s.rawTable+w*s.packedWords=s.scratch+s.rawCount := by
    change s.scratch+s.rawTable+w*s.packedWords=s.scratch+(s.rawTable+w*s.packedWords)
    omega
  have extra : s.rawParams+I.parameters=s.rawTable := rfl
  have start : 2*I.endpointBits+I.advice=s.rawParams := rfl
  have foot : s.parameterBase=BitLayout.footprint I.H := rfl
  have cell : I.firstCell≤BitLayout.footprint I.H := by
    change I.firstCell ≤ I.firstCell + 11*I.H.cells + Fintype.card F * Fintype.card F
    omega
  dsimp only [s] at *
  constructor <;> omega

theorem bounds (h : I.Fits) : I.Bounds := I.bounds_of_limit h.memory

end ThreeFlat.RAM.PhysicalPrelude.Image

end OAI
