import OAI.ThreeFlat.Diagonal.TraceStartupArithmetic
import OAI.ThreeFlat.RAM.RawTickStartup

namespace OAI
/-! # The physical preprocessing machine meets the trace volume and word bounds -/

namespace ThreeFlat.Diagonal.TraceVolume

open RAM
noncomputable section
variable {F : Type} [Fintype F] [CommSemiring F] {t p q b w u : ℕ}
    (G : BitNetwork F q) (input : Fin t → Fin q → BitSource b p)
local notation "X" => PhysicalTraceSource.expanded G input
local notation "n" => FixedTraceImage.count G
local notation "W" => 16*u^10

omit [Fintype F] in
theorem startup_cost : RawTickStartup.cost (w:=w) G input ≤
    work t p b G.internal G.cells q w (FixedTraceProgram.program w).binds :=
  preparation_cost t p b G.cells G.internal q w _

omit [Fintype F] in
theorem startup_fits_after_input (hu : 1≤u) (ht : 1≤t) {source : ℕ} (hsource : source≤2^(2*u^10))
    (hw : work t p b G.internal G.cells q W (FixedTraceProgram.program W).binds ≤ 2^(u^10)) :
    let raw := source+W*n
    let packed := raw+11*(X).cells
    RawTickStartup.Fits (w:=W) G input source raw packed := by
  obtain ⟨rawFit,packedFit,rawSmall,cellSmall,sourceSmall,localFit,cellFit⟩ :=
    preparation_space_after_input hu ht hsource hw
  exact ⟨Or.inr (Nat.le_add_right _ _),packedFit,rawFit,le_rfl,
    RawTickBuilder.diagonal_fit X u _ hu rawSmall cellSmall sourceSmall,localFit,cellFit⟩

omit [Fintype F] in
theorem startup_fits (hu : 1≤u) (ht : 1≤t) {source : ℕ} (hsource : source≤2^(u^10))
    (hw : work t p b G.internal G.cells q W (FixedTraceProgram.program W).binds ≤ 2^(u^10)) :
    let raw := source+W*n
    let packed := raw+11*(X).cells
    RawTickStartup.Fits (w:=W) G input source raw packed :=
  startup_fits_after_input G input hu ht (hsource.trans (Nat.pow_le_pow_right (by decide) (by omega))) hw

end
end ThreeFlat.Diagonal.TraceVolume

end OAI
