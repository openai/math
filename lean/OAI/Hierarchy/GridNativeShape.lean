import OAI.Hierarchy.GridPhysicalAges
import OAI.Hierarchy.GridAdmissionRoom
import OAI.Hierarchy.GridStructuralHeader
import OAI.Hierarchy.GridProgrammed

namespace OAI
/-! # Selecting the small native input aperture before the programs are installed -/

noncomputable section
namespace Hierarchy.GridNativeShape
open ThreeFlat RAM Diagonal Diagonal.PhysicalStage
open Computability.VPVNP.BurstRAM PrivateRAM Filter GridScale GridDescription TraceDistribution
open scoped Classical

variable {F : Type} [Field F] [Fintype F] (B : Block F)

/-- All machine dimensions, the original input size, and the compact prototype
length are chosen before either controller is installed. A preliminary input
with an empty parameter vector supplies the prototype cardinality. Gate
records and caller addresses are then generated for the true input length. -/
theorem choose {Q : ℕ→ℕ} {D : ℕ→ℝ} (env : Envelopes Q D) (k A c : ℕ) (positive : 0<k) :
    ∀ᶠ w : ℕ in atTop, ∀ q,0<q→q≤Q w→
      let a:=overhead Q D w
      let bank:=pairs A w q
      let E:=external k a bank
      let u:=evalDepth w k A c a q
      let arch:=capacity w
      let reps:=traceBlocks k a
      let cap:=selector k w a-1
      let mount:=E*2+SelfAdvice.textSize (64*w) arch arch
      ∀ {axes : ℕ} (_depth : (axes+1)+w/2=u+1),
      ∃ (S n : ℕ), S=GridSelfHeader.rawSize w E bank n ∧
        n≤(GridStructuralHeader.coefficient B)*(w+1)^14 ∧
        S≤ sector w ∧ 2^(3*w/5)≤cap ∧ cap≤ sector w ∧ 12*bank≤ sector w ∧
        ∀ M : Machine (64*w) arch arch arch, ∃ fit : NativeTrace.Fits M S mount ((axes+1)+w/2) (2^u),
          ∀ hF : Fintype.card F≤2^(64*w),
            let G:=TraceStaticRow.gateTable hF fit.width fit.labels mount (2^u) 0 arch arch ((axes+1)+w/2)
            n=GridStructuralHeader.wordCount (GridStructuralHeader.directory (w:=w) B (axes+1) reps cap).length (TraceReceiverTemplate.count G) (HistoryStageBody.Physical.libraryWords B (64*w)) := by
  let coeff := GridStructuralHeader.coefficient B
  filter_upwards [GridSelfHeader.raw_room_of_poly env k A c coeff 14 positive,
    GridPhysicalAdmission.admission_room env k A c coeff 14 positive,depth_range env k A c,
    sublinear env (10*k+3),sublinear env (20*k+32),
    eventually_ge_atTop (max (Fintype.card F) 1024)] with w raw space dep dex steps hw
  intro q qp qt a bank E u arch reps cap mount axes depth
  have age : 1024≤w := (le_max_right ..).trans hw
  have small : arch≤w := Nat.div_le_self w 1024
  have active : 0<arch := (Nat.div_pos age (by decide))
  have hf : Fintype.card F≤64*w := (le_max_left ..).trans (hw.trans (by omega))
  have hF : Fintype.card F≤2^(64*w) := hf.trans Nat.lt_two_pow_self.le
  have depthHi : u ≤ w+(10*k+3)*a := (dep q qp qt).2
  change (10*k+3)*a ≤ w at dex
  have up : u ≤ 2*w := depthHi.trans ((Nat.add_le_add_left dex w).trans (by omega))
  have dc : (axes+1)+w/2≤64*w := by omega
  have count : reps≤w := steps
  have text := GridDescription.room (age:=age) (p:=arch) (k:=arch) (p':=arch) (k':=arch)
    le_rfl le_rfl le_rfl le_rfl
  have code (n : ℕ) : mount+(1+6*arch+arch)*(64*w)≤GridSelfHeader.rawSize w E bank n := by
    have sc := text.room
    change SelfAdvice.textSize (64*w) arch arch+SelfAdvice.textSize (64*w) arch arch+0≤w^2 at sc
    dsimp only [mount,SelfAdvice.textSize,GridSelfHeader.rawSize] at sc ⊢;omega
  have make (M : Machine (64*w) arch arch arch) (n : ℕ) (ncap : n≤coeff*(w+1)^14) :
      NativeTrace.Fits M (GridSelfHeader.rawSize w E bank n) mount ((axes+1)+w/2) (2^u) := by
    rw [depth]
    exact evaluatorFits M (by omega) up active small small small (raw q qp qt n ncap).1 le_rfl (code n)
  let dummy:=UniversalTick.accept (64*w) arch arch arch active
  let pre:=make dummy 0 (Nat.zero_le _)
  let G:=TraceStaticRow.gateTable hF pre.width pre.labels mount (2^u) 0 arch arch ((axes+1)+w/2)
  let n:=GridStructuralHeader.wordCount (GridStructuralHeader.directory (w:=w) B (axes+1) reps cap).length (TraceReceiverTemplate.count G) (HistoryStageBody.Physical.libraryWords B (64*w))
  have bound : n≤coeff*(w+1)^14 :=
    GridStructuralHeader.parameter_count B (axes+1) reps cap dummy pre hF 0 count hf
      (small.trans (by omega)) (small.trans (by omega)) (small.trans (by omega)) dc
  obtain ⟨below,work,guard,cut⟩:=space q qp qt n bound
  exact ⟨_,n,rfl,bound,below,cut,guard,work,fun M=>⟨make M n bound,fun _=>rfl⟩⟩

theorem even_input {w : ℕ} (even : Even w) (e bank words : ℕ) :
    Even (GridSelfHeader.rawSize w e bank words) := by
  obtain ⟨z,rfl⟩:=even
  refine ⟨e+2*z^2+bank*(2*z^2)+(words+GridReceiverHeader.count (z+z))*(64*z),?_⟩
  unfold GridSelfHeader.rawSize
  ring

end Hierarchy.GridNativeShape
end

end OAI
