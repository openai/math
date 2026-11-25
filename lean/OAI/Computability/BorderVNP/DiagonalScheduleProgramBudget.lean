import OAI.Computability.BorderVNP.DiagonalAdmissibleRange
import OAI.Computability.BorderVNP.PackedPotential
import OAI.Computability.BorderVNP.TeamSiteTimedGeometry
import OAI.Computability.BorderVNP.TransmissionJointGeometry

/-! # The executable processor table and the normalized shortening recurrence -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Filter TeamScales TeamContraction TeamContraction.ProcessorSlots TeamSite VPVNP BurstRAM
open GeometryAdviceRate (packetWords)

/-- Quantitative (6.1) iteration, at the same rounded epoch count and exterior
link budget as the physical machine. -/
def nonlocalWidthAt (τ : ℝ) (d : ℕ) (A B ε : ℝ) (n r : ℕ) : Prop :=
  ∀ I : ℕ → ℝ, I 0 ≤ A*volume τ r n*(logWidth r n:ℝ)^d →
    (∀ i < epochs τ n, I (i+1) ≤ I i/2+B*r*(n:ℝ)^(9/10:ℝ)) →
    I (epochs τ n) ≤ ε*exterior (τ/5) r n

/-- The concrete stream for the processor's true (possibly timed) table and
its private half-literal. The prefix is computed from that table's code. -/
def programStreamAt (physical : UniversalMachine.Program) (E d : ℕ) (α A : ℝ) (n r : ℕ) : Prop :=
  ∀ original gates u o b dense : ℕ, ∀ L : Packing.Directory.Layout,
    1 ≤ b → gates ≤ 4*original →
    ((original+u+o*b:ℕ):ℝ) ≤ A*r*(n:ℝ)^(93/100:ℝ)*(logWidth r n:ℝ)^d →
    L.literal = literal α n →
    let w := logWidth r n^(E+1)
    let start := freeStartWith physical r 32 64 w n
    let words := packetWords gates u o b
    let bits := words*w
    let stripe := geometryStripe L.literal bits r dense words
    JointRoom L start (FieldProcessor.freeWidth physical α 32 64 r w n) (emptyBoot start) stripe ∧
      bits ≤ r*stripe.width ∧ GeometryAdviceRate.ticks gates u o b w+bits ≤ r*width n (95/100:ℝ)

/-- Geometry for the actual supplied public table, including the trusted
private timer, and the nonlocal-width allowance for every measured history. -/
structure ProgramBudget (α τ : ℝ) (E d : ℕ) (ω : ℝ) : Prop where
  table : ∀ {pc μ g : ℕ} {Q Γ : Type} [Fintype Q]
    (_P : TeamOpcode.Program pc 64 32 8) (_lib : Fin 8 → Macro Q Γ μ g)
    (physical : UniversalMachine.Program), AdmissibleRange ω (fun n r => ∀ other : ℕ,
      FieldProcessor.Scale physical pc 64 32 α (τ/5) r n other (logWidth r n^(E+1))
        (Wires.sortExponent (block (τ/5) n)))
  stream : ∀ A : ℝ, 0 ≤ A → ∀ physical, AdmissibleRange ω (programStreamAt physical E d α A)
  nonlocalWidth : ∀ A B ε : ℝ, 0 ≤ A → 0 ≤ B → 0 < ε →
    AdmissibleRange ω (nonlocalWidthAt τ d A B ε)

theorem ProgramBudget.shrink {α τ : ℝ} {E d : ℕ} {u v : ℝ}
    (h : ProgramBudget α τ E d v) (le : u ≤ v) : ProgramBudget α τ E d u where
  table P lib physical := (h.table P lib physical).shrink le
  stream A ha physical := (h.stream A ha physical).shrink le
  nonlocalWidth A B ε ha hb hε := (h.nonlocalWidth A B ε ha hb hε).shrink le

theorem exists_programBudget {α τ : ℝ} (_ha : 0 < α) (hs : α < 1/1000)
    (ht : 0 < τ) (hts : τ < α/100) (E d : ℕ) :
    ∃ ω : ℝ, 0 < ω ∧ ProgramBudget α τ E d ω := by
  obtain ⟨wp,hp,programs⟩ := FieldProcessor.eventually_programGeometry E
    (show α < 3 by linarith) (show 0 < τ/5 by positivity) (by linarith) (by linarith)
  obtain ⟨wd,hd,decay⟩ := Packing.eventually_charged_width ht (by linarith) d
  obtain ⟨ws,hws,stripes⟩ := GeometryAdviceRate.eventually_fits d (E+1) (α := α) (by linarith)
  refine ⟨min wp (min ws wd),lt_min hp (lt_min hws hd),⟨?_,?_,?_⟩⟩
  · intro pc μ g Q Γ inst P lib physical
    exact (show AdmissibleRange wp _ from programs P lib physical).shrink (min_le_left ..)
  · intro A hA physical
    apply AdmissibleRange.shrink (v := ws) _ ((min_le_right ..).trans (min_le_left ..))
    filter_upwards [stripes A 1 hA (by norm_num) physical 32 64] with n fit
    intro r hr range original gates u o b dense L hb hg size lit w start words bits stripe
    have hw : (w:ℝ) ≤ 1*(logWidth r n:ℝ)^(E+1) := by simp [w]
    obtain ⟨time,head,cap,_,endCap⟩ := fit r original gates u o b w hr range hb hg size hw
    have hstart : start ≤ L.literal/4 := lit ▸ head.le
    refine ⟨⟨?_,le_rfl,?_,?_⟩,cap,time⟩
    · change start+(literal α n-start)=L.literal
      rw [← lit]; omega
    · change start+0 ≤ L.literal/4
      omega
    · simpa only [stripe,geometryStripe,lit] using endCap
  · intro A B ε ha hb hε
    exact (show AdmissibleRange wd _ from decay A B ε ha hb hε).shrink ((min_le_right ..).trans (min_le_right ..))

end Diagonal

end BorderVNP
end Computability
end OAI
