import OAI.Computability.NearSquareRoot.CRTPositionNamedBranch
import OAI.Computability.NearSquareRoot.KernelEffectiveFamilyProduct
import OAI.Computability.NearSquareRoot.ScheduleRegisterSelect
import OAI.Computability.IntegerMultiplication.Binary

/-! # Packed strip programs with a rectangular interchange parameter -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace NamedPacked
open IntegerMultiplication Code Strip KernelEffectiveFamily

theorem CarriesAt.right {X : Type} {a : X → ℝ} {u v h : X → Tree} {c : Cmd}
    (r : CarriesAt c a u v) (park : Volume a h) :
    CarriesAt (rightCmd c) a (together h u) (together h v) := by
  obtain ⟨t,run,C,cost⟩ := r.work
  obtain ⟨D,hd⟩ := park
  refine ⟨r.budget,⟨fun x => (h x).count + t x,?_,D+C,fun x => ?_⟩,
    (Volume.fork ⟨D,hd⟩ r.small r.budget)⟩
  · exact command_contract (rightCmd c) from (show Task t u v from ⟨c,run⟩).right h
  · push_cast
    linarith [hd x,cost x]

theorem BreezeAt.right {X : Type} {a : X → ℝ} {r : Regime X} {n l : X → ℕ} {u v h : X → Tree} {c : Cmd}
    (run : BreezeAt c a r n l u v) (park : Alive r n l h) :
    BreezeAt (rightCmd c) a r n l (together h u) (together h v) := by
  obtain ⟨pos,m,go⟩ := run
  obtain ⟨d,stay⟩ := park
  have le (x : X) : mass r n l d x ≤ runrate a r n l (m+d) x :=
    (mass_le (show d ≤ m+d by omega) x).trans (le_mul_of_one_le_right (by unfold mass; positivity) (pos x))
  refine ⟨pos,m+d,(go.larger fun x => rate_higher x (pos x) (show m ≤ m+d by omega)).right ?_⟩
  exact (stay.larger le).small

end NamedPacked

namespace Controlled.Effective

open IntegerMultiplication Code Strip KernelEffectiveFamily NamedPacked CommonRegisters GeneratorSyntax Filter

/-- A command constructor with a computable emitter and a common register limit
on every register-bounded family of children. -/
structure Frame where
  apply : Cmd → Cmd
  effective : ∀ {P : Type} [Primcodable P] {child : P → Cmd}, GeneratorSyntax.Effective ltr child →
    GeneratorSyntax.Effective ltr (fun p => apply (child p))
  within : ∀ R, ∃ B, 0 < B ∧ ∀ child, Within R child → Within B (apply child)

/-- A fixed finite instruction context. The rectangular command is its only
replaceable leaf. Its subcalls never install a new recursive binder. -/
inductive Template where
  | rectangle
  | fixed (cmd : Cmd)
  | next (a b : Template)
  | right (a : Template)
  | branch (pre : Cmd) (a b : Template)
  | frame (f : Frame) (a : Template)

def Template.eval : Template → Cmd → Cmd
  | .rectangle, c => c
  | .fixed f, _ => f
  | .next a b, c => (a.eval c).join (b.eval c)
  | .right a, c => rightCmd (a.eval c)
  | .branch pre a b, c => PositionProgram.branchCmd pre (a.eval c) (b.eval c)
  | .frame f a, c => f.apply (a.eval c)

theorem Template.effective (t : Template) {P : Type} [Primcodable P] {child : P → Cmd}
    (hc : GeneratorSyntax.Effective ltr child) :
    GeneratorSyntax.Effective ltr (fun p => t.eval (child p)) := by
  induction t with
  | rectangle => exact hc
  | fixed c => exact effective_const _ _
  | next a b ha hb => exact ha.join hb
  | right a ha => exact effective_right ha
  | branch pre a b ha hb => exact PositionProgram.effective_branchCmd pre ha hb
  | frame f a ha => exact f.effective ha

theorem Template.within (t : Template) (R : ℕ) :
    ∃ B, 0 < B ∧ ∀ c, Within R c → Within B (t.eval c) := by
  induction t with
  | rectangle =>
    exact ⟨R+1,by omega,fun c hc => RegisterSelect.within_mono (by omega) c hc⟩
  | fixed cmd =>
    obtain ⟨B,pos,h⟩ := ((eventually_gt_atTop (0:ℕ)).and (RegisterSelect.within_eventually cmd)).exists
    exact ⟨B,pos,fun _ _ => h⟩
  | next a b ha hb =>
    obtain ⟨A,hA,ca⟩ := ha
    obtain ⟨B,_,cb⟩ := hb
    exact ⟨max A B,hA.trans_le (le_max_left ..),fun c h => ⟨
      RegisterSelect.within_mono (le_max_left ..) _ (ca c h),
      RegisterSelect.within_mono (le_max_right ..) _ (cb c h)⟩⟩
  | right a ha =>
    obtain ⟨A,_,ca⟩ := ha
    exact ⟨max 3 A,by omega,fun c h =>
      within_right (le_max_left ..) (RegisterSelect.within_mono (le_max_right ..) _ (ca c h))⟩

  | branch pre a b ha hb =>
    obtain ⟨A,pa,ca⟩ := ha
    obtain ⟨B,_,cb⟩ := hb
    obtain ⟨E,preCap⟩ := (RegisterSelect.within_eventually pre).exists
    let M := max (max A B) E
    have aM : A ≤ M := (le_max_left ..).trans (le_max_left ..)
    have bM : B ≤ M := (le_max_right ..).trans (le_max_left ..)
    exact ⟨M,pa.trans_le aM,fun c hc => PositionProgram.within_branchCmd (pa.trans_le aM)
      (RegisterSelect.within_mono (le_max_right ..) _ preCap)
      (RegisterSelect.within_mono aM _ (ca c hc)) (RegisterSelect.within_mono bM _ (cb c hc))⟩
  | frame f a ha =>
    obtain ⟨A,_,ca⟩ := ha
    obtain ⟨B,pb,cb⟩ := f.within A
    exact ⟨B,pb,fun c hc => cb _ (ca _ hc)⟩

/-- One command template for all interchange files and exponents fulfilling
`rect`, across the entire input domain `X`. -/
def Program {X : Type} (rect : Cmd → ℝ → Prop) (width : X → ℕ) (r : Regime X) (n l : X → ℕ)
    (u v : X → Tree) : Prop :=
  ∃ t : Template, ∀ c ρ, 0 ≤ ρ → rect c ρ →
    BreezeAt (t.eval c) (Spindle.modes width (τ := ρ)) r n l u v

namespace Program
variable {X : Type} {rect : Cmd → ℝ → Prop} {width n l : X → ℕ} {r : Regime X} {u v w : X → Tree}

/-- A single zero-exponent computation can be hardwired for all exponents. -/
theorem fixed (h : Breeze (Spindle.modes width (τ := 0)) r n l u v) : Program rect width r n l u v := by
  obtain ⟨c,run⟩ := BreezeAt.exists_of_breeze h
  refine ⟨.fixed c,fun _ _ hr _ => run.raise fun x => ?_⟩
  simpa only [Spindle.modes,Real.rpow_zero] using (Spindle.belly width hr x)

theorem ofRip (h : Rip r n l u v) : Program rect width r n l u v :=
  fixed (Strip.Breeze.launch h (Spindle.belly _ le_rfl))

theorem next (h : Program rect width r n l u v) (g : Program rect width r n l v w) :
    Program rect width r n l u w := by
  obtain ⟨a,go⟩ := h
  obtain ⟨b,run⟩ := g
  exact ⟨.next a b,fun c ρ hρ hc => (go c ρ hρ hc).next (run c ρ hρ hc)⟩

theorem right (h : Program rect width r n l u v) {a : X → Tree} (ha : Alive r n l a) :
    Program rect width r n l (together a u) (together a v) := by
  obtain ⟨t,run⟩ := h
  exact ⟨.right t,fun c ρ hρ hc => (run c ρ hρ hc).right ha⟩

/-- Preserve the original header while the first subroutine consumes its input,
then pass its result and header into the second subroutine. -/
theorem pipe (h : Program rect width r n l (together r.header u) v)
    (g : Program rect width r n l (together r.header v) w)
    (pos : ∀ x, 1 ≤ n x) (data : Alive r n l u) :
    Program rect width r n l (together r.header u) w := by
  have start := Drive.started (l := l) (r := r) pos
  have copy := (Drive.fetch pos data).twice (Rip.alivePair start data)
  exact ((ofRip copy).next (h.right start)).next g

/-- Substitute an effectively emitted rectangle family. One register cutoff
works across all parameters, while the individual header polynomial may vary. -/
theorem emit (h : Program rect width r n l u v) {P : Type} [Primcodable P]
    (child : P → Cmd) (ρ : P → ℝ) (R : ℕ) (effective : GeneratorSyntax.Effective ltr child)
    (registers : ∀ p, Within R (child p)) (positive : ∀ p, 0 ≤ ρ p)
    (correct : ∀ p, rect (child p) (ρ p)) :
    ∃ (cmd : P → Cmd) (B : ℕ), GeneratorSyntax.Effective ltr cmd ∧ 0 < B ∧
      ∀ p, Within B (cmd p) ∧ BreezeAt (cmd p) (Spindle.modes width (τ := ρ p)) r n l u v := by
  obtain ⟨t,run⟩ := h
  obtain ⟨B,pos,bound⟩ := t.within R
  exact ⟨fun p => t.eval (child p),B,t.effective effective,pos,
    fun p => ⟨bound (child p) (registers p),run _ _ (positive p) (correct p)⟩⟩

end Program
end Controlled.Effective

end NearSquareRoot
end Computability
end OAI
