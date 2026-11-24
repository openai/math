import OAI.Computability.VPVNP.RAMProcessorCallInvariant
import OAI.Computability.VPVNP.RAMApplications
import OAI.Computability.VPVNP.RAMTapeSitePostClock
import OAI.Computability.VPVNP.RAMTapeNamed

/-!
# The literal processor clock for the two RAM transcript applications

The estimate counts the site-entry and call loops, the closing checks, all
startup and sorting work, and the two-tape simulation of the named bit stacks.
The constants for a fixed template and its ports affect the threshold in the
input length. The clock exponent is uniform over the site and its choices.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.SiteProcessor

open Filter BurstRAM

/-- Upper bound for starting a bucket call, resetting its registers and private
log, and executing its private and external instruction segments. -/
def perCallEstimate (regs w H fuel : ℕ) :=
  (16*w+7 + 80*(H+fuel+w+1)) + (regs*(8*w+3) + 3*(fuel*(w+1)+1)+2) + callWork w fuel

theorem CallReady.start_and_call_le {w p regs k H fuel : ℕ} {hw : 2 ≤ w} {first : Bool}
    {s : Snapshot w p regs k} {ys} (h : CallReady hw H fuel first s ys) :
    (16*w+7+s.startTicks) + (regs*(8*w+3)+3*(s.cfg.writes.length*(w+1)+1)+2) + callWork w fuel ≤
      perCallEstimate regs w H fuel := by
  have hlog := h.privateClock
  have hcredit := h.callCredit
  have hsaved := h.saved
  have hord := h.ordinal
  have hs : s.startTicks ≤ 80*(H+fuel+w+1) := by
    unfold Snapshot.startTicks CallCredit.resetTicks
    rw [h.publicH, h.publicFuel]
    omega
  have hl := Nat.mul_le_mul_right (w+1) (show s.cfg.writes.length ≤ fuel by omega)
  unfold perCallEstimate
  omega

theorem perCallEstimate_le (regs w H fuel : ℕ) :
    perCallEstimate regs w H fuel ≤ 1000*(regs+1)*(H+1)^2*(fuel+1)^3*(w+1)^4 := by
  let D := (H+1)^2*(fuel+1)^3*(w+1)^4
  have hH : H+1 ≤ (H+1)^2 := Nat.le_self_pow (by decide) _
  have hf : fuel+1 ≤ (fuel+1)^3 := Nat.le_self_pow (by decide) _
  have hw : w+1 ≤ (w+1)^4 := Nat.le_self_pow (by decide) _
  have hBig : (fuel+1)^3*(w+1)^4 ≤ D := by
    dsimp only [D]
    rw [Nat.mul_assoc]
    exact Nat.le_mul_of_pos_left _ (by positivity)
  have hD : H+1 ≤ D := hH.trans ((Nat.le_mul_of_pos_right _ (by positivity :
      0 < (fuel+1)^3)).trans (Nat.le_mul_of_pos_right _ (by positivity)))
  have hfD : fuel+1 ≤ D := hf.trans ((Nat.le_mul_of_pos_right _ (by positivity)).trans hBig)
  have hwD : w+1 ≤ D := hw.trans ((Nat.le_mul_of_pos_left _ (by positivity)).trans hBig)
  have hfw : (fuel+1)*(w+1) ≤ D := (Nat.mul_le_mul hf hw).trans hBig
  have hsq : (fuel+1)^2 ≤ D := (Nat.pow_le_pow_right (Nat.succ_pos _) (by decide : 2 ≤ 3)).trans
    ((Nat.le_mul_of_pos_right _ (by positivity)).trans hBig)
  have hcube : (fuel+1)^3*(w+1)^2 ≤ D := (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right
    (Nat.succ_pos _) (by decide : 2 ≤ 4))).trans hBig
  have hscan : callWork w fuel ≤ 304*D := by
    rw [show callWork w fuel = 100*((fuel+1)^3*(w+1)^2) + 4*(fuel+1)^2 + 200*((fuel+1)*(w+1)) by
      unfold callWork segmentWork ISA.prepareBound; ring]
    omega
  have hreg : regs*(8*w+3) ≤ 11*(regs*D) := by
    rw [show 11*(regs*D)=regs*(11*D) by ring]
    exact Nat.mul_le_mul_left _ (by omega)
  have hlog : fuel*(w+1) ≤ D := (Nat.mul_le_mul_right _ (Nat.le_succ fuel)).trans hfw
  rw [show 1000*(regs+1)*(H+1)^2*(fuel+1)^3*(w+1)^4 = 1000*(regs*D)+1000*D by dsimp [D]; ring]
  unfold perCallEstimate
  omega

private theorem startup_le {u n c startup : ℕ} (hn : 1 ≤ n)
    (hc : c * 2 ^ max 7 (u+1) ≤ n)
    (hstart : startup ≤ c * (n+1) ^ max 7 (u+1)) :
    startup ≤ n^(3*u+8) := by
  let k := max 7 (u+1)
  calc
    startup ≤ c*(2*n)^k := hstart.trans (Nat.mul_le_mul_left c (Nat.pow_le_pow_left (by omega) _))
    _ = (c*2^k)*n^k := by rw [mul_pow, Nat.mul_assoc]
    _ ≤ n*n^k := Nat.mul_le_mul_right _ hc
    _ = n^(k+1) := by rw [pow_succ, Nat.mul_comm]
    _ ≤ n^(3*u+8) := Nat.pow_le_pow_right hn (by dsimp [k]; omega)

private theorem call_le {u n c fuel H w work : ℕ} (hn : 1 ≤ n) (hc : 1152*c ≤ n)
    (hw : w ≤ n) (hH : H ≤ 2*n) (hf : fuel ≤ n^u)
    (hwork : work ≤ c*(H+1)^2*(fuel+1)^3*(w+1)^4) :
    work ≤ n^(3*u+7) := by
  have hp : 1 ≤ n^u := Nat.one_le_pow _ _ hn
  calc
    work ≤ c*(3*n)^2*(2*n^u)^3*(2*n)^4 := hwork.trans (Nat.mul_le_mul
      (Nat.mul_le_mul (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _))
        (Nat.pow_le_pow_left (by omega) _)) (Nat.pow_le_pow_left (by omega) _))
    _ = (1152*c)*n^(3*u+6) := by
      rw [show 3*u+6=u*3+6 by omega, pow_add, pow_mul]
      ring
    _ ≤ n*n^(3*u+6) := Nat.mul_le_mul_right _ hc
    _ = n^(3*u+7) := by rw [pow_succ n (3*u+6), Nat.mul_comm]

private theorem loop_le {n H w work E : ℕ} (hn : 1 ≤ n) (hw : w ≤ n) (hH : H ≤ 2*n)
    (hE : n ≤ E) (hwork : work ≤ E) :
    siteWork w H work + closeWork w H ≤ 1020*(n*E) := by
  have h₁ : 60*w+41+work ≤ 102*E := by omega
  have h₂ : (2*H-1)*(work+(40*w+30)) ≤ (4*n)*(71*E) :=
    Nat.mul_le_mul (by omega) (by omega)
  have h₃ : (4*H)*(25*w+12) ≤ (8*n)*(37*E) := Nat.mul_le_mul (by omega) (by omega)
  have h₄ : (4*H*5*w) ≤ (40*n)*E := Nat.mul_le_mul (by omega) (by omega)
  have h₅ : 40*w+42+1+1 ≤ 84*E := by omega
  have hE' : E ≤ n*E := Nat.le_mul_of_pos_left _ hn
  unfold siteWork closeWork
  nlinarith only [h₁,h₂,h₃,h₄,h₅,hE',Nat.zero_le (n*E)]

/-- Absorb all concrete stack stages into a single `n` power. The threshold is
independent of the register contents, site, bucket, and clock realization. -/
theorem eventually_stack_clock (u cstart ccall : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ w H fuel startup post work T : ℕ,
      w ≤ n → H ≤ 2*n → fuel ≤ n^u →
      startup ≤ cstart*(n+1)^max 7 (u+1) → post ≤ n^7 →
      work ≤ ccall*(H+1)^2*(fuel+1)^3*(w+1)^4 →
      T ≤ startup + siteWork w H work + closeWork w H + post → T ≤ n^(3*u+9) := by
  filter_upwards [eventually_ge_atTop 1024, eventually_ge_atTop (1152*ccall),
    eventually_ge_atTop (cstart*2^max 7 (u+1))] with n hn hcall hstart
  intro w H fuel startup post work T hw hH hf hs hp hc hT
  have h₀ : 1 ≤ n := by omega
  have start := startup_le h₀ hstart hs
  have call := call_le h₀ hcall hw hH hf hc
  have loop := loop_le h₀ hw hH (Nat.le_self_pow (by omega : 3*u+7 ≠ 0) n) call
  rw [← Nat.pow_succ'] at loop
  change siteWork w H work + closeWork w H ≤ 1020 * n^(3*u+8) at loop
  have fin := hp.trans (Nat.pow_le_pow_right h₀ (by omega : 7 ≤ 3*u+8))
  have bound : T ≤ 1024*n^(3*u+8) := by omega
  exact bound.trans ((Nat.mul_le_mul_right _ hn).trans_eq (Nat.pow_succ' ..).symm)

/-- Exact physical two-tape simulation overhead used by `input_count_labeled`. -/
theorem eventually_physical_clock (u cstart ccall ports : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ w H fuel startup post work T : ℕ,
      w ≤ n → H ≤ 2*n → fuel ≤ n^u →
      startup ≤ cstart*(n+1)^max 7 (u+1) → post ≤ n^7 →
      work ≤ ccall*(H+1)^2*(fuel+1)^3*(w+1)^4 →
      T ≤ startup + siteWork w H work + closeWork w H + post →
      T*(6*(n+(ports+1)+T)+4) ≤ n^(10*u+30) := by
  filter_upwards [eventually_stack_clock u cstart ccall, eventually_ge_atTop ports,
    eventually_ge_atTop 28] with n stack hports hn
  intro w H fuel startup post work T hw hH hf hs hp hc hT
  have hs' := stack w H fuel startup post work T hw hH hf hs hp hc hT
  let A := n^(3*u+9)
  have hA : n ≤ A := Nat.le_self_pow (by omega : 3*u+9 ≠ 0) _
  have ht : T ≤ A := hs'
  calc
    _ ≤ A*(28*A) := Nat.mul_le_mul ht (by omega)
    _ = 28*n^((3*u+9)*2) := by dsimp [A]; rw [pow_mul]; ring
    _ ≤ n*n^((3*u+9)*2) := Nat.mul_le_mul_right _ hn
    _ = n^((3*u+9)*2+1) := (Nat.pow_succ' ..).symm
    _ ≤ n^(10*u+30) := Nat.pow_le_pow_right (by omega) (by omega)

/-- Physical stack budget through the last incident-record check. The
postprocessor includes its sorting startup, all row exchanges, and its terminal
flag and boundary scans. -/
def totalStackCutoff (d e w regs fuel startup : ℕ) :=
  startup + siteWork w (2^e) (perCallEstimate regs w (2^e) fuel) +
    closeWork w (2^e) + SitePost.budget d e w 0

/-- A graph realization whose individual call costs satisfy the physical
estimate is covered by the same total cutoff. -/
theorem le_totalStackCutoff {d e w regs fuel startup work T : ℕ}
    (hcall : work ≤ perCallEstimate regs w (2^e) fuel)
    (hT : T ≤ startup + siteWork w (2^e) work + closeWork w (2^e) + SitePost.budget d e w 0) :
    T ≤ totalStackCutoff d e w regs fuel startup := by
  apply hT.trans
  unfold totalStackCutoff siteWork
  gcongr

/-- The actual named-stack tape clock, including the closed memory checker,
at the paper's processor parameters. -/
def ApplicationClock (n d e w u regs cstart ports : ℕ) : Prop :=
  ∀ fuel startup T : ℕ, fuel ≤ n^u → startup ≤ cstart*(n+1)^max 7 (u+1) →
    T ≤ totalStackCutoff d e w regs fuel startup →
    T*(6*(n+(ports+1)+T)+4) ≤ n^(10*u+30) ∧ T*(6*(n+(ports+1)+T)+4) ≤ n^clockExponent

theorem eventually_application_clock (u regs cstart ports : ℕ) (hexp : 10*u+30 ≤ clockExponent) :
    ∀ᶠ n : ℕ in atTop, ∀ d e w, ProcessorBudget n d e w → ApplicationClock n d e w u regs cstart ports := by
  filter_upwards [eventually_physical_clock u cstart (1000*(regs+1)) ports,
    eventually_ge_atTop 4000010] with n hclock hn
  intro d e w budget fuel startup T hf hstart hT
  have hpost := SitePost.budget_le (d := d) hn budget.bucket_le (by have := budget.phase_le; omega) budget.word_le
  have h := hclock w (2^e) fuel startup (SitePost.budget d e w 0)
    (perCallEstimate regs w (2^e) fuel) T budget.word_le budget.bucket_le hf hstart hpost
    (perCallEstimate_le ..) hT
  exact ⟨h, h.trans (Nat.pow_le_pow_right (by omega) hexp)⟩

/-- One length threshold covers the live and virtual processors, with their
respective private fuels `n^10000` and `n^10`. The two templates and their
numbers of ports and registers may differ. -/
theorem eventually_both_application_clocks {B : ℕ} (hB : 1 ≤ B) {δ : ℝ}
    (hδ : 0 ≤ δ) (hδ' : δ ≤ 1) (liveRegs liveStart livePorts virtualRegs virtualStart virtualPorts : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      ApplicationClock n (addressWidth B n) (Compression.bucketExponent (1-δ) n)
        (CursorBounds.wordBits B n) 10000 liveRegs liveStart livePorts ∧
      ApplicationClock n (CursorBounds.virtualBits B n) (roundedUp 1 4 n)
        (CursorBounds.wordBits B n) 10 virtualRegs virtualStart virtualPorts := by
  filter_upwards [eventually_bothProcessorBudgets hB hδ hδ',
    eventually_application_clock 10000 liveRegs liveStart livePorts (by decide),
    eventually_application_clock 10 virtualRegs virtualStart virtualPorts (by decide)] with n h live virtual
  exact ⟨live _ _ _ h.1, virtual _ _ _ h.2⟩

end RAMTape.SiteProcessor

end VPVNP
end Computability
end OAI
