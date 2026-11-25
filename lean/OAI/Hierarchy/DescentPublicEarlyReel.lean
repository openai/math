import OAI.Hierarchy.DescentPublicRotationROM
import OAI.Hierarchy.DescentPublicExteriorRelocation

namespace OAI
/-! # Run the initial cumulative exterior matrix before the terminal cohort is measured -/
namespace Hierarchy.DescentExteriorMatrixUpdate.Calendar
open DescentCompiler DescentSixParty.Chronology DescentColonies DescentPackedColony.Phase.Arena
open DescentExteriorShelf ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
noncomputable section
variable (S : AtomSchedule) (k tail base : ℕ) (tag : ℕ→Bool) (rotation : ℕ→ℕ)
variable (j r t e compact : ℕ)
local notation "B" => S.groupWidth k tail 0+k
local notation "last" => stop S k tail base
local notation "R" => reel S k tail base tag rotation
local notation "span₀" => span j r t e

def earlyAt :=stop S k tail base+S.length+1
def earlyEnd :=earlyAt S k tail base+max (17*span j r t e) (span j r t e+e)
local notation "origin" => earlyAt S k tail base
local notation "roof" => earlyEnd S k tail base j r t e
def earlyProgram (w : ℕ) :=
  (((sheet S k tail base tag w).program).seq (relocate j r t e w compact origin)).seq
    ((R).program j r t e w B S.length origin)
def earlyImage {w : ℕ} (m : Memory w) :=
  (R).result j r t e B S.length origin
    (relocated j r t e compact origin ((sheet S k tail base tag w).output m))
def earlyClock :=(4+10*(S.length*stride S k tail)+(4+18*(17*span j r t e)))+
  (10+((4+58*S.length)+(4+16*e)))

set_option maxHeartbeats 400000 in
theorem early_run {w : ℕ} (m : Memory w) (positive : 0<w) (prev : ∀i<S.length,rotation i<base)
    (lower : compact+32*span₀≤base) (limit : roof<2^w) :
    let P:=earlyProgram S k tail base tag rotation j r t e compact w
    let o:=earlyImage S k tail base tag rotation j r t e compact m
    P.Exec m o (earlyClock S k tail j r t e) ∧ CheapCode P ∧
      (∀a,a<base ∨ roof≤a → o a=m a) :=by
  intro P o
  have spanPos : 0<span₀:=Nat.two_pow_pos _
  have top₁ : origin+17*span₀≤roof:=Nat.add_le_add_left (Nat.le_max_left ..) _
  have top₂ : origin+span₀+e≤roof:=by
    change _≤origin+max (17*span₀) (span₀+e)
    rw [Nat.add_assoc];exact Nat.add_le_add_left (Nat.le_max_right ..) _
  have bot : base≤last:=Nat.le_add_right ..
  have gap : last+S.length+2<2^w:=by change last+S.length+1+17*span₀≤roof at top₁;omega
  have geometry:=room S k tail base tag rotation prev gap
  let s:=sheet S k tail base tag w
  let pre:=s.output m
  let mid:=relocated j r t e compact origin pre
  obtain ⟨print,cheap₁,_,_,kept⟩:=issue S k tail base tag m (by omega)
  obtain ⟨copy,cheap₂,_,edges⟩:=relocate_run (j:=j) (r:=r) (t:=t) (e:=e) compact origin pre
    (by change _≤last+S.length+1;omega) (top₁.trans_lt limit)
  obtain ⟨fold,cheap₃,past⟩:=(R).run (j:=j) (r:=r) (t:=t) (e:=e) B S.length last origin mid
    geometry positive (top₂.trans_lt limit)
  let copyCode := relocate j r t e w compact origin
  let replayCode := (R).program j r t e w B S.length origin
  have copyCheap : CheapCode (s.program.seq copyCode) :=
    cheap_seq (A:=s.program) («B»:=copyCode) cheap₁ cheap₂
  have firstRun : (s.program.seq copyCode).Exec m mid
      ((4+10*(S.length*stride S k tail))+(4+18*(17*span₀))) := by
    intro labels regs keys machine
    exact Procedure.Exec.then (A:=s.program) («B»:=copyCode) (a:=m) (b:=pre) (c:=mid) print copy machine
  have codeEq : P = (s.program.seq copyCode).seq replayCode := rfl
  have resultEq : o = (R).result j r t e B S.length origin mid := rfl
  rw [codeEq]
  constructor
  · rw [resultEq]
    unfold earlyClock
    intro labels regs keys machine
    exact Procedure.Exec.then (A:=s.program.seq copyCode) («B»:=replayCode) (a:=m) (b:=mid)
      (c:=(R).result j r t e B S.length origin mid) firstRun fold machine
  constructor
  · have replayCheap : CheapCode replayCode := by
      dsimp only [replayCode]
      exact @cheap₃
    exact @ProtocolRAM.cheap_seq w (s.program.seq copyCode) replayCode (@copyCheap) (@replayCheap)
  · intro a outside
    have low₀ : last<origin:=by change last<last+S.length+1;omega
    have upper : origin≤roof:=(Nat.le_add_right ..).trans top₁
    have unchanged : o a=mid a:=by
      rcases outside with lo|high
      · exact past a (lo.trans_le bot)
      · have done_:=published_frame (j:=j) (r:=r) (t:=t) (e:=e) origin S.length ((R).cells B)
          (initialized ((R).old 0) B mid) a (fun i alive=>ne_of_lt ((geometry.high i alive).trans_le (upper.trans high)))
          (.inr (top₂.trans high))
        have init:=«initialize» ((R).old 0) B mid geometry.startFit
        exact done_.trans (init.2.2.2 a (ne_of_lt (geometry.startLow.trans_le (upper.trans high))))
    exact unchanged.trans ((edges a (outside.imp (fun h=>h.trans_le (bot.trans low₀.le))
      (fun h=>top₁.trans h))).trans (kept a (outside.imp_right (fun h=>low₀.le.trans (upper.trans h)))))

end
end Hierarchy.DescentExteriorMatrixUpdate.Calendar

end OAI
