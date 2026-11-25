import OAI.Computability.BorderVNP.RoutingISATableSetup

/-! # Installing the positional divisors for cube labels

For an alphabet of size d and a coordinates the fixed loop writes d^j in
position j of the table named by frame 62. The last multiplication also
fits because the full label count is d^a.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.CubePowers

open VPVNP.BurstRAM

/-- Read the public dimension, alphabet and destination; start at the zeroth power. -/
def setup : Code := .block [readFrame 30 62 63 59,readFrame 31 62 63 60,readFrame 32 62 63 62,
  .constant 33 0,.constant 34 1,.constant 35 1]

/-- Write one power and advance both the number and its position. -/
def step : Code := .block [.binary .add 36 32 33,.store 36 34,
  .binary .mul 34 34 30,.binary .add 33 33 35]

/-- Initialize every divisor used for decoding label coordinates. -/
def install : Code := .seq setup (.whileLt 33 31 step)

/-- The exact table after the first k consecutive powers have been stored. -/
def image (d base k : ℕ) (m : ℕ → ℕ) (a : ℕ) : ℕ :=
  if base ≤ a ∧ a-base < k then d^(a-base) else m a

private theorem image_succ (d base i : ℕ) (m : ℕ → ℕ) :
    Function.update (image d base i m) (base+i) (d^i) = image d base (i+1) m := by
  funext a
  by_cases e : a=base+i
  · subst a; simp [image]
  · rw [Function.update_of_ne e]
    unfold image
    split_ifs <;> first | rfl | omega

/-- On a real fitted primary frame the fixed program writes the entire base-d
power table, retains the outside words, and uses at most 16+5a ticks. -/
theorem install_run {w : ℕ} (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
    (s : Bank w) (m : Memory w) (d a base : ℕ)
    (hd : readings m (readings pub 0+59)=d) (ha : readings m (readings pub 0+60)=a)
    (hb : readings m (readings pub 0+62)=base) (dpos : 1 ≤ d)
    (fr : readings pub 0+62 < 2^w) (room : base+a < 2^w) (count : d^a < 2^w) :
    BoundedRun pub mac install s m (16+5*a) (fun z ↦ z.mem=image d base a (readings m)) := by
  let I (i : ℕ) (z : NatState) :=
    z.reg 30=d ∧ z.reg 31=a ∧ z.reg 32=base ∧ z.reg 33=i ∧ z.reg 34=d^i ∧ z.reg 35=1 ∧
      z.mem=image d base i (readings m)
  have hw : 1 < 2^w := by omega
  have fs (k : Reg) (f : Word 8) (z : NatState) (h : f.val ≤ 62) :
      (readFrame k 62 63 f).fixedSafe w (readings pub) z :=
    readFrame_fixedSafe _ _ _ _ _ (by omega)
  have start : BoundedRun pub mac setup s m setup.slots (I 0) := by
    apply (setup.runFixed pub mac s m ?_).mono le_rfl
    · rintro z rfl
      simp (config := {decide:=true}) [I,setup,Code.block,readFrame_fixedEval,Code.fixedEval,Code.evalNat,
        NatState.ofWords,hd,ha,hb]
      funext addr; simp [image]
    · simp (disch := decide) [setup,Code.block,Code.fixedSafe,Code.safeReadOnly,fs,hw]
  have body (i : ℕ) (hi : i<a) (t : Bank w) (mt : Memory w) (inv : I i (.ofWords t mt)) :
      BoundedRun pub mac step t mt step.slots (I (i+1)) := by
    let z := NatState.ofWords t mt
    change I i z at inv
    obtain ⟨r30,r31,r32,r33,r34,r35,mem⟩ := inv
    have powFit : d^i*d < 2^w := by
      rw [← pow_succ]
      exact (pow_le_pow_right₀ dpos hi).trans_lt count
    apply (step.runFixed pub mac t mt ?_).mono le_rfl
    · rintro z' rfl
      change I (i+1) (step.fixedEval _ z)
      simp (config := {decide:=true}) [I,step,Code.block,Code.fixedEval,Code.evalNat,addressOp,r30,
        r31,r32,r33,r34,r35,mem,pow_succ,image_succ]
    · change step.fixedSafe w _ z
      simp (config := {decide:=true}) [step,Code.block,Code.fixedSafe,Code.fixedEval,Code.safeReadOnly,
        Code.evalNat,addressOpFits,r30,r32,r33,r34,r35,powFit]
      omega
  have run := start.seq (fun t mt init ↦ run_counted_loop pub mac 33 31 step a step.slots I
    (fun _ _ hz ↦ ⟨hz.2.2.2.1,hz.2.1⟩) body 0 (Nat.zero_le _) t mt init)
  exact run.mono (by change 15+((a-0)*5+1) ≤ _; omega) fun _ h ↦ h.2.2.2.2.2.2

end RoutingISA.CubePowers

end BorderVNP
end Computability
end OAI
