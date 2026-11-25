import OAI.Computability.NearSquareRoot.CRTPositionRowCommandCaps
import OAI.Computability.NearSquareRoot.CRTControlledRowPackets
import OAI.Computability.NearSquareRoot.FixedCandidateEffectiveTask

/-! # Fixed commands for carving and collecting the high-prefix row packets -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Controlled.PositionRows.Window.Packets

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip
open IntegerMultiplication.Adic IntegerMultiplication.Loom
open NearSquareRoot.Space NearSquareRoot.EffectiveBoundedTask

noncomputable section

private def rawWidth (x : Window) := x.mid + x.lo

private theorem hasRawWidth : regime.Has (tally ∘ rawWidth) :=
  (show IntegerMultiplication.Staff.Realizes regime mid from hasMid).plus
    (show IntegerMultiplication.Staff.Realizes regime lo from hasLo)

private theorem area (x : Window) : 2^x.hi * 2^(rawWidth x) ≤ vol x := by
  have fit : x.hi + rawWidth x = x.k := by have := x.fit; unfold rawWidth mid; omega
  rw [← pow_add, fit]
  exact Nat.le_mul_of_pos_right _ x.pos

private theorem positive (x : Window) : 1 ≤ vol x := Nat.mul_pos (Nat.two_pow_pos _) x.pos

private structure Program where
  degree : ℕ
  cap : ℕ
  cost : Window → ℕ
  pre : Cmd
  post : Cmd
  prepare : Runs pre cost cost (fun x => Tree.fork (regime.header x) (flat x)) ins
  gather : Runs post cost cost outs result
  paid : ∀ x, payloadBits degree x.k ≤ x.lo → payloadBits degree x.k ≤ x.hi →
    cost x ≤ cap*vol x ∧ (ins x).count ≤ cap*vol x ∧ (outs x).count ≤ cap*vol x

private theorem program_exists : Nonempty Program := by
  obtain ⟨d, dims⟩ := packetRulers (Adic.terminal (p := 2) (by decide) hi hasHi)
    (Adic.terminal (p := 2) (by decide) rawWidth hasRawWidth)
  obtain ⟨e, heads⟩ := fixedHeaderCarries hi hasHi
  let setup (x : Window) := max (2^x.hi) (2^(rawWidth x))*(x.k+1)^(max d e)
  have powBound (x : Window) (j : ℕ) (h : j ≤ max d e) :=
    Nat.pow_le_pow_right (show 0 < x.k+1 by omega) h
  have dims0 := dims setup (fun x => by
    simp only [lineSize]
    exact Nat.mul_le_mul_left _ (powBound x d (le_max_left ..)))
  have heads0 := heads setup (fun x => Nat.mul_le_mul (le_max_left ..) (powBound x e (le_max_right ..)))
  let budget (x : Window) := max (vol x) (max (setup x) (max (flat x).count (outs x).count))
  let w (x : Window) := (budget x : ℝ)
  have vol_le (x : Window) : vol x ≤ budget x := le_max_left ..
  have pos (x : Window) : 1 ≤ w x := by
    change (1 : ℝ) ≤ (budget x : ℝ)
    exact_mod_cast (positive x).trans (vol_le x)
  have cover (x : Window) : (setup x : ℝ) ≤ w x := by
    change (setup x : ℝ) ≤ (budget x : ℝ)
    exact_mod_cast (show setup x ≤ budget x from (le_max_left ..).trans (le_max_right ..))
  let s (x : Window) := line 2 x.hi
  let t (x : Window) := line 2 (rawWidth x)
  let f (x : Window) (ab : Block 2 x.hi × Block 2 (rawWidth x)) :=
    cells x ((outer x).cast ab)
  let g (x : Window) (ab : Block 2 x.hi × Block 2 (rawWidth x)) :=
    cells x (routed x ((outer x).cast ab))
  have geometry : ∃ E : ℕ, ∀ x : Window, ((s x).count+1 : ℝ)*((t x).count+1) ≤ (E : ℝ)*w x := by
    refine ⟨4, fun x => ?_⟩
    change (((line 2 x.hi).count : ℝ)+1)*(((line 2 (rawWidth x)).count : ℝ)+1) ≤ (4 : ℕ)*(budget x : ℝ)
    simp only [lineSize]
    have h₁ := Nat.two_pow_pos x.hi
    have h₂ := Nat.two_pow_pos (rawWidth x)
    exact_mod_cast (calc
      (2^x.hi+1)*(2^(rawWidth x)+1) ≤ (2*2^x.hi)*(2*2^(rawWidth x)) :=
        Nat.mul_le_mul (by omega) (by omega)
      _ = 4*(2^x.hi*2^(rawWidth x)) := by ring
      _ ≤ _ := Nat.mul_le_mul_left 4 ((area x).trans (vol_le x)))
  have srcEq (x : Window) : stackRun (fun x => (s x).cart (t x)) f x = flat x :=
    ((outer x).packet (cells x)).symm
  have dstEq (x : Window) : stackRun (fun x => (s x).cart (t x)) g x = result x :=
    ((outer x).packet (cells x ∘ routed x)).symm
  have flatCap : Volume w (stackRun (fun x => (s x).cart (t x)) f) := by
    refine ⟨1, fun x => ?_⟩
    rw [srcEq]
    simp only [Nat.cast_one, one_mul]
    exact Nat.cast_le.mpr (show (flat x).count ≤ budget x from
      (le_max_left ..).trans ((le_max_right ..).trans (le_max_right ..)))
  have outCap : Volume w outs := by
    refine ⟨1, fun x => ?_⟩
    simp only [Nat.cast_one, one_mul]
    exact Nat.cast_le.mpr (show (outs x).count ≤ budget x from
      (le_max_right ..).trans ((le_max_right ..).trans (le_max_right ..)))
  have start := boundedOfCarries (prepareRowPackets s t f (dims0.larger cover)
    (heads0.larger cover) geometry flatCap)
  have stop := boundedOfCarries (collectRowPackets s t g pos outCap)
  have prep : BoundedTask budget budget (fun x => Tree.fork (regime.header x) (flat x)) ins :=
    start.conform (fun _ => rfl) (fun _ => rfl)
      (fun x => congrArg (Tree.fork (regime.header x)) (srcEq x)) (fun _ => rfl)
  have gather : BoundedTask budget budget outs result :=
    stop.conform (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) dstEq
  obtain ⟨pre, hp⟩ := prep
  obtain ⟨post, hq⟩ := gather
  obtain ⟨D, C, bound⟩ := caps (max d e)
  refine ⟨⟨D, C+1, budget, pre, post, hp, hq, ?_⟩⟩
  intro x low high
  obtain ⟨metadata, cin, cout, cflat⟩ := bound x low high
  have hV : vol x ≤ (C+1)*vol x := Nat.le_mul_of_pos_left _ (Nat.succ_pos _)
  have hC : C*vol x ≤ (C+1)*vol x := Nat.mul_le_mul_right _ (Nat.le_succ _)
  exact ⟨max_le hV (max_le (metadata.trans hC) (max_le (cflat.trans hC) (cout.trans hC))),
    cin.trans hC, cout.trans hC⟩

private def program : Program := Classical.choice program_exists

def degree : ℕ := program.degree
def capCoefficient : ℕ := program.cap
def preCmd : Cmd := program.pre
def postCmd : Cmd := program.post

/-- The unconditional window budget includes the ruler work and the sizes of both row streams. -/
def cost : Window → ℕ := program.cost

/-- The fixed program files act on every window, including windows with no reserved bits. -/
theorem allRuns : Runs preCmd cost cost (fun x => Tree.fork (regime.header x) (flat x)) ins ∧
    Runs postCmd cost cost outs result :=
  ⟨program.prepare, program.gather⟩

theorem commandRuns {Y : Type} (pick : Y → Window)
    (low : ∀ y, payloadBits degree (pick y).k ≤ (pick y).lo)
    (high : ∀ y, payloadBits degree (pick y).k ≤ (pick y).hi) :
    Runs preCmd (vol ∘ pick) (vol ∘ pick)
      ((fun x => Tree.fork (regime.header x) (flat x)) ∘ pick) (ins ∘ pick) ∧
    Runs postCmd (vol ∘ pick) (vol ∘ pick) (outs ∘ pick) (result ∘ pick) ∧
    (∀ y, (ins (pick y)).count ≤ capCoefficient*vol (pick y)) ∧
    (∀ y, (outs (pick y)).count ≤ capCoefficient*vol (pick y)) := by
  have caps' y := program.paid (pick y) (low y) (high y)
  have bounds y : cost (pick y) + 1 ≤ (capCoefficient+1)*(vol (pick y)+1) := by
    have h : cost (pick y) ≤ capCoefficient * vol (pick y) := (caps' y).1
    simp only [Nat.add_mul, Nat.mul_add, one_mul, mul_one]
    omega
  exact ⟨(allRuns.1.on pick).bound _ _ bounds bounds, (allRuns.2.on pick).bound _ _ bounds bounds,
    fun y => (caps' y).2.1, fun y => (caps' y).2.2⟩

/-- The same commands perform both passes at linear cost once the reserve inequalities hold. -/
theorem commands : ∃ (D C : ℕ) (pre post : Cmd), ∀ {Y : Type} (pick : Y → Window),
    (∀ y, payloadBits D (pick y).k ≤ (pick y).lo) →
    (∀ y, payloadBits D (pick y).k ≤ (pick y).hi) →
    Runs pre (vol ∘ pick) (vol ∘ pick)
      ((fun x => Tree.fork (regime.header x) (flat x)) ∘ pick) (ins ∘ pick) ∧
    Runs post (vol ∘ pick) (vol ∘ pick) (outs ∘ pick) (result ∘ pick) ∧
    (∀ y, (ins (pick y)).count ≤ C*vol (pick y)) ∧
    (∀ y, (outs (pick y)).count ≤ C*vol (pick y)) :=
  ⟨degree, capCoefficient, preCmd, postCmd, fun pick low high => commandRuns pick low high⟩

/-- Both fixed commands use one register bound independent of all window and sweep parameters. -/
theorem commonRegisters : ∃ R : ℕ, 0 < R ∧ CommonRegisters.Within R preCmd ∧ CommonRegisters.Within R postCmd :=
  ((Filter.eventually_gt_atTop (0 : ℕ)).and
    ((RegisterSelect.within_eventually preCmd).and (RegisterSelect.within_eventually postCmd))).exists

end
end Controlled.PositionRows.Window.Packets

end NearSquareRoot
end Computability
end OAI
