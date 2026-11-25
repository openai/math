import OAI.Computability.NearSquareRoot.CRTControlledReserveFourRun
import OAI.Computability.NearSquareRoot.FixedCandidateEffectiveTask
import OAI.Computability.NearSquareRoot.KernelEffectiveFamilyProduct

/-! # Named four-stage position program

Each physical stage consumes, in order, the innermost forward swap-list key,
the middle table and both geometry widths, and the inverse swap-list key.
The command emitter parks exactly the headers of the later stages.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Controlled.PositionCmd

open IntegerMultiplication IntegerMultiplication.Code NearSquareRoot.Space
open CommonRegisters GeneratorSyntax EffectiveBoundedTask KernelEffectiveFamily

variable {k lo hi : ℕ}

def swapKey (s : ReserveStage k lo hi) : Tree := send (flatSwapInput k s.moves)

def middleKey (s : ReserveStage k lo hi) : Tree :=
  send (tally hi,tally (k-lo-hi),tally lo,Reflections.table s.inner)

def shell (s : ReserveStage k lo hi) (v : Tree) : Tree :=
  .fork (swapKey s) (.fork (middleKey s) (.fork (swapKey s) v))

/-- A shared stage body, with one named command in each of its three slots. -/
def stageCmd (forward middle backward : Cmd) : Cmd :=
  ((rightCmd (rightCmd forward)).join (rightCmd middle)).join backward

def underCmd (c : Cmd) := rightCmd (rightCmd (rightCmd c))

def fourCmd (row : Cmd) : Cmd :=
  (((underCmd (underCmd (underCmd row))).join (underCmd (underCmd row))).join (underCmd row)).join row

theorem stage_effective {P : Type} [Primcodable P] {a b c : P → Cmd}
    (ha : Effective ltr a) (hb : Effective ltr b) (hc : Effective ltr c) :
    Effective ltr (fun p => stageCmd (a p) (b p) (c p)) :=
  ((effective_right (effective_right ha)).join (effective_right hb)).join hc

theorem stage_within {R : ℕ} (hr : 3 ≤ R) {a b c : Cmd}
    (ha : Within R a) (hb : Within R b) (hc : Within R c) : Within R (stageCmd a b c) :=
  ⟨⟨within_right hr (within_right hr ha),within_right hr hb⟩,hc⟩

private theorem under_effective {P : Type} [Primcodable P] {a : P → Cmd} (h : Effective ltr a) :
    Effective ltr (fun p => underCmd (a p)) := effective_right (effective_right (effective_right h))

private theorem under_within {R : ℕ} (hr : 3 ≤ R) {c : Cmd} (h : Within R c) :
    Within R (underCmd c) := within_right hr (within_right hr (within_right hr h))

theorem four_effective {P : Type} [Primcodable P] {row : P → Cmd} (h : Effective ltr row) :
    Effective ltr (fun p => fourCmd (row p)) :=
  (((under_effective (under_effective (under_effective h))).join
      (under_effective (under_effective h))).join (under_effective h)).join h

theorem four_within {R : ℕ} (hr : 3 ≤ R) {row : Cmd} (h : Within R row) :
    Within R (fourCmd row) :=
  ⟨⟨⟨under_within hr (under_within hr (under_within hr h)),
       under_within hr (under_within hr h)⟩,under_within hr h⟩,h⟩

variable {I : Type} {t v : I → ℕ} {src dst : I → Tree}

theorem park_runs {c : Cmd} (h : EffectiveBoundedTask.Runs c t v src dst) (spect : I → Tree)
    (room : ∀ i, v i ≤ t i) (C : ℕ) (hC : ∀ i, (spect i).count ≤ C*(v i+1)) :
    EffectiveBoundedTask.Runs (rightCmd c) t v
      (fun i => .fork (spect i) (src i)) (fun i => .fork (spect i) (dst i)) := by
  have right : EffectiveBoundedTask.Runs (rightCmd c) (fun i => (spect i).count+t i)
      (fun i => v i+(spect i).count) _ _ :=
    command_contract (rightCmd c) from h.task.right spect
  apply right.bound (C+1) (C+1)
  · intro i
    have : (spect i).count ≤ C*(t i+1) := (hC i).trans (Nat.mul_le_mul_left C (Nat.succ_le_succ (room i)))
    rw [Nat.succ_mul]; omega
  · intro i
    have := hC i
    rw [Nat.succ_mul]; omega

variable {K L H : I → ℕ}

/-- The single constant for a parked key can absorb polynomial-width tables
even when successive candidates choose different packed payloads. -/
def KeyBound (s : (i : I) → ReserveStage (K i) (L i) (H i)) (v : I → ℕ) : Prop :=
  ∃ C : ℕ, ∀ i, (swapKey (s i)).count ≤ C*(v i+1) ∧ (middleKey (s i)).count ≤ C*(v i+1)

theorem stage_runs {a b c : Cmd} (s : (i : I) → ReserveStage (K i) (L i) (H i))
    (room : ∀ i, v i ≤ t i) (keys : KeyBound s v) {d₁ d₂ : I → Tree}
    (forward : EffectiveBoundedTask.Runs a t v (fun i => .fork (swapKey (s i)) (src i)) d₁)
    (middle : EffectiveBoundedTask.Runs b t v (fun i => .fork (middleKey (s i)) (d₁ i)) d₂)
    (back : EffectiveBoundedTask.Runs c t v (fun i => .fork (swapKey (s i)) (d₂ i)) dst) :
    EffectiveBoundedTask.Runs (stageCmd a b c) t v (fun i => shell (s i) (src i)) dst := by
  obtain ⟨C,cap⟩ := keys
  have f := park_runs (park_runs forward _ room C (fun i => (cap i).2)) _ room C (fun i => (cap i).1)
  have m := park_runs middle _ room C (fun i => (cap i).1)
  exact (f.sequence m).sequence back

private theorem under_runs {c : Cmd} (s : (i : I) → ReserveStage (K i) (L i) (H i))
    (h : EffectiveBoundedTask.Runs c t v src dst) (room : ∀ i, v i ≤ t i) (keys : KeyBound s v) :
    EffectiveBoundedTask.Runs (underCmd c) t v (fun i => shell (s i) (src i))
      (fun i => shell (s i) (dst i)) := by
  obtain ⟨C,cap⟩ := keys
  exact park_runs (park_runs (park_runs h _ room C (fun i => (cap i).1)) _ room C
    (fun i => (cap i).2)) _ room C (fun i => (cap i).1)

def fullShell (s : (j : Fin 4) → ReserveStage k lo hi) (v : Tree) : Tree :=
  shell (s 3) (shell (s 2) (shell (s 1) (shell (s 0) v)))

theorem four_runs {row : Cmd} (s : (j : Fin 4) → (i : I) → ReserveStage (K i) (L i) (H i))
    (state : Fin 5 → I → Tree) (room : ∀ i, v i ≤ t i) (keys : ∀ j, KeyBound (s j) v)
    (step : ∀ j : Fin 4, EffectiveBoundedTask.Runs row t v
      (fun i => shell (s j i) (state j.castSucc i)) (state j.succ)) :
    EffectiveBoundedTask.Runs (fourCmd row) t v
      (fun i => fullShell (fun j => s j i) (state 0 i)) (state 4) := by
  have a := under_runs (s 3) (under_runs (s 2) (under_runs (s 1) (step 0) room (keys 1)) room (keys 2))
    room (keys 3)
  have b := under_runs (s 3) (under_runs (s 2) (step 1) room (keys 2)) room (keys 3)
  have c := under_runs (s 3) (step 2) room (keys 3)
  exact ((a.sequence b).sequence c).sequence (step 3)

end Controlled.PositionCmd

end NearSquareRoot
end Computability
end OAI
