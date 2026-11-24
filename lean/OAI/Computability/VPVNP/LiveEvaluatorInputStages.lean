import OAI.Computability.VPVNP.LiveEvaluatorReindexPrepare
import OAI.Computability.VPVNP.LiveEvaluatorReindexSkeleton
import OAI.Computability.VPVNP.LiveEvaluatorReindexSweep
import OAI.Computability.VPVNP.LiveHeaderUnique

/-!
# Native preparation of the midpoint evaluator input

The four stages write the control, copy the true advice prefix, generate
the zero-exponent runtime field, and install the permuted exponent payloads.
Their executions share ordinary external memory. The source banks are
preserved throughout preparation, and the final bank contains exactly the
tape machine's initial configuration on the advice and true exponents.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveEvaluatorInputStages

open BurstRAM BurstRAM.PrivateRAM LiveEvaluatorInitialize LiveEvaluatorReindex
open EvaluatorProgramRawInput
open scoped Fin.CommRing

variable {w d t Z : ℕ}

/-- Public-word addresses and capacities for the two writes preceding the
scatter. Only the occupied prefix of the advised stream is copied. -/
structure Layout (cp sk sc : Fin 4 → Word w) (permPub : Fin 5 → Word w) (d t Z a : ℕ) : Prop where
  controlBase : sc 1 = cp 1
  wordWidth : (cp 3).val = w
  prefixFit : firstData cp + a ≤ 2^w
  packedSeparate : ∀ j < a, let x := (sourceAddress cp (j : Word w)).val
    x ≠ (cp 1).val ∧ (x < firstData cp ∨ firstData cp+a ≤ x)
  runtimeWidth : (sk 0).val = Z
  runtimeBits : (sk 1).val = t*Z
  runtimeBase : (sk 2).val = firstData cp + a
  runtimeLength : (sk 3).val = 2*(t*Z)+6*Z+4
  runtimeFit : (sk 2).val + (sk 3).val ≤ 2^w
  scatter : LiveEvaluatorReindex.Layout permPub d t Z (cp 1).val (cp 0).val a
  incomingSeparate : ∀ q : Fin (d*Z), let x := (permPub 0).val + q.val
    x ≠ (cp 1).val ∧ (x < firstData cp ∨ firstData cp+a+(sk 3).val ≤ x)
  mapSeparate : ∀ i : Fin d, let x := (permPub 1).val + i.val
    x ≠ (cp 1).val ∧ (x < firstData cp ∨ firstData cp+a+(sk 3).val ≤ x)

/-- Cost of all four midpoint stages before linked stage dispatch. -/
def costBound (a runtimeLen count : ℕ) : ℕ :=
  2 + 3 * max 1 a + 2 * runtimeLen + 4 * max 1 count

private theorem reportCost_le (rs : List (Report w)) (b : ℕ) (h : ∀ r ∈ rs, countProbes r.events ≤ b) :
    RAMBuckets.cost Report.probes rs ≤ (1+b)*rs.length := by
  induction rs with
  | nil => simp [RAMBuckets.cost]
  | cons r rs ih =>
    have head := h r (by simp)
    have tail := ih (fun r hr => h r (List.mem_cons_of_mem _ hr))
    change 1+countProbes r.events+RAMBuckets.cost Report.probes rs ≤ (1+b)*(rs.length+1)
    rw [Nat.mul_succ]
    omega

/-- Actual terminated RAM calls for the four phases, in their execution order. -/
def Runs (cp sk sc : Fin 4 → Word w) (permPub : Fin 5 → Word w) (p : UniversalMachine.Program)
    (a runtimeLen count : ℕ) (m₀ m₄ : Memory w) : Prop :=
  let S := ((putStage (controlTag p)).instantiate w sc).program
  let C := (copyStage.instantiate w (copyPublic cp (a : Word w))).program
  let K := (LiveEvaluatorReindexSkeleton.skeletonStage.instantiate w sk).program
  let R := (scatterPhase.instantiate w permPub).program
  ∃ es cs ks rs,
    let m₁ := after m₀ es
    let m₂ := after m₁ (eventLog cs)
    let m₃ := after m₂ (eventLog ks)
    execute S 4 (S.start 0) m₀ [] = some ⟨es, none⟩ ∧
    runSegment C 23 (some 0) m₁ (List.replicate (max 1 a) []) = some cs ∧ endState (some 0) cs = none ∧
    runSegment K 28 (some 0) m₂ (List.replicate runtimeLen []) = some ks ∧ endState (some 0) ks = none ∧
    runSegment R 27 (some 0) m₃ (List.replicate (max 1 count) []) = some rs ∧ endState (some 0) rs = none ∧
    after m₃ (eventLog rs) = m₄ ∧
    countProbes es = 1 ∧ (∀ r ∈ cs, countProbes r.events ≤ 2) ∧
    (∀ r ∈ ks, countProbes r.events ≤ 1) ∧ (∀ r ∈ rs, countProbes r.events ≤ 3) ∧
    RAMBuckets.cost Report.probes (⟨es, none⟩ :: (cs ++ ks ++ rs)) ≤ costBound a runtimeLen count

/-- Given the physical packed advice bank and the incoming and order-advice
buffers, the four fixed native stages produce the actual evaluator input. -/
theorem run (hw : 2 ≤ w) (cp sk sc : Fin 4 → Word w) (permPub : Fin 5 → Word w)
    (p : UniversalMachine.Program) (running : p.extra ≠ 0) (hs : p.extra+2 ≤ 2^w)
    (perm : Fin d ≃ Fin t) (dense : Fin d → Word Z) (formal : Fin t → Word Z)
    (order : ∀ i, formal (perm i) = dense i) (A : List Bool)
    (L : Layout cp sk sc permPub d t Z A.length) (m₀ : Memory w)
    (space : (A ++ runtime formal).length ≤ (cp 0).val+1)
    (blank : ∀ k : Fin (LiveEvaluatorEncoding.fieldWords (cp 0).val), m₀ ((cp 1).val+k.val) = 0)
    (packed : ∀ j < A.length, m₀ (sourceAddress cp (j : Word w)).val = inputWord w A (j/w))
    (source : Sources permPub perm dense m₀) :
    ∃ m₄, Runs cp sk sc permPub p A.length (2*(t*Z)+6*Z+4) (d*Z) m₀ m₄ ∧
      Stores hw hs (cp 1).val m₄
        (LiveEvaluatorTail.initialCode (cp 0).val (UniversalMachine.initial p (A ++ runtime formal))) := by
  let es : List (Event w) := [.tick, .tick, .write (sc 1) (Fin.ofNat _ (controlTag p).val)]
  let m₁ := after m₀ es
  have hs₁ : m₁ = writeMemory m₀ (cp 1) (Fin.ofNat _ (controlTag p).val) := by
    change writeMemory m₀ (sc 1) _ = _
    rw [L.controlBase]
  have hact : activeLength p A = A.length := ite_eq_right running
  have saved (j : ℕ) (hj : j < A.length) :
      m₁ (sourceAddress cp (j : Word w)).val = inputWord w A (j/w) := by
    rw [hs₁, writeMemory, ite_eq_right (L.packedSeparate j hj).1, packed j hj]
  obtain ⟨cs, hcs, hcend, hc, hcl, hcp⟩ := copyStage_sweep hw cp L.wordWidth p A m₁
    (by simpa only [hact] using L.prefixFit) (by simpa only [hact] using saved)
    (by simpa only [hact] using fun (j : ℕ) (hj : j < A.length) => (L.packedSeparate j hj).2)
  rw [hact] at hcs hc hcl
  let m₂ := after m₁ (eventLog cs)
  let zeros := runtime (fun _ : Fin t => (0 : Word Z))
  have hzeros : zeros.length = 2*(t*Z)+6*Z+4 := runtime_length _
  obtain ⟨ks, hks, hkend, hk, hkl, hkp⟩ := LiveEvaluatorReindexSkeleton.skeletonStage_sweep hw sk m₂
    L.runtimeWidth L.runtimeBits L.runtimeLength L.runtimeFit
  change Copied zeros (sk 2).val zeros.length m₂ (after m₂ (eventLog ks)) at hk
  rw [L.runtimeBase] at hk
  let m₃ := after m₂ (eventLog ks)
  have he₃ : ∀ x, x ≠ (cp 1).val → (x < firstData cp ∨ firstData cp+A.length+(sk 3).val ≤ x) → m₃ x = m₀ x := by
    intro x hx ha
    have copied := hc.append hk
    change m₃ x = m₀ x
    have hy := copied.outside x (by rw [List.length_append, hzeros]; rw [L.runtimeLength] at ha; omega)
    exact hy.trans (by rw [hs₁, writeMemory, ite_eq_right hx])
  have src₃ : Sources permPub perm dense m₃ := {
    incoming := fun q => (he₃ _ (L.incomingSeparate q).1 (L.incomingSeparate q).2).trans (source.incoming q)
    order := fun i => (congrArg Fin.val (he₃ _ (L.mapSeparate i).1 (L.mapSeparate i).2)).trans (source.order i) }
  have prep := prefix_runtime_stores hw cp p running hs A m₀ m₂ m₃
    (by simpa only [List.length_append, runtime_length] using space) blank (hs₁ ▸ hc)
    (by simpa only [← hzeros] using hk)
  obtain ⟨rs, hrs, hrend, store, hrl, hrp⟩ := sweep_native hw permPub perm dense formal order p running hs
    A (cp 1).val (cp 0).val L.scatter m₃ src₃ space prep
  refine ⟨_, ?_, store⟩
  refine ⟨es, cs, ks, rs, execute_putStage _ _ _ _ _ 0, hcs, hcend,
    by simpa only [runtime_length] using hks, hkend, hrs, hrend, rfl, rfl,
    fun r hr => (hcp r hr).2.1, hkp, hrp, ?_⟩
  have cpBound := reportCost_le cs 2 (fun r hr => (hcp r hr).2.1)
  have skBound := reportCost_le ks 1 hkp
  have scBound := reportCost_le rs 3 hrp
  rw [hcl] at cpBound
  rw [hkl, runtime_length] at skBound
  rw [hrl] at scBound
  change 1+1+RAMBuckets.cost Report.probes (cs ++ ks ++ rs) ≤ _
  simp only [RAMBuckets.cost_append, costBound]
  omega

/-- Every accepting execution of these four stages uses the indicated empty
branch streams. In particular the preparation cannot multiply path counts. -/
theorem Runs.forces {cp sk sc : Fin 4 → Word w} {permPub : Fin 5 → Word w} {p : UniversalMachine.Program}
    {a runtimeLen count : ℕ} {m₀ m₄ : Memory w} (h : Runs cp sk sc permPub p a runtimeLen count m₀ m₄)
    (stateBits : List Bool) (copyBits runtimeBits scatterBits : List (List Bool))
    (es : List (Event w)) (cs ks rs : List (Report w))
    (stateRun : let S := ((putStage (controlTag p)).instantiate w sc).program
      execute S 4 (S.start 0) m₀ stateBits = some ⟨es, none⟩)
    (copyRun : let P := (copyStage.instantiate w (copyPublic cp (a : Word w))).program
      runSegment P 23 (some 0) (after m₀ es) copyBits = some cs)
    (copyEnd : endState (some 0) cs = none)
    (runtimeRun : let P := (LiveEvaluatorReindexSkeleton.skeletonStage.instantiate w sk).program
      runSegment P 28 (some 0) (after (after m₀ es) (eventLog cs)) runtimeBits = some ks)
    (runtimeEnd : endState (some 0) ks = none)
    (scatterRun : let P := (scatterPhase.instantiate w permPub).program
      runSegment P 27 (some 0) (after (after (after m₀ es) (eventLog cs)) (eventLog ks)) scatterBits = some rs)
    (scatterEnd : endState (some 0) rs = none) :
    stateBits = [] ∧ copyBits = List.replicate (max 1 a) [] ∧ runtimeBits = List.replicate runtimeLen [] ∧
    scatterBits = List.replicate (max 1 count) [] ∧
      after (after (after (after m₀ es) (eventLog cs)) (eventLog ks)) (eventLog rs) = m₄ := by
  obtain ⟨es₀, cs₀, ks₀, rs₀, he, hc, hce, hk, hke, hr, hre, hafter, _⟩ := h
  obtain ⟨sb, hreport⟩ := execute_empty_forces he stateRun
  have heq : es = es₀ := congrArg Report.events hreport
  subst es
  obtain ⟨cb, rfl⟩ := accepted_empty_unique hc hce copyRun copyEnd
  obtain ⟨kb, rfl⟩ := accepted_empty_unique hk hke runtimeRun runtimeEnd
  obtain ⟨rb, rfl⟩ := accepted_empty_unique hr hre scatterRun scatterEnd
  exact ⟨sb, cb, kb, rb, hafter⟩

end LiveEvaluatorInputStages

end VPVNP
end Computability
end OAI
