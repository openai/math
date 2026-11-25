import OAI.Computability.NearSquareRoot.CRTPositionRowCommandScan
import OAI.Computability.NearSquareRoot.CRTPositionRowCommandLow
import OAI.Computability.NearSquareRoot.CRTPositionRowCommandPackets

/-! # Wrapping a generated table command in a linear-space row scan

The high-prefix packet preparation and the low-field shims are fixed commands.
The row callback is the only part of the resulting source file that depends on
the candidate. Its clock may use a candidate-dependent polynomial slack degree.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Controlled.PositionRows.RowCommand
open IntegerMultiplication Code Adic Strip Loom PositionProgram
open CommonRegisters GeneratorSyntax Filter Window.Packets
open NearSquareRoot.Space

noncomputable section

/-- Carve the stream, scan the rows with low-field shims, and concatenate. -/
def command (core : Cmd) : Cmd := (preCmd.join (RowCommandScan.scanCmd (RowCommandLow.frameCmd core))).join postCmd

theorem effective {P : Type} [Primcodable P] {c : P → Cmd} (h : Effective ltr c) :
    Effective ltr (fun p => command (c p)) :=
  ((effective_const _ _).join (RowCommandScan.effective (RowCommandLow.frame_effective h))).join
    (effective_const _ _)

theorem within (R : ℕ) : ∃ S : ℕ, 0 < S ∧ ∀ c, Within R c → Within S (command c) := by
  obtain ⟨A,hA,ha⟩ := RowCommandLow.frame_within R
  obtain ⟨S,hs,scan,h₁,h₂⟩ := ((eventually_ge_atTop A).and (RowCommandScan.within.and
    ((RegisterSelect.within_eventually preCmd).and (RegisterSelect.within_eventually postCmd)))).exists
  exact ⟨S,by omega,fun c hc => ⟨⟨h₁,scan _ (RegisterSelect.within_mono hs _ (ha c hc))⟩,h₂⟩⟩

/-- The timed contract of the supplied grouped core on its actual input tape.
The slack degree is a resource witness and does not enter the command. -/
def GroupedRuns (core : Cmd) (ρ : ℝ) : Prop :=
  ∃ d : ℕ, ∀ {Y : Type} (select : Y → Window.Row),
    (∀ y, payloadBits d (select y).1.k ≤ (select y).1.lo) →
    EffectiveTask.Runs core (fun y => RowCommandLow.rowVolume (select y)*positionFactor ρ (select y).1.k)
      (RowCommandLow.middleInput ∘ select) (RowCommandLow.groupedOut ∘ select)

private theorem cut_mono {a b k l : ℕ} (h : a ≤ b) (fit : payloadBits b k ≤ l) :
    payloadBits a k ≤ l := (Nat.mul_le_mul_right _ h).trans fit

theorem windowRuns {ρ : ℝ} (positive : 0 ≤ ρ) (core : Cmd) (has : GroupedRuns core ρ) :
    ∃ D : ℕ, ∀ {I : Type} (pick : I → Window),
      (∀ i, payloadBits D (pick i).k ≤ (pick i).lo) →
      (∀ i, payloadBits D (pick i).k ≤ (pick i).hi) →
      (∀ i, positionFactor ρ (pick i).k ≤ 2^(pick i).hi) →
      EffectiveBoundedTask.Runs (command core) (fun i => vol (pick i)*(positionFactor ρ (pick i).k+1))
        (vol ∘ pick) ((fun x => .fork (Window.regime.header x) (flat x)) ∘ pick) (result ∘ pick) := by
  obtain ⟨d,hd⟩ := has
  let D := max Window.Packets.degree (max d RowCommandLow.degree)
  refine ⟨D,fun pick low high budget => ?_⟩
  have k₁ := fun i => cut_mono (le_max_left ..) (low i)
  have k₂ := fun i => cut_mono (le_max_left ..) (high i)
  obtain ⟨first,last,hi,ho⟩ := commandRuns pick k₁ k₂
  let highSeries i := line 2 (pick i).hi
  let z (i : Sigma (fun i => Block 2 (pick i).hi)) : Window.Row := ⟨pick i.1,i.2⟩
  let factor i := positionFactor ρ (pick i).k
  let W i := 2^(pick i).mid*(2^(pick i).lo*(pick i).w)
  have grouped := hd z (fun a => cut_mono ((le_max_left ..).trans (le_max_right ..)) (low a.1))
  have framed := RowCommandLow.frame_runs z (fun a => cut_mono ((le_max_right ..).trans (le_max_right ..))
    (low a.1)) core _ grouped
  have hr i : 1 ≤ factor i := by
    have p := positionFactor_pays (ρ := ρ) positive (le_refl (pick i).k)
    have h := one_le_positionRate positive (pick i).k
    change 1 ≤ positionFactor ρ (pick i).k
    exact_mod_cast (by linarith : (1:ℝ) ≤ positionFactor ρ (pick i).k)
  have cost := framed.bound (b := fun a => W a.1*factor a.1) 2 (fun a => by
    change W a.1*factor a.1+W a.1+1 ≤ 2 * (W a.1*factor a.1+1)
    have h := Nat.mul_le_mul_left (W a.1) (hr a.1)
    rw [Nat.mul_one] at h
    omega)
  have scan := RowCommandScan.seriesRows (RowCommandLow.frameCmd core) highSeries
    (fun i a => rowIn ⟨pick i,a⟩) (fun i a => rowOut ⟨pick i,a⟩) W (vol ∘ pick) factor
    cost capCoefficient hi ho (fun i => by
      dsimp only [highSeries,W,Function.comp_apply,vol]
      rw [lineSize,← Nat.mul_assoc,← Nat.mul_assoc,← pow_add,← pow_add]
      have := (pick i).fit
      rw [show (pick i).hi+(pick i).mid+(pick i).lo = (pick i).k by unfold Window.mid; omega])
    (fun i => by simpa only [highSeries,lineSize] using budget i)
  have run := PhysicalWalsh.AgendaOps.compose (PhysicalWalsh.AgendaOps.compose first scan) last
  exact run.bound 3 1 (fun i => by
    change vol (pick i)+vol (pick i)*(factor i+1)+vol (pick i)+1 ≤ 3*(vol (pick i)*(factor i+1)+1)
    rw [Nat.mul_succ]; omega) (fun i => by simp)

theorem tableMiddle {ρ : ℝ} (positive : 0 ≤ ρ) (core : Cmd) (has : GroupedRuns core ρ) :
    ∃ D : ℕ, ∀ {I : Type} (k lo hi : I → ℕ) (fit : ∀ i, lo i+hi i ≤ k i)
      {U : I → Type} (u : (i : I) → Series (U i)) (_pos : ∀ i, 0 < (u i).count)
      (q : (i : I) → Equiv.Perm (Fin (k i-lo i-hi i)))
      (f : (i : I) → Block 2 (k i) → U i → Bead),
      (∀ i, payloadBits D (k i) ≤ lo i) → (∀ i, payloadBits D (k i) ≤ hi i) →
      (∀ i, positionFactor ρ (k i) ≤ 2^(hi i)) →
      let V i := 2^(k i)*(u i).count
      EffectiveBoundedTask.Runs (command core) (fun i => V i*(positionFactor ρ (k i)+1)) V
        (fun i => .fork (send (tally (hi i),tally (k i-lo i-hi i),tally (lo i),Reflections.table (q i)))
          (cloth (fun i => line 2 (k i)) u f i))
        (cloth (fun i => line 2 (k i)) u (fun i a => f i (ReserveTile.lift (fit i) (flatBitPullback (q i)) a))) := by
  obtain ⟨D,run⟩ := windowRuns positive core has
  refine ⟨D,fun k lo hi fit U u pos q f low high factor => ?_⟩
  let pick i : Window := ⟨k i,lo i,hi i,(u i).count,pos i,fit i,q i,fun z j => f i z ((u i).follow j)⟩
  have h := run pick low high factor
  have cell (i) (a : Block 2 (k i)) : cells (pick i) a = strip (u i) (f i a) :=
    stripe_natural_follow (u i) (fun j => send (f i a j))
  refine PhysicalWalsh.AgendaOps.conform h (fun _ => rfl) (fun _ => rfl) ?_ ?_
  · intro i
    exact congrArg (Tree.fork _) (congrArg (stripe _) (funext (cell i)))
  · intro i
    exact congrArg (stripe _) (funext (fun a => cell i ((pick i).routed a)))

end
end Controlled.PositionRows.RowCommand

end NearSquareRoot
end Computability
end OAI
