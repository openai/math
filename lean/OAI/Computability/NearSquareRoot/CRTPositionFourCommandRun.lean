import OAI.Computability.NearSquareRoot.CRTPositionFourCommandPrepare
import OAI.Computability.NearSquareRoot.CRTPositionFourCommandSwaps
import OAI.Computability.NearSquareRoot.CRTPositionRowCommandClock
import OAI.Computability.NearSquareRoot.CRTControlledReserveCutoff
import OAI.Computability.NearSquareRoot.PhysicalWalshAgendaOps

/-! # Exact native action of the generated four-stage position command -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Controlled.PositionCmd

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip IntegerMultiplication.Adic
open IntegerMultiplication.Loom PositionProgram NearSquareRoot.Space KernelEffectiveFamily CommonRegisters
open EffectiveBoundedTask GeneratorSyntax ReserveStage PositionRows
noncomputable section

def reserveCmd (core : Cmd) : Cmd :=
  prepareCmd.join (fourCmd (stageCmd (swapCmd false) (RowCommand.command core) (swapCmd true)))

theorem reserve_effective {P : Type} [Primcodable P] {core : P → Cmd} (h : Effective ltr core) :
    Effective ltr (fun p => reserveCmd (core p)) :=
  prepare_effective.join (four_effective (stage_effective (swap_effective_const false)
    (RowCommand.effective h) (swap_effective_const true)))

theorem reserve_within (R : ℕ) : ∃ S : ℕ, 0 < S ∧ ∀ c, Within R c → Within S (reserveCmd c) := by
  obtain ⟨A,_,ha⟩ := RowCommand.within R
  obtain ⟨S,hA,h3,hp,hs⟩ := ((Filter.eventually_ge_atTop A).and ((Filter.eventually_ge_atTop (3 : ℕ)).and
    (prepare_within.and swap_within))).exists
  exact ⟨S,by omega,fun c hc => ⟨hp, four_within h3 (stage_within h3 (hs false)
    (RegisterSelect.within_mono hA _ (ha c hc)) (hs true))⟩⟩

private theorem takeStep {k lo hi : ℕ} (stages : List (ReserveStage k lo hi))
    (m : ReserveStage k lo hi → Equiv.Perm (Block 2 k)) {j : ℕ} (h : j < stages.length)
    (x : Block 2 k) : flatReads (stages.take (j+1)) m x =
      flatReads (stages.take j) m (stages[j].flatRead (m stages[j]) x) := by
  rw [List.take_succ_eq_append_getElem h]
  generalize stages[j] = s
  generalize stages.take j = l
  induction l with
  | nil => rfl
  | cons a l ih =>
    change a.flatRead (m a) (flatReads (l++[s]) m x) = a.flatRead (m a) _
    exact congrArg (a.flatRead (m a)) ih

set_option maxHeartbeats 1200000 in
/-- Parameterized by the named compiled table schedule, the explicit command
reads all three widths and twelve stage keys from actual tape. -/
theorem reserve_runs {ρ : ℝ} (positive : 0 ≤ ρ) (core : Cmd) (hc : RowCommand.GroupedRuns core ρ) :
    ∃ D : ℕ, ∀ {I : Type} (k lo hi : I → ℕ)
    (_cap : ∀ i, lo i+hi i ≤ k i/2-2)
    {U : I → Type} (u : (i : I) → Series (U i)) (_pos : ∀ i, 0<(u i).count)
    (p : (i : I) → Equiv.Perm (Fin (k i))) (f : (i : I) → Block 2 (k i) → U i → Bead),
    (∀ i, payloadBits D (k i) ≤ lo i) → (∀ i, payloadBits D (k i) ≤ hi i) →
    (∀ i, positionFactor ρ (k i) ≤ 2^(hi i)) →
    let V i := 2^(k i)*(u i).count
    EffectiveBoundedTask.Runs (reserveCmd core)
      (fun i => (lo i+hi i+1)*V i + V i*(positionFactor ρ (k i)+1)) V
      (fun i => .fork (send (tally (lo i),tally (hi i),Reflections.table (p i)))
        (cloth (fun i => line 2 (k i)) u f i))
      (cloth (fun i => line 2 (k i)) u (fun i z => f i (flatBitPullback (p i) z))) := by
  obtain ⟨D,mid⟩ := RowCommand.tableMiddle positive core hc
  refine ⟨D,fun k lo hi cap U u pos p f low high enough => ?_⟩
  let V i := 2^k i*(u i).count
  let W i := 5*V i
  let T i := (lo i+hi i+1)*W i + V i*(positionFactor ρ (k i)+1)
  let stages i := four (p i) (cap i)
  let s (j : Fin 4) i := ReserveProgram.atStage (p i) (cap i) j
  have fit i : lo i+hi i ≤ k i := by have := cap i; omega
  let m i (a : ReserveStage (k i) (lo i) (hi i)) := ReserveTile.lift (fit i) (flatBitPullback a.inner)
  let act i (n : ℕ) := flatReads ((stages i).take n) (m i)
  let current (j : Fin 5) i a := f i (act i j.val a)
  let file (j : Fin 5) := cloth (fun i => line 2 (k i)) u (current j)
  have wc (y : (i : _) → Block 2 (k i) → U i → Bead) i :
      (cloth (fun i => line 2 (k i)) u y i).count ≤ W i :=
    ReserveSmall.beadClothCap k (fun i => (u i).count) u y pos (fun _ => le_rfl) i
  have room i : W i ≤ T i := (Nat.le_mul_of_pos_left (W i) (Nat.succ_pos _)).trans (Nat.le_add_right _ _)
  let pick i : PreCase := ⟨k i,lo i,hi i,p i,cap i,W i,
    (Nat.le_mul_of_pos_right (2^k i) (pos i)).trans (Nat.le_mul_of_pos_left _ (by decide : 0<5)),
    file 0 i,wc _ i⟩
  have step (j : Fin 4) : EffectiveBoundedTask.Runs (stageCmd (swapCmd false) (RowCommand.command core) (swapCmd true))
      T W (fun i => shell (s j i) (file j.castSucc i)) (file j.succ) := by
    have h (i) := four_bounds (p i) (cap i) (s j i) (ReserveProgram.atStage_mem (p i) (cap i) j)
    let y i := current j.castSucc i ∘ swapsFlat (s j i).moves
    let z i := y i ∘ (m i (s j i))
    have len i := (h i).1.trans (fit i)
    have fast i : ((s j i).moves.length+1)*W i ≤ T i :=
      (Nat.mul_le_mul_right _ (Nat.succ_le_succ (h i).1)).trans (Nat.le_add_right _ _)
    have fwd := (swap_runs false k W (fun i => (s j i).moves) (fun i => (h i).2.1) len
      (fun i a => strip (u i) (current j.castSucc i a)) (wc _)).mono fast (fun _ => le_rfl)
    have work := (mid k lo hi fit u pos (fun i => (s j i).inner) y low high enough).mono (t' := T) (s' := W)
      (fun i => Nat.le_add_left _ _) (fun i => Nat.le_mul_of_pos_left (V i) (by decide : 0<5))
    have back := (swap_runs true k W (fun i => (s j i).moves) (fun i => (h i).2.1) len
      (fun i a => strip (u i) (z i a)) (wc _)).mono fast (fun _ => le_rfl)
    apply stage_runs (s j) room (keyBound_on pick j) fwd work
    apply PhysicalWalsh.AgendaOps.conform back (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
    intro i
    apply congrArg (stripe (line 2 (k i)))
    funext a
    apply congrArg (strip (u i))
    apply congrArg (f i)
    change (act i j.val) ((s j i).flatRead (m i (s j i)) a) = act i (j.val+1) a
    exact (takeStep (stages i) (m i) (j := j.val) (by simp [stages]) a).symm
  have body := four_runs (s := s) file room (keyBound_on pick) step
  have prep := (prepare_runs.on pick).mono room (fun _ => le_rfl)
  have all := prep.sequence body
  apply PhysicalWalsh.AgendaOps.conform (all.bound (t' := fun i => (lo i+hi i+1)*V i + V i*(positionFactor ρ (k i)+1))
    (s' := V) 5 5 (fun i => ?_) (fun i => ?_))
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
  · intro i
    change stripe _ (fun a => strip (u i) (f i (flatReads ((stages i).take 4) (m i) a))) = _
    have len : (stages i).length = 4 := length_four _ _
    rw [← len,List.take_length,show flatReads (stages i) (m i) = flatBitPullback (p i) from four_canonicalReads _ _]
    rfl
  · dsimp only [T,W]
    nlinarith only [Nat.zero_le (V i*(positionFactor ρ (k i)+1))]
  · change 5*V i+1 ≤ 5*(V i+1)
    omega

end
end Controlled.PositionCmd

end NearSquareRoot
end Computability
end OAI
