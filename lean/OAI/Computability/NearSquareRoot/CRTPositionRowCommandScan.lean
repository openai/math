import OAI.Computability.NearSquareRoot.CRTControlledSpace
import OAI.Computability.NearSquareRoot.FixedCandidateEffectiveTask
import OAI.Computability.NearSquareRoot.ScheduleRegisterTagFold
import OAI.Computability.NearSquareRoot.PhysicalWalshAgendaOps

/-! # The register program for the high-row scan

Only the current row is active. The emitted sweep carries the reversed output
prefix on a parked deck, and restores the original row order in one final pass.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Controlled.PositionRows.RowCommandScan
open IntegerMultiplication Code Strip CommonRegisters GeneratorSyntax NearSquareRoot.Space
open Code.Task (forest)
open Filter

def reverseCmd : Cmd := RegisterTagFold.seed.join (RegisterTagFold.command .pass)

def scanCmd (row : Cmd) : Cmd :=
  (RegisterTagFold.seed.join (RegisterTagFold.command (KernelEffectiveFamily.leftCmd row))).join reverseCmd

theorem effective {P : Type} [Primcodable P] {row : P → Cmd} (h : Effective ltr row) :
    Effective ltr (fun p => scanCmd (row p)) :=
  ((effective_const _ _).join (RegisterTagFold.effective (KernelEffectiveFamily.effective_left h))).join
    (effective_const _ _)

theorem within : ∀ᶠ R : ℕ in atTop, ∀ c, Within R c → Within R (scanCmd c) := by
  filter_upwards [RegisterSelect.within_eventually RegisterTagFold.seed,
    RegisterSelect.within_eventually reverseCmd,eventually_ge_atTop 3] with R hs hr hR
  intro c hc
  exact ⟨⟨hs,RegisterTagFold.within hR _ (KernelEffectiveFamily.within_left (by omega) hc)⟩,hr⟩

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 3500 in
theorem execute {X : Type} (row : Cmd) (rows volume : X → ℕ) (input output : X → ℕ → Tree)
    (cost : X → ℕ → ℕ)
    (step : EffectiveTask.Runs row (fun z : (x : X) × Fin (rows x) => cost z.1 z.2.val)
      (fun z => input z.1 z.2.val) (fun z => output z.1 z.2.val))
    (streamIn : ∀ x, (forest (input x) (List.range (rows x))).count ≤ volume x)
    (streamOut : ∀ x, (forest (output x) (List.range (rows x))).count ≤ volume x)
    (room : ∀ x j, j < rows x → (input x j).count + cost x j ≤ volume x) :
    EffectiveBoundedTask.Runs (scanCmd row)
      (fun x => (∑ j ∈ Finset.range (rows x), (cost x j + (input x j).count + 1)) + 2*volume x+2)
      (fun x => 2*volume x+3) (fun x => forest (input x) (List.range (rows x)))
      (fun x => forest (output x) (List.range (rows x))) :=
  command_contract (scanCmd row) from physicalRows rows volume input output cost ⟨row,step⟩ streamIn streamOut room

private def entry {A : Type} (s : Series A) (f : A → Tree) (n : ℕ) :=
  if h : n < s.count then f (s.follow ⟨n,h⟩) else .atom false

private theorem forest_entry {A : Type} (s : Series A) (f : A → Tree) :
    forest (entry s f) (List.range s.count) = stripe s f := by
  trans forest id ((List.range s.count).map (entry s f))
  · exact (Task.forest_map id (entry s f) _).symm
  unfold stripe
  apply congrArg (forest id)
  apply List.ext_getElem
  · simp
  · intro j h₁ h₂
    have hj : j < s.count := by simpa using h₂
    simp [entry,Series.follow,Series.tab,hj]

private theorem forest_cost (f : ℕ → Tree) (n : ℕ) :
    (forest f (List.range n)).count = (∑ j ∈ Finset.range n, ((f j).count + 1))+1 := by
  induction n with
  | zero => simp [Task.forest_nil,Tree.count]
  | succ n ih =>
    rw [Task.forest_count,List.range_succ,List.length_append,costSum_cat,List.length_range,
      List.length_cons,List.length_nil,costSum_cons,costSum_nil,Finset.sum_range_succ]
    rw [Task.forest_count,List.length_range] at ih
    omega

/-- Charge the same row command and each parked prefix against the high reserve. -/
theorem seriesRows {I : Type} {A : I → Type} (c : Cmd) (s : (i : I) → Series (A i))
    (src dst : (i : I) → A i → Tree) (W V factor : I → ℕ)
    (localRun : EffectiveTask.Runs c (fun a : Sigma A => W a.1*factor a.1)
      (fun a => src a.1 a.2) (fun a => dst a.1 a.2))
    (H : ℕ) (hin : ∀ i, (stripe (s i) (src i)).count ≤ H*V i)
    (hout : ∀ i, (stripe (s i) (dst i)).count ≤ H*V i)
    (space : ∀ i, (s i).count * W i ≤ V i) (reserve : ∀ i, factor i ≤ (s i).count) :
    EffectiveBoundedTask.Runs (scanCmd c) (fun i => V i*(factor i+1)) V
      (fun i => stripe (s i) (src i)) (fun i => stripe (s i) (dst i)) := by
  let n i := (s i).count
  let inp i := entry (s i) (src i)
  let out i := entry (s i) (dst i)
  let vol i := (H+1)*V i
  have hIn i : (forest (inp i) (List.range (n i))).count ≤ H*V i := forest_entry .. ▸ hin i
  have hOut i : (forest (out i) (List.range (n i))).count ≤ H*V i := forest_entry .. ▸ hout i
  have run := localRun.on (fun z : (i : I) × Fin (n i) => ⟨z.1,(s z.1).follow z.2⟩)
  have h := execute c n vol inp out (fun i _ => W i*factor i)
    (run.conform (fun _ => rfl) (fun z => by simp [inp,entry,z.2.isLt,n])
      (fun z => by simp [out,entry,z.2.isLt,n]))
    (fun i => (hIn i).trans (Nat.mul_le_mul_right _ (by omega)))
    (fun i => (hOut i).trans (Nat.mul_le_mul_right _ (by omega))) (fun i j hj => by
      have hcell := Finset.single_le_sum (f := fun j => (inp i j).count+1)
        (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr hj)
      have row := hIn i
      rw [forest_cost] at row
      have clock := (Nat.mul_le_mul_right (W i) (reserve i)).trans (space i)
      dsimp only [vol]
      rw [Nat.succ_mul,Nat.mul_comm (W i) (factor i)]
      omega)
  refine PhysicalWalsh.AgendaOps.conform (h.bound (t' := fun i => V i*(factor i+1)) (s' := V)
    (3*H+6) (2*H+6) ?_ ?_) (fun _ => rfl) (fun _ => rfl) (fun i => forest_entry ..) (fun i => forest_entry ..)
  · intro i
    have q := hIn i
    rw [forest_cost] at q
    have fee := Nat.mul_le_mul_right (factor i) (space i)
    have total : (∑ j ∈ Finset.range (n i), (W i*factor i+(inp i j).count+1)) =
        n i * W i * factor i + ∑ j ∈ Finset.range (n i), ((inp i j).count+1) := by
      simp [Nat.add_assoc, Finset.sum_add_distrib, Nat.mul_assoc]
    rw [total]
    change n i * W i * factor i ≤ V i * factor i at fee
    rw [Nat.mul_assoc] at fee
    dsimp only [vol]
    simp only [Nat.mul_succ,Nat.succ_mul,Nat.mul_add,Nat.add_mul,Nat.mul_assoc]
    omega
  · intro i
    dsimp only [vol]
    simp only [Nat.succ_mul,Nat.mul_add,Nat.add_mul,Nat.mul_one,Nat.mul_assoc]
    omega

end Controlled.PositionRows.RowCommandScan

end NearSquareRoot
end Computability
end OAI
