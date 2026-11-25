import OAI.Computability.NearSquareRoot.SynchronizedPermutationSweepTicket

/-! # The raw Fourier permutation from one compiled batch kernel -/

namespace OAI
namespace Computability
namespace NearSquareRoot

set_option maxHeartbeats 2400000
set_option maxRecDepth 6000
noncomputable section
namespace FixedLayer

open IntegerMultiplication Code FixedCandidate FixedPoint Space DigitPacking
open ShortFourier.BatchWord SynchronizedLayers SynchronizedLayers.ScheduleProgram BoxFin PermutationSweep
open PermDirectory (Query BatchTicket batchTicket)
open SynchronizedPermutationBudget (order batches)

theorem recordForest {n : ℕ} (v : FixedCandidate.Array n) :
    Task.forest (fun a => send (Dusk.mark a)) (List.ofFn v) = send (records v) := by
  rw [← Task.forest_map,Task.forest_send,List.map_ofFn]
  rfl

theorem recordVolume {n : ℕ} (hn : 2 ≤ n) (v : FixedCandidate.Array n) :
    size (records v) ≤ 75000*(n+1) := by
  have h := framed_size hn v
  change size (tally n,records v) ≤ _ at h
  rw [size_prod] at h
  dsimp only at h
  omega

/-- The remaining physical premise for a complete FFT permutation row is one
uniform call on a generated descriptor and any intermediate reordering of the
coefficient records. The ticket, sweep stack and restored array frame are charged. -/
theorem permutationFromBatches {I H : Type} [Codec H] [Inhabited H]
    (key : Query × BatchTicket → H) (program : Poly key) (n : I → ℕ)
    (hn : ∀ i, 2 ≤ n i) (h : ∀ i, Directory (n i)) [∀ i j, NeZero (modulus (box (n i)) j)] (hd : ∀ i, 4 ≤ (box (n i)).length)
    (dir : I → Bool) (s : (i : I) → Fin (directedPlan (dir i,tally (addressBits (n i)))).length)
    (tag : ∀ i, (directedPlan (dir i,tally (addressBits (n i))))[(s i).val].2.1 = kindCode .permutation)
    (room : ∀ i, 8*SynchronizedPermutationBudget.width (addressBits (n i)) ≤ addressBits (n i))
    (v : (i : I) → FixedCandidate.Array (n i)) (clock tick : I → ℕ)
    (hc : ∀ i, n i ≤ clock i) (C : ℕ)
    (rate : ∀ i, (order (addressBits (n i)) ((box (n i)).length/4)).length * tick i ≤ C*(clock i+1)) :
    let k i := addressBits (n i)
    let w i := physicalWidth (box := box (n i))
    let rank i := packedRecord (h i) (hd i)
    let jobs i := order (k i) ((box (n i)).length/4)
    let query i : Query := (dir i,tally (k i),tally (s i).val)
    let header i a := send (key (query i,batchTicket a))
    let place i := tapeArray (rank i) (fun a : Record (k i) => send (Dusk.mark a))
    let input i := v i ∘ (rank i).symm
    let step i (a : (Bool × ℕ) × ℕ) := Benes.batchStage (fun b => b.val / SynchronizedPermutationBudget.capacity (k i))
      (w i) (fun _ : Unit => PermDirectory.switchTable (dir i) (s i).val) a.1 a.2
    BoundedTask (fun z : (i : I) × {a // a ∈ jobs i} × Equiv.Perm (Benes.PackedAddress Unit (w i)) => tick z.1)
        (fun z => n z.1)
        (fun z => .fork (header z.1 z.2.1) (place z.1 (Benes.scatter z.2.2 (input z.1))))
        (fun z => place z.1 (Benes.scatter (step z.1 z.2.1) (Benes.scatter z.2.2 (input z.1)))) →
      BoundedTask clock n
        (fun i => send (phaseStageTicket (k i) (dir i) (s i).val (s i).isLt,records (v i)))
        (fun i => send (records (permutedRow (h i) (hd i)
          (directedPlan (dir i,tally (k i)))[(s i).val] (v i)))) := by
  intro k w rank jobs query header place input step kernel
  let d i := passDirectory key (dir i) (k i) (s i).val
  let t i := phaseStageTicket (k i) (dir i) (s i).val (s i).isLt
  obtain ⟨⟨A,cap⟩,prep⟩ := preparePermutationTicket key program n hn dir s
  let V i := (A + 75000)*(n i+1)
  have hD i (b : Fin ((box (n i)).length/4)) : w i b ≤ SynchronizedPermutationBudget.width (k i) :=
    (physicalWidth_log (h i) b).trans (Nat.mul_le_mul_left 140
      ((Nat.clog_monotone 2 (Nat.le_succ (k i))).trans (Nat.le_add_left ..)))
  have fitsD i : (d i).count ≤ V i :=
    (cap i).trans (Nat.mul_le_mul_right _ (Nat.le_add_right ..))
  have fitsA i : (Task.forest (fun z => send (Dusk.mark z)) (List.ofFn (v i))).count ≤ V i := by
    rw [recordForest]
    exact (recordVolume (hn i) (v i)).trans (Nat.mul_le_mul_right _ (Nat.le_add_left ..))
  have full := PermDirectory.bounded_indexedRow k (fun i => BoxScale.width (k i)) (fun i => SynchronizedPermutationBudget.width (k i))
    (fun i => batches ((box (n i)).length/4) (k i)) h hd dir s tag
    (fun i b => b.val / SynchronizedPermutationBudget.capacity (k i)) hD
    (fun i b => SynchronizedPermutationBudget.batch_index_lt (SynchronizedPermutationBudget.capacity_pos (room i)) b)
    header (fun _ z => send (Dusk.mark z)) v tick V n fitsD fitsA kernel
  have bounded := full.bound (time' := clock) (space' := n) (C+A+75001) (A+75001) (fun i => by
    have hr := rate i
    change (Benes.batchOrder _ _).length * tick i ≤ _ at hr
    rw [Benes.batchOrder_length] at hr
    have hv := Nat.mul_le_mul_left (A+75000) (Nat.succ_le_succ (hc i))
    change _ + (A+75000)*(n i+1)+1 ≤ _
    calc
      _ ≤ C*(clock i+1)+(A+75000)*(clock i+1)+(clock i+1) :=
        Nat.add_le_add (Nat.add_le_add hr hv) (Nat.succ_le_succ (Nat.zero_le _))
      _ = _ := by ring) (fun i => by
      change (A+75000)*(n i+1)+n i+1 ≤ (A+75001)*(n i+1)
      exact le_of_eq (by ring))
  have scan := bounded.conform (fun _ => rfl) (fun _ => rfl)
    (input' := fun i => Tree.fork (d i) (send (records (v i))))
    (output' := fun i => send (records (permutedRow (h i) (hd i)
      (directedPlan (dir i,tally (k i)))[(s i).val] (v i))))
    (fun i => congrArg (Tree.fork (d i)) (recordForest (v i)))
    (fun i => recordForest (permutedRow (h i) (hd i) _ (v i)))
  have parked := (prep.left (fun i => send (records (v i)))).bound (time' := clock) (space' := n)
    1 75001 (fun i => by simpa using Nat.succ_le_succ (hc i)) (fun i => by
      have capA := recordVolume (hn i) (v i)
      change n i + size (records (v i)) + 1 ≤ _
      rw [show 75001 = 75000 + 1 by decide,Nat.add_mul,Nat.one_mul]
      omega)
  exact FixedCandidate.sequence parked scan

end FixedLayer

end

end NearSquareRoot
end Computability
end OAI
