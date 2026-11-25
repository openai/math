import OAI.Computability.NearSquareRoot.SynchronizedPermutationSweepKernel
import OAI.Computability.NearSquareRoot.SynchronizedPermutationSweepEffectiveHeader
import OAI.Computability.NearSquareRoot.SynchronizedPermutationSweepEffectiveFFT

/-! # Complete effective compilation of a permutation opcode from its batch kernels -/

namespace OAI
namespace Computability
namespace NearSquareRoot

set_option maxHeartbeats 2400000
set_option maxRecDepth 4000
noncomputable section
namespace FixedLayer

open IntegerMultiplication Code FixedCandidate FixedPoint Space DigitPacking EffectiveBoundedTask
open ShortFourier.BatchWord SynchronizedLayers SynchronizedLayers.ScheduleProgram BoxFin PermutationSweep
open PermDirectory (Query BatchTicket batchTicket)
open SynchronizedPermutationBudget (order batches)

private theorem familyBudget {P : Type} [Primcodable P] {I : P → Type}
    {t s t' s' : ∀ p, I p → ℕ} {u v : ∀ p, I p → Tree}
    (f : Family t s u v) (K L : P → ℕ)
    (ht : ∀ p i, t p i+1 ≤ K p*(t' p i+1)) (hs : ∀ p i, s p i+1 ≤ L p*(s' p i+1)) :
    Family t' s' u v := by
  obtain ⟨c,R,eff,hR,hr⟩ := f
  exact ⟨c,R,eff,hR,fun p => ⟨(hr p).1,(hr p).2.bound (K p) (L p) (ht p) (hs p)⟩⟩

/-- Assemble the physical directory generator and generated batch switch kernels into
a uniform opcode acting on Fourier records in natural order. The directory size and
the running-time coefficient may vary with the candidate. -/
theorem effectivePermutationFromBatchesAt {P H : Type} [Primcodable P] {I : P → Type} [Codec H]
    (key : P → Query × BatchTicket → H) (n : ∀ p, I p → ℕ)
    (hn : ∀ p i, 2 ≤ n p i) (h : ∀ p i, Directory (n p i)) [∀ p i j, NeZero (modulus (box (n p i)) j)] (hd : ∀ p i, 4 ≤ (box (n p i)).length)
    (dir : ∀ p, I p → Bool) (s : ∀ p (i : I p), Fin (directedPlan (dir p i,tally (addressBits (n p i)))).length)
    (tag : ∀ p i, (directedPlan (dir p i,tally (addressBits (n p i))))[(s p i).val].2.1 = kindCode .permutation)
    (room : ∀ p i, 8*SynchronizedPermutationBudget.width (addressBits (n p i)) ≤ addressBits (n p i))
    (v : ∀ p (i : I p), FixedCandidate.Array (n p i)) (arena clock tick : ∀ p, I p → ℕ)
    (fit : ∀ p i, n p i ≤ arena p i) (hc : ∀ p i, n p i ≤ clock p i) (C : P → ℕ)
    (rate : ∀ p i, (order (addressBits (n p i)) ((box (n p i)).length/4)).length * tick p i ≤ C p*(clock p i+1)) :
    let k p i := addressBits (n p i)
    let w p i := physicalWidth (box := box (n p i))
    let rank p i := packedRecord (h p i) (hd p i)
    let jobs p i := order (k p i) ((box (n p i)).length/4)
    let query p i : Query := (dir p i,tally (k p i),tally (s p i).val)
    let header p i a := send (key p (query p i,batchTicket a))
    let place p i := tapeArray (rank p i) (fun a : Record (k p i) => send (Dusk.mark a))
    let input p i := v p i ∘ (rank p i).symm
    let step p i (a : (Bool × ℕ) × ℕ) := Benes.batchStage (fun b => b.val / SynchronizedPermutationBudget.capacity (k p i))
      (w p i) (fun _ : Unit => PermDirectory.switchTable (dir p i) (s p i).val) a.1 a.2
    ((∃ A : P → ℕ, ∀ p i, (passDirectory (key p) (dir p i) (k p i) (s p i).val).count ≤ A p*(n p i+1)) ∧
      Family n n (fun p i => send (phaseStageTicket (k p i) (dir p i) (s p i).val (s p i).isLt))
        (fun p i => passDirectory (key p) (dir p i) (k p i) (s p i).val)) →
    Family (fun p (z : (i : I p) × {a // a ∈ jobs p i} × Equiv.Perm (Benes.PackedAddress Unit (w p i))) => tick p z.1)
        (fun p z => arena p z.1)
        (fun p z => .fork (header p z.1 z.2.1) (place p z.1 (Benes.scatter z.2.2 (input p z.1))))
        (fun p z => place p z.1 (Benes.scatter (step p z.1 z.2.1) (Benes.scatter z.2.2 (input p z.1)))) →
      Family clock arena
        (fun p i => send (phaseStageTicket (k p i) (dir p i) (s p i).val (s p i).isLt,records (v p i)))
        (fun p i => send (records (permutedRow (h p i) (hd p i)
          (directedPlan (dir p i,tally (k p i)))[(s p i).val] (v p i)))) := by
  intro k w rank jobs query header place input step prepare kernel
  let d p i := passDirectory (key p) (dir p i) (k p i) (s p i).val
  obtain ⟨⟨A,cap⟩,prep⟩ := prepare
  let V p i := (A p + 75000)*(n p i+1)
  have hD p i (b : Fin ((box (n p i)).length/4)) : w p i b ≤ SynchronizedPermutationBudget.width (k p i) :=
    (physicalWidth_log (h p i) b).trans (Nat.mul_le_mul_left 140
      ((Nat.clog_monotone 2 (Nat.le_succ (k p i))).trans (Nat.le_add_left ..)))
  have fitsD p i : (d p i).count ≤ V p i :=
    (cap p i).trans (Nat.mul_le_mul_right _ (Nat.le_add_right ..))
  have fitsA p i : (Task.forest (fun z => send (Dusk.mark z)) (List.ofFn (v p i))).count ≤ V p i := by
    rw [recordForest]
    exact (recordVolume (hn p i) (v p i)).trans (Nat.mul_le_mul_right _ (Nat.le_add_left ..))
  have full := PermDirectory.bounded_indexedRowFamily k (fun p i => BoxScale.width (k p i)) (fun p i => SynchronizedPermutationBudget.width (k p i))
    (fun p i => batches ((box (n p i)).length/4) (k p i)) h hd dir s tag
    (fun p i b => b.val / SynchronizedPermutationBudget.capacity (k p i)) hD
    (fun p i b => SynchronizedPermutationBudget.batch_index_lt (SynchronizedPermutationBudget.capacity_pos (room p i)) b)
    header (fun _ _ z => send (Dusk.mark z)) v tick V arena fitsD fitsA kernel
  have bounded := familyBudget (t' := clock) (s' := arena) full (fun p => C p+A p+75001) (fun p => A p+75001) (fun p i => by
    have hr := rate p i
    change (Benes.batchOrder _ _).length * tick p i ≤ _ at hr
    rw [Benes.batchOrder_length] at hr
    have hv := Nat.mul_le_mul_left (A p+75000) (Nat.succ_le_succ (hc p i))
    change _ + (A p+75000)*(n p i+1)+1 ≤ _
    calc
      _ ≤ C p*(clock p i+1) + (A p+75000)*(clock p i+1) + (clock p i+1) :=
        Nat.add_le_add (Nat.add_le_add hr hv) (Nat.succ_le_succ (Nat.zero_le _))
      _ = _ := by ring
    ) (fun p i => by
      change (A p+75000)*(n p i+1) + arena p i + 1 ≤ (A p+75001)*(arena p i+1)
      calc
        _ ≤ (A p+75000)*(arena p i+1) + arena p i + 1 := by gcongr; exact fit p i
        _ = _ := by ring)
  have scan := bounded.conform (fun _ _ => rfl) (fun _ _ => rfl)
    (u' := fun p i => Tree.fork (d p i) (send (records (v p i))))
    (v' := fun p i => send (records (permutedRow (h p i) (hd p i)
      (directedPlan (dir p i,tally (k p i)))[(s p i).val] (v p i))))
    (fun p i => congrArg (Tree.fork (d p i)) (recordForest (v p i)))
    (fun p i => recordForest (permutedRow (h p i) (hd p i) _ (v p i)))
  have parked := (familyBudget (t' := clock) (s' := arena) (prep.left (fun p i => send (records (v p i))))
    (fun _ => 1) (fun _ => 75001) (fun p i => by simpa using Nat.succ_le_succ (hc p i)) (fun p i => by
      have capA := recordVolume (hn p i) (v p i)
      change n p i + size (records (v p i)) + 1 ≤ _
      have vol := capA.trans (Nat.mul_le_mul_left 75000 (Nat.succ_le_succ (fit p i)))
      have := fit p i
      rw [show 75001 = 75000 + 1 by decide,Nat.add_mul,Nat.one_mul]
      omega))
  exact parked.sequence scan

/-- A linear-space full row when each batch kernel fits the operand budget. -/
theorem effectivePermutationFromBatches {P H : Type} [Primcodable P] {I : P → Type} [Codec H]
    (key : P → Query × BatchTicket → H) (n : ∀ p, I p → ℕ)
    (hn : ∀ p i, 2 ≤ n p i) (h : ∀ p i, Directory (n p i)) [∀ p i j, NeZero (modulus (box (n p i)) j)] (hd : ∀ p i, 4 ≤ (box (n p i)).length)
    (dir : ∀ p, I p → Bool) (s : ∀ p (i : I p), Fin (directedPlan (dir p i,tally (addressBits (n p i)))).length)
    (tag : ∀ p i, (directedPlan (dir p i,tally (addressBits (n p i))))[(s p i).val].2.1 = kindCode .permutation)
    (room : ∀ p i, 8*SynchronizedPermutationBudget.width (addressBits (n p i)) ≤ addressBits (n p i))
    (v : ∀ p (i : I p), FixedCandidate.Array (n p i)) (clock tick : ∀ p, I p → ℕ)
    (hc : ∀ p i, n p i ≤ clock p i) (C : P → ℕ)
    (rate : ∀ p i, (order (addressBits (n p i)) ((box (n p i)).length/4)).length * tick p i ≤ C p*(clock p i+1)) :
    let k p i := addressBits (n p i)
    let w p i := physicalWidth (box := box (n p i))
    let rank p i := packedRecord (h p i) (hd p i)
    let jobs p i := order (k p i) ((box (n p i)).length/4)
    let query p i : Query := (dir p i,tally (k p i),tally (s p i).val)
    let header p i a := send (key p (query p i,batchTicket a))
    let place p i := tapeArray (rank p i) (fun a : Record (k p i) => send (Dusk.mark a))
    let input p i := v p i ∘ (rank p i).symm
    let step p i (a : (Bool × ℕ) × ℕ) := Benes.batchStage (fun b => b.val / SynchronizedPermutationBudget.capacity (k p i))
      (w p i) (fun _ : Unit => PermDirectory.switchTable (dir p i) (s p i).val) a.1 a.2
    ((∃ A : P → ℕ, ∀ p i, (passDirectory (key p) (dir p i) (k p i) (s p i).val).count ≤ A p*(n p i+1)) ∧
      Family n n (fun p i => send (phaseStageTicket (k p i) (dir p i) (s p i).val (s p i).isLt))
        (fun p i => passDirectory (key p) (dir p i) (k p i) (s p i).val)) →
    Family (fun p (z : (i : I p) × {a // a ∈ jobs p i} × Equiv.Perm (Benes.PackedAddress Unit (w p i))) => tick p z.1)
        (fun p z => n p z.1)
        (fun p z => .fork (header p z.1 z.2.1) (place p z.1 (Benes.scatter z.2.2 (input p z.1))))
        (fun p z => place p z.1 (Benes.scatter (step p z.1 z.2.1) (Benes.scatter z.2.2 (input p z.1)))) →
      Family clock n
        (fun p i => send (phaseStageTicket (k p i) (dir p i) (s p i).val (s p i).isLt,records (v p i)))
        (fun p i => send (records (permutedRow (h p i) (hd p i)
          (directedPlan (dir p i,tally (k p i)))[(s p i).val] (v p i)))) :=
  effectivePermutationFromBatchesAt key n hn h hd dir s tag room v n clock tick
    (fun _ _ => le_rfl) hc C rate

end FixedLayer

end

end NearSquareRoot
end Computability
end OAI
