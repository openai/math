import OAI.ThreeFlat.Diagonal.TraceMemoryPacketInputs
import OAI.ThreeFlat.Diagonal.TracePhysicalPorts
import OAI.ThreeFlat.Diagonal.TraceMemoryPassCircuit

namespace OAI
/-! # Physical CPU and public header pins drive the distributed memory checker -/

namespace ThreeFlat.Diagonal.TraceRowPackets

open Computability.VPVNP BurstRAM RAMSerialization
open TraceBanks TraceWords TraceSlots TraceRows TraceSortSite
open BinPackingGames.Foundations.Complexity.CookLevin.StatementCircuit (Expr)

variable {w p r S f d : ℕ}

private theorem wide_fits (hs : S ≤ 2^w) : S ≤ 2^(w+1) :=
  hs.trans (Nat.pow_le_pow_right (by decide) (Nat.le_succ w))

private theorem headerExpr_read (hw : 2 ≤ w+1) (v : Fin (2^d)) (s : Fin 2)
    (header : ℕ → Word w) (cpu : CpuBits w r f) (z : SortBits d (w+1))
    (active : slotAddress d v s < S) (j : Fin (w+1)) :
    (headerExpr s j).eval (TracePhysical.valuation hw v (fun i : Fin S => header i.val) cpu z) =
      bits (wide (header (slotAddress d v s))) j := by
  have ha : 2*v.val+s.val < S := active
  induction j using Fin.lastCases with
  | cast j =>
    simpa [headerExpr, TracePhysical.valuation, slotAddress, ha, Expr.eval, bits, wide] using
      (Computability.VPVNP.LiveHeader.testBit_wordBits (header (slotAddress d v s)) j).symm
  | last =>
    simp [headerExpr, Expr.eval, bits, wide,
      Nat.testBit_lt_two_pow (header (slotAddress d v s)).isLt]

private theorem cpuExpr_read (hw : 3 ≤ w+1) (hp : p ≤ 2^(w+1)) (_hs : S ≤ 2^w)
    (v : Fin (2^d)) (s : Fin 2) (header : ℕ → Word w)
    (xs : Fin f → Row (w+1) (Snapshot w p r)) (z : SortBits d (w+1))
    (lo : S ≤ slotAddress d v s) (hi : slotAddress d v s-S < f)
    (j : Fin (5+r)) (k : Fin (w+1)) :
    (cpuExpr s.castSucc (j,k)).eval
      (TracePhysical.valuation (by omega) v (fun i : Fin S => header i.val) (writeCpu hw hp xs) z) =
      bits ((rowFormat hw hp).words (xs ⟨slotAddress d v s-S,hi⟩) j) k := by
  change atClock false S (fun t => (writeCpu hw hp xs) t (finProdFinEquiv (j,k)))
    (slotAddress d v s) = _
  simp only [atClock,lo,ite_true,dite_eq_left hi,writeCpu,Format.encode,arrayBits_at]
  exact (Computability.VPVNP.LiveHeader.testBit_wordBits _ _).symm

/-- For canonical CPU words, every input to the memory circuit receives the
same bit as direct assembly of local records and the shared sort messages. -/
theorem memoryInput_physical (hw : 3 ≤ w+1) (hp : p ≤ 2^(w+1))
    (hs : S ≤ 2^w) (hf : f ≤ 2^(w+1)) (v : Fin (2^d)) (header : ℕ → Word w)
    (xs : Fin f → Row (w+1) (Snapshot w p r)) (z : SortBits d (w+1))
    (a : TraceMemoryCircuit.Port d (w+1)) :
    (memoryInput hw hs hf v a).2.eval
      (TracePhysical.valuation (by omega) v (fun i : Fin S => header i.val) (writeCpu hw hp xs) z) =
    TraceMemoryCircuit.inputAt (by omega)
      (fun s => localWordSlot S (wide_fits hs) hf (wide ∘ header) xs (slotAddress d v s)) v z a := by
  rcases a with ⟨s,g,j⟩ | (⟨l,own,s,g,j⟩ | ⟨out,g,j⟩)
  · change _ = (slotFormat _).encode _ (finProdFinEquiv (g,j))
    rw [slotFormat_encode_at]
    by_cases h₁ : slotAddress d v s < S
    · simp only [initialInput_eval, dite_eq_left h₁, localWordSlot,
        Function.comp_apply]
      apply initKey_eval
      exact headerExpr_read _ _ _ header _ _ h₁
    · by_cases h₂ : slotAddress d v s-S < f
      · simp only [initialInput_eval, dite_eq_right h₁, dite_eq_left h₂, localWordSlot]
        apply probeKey_eval hw hp
        exact cpuExpr_read hw hp hs v s header xs z (Nat.le_of_not_gt h₁) h₂
      · simp only [initialInput_eval, dite_eq_right h₁, dite_eq_right h₂, localWordSlot]
  · rfl
  · cases out with
    | true =>
      simp only [memoryInput,read,Computability.VPVNP.BooleanTranscript.Circuit.eval,Computability.VPVNP.Ref.read,
        TracePhysical.valuation,TraceMemoryCircuit.inputAt,TraceMemoryCircuit.outgoingBits];
      split <;> rfl
    | false =>
      cases v with | mk v hv =>
        cases v with
        | zero => rfl
        | succ v => simp [memoryInput,read,Computability.VPVNP.BooleanTranscript.Circuit.eval,Computability.VPVNP.Ref.read,
            TracePhysical.valuation,TraceMemoryCircuit.inputAt,TraceMemoryCircuit.incomingBits]

private theorem local_slots_eq (_hw : 3 ≤ w+1) (hs : S ≤ 2^w) (hf : f ≤ 2^(w+1))
    (xs : Fin f → Row (w+1) (Snapshot w p r)) (header : ℕ → Word w)
    {P : Program (w+1) (Snapshot w p r)} {c}
    (hl : Local P c (List.ofFn xs)) (fit : S+f ≤ 2^(1+d)) (v : Fin (2^d))
    (ht : (report (List.ofFn xs)).events.length ≤ 2^(w+1)) :
    (fun s => localWordSlot S (wide_fits hs) hf (wide ∘ header) xs (slotAddress d v s)) =
      TraceMemoryCircuit.initialSlots S d (wide ∘ header) (report (List.ofFn xs)).events
        (wide_fits hs) ht v := by
  funext i
  apply toOrdered_injective
  apply congrArg RAMMemory.OrderedSlot.mk
  rw [localWordSlot_widen]
  unfold TraceMemoryCircuit.initialSlots
  rw [widen_narrowSlot, wire_eq_source hl S (1+d) _ fit]
  simp [slotAddress,Nat.mul_comm]

private theorem report_fits (hf : f ≤ 2^(w+1)) {xs : Fin f → Row (w+1) (Snapshot w p r)}
    {P : Program (w+1) (Snapshot w p r)} {c} (hl : Local P c (List.ofFn xs)) :
    (report (List.ofFn xs)).events.length ≤ 2^(w+1) := by
  have h := (local_spec hl).1.length_lt
  simp only [List.length_ofFn] at h
  omega

theorem memoryPacket_on_run (hw : 3 ≤ w+1) (hp : p ≤ 2^(w+1))
    (hs : S ≤ 2^w) (hf : f ≤ 2^(w+1)) (v : Fin (2^d)) (header : ℕ → Word w)
    (xs : Fin f → Row (w+1) (Snapshot w p r)) (z : SortBits d (w+1))
    {P : Program (w+1) (Snapshot w p r)} {c} (hl : Local P c (List.ofFn xs))
    (fit : S+f ≤ 2^(1+d)) :
    (memoryPacket hw hs hf v).2.eval
      (TracePhysical.valuation (by omega) v (fun i : Fin S => header i.val) (writeCpu hw hp xs) z) =
      ((TraceMemoryCircuit.row (by omega) v).circuit ()).eval
        (TraceMemoryCircuit.inputAt (by omega) (TraceMemoryCircuit.initialSlots S d
          (wide ∘ header) (report (List.ofFn xs)).events (wide_fits hs) (report_fits hf hl) v) v z) := by
  rw [memoryPacket_eval]
  apply congrArg
  funext a
  simpa only [local_slots_eq hw hs hf xs header hl fit v (report_fits hf hl)] using
    memoryInput_physical hw hp hs hf v header xs z a

theorem all_memoryPacket_iff (hw : 3 ≤ w+1) (hp : p ≤ 2^(w+1))
    (hs : S ≤ 2^w) (hf : f ≤ 2^(w+1)) (header : ℕ → Word w)
    (xs : Fin f → Row (w+1) (Snapshot w p r)) (z : SortBits d (w+1))
    {P : Program (w+1) (Snapshot w p r)} {c} (hl : Local P c (List.ofFn xs))
    (fit : S+f ≤ 2^(1+d)) :
    (∀ v : Fin (2^d), (memoryPacket hw hs hf v).2.eval
      (TracePhysical.valuation (by omega) v (fun i : Fin S => header i.val) (writeCpu hw hp xs) z) = true) ↔
      memoryPass (by omega) S d (wide ∘ header) (report (List.ofFn xs)).events z := by
  simp_rw [memoryPacket_on_run hw hp hs hf _ header xs z hl fit]
  exact TraceMemoryCircuit.rows_iff_memoryPass _ S d _ _ _ _ z

end ThreeFlat.Diagonal.TraceRowPackets

end OAI
