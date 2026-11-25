import OAI.ThreeFlat.Diagonal.TraceClockFactors
import OAI.ThreeFlat.Diagonal.TracePairCorrect

namespace OAI
/-! # Physical CPU validation, adjacency and terminal weights -/

namespace ThreeFlat.Diagonal.TraceRowPackets

open Computability.VPVNP BurstRAM BurstRAM.PrivateRAM RAMSerialization BooleanTranscript
open Computability.VPVNP.VerifierNetwork (Frame)
open TraceBanks TraceWords TraceRows TraceCompose
open BinPackingGames.Foundations.Complexity.CookLevin.StatementCircuit (Expr)

variable {F : Type*} [Fintype F] [CommSemiring F] {w p r k f S d : ℕ}

private abbrev R w p r := Row (w+1) (Snapshot w p r)

private theorem literal_eval {σ : Type*} (b : Bool) (x : σ → Bool) : (literal b).2.eval x = b := rfl
private theorem read_eval {σ : Type*} (j : σ) (x : σ → Bool) : (read j).2.eval x = x j := rfl

theorem all_canonical (hF : Fintype.card F ≤ 2^w) (hw : 3 ≤ w+1) (hp : p ≤ 2^(w+1))
    (M : Machine w p r k) (st : Word w) (hs : S ≤ 2^w) (hf : f ≤ 2^(w+1))
    (header : Fin S → Word w) (cpu : CpuBits w r f) (z : SortBits d (w+1)) (fit : S+f ≤ 2^(1+d)) :
    (∀ v s, rowBits hF hw hp M st hs hf header cpu z v (.inr (s,.inl 0)) = true) ↔
      writeCpu hw hp (readCpu hw hp cpu) = cpu := by
  rw [funext_iff]
  rw [← all_clock_sites S d fit (fun i => writeCpu hw hp (readCpu hw hp cpu) i = cpu i)]
  apply forall_congr'; intro v
  apply forall_congr'; intro s
  by_cases h : S ≤ slotAddress d v s
  · by_cases ht : slotAddress d v s-S < f
    · let t : Fin f := ⟨slotAddress d v s-S,ht⟩
      have val (j) : TracePhysical.valuation (by omega) v header cpu z (cpuPin s.castSucc j) = cpu t j := by
        change atClock false S (fun u => cpu u j) (slotAddress d v s)=cpu t j
        simp [atClock,h,ht,t]
      simpa only [rowBits, guardZero,packetIf_eval, h, ht, and_self, decide_true, ite_true, dite_true, substituteFintype_eval,
        read_eval, val, atClock, writeCpu, readCpu, t] using
        canonical_roundtrip hw hp M.entry (cpu t)
    · simp [rowBits,guardZero,packetIf_eval,h,ht,atClock,literal_eval]
  · simp [rowBits,guardZero,packetIf_eval,h,atClock,literal_eval]

theorem all_pairs (hF : Fintype.card F ≤ 2^w) (hw : 3 ≤ w+1) (hp : p ≤ 2^(w+1))
    (M : Machine w p r k) (st : Word w) (hs : S ≤ 2^w) (hf : f ≤ 2^(w+1))
    (header : Fin S → Word w) (xs : Fin f → R w p r) (z : SortBits d (w+1)) (fit : S+f ≤ 2^(1+d)) :
    (∀ v s, rowBits hF hw hp M st hs hf header (writeCpu hw hp xs) z v (.inr (s,.inl 1)) = true) ↔
      pairs (exposed M) (List.ofFn xs) := by
  rw [pairs_ofFn_iff, ← all_clock_sites S d fit]
  apply forall_congr'; intro v
  apply forall_congr'; intro s
  by_cases h : S ≤ slotAddress d v s
  · by_cases ht : slotAddress d v s-S < f
    · simp only [rowBits,guardOne,packetIf_eval,h,ht,and_self,decide_true,ite_true,substituteFintype_eval,atClock]
      rw [show (fun i => (pairRead s i).2.eval (TracePhysical.valuation (by omega) v header (writeCpu hw hp xs) z)) =
          TracePair.packed hw hp (clockAt xs (slotAddress d v s-S)) (clockAt xs (slotAddress d v s-S+1)) from
        funext (pairRead_clock hw hp v s header xs z h)]
      simpa [clockAt,ht] using TracePair.pairCircuit_correct hw hp M (clockAt xs (slotAddress d v s-S))
        (clockAt xs (slotAddress d v s-S+1))
    · simp [rowBits,guardOne,packetIf_eval,h,ht,atClock,literal_eval]
  · simp [rowBits,guardOne,packetIf_eval,h,atClock,literal_eval]

theorem first_guard_at (hF : Fintype.card F ≤ 2^w) (hw : 3 ≤ w+1) (hp : p ≤ 2^(w+1))
    (M : Machine w p r k) (st : Word w) (hs : S ≤ 2^w) (hf : f ≤ 2^(w+1))
    (header : Fin S → Word w) (xs : Fin f → R w p r) (z : SortBits d (w+1))
    (v : Fin (2^d)) (s : Fin 2) (ha : slotAddress d v s = S) (ht : 0 < f) :
    rowBits hF hw hp M st hs hf header (writeCpu hw hp xs) z v (.inr (s,.inl 2)) = true ↔
      before (clockAt xs 0) = some ((exposed M).start (wide st)) := by
  simp only [rowBits,guardTwo,packetIf_eval,ha,ht,true_and,ite_true,TracePair.formulaPacket_eval]
  apply (initialCheck_at hw hp M.entry st _ _ _ (clockAt xs 0) (fun _ => rfl) ?_).trans
  · simp [exposed]
  intro j k
  have he := cpuPin_clock hw hp v s.castSucc header xs z (by change S ≤ slotAddress d v s; rw [ha]) (finProdFinEquiv (j,k))
  change _ = (rowFormat hw hp).encode (clockAt xs (slotAddress d v s-S)) _ at he
  rw [ha,Nat.sub_self] at he
  have hbit := TracePair.packed_encode hw hp (clockAt xs 0) (clockAt xs 0) false j k
  exact he.trans hbit.symm

theorem all_first (hF : Fintype.card F ≤ 2^w) (hw : 3 ≤ w+1) (hp : p ≤ 2^(w+1))
    (M : Machine w p r k) (st : Word w) (hs : S ≤ 2^w) (hf : f ≤ 2^(w+1))
    (header : Fin S → Word w) (xs : Fin f → R w p r) (z : SortBits d (w+1)) (fit : S+f ≤ 2^(1+d)) :
    (∀ v s, rowBits hF hw hp M st hs hf header (writeCpu hw hp xs) z v (.inr (s,.inl 2)) = true) ↔
      before ((List.ofFn xs).headD .pad) = some ((exposed M).start (wide st)) := by
  rw [ofFn_headD]
  by_cases ht : 0 < f
  · have hbound : S/2 < 2^d := by rw [Nat.pow_add,Nat.pow_one] at fit; omega
    let v : Fin (2^d) := ⟨S/2,hbound⟩
    let s : Fin 2 := ⟨S%2,Nat.mod_lt _ (by decide)⟩
    have he : slotAddress d v s = S := by dsimp [slotAddress,v,s]; omega
    constructor
    · intro x
      exact (first_guard_at hF hw hp M st hs hf header xs z v s he ht).mp (x v s)
    · intro x v' s'
      by_cases he' : slotAddress d v' s' = S
      · exact (first_guard_at hF hw hp M st hs hf header xs z v' s' he' ht).mpr x
      · simp [rowBits,guardTwo,packetIf_eval,he',ht,literal_eval]
  · have hf0 : f = 0 := Nat.eq_zero_of_not_pos ht
    subst f
    simp [rowBits,guardTwo,packetIf_eval,literal_eval,clockAt,before]

end ThreeFlat.Diagonal.TraceRowPackets

end OAI
