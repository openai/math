import OAI.ThreeFlat.Diagonal.TraceRowPackets
import OAI.ThreeFlat.Diagonal.TracePairRead

namespace OAI
/-! # Raw CPU pins seen by a physical row verifier -/

namespace ThreeFlat.Diagonal.TraceRowPackets

open Computability.VPVNP BurstRAM BurstRAM.PrivateRAM RAMSerialization TraceWords TraceRows TraceBanks

variable {w p r d f S : ℕ}

private abbrev R (w p r : ℕ) := Row (w+1) (Snapshot w p r)

/-- Reading the canonical binary representation of a padding row yields zero
at every logical register/operand bit, also when the terminal row is last. -/
theorem padding_encode (hw : 3 ≤ w+1) (hp : p ≤ 2^(w+1)) :
    (rowFormat (r:=r) hw hp).encode .pad = fun _ => false := by
  funext j
  obtain ⟨⟨fld,b⟩,rfl⟩ := finProdFinEquiv.surjective j
  rw [Format.encode, arrayBits_at]
  have hz : (rowFormat hw hp).words (.pad : R w p r) fld = 0 := by
    induction fld using Fin.addCases <;> simp [header,regs]
  rw [hz, wordBits_zero]

/-- The canonicality bit tests the exact local read/encode fixed point on
an arbitrary physical CPU bundle. -/
theorem canonical_roundtrip (hw : 3 ≤ w+1) (hp : p ≤ 2^(w+1)) (entry : Fin p)
    (z : Fin ((5+r)*(w+1)) → Bool) :
    ((canonicalFrame hw hp).circuit ()).eval (fun jk => z (finProdFinEquiv jk)) = true ↔
      let fmt := rowFormat (r:=r) hw hp
      fmt.encode (fmt.parse ((arrayBits _ _).symm z)) = z := by
  rw [canonicalCircuit_at hw hp entry]
  constructor
  · rintro ⟨x,rfl⟩
    simp [Format.encode, Format.parse_words]
  · exact fun h => ⟨_,h⟩

private theorem codeAt_time (hw : 3 ≤ w+1) (hp : p ≤ 2^(w+1)) (rows : Fin f → R w p r)
    (t : ℕ) (j : Fin ((5+r)*(w+1))) :
    (if h : t < f then (writeCpu hw hp rows ⟨t,h⟩) j else false) =
      (rowFormat hw hp).encode (clockAt rows t) j := by
  by_cases h : t < f <;> simp [h, writeCpu, clockAt, padding_encode]

theorem cpuPin_clock (hw : 3 ≤ w+1) (hp : p ≤ 2^(w+1)) (v : Fin (2^d)) (s : Fin 3)
    (header : Fin S → Word w) (rows : Fin f → R w p r) (z : SortBits d (w+1))
    (inCpu : S ≤ 2*v.val+s.val) (j : Fin ((5+r)*(w+1))) :
    TracePhysical.valuation (by omega) v header (writeCpu hw hp rows) z (cpuPin s j) =
      (rowFormat hw hp).encode (clockAt rows (2*v.val+s.val-S)) j := by
  simpa only [TracePhysical.valuation, cpuPin, atClock, ite_eq_left inCpu] using
    codeAt_time hw hp rows (2*v.val+s.val-S) j

theorem pairRead_clock (hw : 3 ≤ w+1) (hp : p ≤ 2^(w+1)) (v : Fin (2^d)) (s : Fin 2)
    (header : Fin S → Word w) (rows : Fin f → R w p r) (z : SortBits d (w+1))
    (h : S ≤ slotAddress d v s) (i : TracePair.Raw w r) :
    ((pairRead s i).2.eval (TracePhysical.valuation (by omega) v header (writeCpu hw hp rows) z)) =
      TracePair.packed hw hp (clockAt rows (slotAddress d v s-S))
        (clockAt rows (slotAddress d v s-S+1)) i := by
  obtain ⟨side,field,k⟩ := i
  rw [TracePair.packed_encode]
  cases side with
  | false => exact cpuPin_clock hw hp v s.castSucc header rows z h _
  | true =>
    have hk : S ≤ 2*v.val+s.succ.val := by
      simp only [slotAddress, Fin.val_succ] at h ⊢
      omega
    have he : 2*v.val+s.succ.val-S = slotAddress d v s-S+1 := by
      simp only [slotAddress, Fin.val_succ] at h ⊢
      omega
    change TracePhysical.valuation (by omega) v header (writeCpu hw hp rows) z (cpuPin s.succ (finProdFinEquiv (field,k))) =
      (rowFormat hw hp).encode (clockAt rows (slotAddress d v s-S+1)) (finProdFinEquiv (field,k))
    rw [← he]
    exact cpuPin_clock hw hp v s.succ header rows z hk _

variable {F : Type*} [Fintype F] [CommSemiring F] {k : ℕ}

noncomputable def rowBits (hF : Fintype.card F ≤ 2^w) (hw : 3 ≤ w+1) (hp : p ≤ 2^(w+1))
    (M : Machine w p r k) (st : Word w) (hs : S ≤ 2^w) (hf : f ≤ 2^(w+1))
    (header : Fin S → Word w) (cpu : CpuBits w r f) (z : SortBits d (w+1)) (v : Fin (2^d)) (a : Factor F) : Bool :=
  (packet hF hw hp M st hs hf v a).2.eval (TracePhysical.valuation (by omega) v header cpu z)

end ThreeFlat.Diagonal.TraceRowPackets

end OAI
