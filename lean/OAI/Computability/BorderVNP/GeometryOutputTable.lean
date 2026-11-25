import OAI.Computability.BorderVNP.GeometryOutput
import OAI.Computability.BorderVNP.GeometryOutputModel

/-! # Native output of a typed geometry table

After the shared gate program has populated its valuation bank, the compiled
reference directory supplies the operands of the guard and the gather. A
valid frame returns its output words and a false validity flag rejects.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace GeometryOutput

open VPVNP VPVNP.BurstRAM RoutingISA GeometryFrameEncoding DiagonalResidueRAM

variable {o b w u v : ℕ}

/-- Exact number of temporary one-word bits written for the complete geometry output. -/
theorem chunks_flatten_length {σ : Type*} (t : Table σ o b) (x : σ → Bool) :
    (chunks t x).flatten.length = o*b := by
  rw [List.length_flatten,
    List.map_eq_replicate_iff.mpr (chunk_width t x), List.sum_replicate_nat, chunks_length]

private theorem base_le_address {k : ℕ} (base : ℕ) (r : Ref Bool (Fin u ⊕ Fin v) k) :
    base ≤ address base r := by
  cases r with
  | const b => simp [address]
  | var i => cases i <;> simp [address] <;> omega
  | gate i => simp [address,gateBase]; omega

/-- Each gathered output is a constant, input or gate inside the shared valuation bank. -/
theorem outputPairs_address_range (base : ℕ) (t : Table (Fin u ⊕ Fin v) o b)
    (x : Fin u ⊕ Fin v → Bool) (p : ℕ × Bool) (hp : p ∈ outputPairs base t x) :
    base ≤ p.1 ∧ p.1 < gateBase base u v + t.size := by
  refine ⟨?_,outputPairs_address_lt base t x p hp⟩
  obtain ⟨r,_,rfl⟩ := List.mem_map.mp hp
  exact base_le_address base r

/-- A valid typed table returns the specified packed words after exactly the native output
tick count. Either ordering of the temporary buffer and the valuation bank is allowed. -/
theorem table_runs (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
    (s : Bank w) (m : Memory w) (l : Layout) (base : ℕ) (t : Table (Fin u ⊕ Fin v) o b)
    (x : Fin u → Bool) (y : Fin v → Bool) (count : l.count = o) (width : l.width = b)
    (fit : l.Fits w) (loaded : l.loaded pub m) (hb : (pub 0).val+108 < 2^w)
    (advice : Words m l.refs (referenceWords w base t))
    (knows : Knows base x y (t.program.run (Sum.elim x y)) m)
    (bound : gateBase base u v + t.size ≤ 2^w)
    (disjoint : l.temp+o*b ≤ base ∨ gateBase base u v + t.size ≤ l.temp)
    (valid : validBit t (Sum.elim x y) = true) :
    ∃ z, Exact pub mac code s m [] (ticks l.count l.width) z (resultMemory m l (chunks t (Sum.elim x y))) := by
  obtain ⟨ref,bit,src⟩ := references_loaded base l.refs t x y m advice knows bound
  rw [valid] at bit
  refine code_runs pub mac s m l (address base t.valid) (outputPairs base t _) (chunks t _) fit loaded hb
    ((address_lt base t.valid).trans_le bound) ref bit src ?_ (outputPairs_bits ..)
    ((chunks_length ..).trans count.symm) (fun bs h => (chunk_width t _ bs h).trans width.symm)
  intro p hp
  obtain ⟨lo,hi⟩ := outputPairs_address_range base t _ p hp
  rw [count,width]
  exact disjoint.elim (fun h => .inr (h.trans lo)) (fun h => .inl (hi.trans_le h))

/-- If the typed validity reference evaluates to false, the native output interpreter
rejects before either write loop. This holds for every event trace and final state. -/
theorem table_invalid_no_run (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
    (s : Bank w) (m : Memory w) (l : Layout) (base : ℕ) (t : Table (Fin u ⊕ Fin v) o b)
    (x : Fin u → Bool) (y : Fin v → Bool) (fit : l.Fits w) (loaded : l.loaded pub m)
    (hb : (pub 0).val+108 < 2^w) (advice : Words m l.refs (referenceWords w base t))
    (knows : Knows base x y (t.program.run (Sum.elim x y)) m)
    (bound : gateBase base u v + t.size ≤ 2^w) (invalid : validBit t (Sum.elim x y) = false)
    {es z mz} : ¬ Runs pub mac code s m es z mz := by
  obtain ⟨ref,bit,_⟩ := references_loaded base l.refs t x y m advice knows bound
  rw [invalid] at bit
  have hr := fit.refsEnd
  exact invalid_no_run pub mac s m l (address base t.valid) loaded hb (by omega)
    ((address_lt base t.valid).trans_le bound) ref bit

end GeometryOutput

end BorderVNP
end Computability
end OAI
