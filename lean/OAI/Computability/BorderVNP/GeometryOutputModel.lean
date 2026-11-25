import OAI.Computability.BorderVNP.DiagonalResidueRAMPayload
import OAI.Computability.BorderVNP.GeometryFrameEncoding
import OAI.Computability.BorderVNP.ParseBatchSortCompare
import OAI.Computability.VPVNP.RAMTapeWordSlice

/-! # Geometry output addresses and word order

Geometry frames name bits from high to low. The literal output directory names the
validity wire first, then all word bits from low to high, as consumed by the packer.
The same gate valuation supplies both the validity check and the complete word array.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace GeometryOutput

open VPVNP VPVNP.BurstRAM GeometryFrameEncoding DiagonalResidueRAM

variable {σ : Type*} {o b w u v : ℕ}

/-- Output references grouped by word, in the order consumed by the RAM packer. -/
private def refChunks (t : Table σ o b) : List (List (Ref Bool σ t.size)) :=
  List.ofFn fun i => (List.ofFn (t.bit i)).reverse

/-- Read a geometry reference after executing the one shared gate program. -/
private def readBit (t : Table σ o b) (x : σ → Bool) (r : Ref Bool σ t.size) : Bool :=
  r.read id x (t.program.run x)

/-- The valid flag read by the native output guard. -/
def validBit (t : Table σ o b) (x : σ → Bool) : Bool := readBit t x t.valid

/-- Actual low-to-high output digits, with a separate list for each word. -/
def chunks (t : Table σ o b) (x : σ → Bool) : List (List Bool) :=
  (refChunks t).map (List.map (readBit t x))

@[simp] theorem chunks_length (t : Table σ o b) (x : σ → Bool) : (chunks t x).length = o := by
  simp [chunks,refChunks]

/-- Each chunk is the reverse of the named geometry wires for that word. -/
theorem chunk_eq (t : Table σ o b) (x : σ → Bool) (i : Fin o) :
    (chunks t x)[i.val]'(by simp) =
      (List.ofFn fun j => (t.bit i j).read id x (t.program.run x)).reverse := by
  simp [chunks,refChunks,readBit,List.map_reverse, List.map_ofFn, Function.comp_def]

/-- All output chunks have the frame's specified bit width, including width zero. -/
theorem chunk_width (t : Table σ o b) (x : σ → Bool) (bits : List Bool)
    (h : bits ∈ chunks t x) : bits.length = b := by
  obtain ⟨_,hr,rfl⟩ := List.mem_map.mp h
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hr
  simp

/-- Reversing the named wires changes an MSB-first word into its LSB-first
representation with the identical natural value. -/
theorem value_reverse_ofFn (bits : Fin b → Bool) :
    TapeWord.value (List.ofFn bits).reverse = ParseBatchSort.value bits := by
  induction b with
  | zero => simp [TapeWord.value,ParseBatchSort.value]
  | succ b ih =>
    rw [List.ofFn_succ,List.reverse_cons,TapeWord.value_append,ParseBatchSort.value,ih]
    simp [TapeWord.value, Nat.mul_comm, Nat.add_comm]

/-- The packed RAM word has the same numerical value as the original geometry word. -/
theorem chunk_value (t : Table σ o b) (x : σ → Bool) (i : Fin o) :
    TapeWord.value ((chunks t x)[i.val]'(by simp)) =
      ParseBatchSort.value (fun j => (t.bit i j).read id x (t.program.run x)) := by
  rw [chunk_eq,value_reverse_ofFn]

/-- On a compiled geometry frame this is exactly the validity flag of the original circuit. -/
theorem compiled_valid {τ : Type*} [Fintype σ] (f : VerifierNetwork.Frame σ (Outputs o b))
    (pins : σ → τ ⊕ Bool) (x : τ → Bool) :
    validBit (compile f pins) x = f.eval (fun j => (pins j).elim x id) (.inr ()) :=
  valid_eval f pins x

/-- The packed output of a compiled frame gives its original MSB-first numerical word. -/
theorem compiled_chunk_value {τ : Type*} [Fintype σ] (f : VerifierNetwork.Frame σ (Outputs o b))
    (pins : σ → τ ⊕ Bool) (x : τ → Bool) (i : Fin o) :
    TapeWord.value ((chunks (compile f pins) x)[i.val]'(by simp)) =
      ParseBatchSort.value (fun j => f.eval (fun a => (pins a).elim x id) (.inl (i,j))) := by
  rw [chunk_value]
  exact congrArg ParseBatchSort.value (funext fun j => bit_eval f pins i j x)

/-- Address/bit pairs expected by the native indirect-gather loop, excluding the validity flag. -/
def outputPairs (base : ℕ) (t : Table (Fin u ⊕ Fin v) o b) (x : Fin u ⊕ Fin v → Bool) :
    List (ℕ × Bool) :=
  (refChunks t).flatten.map fun r => (address base r, readBit t x r)

/-- Literal address table. Its contents depend only on the compiled circuit and its base. -/
def referenceWords (w base : ℕ) (t : Table (Fin u ⊕ Fin v) o b) : List (Word w) :=
  word w (address base t.valid) :: (refChunks t).flatten.map (word w ∘ address base)

private theorem ref_count (t : Table σ o b) : (refChunks t).flatten.length = o*b := by
  rw [List.length_flatten]
  simp [refChunks, List.map_ofFn, Function.comp_def,List.ofFn_const]

@[simp] theorem referenceWords_length (base : ℕ) (t : Table (Fin u ⊕ Fin v) o b) :
    (referenceWords w base t).length = o*b+1 := by simp only [referenceWords,List.length_cons,List.length_map,ref_count]

@[simp] theorem outputPairs_length (base : ℕ) (t : Table (Fin u ⊕ Fin v) o b)
    (x : Fin u ⊕ Fin v → Bool) : (outputPairs base t x).length = o*b := by
  simp only [outputPairs,List.length_map,ref_count]

/-- The bit stream gathered through the directory is the concatenation of the packed chunks. -/
theorem outputPairs_bits (base : ℕ) (t : Table (Fin u ⊕ Fin v) o b) (x : Fin u ⊕ Fin v → Bool) :
    (outputPairs base t x).map Prod.snd = (chunks t x).flatten := by
  simp only [outputPairs,List.map_map, Function.comp_def, List.map_flatten, chunks]

/-- Every selected output points into the finite valuation bank, including repeated references. -/
theorem outputPairs_address_lt (base : ℕ) (t : Table (Fin u ⊕ Fin v) o b)
    (x : Fin u ⊕ Fin v → Bool) (p : ℕ × Bool) (hp : p ∈ outputPairs base t x) :
    p.1 < gateBase base u v + t.size := by
  obtain ⟨r,_,rfl⟩ := List.mem_map.mp hp
  exact address_lt base r

/-- The actual literal words and the gate-memory invariant supply the guard operand and
the complete indirect address/bit stream required by the native output reader. -/
theorem references_loaded (base ptr : ℕ) (t : Table (Fin u ⊕ Fin v) o b)
    (x : Fin u → Bool) (y : Fin v → Bool) (m : Memory w)
    (advice : Words m ptr (referenceWords w base t))
    (run : Knows base x y (t.program.run (Sum.elim x y)) m)
    (fit : gateBase base u v + t.size ≤ 2^w) :
    m ptr = word w (address base t.valid) ∧
      m (address base t.valid) = wordBit w (validBit t (Sum.elim x y)) ∧
      sourcesAt m (ptr+1) (outputPairs base t (Sum.elim x y)) := by
  change Words m ptr ([word w (address base t.valid)] ++ _) at advice
  obtain ⟨first,rest⟩ := advice.append
  refine ⟨by simpa using first ⟨0, by simp⟩,run t.valid,?_⟩
  apply sourcesAt_of_words
  · simpa only [outputPairs,List.map_map,Function.comp_def,List.length_singleton] using rest
  · intro pair hp
    obtain ⟨r,_,rfl⟩ := List.mem_map.mp hp
    exact ⟨(address_lt base r).trans_le fit, run r⟩

end GeometryOutput

end BorderVNP
end Computability
end OAI
