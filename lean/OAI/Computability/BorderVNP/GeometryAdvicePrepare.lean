import OAI.Computability.BorderVNP.GeometryAdvicePrepareGather
import OAI.Computability.BorderVNP.DiagonalResidueRAMReplay

/-! # Full geometry-advice staging and gate valuation on physical RAM

The prefix of the bit stream encodes the ordinary six-word header, shared
AND/NOT program and input-address list. Any remaining words are packed in
the same loop and retained for the output reader. The evaluator makes no
private choices, since all geometry inputs are public.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace GeometryAdvicePrepare

open VPVNP VPVNP.BurstRAM VPVNP.BooleanTranscript RoutingISA DiagonalResidueRAM

variable {w u k : ℕ}

/-- Native preparation produces the circuit register frame and query bank, preserves
the entire packed packet, and leaves all memory outside its two write intervals intact. -/
theorem prepare_runs (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
    (s : Bank w) (m : Memory w) (base start dense : ℕ) (src : Fin u → ℕ)
    (c : Circuit (Fin u ⊕ Fin 0) k) (x : Fin u → Bool) (suffix : List (Word w))
    (L : Layout base start dense src k w (6+3*k+u+suffix.length))
    (hpub : (pub 0).val+101 < 2^w) (hframe : frame98 pub m dense start (6+3*k+u+suffix.length))
    (hbits : DiagonalTallyBits.WordsAt m dense ((payload w base start c src ++ suffix).map BurstRAM.wordBits))
    (hsrc : ∀ i, m (src i) = wordBit w (x i)) :
    ∃ z mz, Exact pub mac prepare s m [] (prepareTicks u (6+3*k+u+suffix.length) w) z mz ∧
      (frame base (start+6) c).loaded z ∧ queryLoaded mz base x ∧
      Words mz start (payload w base start c src ++ suffix) ∧
      ∀ a, (a < base ∨ base+2+u ≤ a) → (a < start ∨ start+(6+3*k+u+suffix.length) ≤ a) →
        mz a = m a := by
  let words := payload w base start c src ++ suffix
  let data := words.map BurstRAM.wordBits
  let count := 6+3*k+u+suffix.length
  have hlen : data.length = count := by simp [data,words,count,payload_length]
  have hp : start+count < 2^w := L.packed
  have hd : dense+count*w < 2^w := L.denseFit
  have hv : gateBase base u 0+k ≤ start := L.valuation
  have hW : w < 2^w := Nat.lt_pow_self (by decide)
  have hw₂ : 1 < 2^w := by omega
  obtain ⟨t,rt,hs₀,hs₁,hs₂,hs₃,hs₄,hs₅⟩ := beginPack_runs pub mac s m dense start count hframe hpub
  obtain ⟨es,b,rb,tb,keep,_,_⟩ := DiagonalTallyBits.pack_runs pub mac t m data
    (p := dense) (d := start) (width := w)
    (by rw [hs₀,word_val _ _ (by omega)]) (by rw [hs₁,word_val _ _ (by omega)])
    (by rw [hs₂,word_val _ _ (by omega),hlen]) (by rw [hs₃,word_val _ _ hW])
    (by rw [hs₄]; exact word_val _ _ hw₂) le_rfl
    (by intro bits h; obtain ⟨_,_,rfl⟩ := List.mem_map.mp h; simp [BurstRAM.wordBits])
    (hlen ▸ hd) (hlen ▸ hp) (hlen ▸ L.denseSeparate) hbits
  let packed := DiagonalTallyBits.outputMemory m start data
  have packRun : Exact pub mac DiagonalTallyBits.pack t m [] (DiagonalTallyBits.ticks count w) b packed :=
    ⟨es,rb,hlen ▸ tb⟩
  have allWords : Words packed start words := words_after_pack m start words
  have headWords := (Words.append allWords).1
  have sources (i : Fin u) : packed (src i) = wordBit w (x i) :=
    (DiagonalTallyBits.outputMemory_outside m start _ data (hlen ▸ L.sourcePacked i)).trans (hsrc i)
  obtain ⟨z,rg,hload⟩ := headerGather_runs pub mac b packed base start src c x
    ((keep 48 (by decide)).trans hs₅) ((keep 63 (by decide)).trans hs₄) hv
    (by dsimp [count] at hp; omega) L.sourceFit L.sourceQuery sources headWords
  refine ⟨z, queryMemory packed base x, ?_, hload, queryMemory_loaded .., ?_, ?_⟩
  · have run := rt.seq (packRun.seq rg)
    simpa only [prepare,prepareTicks,count,Nat.add_assoc,List.nil_append] using run
  · intro i
    rw [queryMemory_outside packed base x _ (.inr (by unfold gateBase at hv; omega))]
    exact allWords i
  · intro a hval hpack
    rw [queryMemory_outside packed base x a hval]
    exact DiagonalTallyBits.outputMemory_outside _ _ _ _ (hlen ▸ hpack)

/-- Running the staged geometry evaluator materializes every shared gate and returns
the validity bit. The packed references and all memory outside the valuation and
packed regions survive the whole run. -/
theorem stage_runs (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
    (s : Bank w) (m : Memory w) (base start dense : ℕ) (src : Fin u → ℕ)
    (c : Circuit (Fin u ⊕ Fin 0) k) (x : Fin u → Bool) (suffix : List (Word w))
    (L : Layout base start dense src k w (6+3*k+u+suffix.length))
    (hpub : (pub 0).val+101 < 2^w) (hframe : frame98 pub m dense start (6+3*k+u+suffix.length))
    (hbits : DiagonalTallyBits.WordsAt m dense ((payload w base start c src ++ suffix).map BurstRAM.wordBits))
    (hsrc : ∀ i, m (src i) = wordBit w (x i)) :
    ∃ z mz, Exact pub mac stage s m [] (stageTicks u k (6+3*k+u+suffix.length) w) z mz ∧
      z 42 = wordBit w (c.eval (Sum.elim x Fin.elim0)) ∧ z 38 = 1 ∧
      Knows base x Fin.elim0 (c.program.run (Sum.elim x Fin.elim0)) mz ∧
      Words mz start (payload w base start c src ++ suffix) ∧
      ∀ a, (a < base ∨ gateBase base u 0+k ≤ a) → (a < start ∨ start+(6+3*k+u+suffix.length) ≤ a) →
        mz a = m a := by
  obtain ⟨t,mt,rp,hload,hx,hw,hkeep⟩ := prepare_runs pub mac s m base start dense src c x suffix
    L hpub hframe hbits hsrc
  have hv := L.valuation
  have hp := L.packed
  have hf : (frame base (start+6) c).fits w := ⟨by change gateBase base u 0+k ≤ start+6; omega,
    by change start+6+3*k < _; omega⟩
  obtain ⟨z,mz,rv,hbit,hone,hknows,hstable⟩ :=
    evaluate_stores_preserves pub mac base (start+6) c x Fin.elim0 t mt hf hload hx
      (payload_parts (Words.append hw).1).2.1
  refine ⟨z,mz,?_,hbit,hone,hknows,?_,?_⟩
  · simpa [stage,stageTicks] using rp.seq rv
  · intro i
    rw [hstable _ (.inr (by omega))]
    exact hw i
  · intro a hval hpack
    rw [hstable a (by unfold gateBase at hval ⊢; omega)]
    exact hkeep a (by unfold gateBase at hval; omega) hpack

/-- Staging and evaluation cost linearly many ticks in the serialized bit count,
the query length, and the number of shared gates. -/
theorem stageTicks_le (u k count w : ℕ) :
    stageTicks u k count w ≤ 8*count*(w+1)+7*u+14*k+58 := by
  have h := DiagonalTallyBits.ticks_le count w
  unfold stageTicks prepareTicks
  omega

/-- An empty private tape in one returning geometry execution fixes the entire
native execution, including the final registers and memory. -/
theorem stage_unique {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8}
    {s m es z mz fs t mt n} (run : Runs pub mac stage s m es z mz) (h : TraceOK es [] n)
    (other : Runs pub mac stage s m fs t mt) : es = fs ∧ z = t ∧ mz = mt :=
  unique_returns (c := stage) (by decide) run other
    (tail := fs.flatMap TeamRAM.Event.choices) (tail' := []) (by simp [h.2.1])

end GeometryAdvicePrepare

end BorderVNP
end Computability
end OAI
