import OAI.Computability.BorderVNP.DiagonalResidueRAMStage

/-!
# Complete physical staging from the delivered advice and source bits

The deterministic prefix performs the actual literal-bit packing, header
reads and indirect gathers. Its post-state has the exact circuit and query
required by the fixed reader, independently of all initial scratch.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace DiagonalResidueRAM

open VPVNP VPVNP.BurstRAM VPVNP.BooleanTranscript RoutingISA

variable {w u v k : ℕ}

/-- Separated physical source and destination regions for a fixed payload.
The locations may be before or after either writable interval. -/
structure Layout (base start dense : ℕ) (src : Fin u → ℕ) (v k w : ℕ) : Prop where
  /-- All valuation words precede the decoded literal region. -/
  valuation : gateBase base u v + k ≤ start
  /-- End of the packed word region, including the gather list. -/
  packed : start+(6+3*k+u) < 2^w
  /-- End of the source bit stream in the physical memory. -/
  denseFit : dense+(6+3*k+u)*w < 2^w
  /-- Packed output words cannot overwrite unread literal bits. -/
  denseSeparate : dense+(6+3*k+u)*w ≤ start ∨ start+(6+3*k+u) ≤ dense
  /-- Query source addresses fit the actual address bank. -/
  sourceFit : ∀ i, src i < 2^w
  /-- The query gather never overwrites an unread query source. -/
  sourceQuery : ∀ i, src i < base ∨ base+2+u ≤ src i
  /-- The advice unpack never overwrites a query source. -/
  sourcePacked : ∀ i, src i < start ∨ start+(6+3*k+u) ≤ src i

/-- Precise instruction cost before the first verifier instruction. -/
def prepareTicks (u k w : ℕ) := 15 + DiagonalTallyBits.ticks (6+3*k+u) w + 12 + 11 + 7*u + 1

private theorem setConstants_preserves {m : Memory w} {base a : ℕ} (h : a<base ∨ base+2 ≤ a) :
    setConstants m base a = m a := by
  simp [setConstants,Function.update_of_ne (by omega : a ≠ base+1),Function.update_of_ne (by omega : a ≠ base)]

private theorem gathered_query {m : Memory w} (base : ℕ) (x : Fin u → Bool) :
    queryLoaded (putBits (setConstants m base) (base+2) (List.ofFn x)) base x := by
  refine ⟨fun b => ?_,fun i => ?_⟩
  · rw [putBits_outside _ _ _ _ (.inl (by cases b <;> simp))]
    cases b <;> simp [setConstants,wordBit]
    rfl
  · simpa using putBits_get (setConstants m base) (base+2) (List.ofFn x) ⟨i.val, by simp⟩

set_option maxHeartbeats 1600000 in
/-- The deterministic native prefix constructs the entire input for the
residue evaluator from its delivered payload bits and shared source cells. -/
theorem prepare_runs (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
    (s : Bank w) (m : Memory w) (base start dense : ℕ) (src : Fin u → ℕ)
    (c : Circuit (Fin u ⊕ Fin v) k) (x : Fin u → Bool)
    (L : Layout base start dense src v k w) (hpub : (pub 0).val+30 < 2^w)
    (hframe : packFrame pub m dense start (6+3*k+u))
    (hbits : DiagonalTallyBits.WordsAt m dense ((payload w base start c src).map BurstRAM.wordBits))
    (hsrc : ∀ i, m (src i) = wordBit w (x i)) :
    ∃ z mz, Exact pub mac prepare s m [] (prepareTicks u k w) z mz ∧
      (frame base (start+6) c).loaded z ∧ queryLoaded mz base x ∧ hasAdvice mz base (start+6) c := by
  let words := payload w base start c src
  let data := words.map BurstRAM.wordBits
  let n := 6+3*k+u
  let d := frame base (start+6) c
  have hlen : data.length = n := by simp [data,words,n,payload_length]
  have hv : gateBase base u v + k ≤ start := L.valuation
  have hp : start+n < 2^w := L.packed
  have hd : dense+n*w < 2^w := L.denseFit
  have hW : w < 2^w := Nat.lt_pow_self (by decide)
  have hw₂ : 1 < 2^w := by omega
  obtain ⟨t,rt,hs₀,hs₁,hs₂,hs₃,hs₄,hs₅⟩ := beginPack_runs pub mac s m dense start n hframe hpub
  obtain ⟨es,z,rp,tp,keep,_,_⟩ := DiagonalTallyBits.pack_runs pub mac t m data
    (p := dense) (d := start) (width := w)
    (by rw [hs₀,word_val _ _ (by omega)]) (by rw [hs₁,word_val _ _ (by omega)])
    (by rw [hs₂,word_val _ _ (by omega),hlen]) (by rw [hs₃,word_val _ _ hW])
    (by rw [hs₄]; exact word_val _ _ hw₂) le_rfl
    (by intro b hb; obtain ⟨_,_,rfl⟩ := List.mem_map.mp hb; simp [BurstRAM.wordBits]) (hlen ▸ hd)
    (hlen ▸ hp) (hlen ▸ L.denseSeparate) hbits
  let m₀ := DiagonalTallyBits.outputMemory m start data
  have packRun : Exact pub mac DiagonalTallyBits.pack t m [] (DiagonalTallyBits.ticks n w) z m₀ :=
    ⟨es,rp,hlen ▸ tp⟩
  have packed := words_after_pack m start words
  obtain ⟨head,advised,whereAt⟩ := payload_parts (m := m₀) packed
  obtain ⟨q,rh,hload⟩ := loadHeader_runs pub mac z m₀ start d
    ((keep 48 (by decide)).trans hs₅) ((keep 63 (by decide)).trans hs₄) (by dsimp [n] at hp; omega) head
  have hbase : base+2+u ≤ start := by unfold gateBase at hv; omega
  let e := effect false q m₀ gatherSetup
  obtain ⟨hst,hc,hi,hip,hm,htr⟩ := gather_setup_effect d q m₀ hload (by change base+1 < _; omega)
  let m₁ := setConstants m₀ base
  have gsetup : Exact pub mac gatherSetup q m₀ [] 11 e.bank m₁ := by
    have eqm : (effect false q m₀ gatherSetup).mem = m₁ := hm
    exact ⟨e.trace,by simpa only [eqm,e] using effect_runs pub mac false q m₀ gatherSetup (by decide),htr⟩
  let xs := pairs src x
  have hxs : xs.length = u := by simp [xs,pairs]
  have hb : xs.map Prod.snd = List.ofFn x := by simp [xs,pairs,List.map_ofFn,Function.comp_def]
  have sources : sourcesAt m₁ (start+6+3*k) xs := by
    apply sourcesAt_of_words
    · intro i
      have lt : i.val < u := by simpa [xs,pairs] using i.isLt
      rw [show m₁ (start+6+3*k+i.val) = m₀ _ from setConstants_preserves (Or.inr (by omega))]
      simpa [xs,pairs,List.map_ofFn] using whereAt ⟨i.val,lt⟩
    · intro t ht
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp ht
      have qs := L.sourceQuery i
      have ps := L.sourcePacked i
      have unp : m₀ (src i) = m (src i) :=
        DiagonalTallyBits.outputMemory_outside _ _ _ _ (by rw [hlen]; exact ps)
      exact ⟨L.sourceFit i, (setConstants_preserves (by omega : src i < base ∨ base+2 ≤ src i)).trans
        (unp.trans (hsrc i))⟩
  obtain ⟨last,gl,hlast⟩ := gather_loop pub mac d e.bank m₁ (base+2) (start+6+3*k) 0 xs hst hc hi hip
    (by simpa [d,frame] using hxs) (by change u<_; dsimp [n] at hp; omega) sources
    (by rw [hxs]; omega) (by rw [hxs]; dsimp [n] at hp; omega)
    (fun t ht => by obtain ⟨i,rfl⟩ := List.mem_ofFn.mp ht; have hh := L.sourceQuery i; rw [hxs]; dsimp; omega)
  have run := rt.seq (packRun.seq (rh.seq (gsetup.seq gl)))
  rw [hb] at run
  refine ⟨last,putBits m₁ (base+2) (List.ofFn x),?_,hlast.1,gathered_query base x,?_⟩
  · rw [show prepareTicks u k w = 15+(DiagonalTallyBits.ticks n w+(12+(11+(7*xs.length+1)))) by
      dsimp only [prepareTicks,n]; rw [hxs]; omega]
    exact run
  · intro i
    rw [putBits_outside _ _ _ _ (Or.inr (by simp; omega))]
    change setConstants m₀ base (start+6+i.val) = _
    rw [setConstants_preserves (Or.inr (by omega))]
    exact advised i

end DiagonalResidueRAM

end BorderVNP
end Computability
end OAI
