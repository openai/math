import OAI.Computability.BorderVNP.GeometryAdvicePrepareFrame

/-! # Reading the packed geometry header and gathering the input wires

The native gather dereferences the addresses following the gate records.
Its only writes are the constants and the query bits at the valuation base.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace GeometryAdvicePrepare

open VPVNP VPVNP.BurstRAM VPVNP.BooleanTranscript RoutingISA DiagonalResidueRAM

variable {w u k : ℕ}

private theorem constants_outside (m : Memory w) {base a : ℕ} (h : a<base ∨ base+2 ≤ a) :
    setConstants m base a = m a := by
  simp [setConstants,Function.update_of_ne (by omega : a ≠ base+1),Function.update_of_ne (by omega : a ≠ base)]

/-- Memory obtained by setting the two constant cells and gathering the public input. -/
def queryMemory (m : Memory w) (base : ℕ) (x : Fin u → Bool) : Memory w :=
  putBits (setConstants m base) (base+2) (List.ofFn x)

/-- Gathered cells realize the query and both constants, including an empty query. -/
theorem queryMemory_loaded (m : Memory w) (base : ℕ) (x : Fin u → Bool) :
    queryLoaded (queryMemory m base x) base x := by
  refine ⟨fun b => ?_,fun i => ?_⟩
  · rw [queryMemory, putBits_outside _ _ _ _ (.inl (by cases b <;> simp))]
    cases b <;> simp [setConstants,wordBit]
    rfl
  · simpa [queryMemory] using putBits_get (setConstants m base) (base+2) (List.ofFn x) ⟨i.val, by simp⟩

/-- The writes leave all cells outside the constant/query interval untouched. -/
theorem queryMemory_outside (m : Memory w) (base : ℕ) (x : Fin u → Bool) (a : ℕ)
    (h : a<base ∨ base+2+u ≤ a) : queryMemory m base x a = m a := by
  rw [queryMemory, putBits_outside _ _ _ _ (by simp; omega)]
  exact constants_outside _ (by omega)

/-- The six header probes and indirect input gathers preserve all gate records and the
output-reference suffix. This contract gives the complete post-gather memory. -/
theorem headerGather_runs (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
    (s : Bank w) (m : Memory w) (base start : ℕ) (src : Fin u → ℕ)
    (c : Circuit (Fin u ⊕ Fin 0) k) (x : Fin u → Bool)
    (hp : s 48 = word w start) (hone : s 63 = 1)
    (hv : gateBase base u 0 + k ≤ start) (hf : start+(6+3*k+u) < 2^w)
    (srcFit : ∀ i, src i < 2^w) (srcQuery : ∀ i, src i < base ∨ base+2+u ≤ src i)
    (hsrc : ∀ i, m (src i) = wordBit w (x i))
    (hwords : Words m start (payload w base start c src)) :
    ∃ z, Exact pub mac (.seq loadHeader gather) s m [] (12+(11+(7*u+1))) z (queryMemory m base x) ∧
      (frame base (start+6) c).loaded z := by
  let d := frame base (start+6) c
  have hbase : base+2+u ≤ start := by unfold gateBase at hv; omega
  obtain ⟨head,_,whereAt⟩ := payload_parts hwords
  obtain ⟨q,rh,hload⟩ := loadHeader_runs pub mac s m start d hp hone (by omega) head
  let e := effect false q m gatherSetup
  let m₁ := setConstants m base
  obtain ⟨hst,hc,hi,hip,hm,htr⟩ := gather_setup_effect d q m hload (by change base+1 < _; omega)
  have rs : Exact pub mac gatherSetup q m [] 11 e.bank m₁ := by
    have eqm : (effect false q m gatherSetup).mem = m₁ := hm
    exact ⟨e.trace,by simpa only [eqm,e] using effect_runs pub mac false q m gatherSetup (by decide),htr⟩
  let xs := pairs src x
  have hxs : xs.length = u := by simp [xs,pairs]
  have hb : xs.map Prod.snd = List.ofFn x := by simp [xs,pairs,List.map_ofFn,Function.comp_def]
  have sources : sourcesAt m₁ (start+6+3*k) xs := by
    apply sourcesAt_of_words
    · intro i
      have lt : i.val < u := by simpa [xs,pairs] using i.isLt
      rw [show m₁ (start+6+3*k+i.val) = m _ from constants_outside _ (.inr (by omega))]
      simpa [xs,pairs,List.map_ofFn] using whereAt ⟨i.val,lt⟩
    · intro t ht
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp ht
      have hsep := srcQuery i
      exact ⟨srcFit i, (constants_outside m (by omega : src i < base ∨ base+2 ≤ src i)).trans (hsrc i)⟩
  obtain ⟨z,rl,hz⟩ := gather_loop pub mac d e.bank m₁ (base+2) (start+6+3*k) 0 xs hst hc hi hip
    (by simpa [d,frame] using hxs) (by change u < _; omega) sources
    (by rw [hxs]; omega) (by rw [hxs]; omega)
    (fun t ht => by obtain ⟨i,rfl⟩ := List.mem_ofFn.mp ht; have hh := srcQuery i; rw [hxs]; dsimp; omega)
  rw [hb,hxs] at rl
  exact ⟨z,rh.seq (rs.seq rl),hz.1⟩

end GeometryAdvicePrepare

end BorderVNP
end Computability
end OAI
