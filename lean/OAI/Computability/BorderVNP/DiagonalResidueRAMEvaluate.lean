import OAI.Computability.BorderVNP.DiagonalResidueRAMLoad
import OAI.Computability.BorderVNP.RoutingISAInverse

/-!
# Native evaluation of an advised bit circuit on a residue-entry query

The RAM fixes its code independently of every field, length and advice word.
Correctness includes arbitrary shared gate references and all gate-free outputs.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace DiagonalResidueRAM

open VPVNP VPVNP.BurstRAM VPVNP.BooleanTranscript RoutingISA

variable {w u v k : ℕ} (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8)

/-- Six native operand words for the selected bit verifier. -/
def frame (base advice : ℕ) (c : Circuit (Fin u ⊕ Fin v) k) : Frame :=
  ⟨k,v,advice,base,address base c.output,u⟩

/-- Memory supplies the compiled gate records packed in consecutive words. -/
def hasAdvice (m : Memory w) (base advice : ℕ) (c : Circuit (Fin u ⊕ Fin v) k) : Prop :=
  let data := adviceData (w := w) (List.ofFn (rows base c.program))
  ∀ i : Fin data.length, m (advice+i.val) = data[i.val]

/-- Each of the six operands and the compiled advice fit, so the gate reader
reaches the designated value after the two complete loops. Its count of ordinary
instructions is exact for each private tape, independently of its bits. -/
theorem evaluate_stores_preserves (base advice : ℕ) (c : Circuit (Fin u ⊕ Fin v) k)
    (x : Fin u → Bool) (y : Fin v → Bool) (s : Bank w) (m : Memory w)
    (hf : (frame base advice c).fits w) (hs : (frame base advice c).loaded s)
    (hx : queryLoaded m base x) (ha : hasAdvice m base advice c) :
    ∃ z mz, Exact pub macros evaluate s m (List.ofFn y) (6*v+14*k+11) z mz ∧
      z 42 = wordBit w (c.eval (Sum.elim x y)) ∧ z 38 = 1 ∧
      Knows base x y (c.program.run (Sum.elim x y)) mz ∧
      ∀ a, a < base+2+u ∨ gateBase base u v+k ≤ a → mz a = m a := by
  let d := frame base advice c
  let bs := List.ofFn y
  let rs := List.ofFn (rows base c.program)
  let start := base + 2 + u
  let dest := gateBase base u v
  have hspace : dest + k ≤ advice := hf.1
  have hlimit : advice + 3*k < 2^w := hf.2
  have hword : 1 < 2^w := by dsimp only [dest,gateBase] at hspace; omega
  let e := effect false s m setup
  obtain ⟨hstable,hcursor,hcounter,hmem,htrace⟩ := setup_effect d s m hs
  have hsetup : Exact pub macros setup s m [] 6 e.bank m :=
    ⟨e.trace, by simpa only [hmem] using setup_runs pub macros s m, htrace⟩
  obtain ⟨t,hrguess,ht,hc⟩ := guess_loop pub macros d bs e.bank m 0 start hstable hcounter hcursor
    (by simp [d,frame,bs]) (by dsimp only [d,frame,dest,gateBase] at *; omega)
    (by simp [bs,start]; dsimp only [dest,gateBase] at hspace; omega)
  let mt := putBits m start bs
  let t₁ := Function.update t (41 : Reg) (t 39)
  let t₂ := Function.update t₁ (42 : Reg) (t₁ 34)
  have cp₁ : Exact pub macros (.copy 41 39) t mt [] 1 t₁ mt :=
    ⟨_, Runs.localStep mt rfl rfl, by simp [TraceOK,tick]⟩
  have cp₂ : Exact pub macros (.copy 42 34) t₁ mt [] 1 t₂ mt :=
    ⟨_, Runs.localStep mt rfl rfl, by simp [TraceOK,tick]⟩
  have ht₂ : d.stable t₂ := by
    rcases ht with ⟨⟨h₀,h₁,h₂,h₃,h₄,h₅⟩,h₆,h₇⟩
    simp [Frame.stable, Frame.loaded, t₂, t₁, Function.update,h₀,h₁,h₂,h₃,h₄,h₅,h₆,h₇]
  have hi₂ : t₂ 41 = word w 0 := by simp [t₂,t₁,Function.update,ht.2.2]
  have hc₂ : t₂ 40 = word w dest := by simpa [t₂,t₁,Function.update,dest,gateBase,start,bs] using hc
  have hp₂ : t₂ 42 = word w advice := by simpa [t₂,t₁,Function.update] using (show t 34 = word w advice from ht.1.2.2.1)
  have hrows : loadedRows mt advice rs := by
    apply loadedRows_congr _ _ (fun j hj => putBits_outside m start bs j (Or.inr (by
      simp [bs,start]; dsimp only [dest,gateBase] at hspace; omega)))
    apply loadedRows_of_packed m advice rs ha
    intro r hr
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hr
    have h := rows_addresses base c.program i
    change _ < dest+k ∧ _ < dest+k at h
    exact ⟨h.1.trans_le (by omega),h.2.trans_le (by omega)⟩
  obtain ⟨z,hgate,hz⟩ := gate_loop pub macros d rs t₂ mt 0 dest advice ht₂ hi₂ hc₂ hp₂
    (by simp [rs,d,frame]) (by dsimp only [d,frame]; omega) (by simpa [rs] using hspace)
    (by simpa [rs] using hlimit) hrows
  let mz := putRows mt dest rs
  let z' := Function.update z (42 : Reg) (mz (z 36).val)
  have hload : Exact pub macros (.load 42 36) z mz [] 1 z' mz :=
    ⟨_,Runs.load pub macros _ _ z mz,by simp [TraceOK]⟩
  have full := hsetup.seq (hrguess.seq (cp₁.seq (cp₂.seq (hgate.seq hload))))
  refine ⟨z',mz,?_,?_,?_,?_,?_⟩
  · convert full using 1 <;> simp [evaluate,Code.block,bs,rs]
    omega
  · have houtput := read_output hword (putBits_knows m base x y hx) c
    have haddr := address_lt base c.output
    have hreg : z 36 = word w (address base c.output) := hz.1.2.2.2.2.1
    rw [show z' 42 = mz (z 36).val by simp [z'], hreg, word_val _ _ (by change _ < dest+k at haddr; omega)]
    exact (congrFun (putRows_typed mt base c.program) _).trans houtput
  · simp [z',hz.2.1]
  · change Knows base x y _ (putRows mt (gateBase base u v) (List.ofFn (rows base c.program)))
    rw [putRows_typed]
    exact executeGates_correct hword (putBits_knows m base x y hx) c.program

  · intro a ha
    change putRows mt dest rs a = m a
    rw [putRows_outside mt dest rs a (by simp [dest,rs,gateBase] at *; omega)]
    exact putBits_outside m start bs a (by simp [start,bs,gateBase] at *; omega)

/-- Normal execution materializes every shared input and output wire, including
those read by a subsequent multi-output decoder. -/
theorem evaluate_stores (base advice : ℕ) (c : Circuit (Fin u ⊕ Fin v) k)
    (x : Fin u → Bool) (y : Fin v → Bool) (s : Bank w) (m : Memory w)
    (hf : (frame base advice c).fits w) (hs : (frame base advice c).loaded s)
    (hx : queryLoaded m base x) (ha : hasAdvice m base advice c) :
    ∃ z mz, Exact pub macros evaluate s m (List.ofFn y) (6*v+14*k+11) z mz ∧
      z 42 = wordBit w (c.eval (Sum.elim x y)) ∧ z 38 = 1 ∧
      Knows base x y (c.program.run (Sum.elim x y)) mz := by
  obtain ⟨z,mz,r,b,one,values,_⟩ := evaluate_stores_preserves pub macros base advice c x y s m hf hs hx ha
  exact ⟨z,mz,r,b,one,values⟩

/-- Normal evaluation returns the circuit's selected output in register 42. -/
theorem evaluate_checked (base advice : ℕ) (c : Circuit (Fin u ⊕ Fin v) k)
    (x : Fin u → Bool) (y : Fin v → Bool) (s : Bank w) (m : Memory w)
    (hf : (frame base advice c).fits w) (hs : (frame base advice c).loaded s)
    (hx : queryLoaded m base x) (ha : hasAdvice m base advice c) :
    ∃ z mz, Exact pub macros evaluate s m (List.ofFn y) (6*v+14*k+11) z mz ∧
      z 42 = wordBit w (c.eval (Sum.elim x y)) ∧ z 38 = 1 := by
  obtain ⟨z,mz,run,answer,one,_⟩ := evaluate_stores pub macros base advice c x y s m hf hs hx ha
  exact ⟨z,mz,run,answer,one⟩

/-- A verifier returning one passes the guard and the physical program accepts
after precisely the advertised number of ticks. -/
theorem reader_accepts (base advice : ℕ) (c : Circuit (Fin u ⊕ Fin v) k)
    (x : Fin u → Bool) (y : Fin v → Bool) (s : Bank w) (m : Memory w)
    (hf : (frame base advice c).fits w) (hs : (frame base advice c).loaded s)
    (hx : queryLoaded m base x) (ha : hasAdvice m base advice c) (hy : c.eval (Sum.elim x y) = true) :
    ∃ es, TeamRAM.execute (machine.fetch pub macros) ⟨0,s⟩ m (es.map TeamRAM.Event.choices) = some es ∧
      TraceOK es (List.ofFn y) (ticks k v) := by
  obtain ⟨z,mz,⟨es,run,htr⟩,hz,hone⟩ := evaluate_checked pub macros base advice c x y s m hf hs hx ha
  have accept : z 42 = z 38 := by rw [hz,hone,hy]; rfl
  have ok : Runs pub macros (.ifEq 42 38 .nop .reject) z mz [tick w,tick w] z mz :=
    .ifEq (by rw [ite_eq_left accept]; exact Runs.localStep mz rfl rfl)
  have whole : Runs pub macros reader s m (es++[tick w,tick w]) z mz := .seq run ok
  have finalTrace : TraceOK [tick w,tick w] [] 2 := by simp [TraceOK,tick]
  exact ⟨_,whole.execute,by simpa [ticks,Nat.add_assoc] using htr.append finalTrace⟩

end DiagonalResidueRAM

end BorderVNP
end Computability
end OAI
