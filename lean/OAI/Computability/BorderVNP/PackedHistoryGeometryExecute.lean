import OAI.Computability.BorderVNP.PackedHistoryGeometryInput
import OAI.Computability.BorderVNP.PackedHistoryGeometryTable

/-! # Executing the guarded history and its public row emitter on the real geometry table

The program's active inputs are the profile words delivered by the common header. A returning
trace produces the emitter's actual rows. Every unassigned profile suffix bit and the recursive
validity flag are checked by the gate interpreter.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit

open VPVNP BurstRAM RoutingISA TeamContraction ProcessorSlots JointHeader GeometryAdvice GeometryFrameEncoding
open VerifierNetwork DiagonalResidueRAM

/-- A successful geometry trace, with its address readback, full clock, untouched lower
memory, and unique sequence of physical choices. -/
structure GeometryReturn {w o : ℕ} (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
    (bank : Bank w) (m : Memory w) (fresh dest clock : ℕ) (output : Fin o → ℕ)
    (trace : List (TeamRAM.Event w)) (after : Bank w) (result : Memory w) : Prop where
  /-- Full fixed native table execution. -/
  run : Runs pub mac reconstruct bank m trace after result
  /-- True ordinary ticks, including stripe delivery and output-word packing. -/
  time : traceCost trace ≤ clock
  /-- Each output address holds the integer value of the selected frame bits. -/
  words : ∀ i, readings result (dest+i.val) = output i
  /-- All earlier allocated words survive. -/
  preserved : ∀ a < fresh, result a = m a
  /-- Ordinary one-tick events with no local choices and total sign positive. -/
  effects : traceCost trace = trace.length ∧ signedWeight trace = 1 ∧ trace.flatMap TeamRAM.Event.choices = []
  /-- The interpreter's chronological trace and its per-event choice lists are unique. -/
  unique : ∀ bits fs, TeamRAM.execute (reconstruct.program.fetch pub mac) ⟨0,bank⟩ m bits = some fs ↔
    fs = trace ∧ bits = trace.map TeamRAM.Event.choices

variable {σ S V : Type*} [Fintype σ] [Fintype S] [Fintype V]
variable {active reserve o b w : ℕ}

/-- The shared geometry input table, selected once before any profile word is received. -/
noncomputable def geometryTable (history : Frame (σ ⊕ S) (V ⊕ Unit)) (order : S ≃ Fin active)
    (fit : active ≤ reserve) (emit : Frame ((σ ⊕ Fin reserve) ⊕ V) (Fin o × Fin b)) (x : σ → Bool) :=
  GeometryFrameEncoding.compile (exportRows history order fit emit) (profilePins x)

/-- Word array produced by the original row emitter on the true terminal state and all the
physical public pins. -/
noncomputable def emittedWords (history : Frame (σ ⊕ S) (V ⊕ Unit)) (order : S ≃ Fin active)
    (fit : active ≤ reserve) (emit : Frame ((σ ⊕ Fin reserve) ⊕ V) (Fin o × Fin b)) (x : σ → Bool)
    (word : Fin reserve → Bool) (i : Fin o) : ℕ :=
  ParseBatchSort.value (fun j => emit.eval (Sum.elim (Sum.elim x word)
    (fun v => history.eval (Sum.elim x (readProfile order fit word)) (.inl v))) (i,j))

set_option maxRecDepth 4000 in
/-- Actual public execution iff the active history is valid and all reserved tail words are
zero. The caller's inputs are exactly the boot result and the jointly assigned literal from
its chosen reader site. No populated circuit valuation or decoded table is supplied. -/
theorem checked_geometry_runs {d teams tallyDim : ℕ} {L : Pins.Layout}
    (history : Frame (σ ⊕ S) (V ⊕ Unit)) (order : S ≃ Fin active) (fit : active ≤ reserve)
    (emit : Frame ((σ ⊕ Fin reserve) ⊕ V) (Fin o × Fin b)) (x : σ → Bool)
    (P : Pins.ProcessorFields L) (f : BroadcastFrame) (A : AdviceLayout) (rp : ReferencePacket w d)
    (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8) (bank : Bank w) (m : Memory w)
    (word : Fin reserve → Bool) (declarations : List Bool) (tally extra : ℕ) (claims : Fin teams → Fin tallyDim → ℕ)
    (post : ProfileOperands P f A rp pub (padded (evaluation (List.ofFn word++declarations) tally claims) extra) m)
    (D : Packing.Directory.Layout) (head free team : ℕ) (boot : Stripe) (bootBits : List Bool)
    (strings : Fin D.entries → Fin D.description → Bool) (fresh off ell : ℕ) (old : Fin 81 → Word w)
    (froom : f.Fits w (pub 0).val) :
    let t := geometryTable history order fit emit x
    let st := Allocation.stripe fresh reserve t.size o b off ell
    let packed := Allocation.packed fresh reserve t.size o b w
    let bits := serialized (packet (w := w) fresh packed t (profileSources f))
    let fs := Allocation.fields old fresh reserve t.size o b off ell
    let ok := validProfile order fit (fun g => history.eval (Sum.elim x g) (.inr ()) = true) word
    JointImage D head free boot st bootBits bits strings team P → rp.extension = fs →
    (pub 0).val+112 ≤ f.dst → f.dst+1+reserve ≤ fresh → b ≤ w → 0 < ell →
    off+ell ≤ f.literal → GeometryOutput.packetCount reserve t.size o b*w ≤ f.processors*ell →
    Allocation.stop fresh reserve t.size o b w < 2^w →
      ((∃ es guesses, TeamRAM.execute (reconstruct.program.fetch pub mac) ⟨0,bank⟩ m guesses = some es) ↔ ok) ∧
      (ok → ∃ es after result, GeometryReturn pub mac bank m fresh (Allocation.dest fresh reserve t.size o b)
        (GeometryAdviceRate.ticks t.size reserve o b w) (emittedWords history order fit emit x word) es after result) := by
  intro t st packed bits fs ok im ext hp hs bw hw lit cap room
  let l := Allocation.output fresh reserve t.size o b w
  let src := profileSources (reserve := reserve) f
  let g := exportRows history order fit emit
  let pins := profilePins (reserve := reserve) x
  let val := Sum.elim x word
  obtain ⟨space,place,input⟩ := profile_geometry_input P f A rp pub m word declarations tally extra claims post
    D head free team boot bootBits strings t fresh off ell old froom im ext hp hs bw hw lit cap room
  have result := frame_execute pub mac bank m f st L P l fresh packed src g pins word froom space place input
  rw [show (fun i => (pins i).elim (Sum.elim word Fin.elim0) id) = val from profilePins_eval x word] at result
  have guard := exportRows_valid history order fit emit x word
  refine ⟨result.1.trans guard,fun valid => ?_⟩
  have hv : g.eval val (.inr ()) = true := guard.mpr valid
  obtain ⟨es,after,out,run,time,words,uniq⟩ := result.2 hv
  have passing : GeometryOutput.validBit t (Sum.elim word Fin.elim0) = true :=
    (GeometryOutput.compiled_valid g pins _).trans ((profilePins_eval x word).symm ▸ hv)
  obtain ⟨ds,z,other,run',_,choices,image⟩ := reconstruct_runs pub mac bank m f st L P l fresh packed src t word
    froom space place input passing
  obtain rfl := ((uniq _ ds).mp run'.execute).1
  obtain ⟨_,rfl,rfl⟩ := run.eq_of_shared_events run' (tail := []) (tail' := []) rfl
  have plain := plain_return reconstruct (by decide) run
  refine ⟨_,_,_,run,time,?_,?_,⟨plain.1,plain.2,choices⟩,uniq⟩
  · intro i
    have eq : (fun j => g.eval val (.inl (i,j))) = _ := funext (fun j => exportRows_bit history order fit emit x word (i,j))
    change (out (l.dest+i.val)).val = _
    rw [words i,eq]
    exact word_val w _ ((ParseBatchSort.value_lt _).trans_le (Nat.pow_le_pow_right (by decide) bw))
  · intro addr h
    have below : addr < l.temp ∧ addr < l.dest ∧ addr < packed ∧ addr < st.dense := by
      dsimp [l,packed,st,Allocation.output,Allocation.packed,Allocation.dense,Allocation.dest,Allocation.temp,Allocation.stripe]; omega
    exact (image.outside addr (Or.inl h) (Or.inl below.2.2.1) (Or.inl below.1) (Or.inl below.2.1)).trans
      (st.image_outside m (Or.inl below.2.2.2))

end PackedHistoryCircuit

end BorderVNP
end Computability
end OAI
