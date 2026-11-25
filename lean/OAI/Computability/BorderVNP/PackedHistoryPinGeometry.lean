import OAI.Computability.BorderVNP.PackedHistoryGeometryExecute

/-! # Every substituted pin choice reaches the geometry table with its real copied profile

The native evaluation branch performs its finite pin guess before interpreting the history.
All its returns are indexed by the actual guessed bits. The geometry trace following any such
return is unique if its public history is valid and is absent otherwise.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit

open VPVNP BurstRAM RoutingISA TeamContraction ProcessorSlots JointHeader GeometryAdvice GeometryFrameEncoding VerifierNetwork

/-- The setup words and pointer bounds for the history circuit's actual physical installation.
These depend on the public circuit and fixed allocation, independently of the trial profile. -/
structure ProfileAllocation {reserve o b w d : ℕ} {L : Pins.Layout} (P : Pins.ProcessorFields L)
    (f : BroadcastFrame) (rp : ReferencePacket w d) (pub : Arg → Word w)
    (D : Packing.Directory.Layout) (head free team : ℕ) (boot : Stripe) (bootBits : List Bool)
    (strings : Fin D.entries → Fin D.description → Bool) (t : Table (Fin reserve ⊕ Fin 0) o b)
    (fresh off ell : ℕ) (old : Fin 81 → Word w) : Prop where
  /-- The input processors hold the actual serialized geometry packet and private site strings. -/
  image : JointImage D head free boot (Allocation.stripe fresh reserve t.size o b off ell) bootBits
    (serialized (packet (w := w) fresh (Allocation.packed fresh reserve t.size o b w) t (profileSources f))) strings team P
  /-- The chosen reference packet carries the physical geometry operands. -/
  extension : rp.extension = Allocation.fields old fresh reserve t.size o b off ell
  /-- Logical broadcast and processor input ranges fit the machine word. -/
  broadcast : f.Fits w (pub 0).val
  /-- The copied header follows all ordinary and extended frame fields. -/
  headerAfter : (pub 0).val+112 ≤ f.dst
  /-- The copied profile finishes before the five geometry working regions. -/
  profileEnd : f.dst+1+reserve ≤ fresh
  /-- An emitted word fits. -/
  width : b ≤ w
  /-- The deinterleaver uses positive width. -/
  positive : 0 < ell
  /-- The physical stripe fits each literal. -/
  literal : off+ell ≤ f.literal
  /-- The serialized geometry packet fits all stripes. -/
  capacity : GeometryOutput.packetCount reserve t.size o b*w ≤ f.processors*ell
  /-- The last allocated geometry word and its sentinel fit. -/
  stop : Allocation.stop fresh reserve t.size o b w < 2^w

variable {σ S V : Type*} [Fintype σ] [Fintype S] [Fintype V] {active reserve o b w : ℕ}

/-- All the native index-guess returns, with the exact geometry acceptance criterion,
complete trace and public words after each one. -/
theorem pin_geometry_runs {d teams tallyDim : ℕ} {L : Pins.Layout}
    (history : Frame (σ ⊕ S) (V ⊕ Unit)) (order : S ≃ Fin active) (fit : active ≤ reserve)
    (emit : Frame ((σ ⊕ Fin reserve) ⊕ V) (Fin o × Fin b)) (x : σ → Bool)
    (P : Pins.ProcessorFields L) (f : BroadcastFrame) (A : AdviceLayout) (rp : ReferencePacket w d)
    (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8) (bank : Bank w) (m : Memory w)
    (word : Fin reserve → Bool) (declarations : List Bool) (tally extra : ℕ) (claims : Fin teams → Fin tallyDim → ℕ)
    (post : ProfileOperands P f A rp pub (padded (evaluation (List.ofFn word++declarations) tally claims) extra) m)
    (D : Packing.Directory.Layout) (head free team : ℕ) (boot : Stripe) (bootBits : List Bool)
    (strings : Fin D.entries → Fin D.description → Bool) (fresh off ell : ℕ) (old : Fin 81 → Word w) :
    let t := geometryTable history order fit emit x
    let ok := validProfile order fit (fun g => history.eval (Sum.elim x g) (.inr ()) = true) word
    ProfileAllocation P f rp pub D head free team boot bootBits strings t fresh off ell old →
    PinClear L 0 P.header.length → PinClear L (pub 0).val 112 →
    PinClear L f.dst (padded (evaluation (List.ofFn word++declarations) tally claims) extra).length →
    L.width ≤ L.count → Pins.LoopFits w L →
    ∃ pins : (Fin L.guessWidth → Bool) ≃ Pins.Return pub mac bank m,
    (∀ g, (pins g).val.2.2 = Pins.preparedMemory L (Pins.extendGuess g) m L.count) ∧ ∀ g,
      let h := pins g
      h.val.1.flatMap TeamRAM.Event.choices = List.ofFn g ∧ traceCost h.val.1 ≤ pinSetup.slots + 17*L.count+1 ∧
      ((∃ es choices, TeamRAM.execute (reconstruct.program.fetch pub mac) ⟨0,h.val.2.1⟩ h.val.2.2 choices = some es) ↔ ok) ∧
      (ok → ∃ es after result, GeometryReturn pub mac h.val.2.1 h.val.2.2 fresh (Allocation.dest fresh reserve t.size o b)
        (GeometryAdviceRate.ticks t.size reserve o b w) (emittedWords history order fit emit x word) es after result) := by
  intro t ok alloc ci cf ch width loops
  obtain ⟨dims,lit,stride⟩ := packet_dimensions post.frame
  have ff := alloc.broadcast
  have fs := ff.frame
  have fe := ff.out
  have fn := ff.input
  have nt := ff.three
  have hp := ff.procs
  have hstr : L.stride < 2^w := by rw [stride]; have := Nat.le_mul_of_pos_left f.stride hp; omega
  have ht : 0 < L.teams := by
    have he := post.frame.pins.teams.symm.trans post.frame.broadcast.2.1; omega
  have hc : L.count < 2^w := by
    change L.processors*L.literal < 2^w
    have lb : f.literal ≤ f.stride := by unfold BroadcastFrame.stride; omega
    rw [dims,lit]; exact (Nat.mul_le_mul_left _ lb).trans_lt (by omega)
  obtain ⟨pins,eff⟩ := Pins.preparePins_exact L pub mac m bank post.frame.pins (by change (pub 0).val+24 < _; omega)
    ht hstr hc width loops
  refine ⟨pins,fun g => (eff g).2.2.2.2,fun g => ?_⟩
  have h := eff g
  have copied := post.prepared (Pins.extendGuess g) ci cf ch
  rw [← h.2.2.2.2] at copied
  have run := checked_geometry_runs history order fit emit x P f A rp pub mac (pins g).val.2.1 (pins g).val.2.2
    word declarations tally extra claims copied D head free team boot bootBits strings fresh off ell old alloc.broadcast
    alloc.image alloc.extension alloc.headerAfter alloc.profileEnd alloc.width alloc.positive alloc.literal alloc.capacity alloc.stop
  exact ⟨h.1,h.2.1,run⟩

end PackedHistoryCircuit

end BorderVNP
end Computability
end OAI
