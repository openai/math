import OAI.Computability.BorderVNP.PackedHistoryReservedExecute
import OAI.Computability.BorderVNP.PackedHistoryGeometryBranch

/-! # Actual pin-to-geometry entry at a fixed circuit reservation -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit

open VPVNP BurstRAM RoutingISA TeamContraction ProcessorSlots JointHeader GeometryAdvice GeometryFrameEncoding
open VerifierNetwork RoutingISA.Evaluator

variable {reserve o b w : ℕ}

/-- Every actual substituted pin return runs the explicitly supplied geometry
table on the copied public broadcast. -/
theorem pin_geometry_table_runs {d teams tallyDim : ℕ} {L : Pins.Layout}
    (t : Table (Fin reserve ⊕ Fin 0) o b)
    (P : Pins.ProcessorFields L) (f : BroadcastFrame) (A : AdviceLayout) (rp : ReferencePacket w d)
    (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8) (bank : Bank w) (m : Memory w)
    (word : Fin reserve → Bool) (declarations : List Bool) (tally extra : ℕ) (claims : Fin teams → Fin tallyDim → ℕ)
    (post : ProfileOperands P f A rp pub (padded (evaluation (List.ofFn word++declarations) tally claims) extra) m)
    (D : Packing.Directory.Layout) (head free team : ℕ) (boot : Stripe) (bootBits : List Bool)
    (strings : Fin D.entries → Fin D.description → Bool) (fresh off ell : ℕ) (old : Fin 81 → Word w) :
    let ok := GeometryOutput.validBit t (Sum.elim word Fin.elim0) = true
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
        (GeometryAdviceRate.ticks t.size reserve o b w) (nativeTableWords t word) es after result) := by
  intro ok alloc ci cf ch width loops
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
  have run := checked_profile_table_runs t P f A rp pub mac (pins g).val.2.1 (pins g).val.2.2
    word declarations tally extra claims copied D head free team boot bootBits strings fresh off ell old alloc
  exact ⟨h.1,h.2.1,run⟩

/-- Read the explicitly supplied table through the complete native pin and
geometry path, with its actual private choices and lower-memory image. -/
theorem profile_paths_table {d teams tallyDim : ℕ} {L : Pins.Layout}
    (t : Table (Fin reserve ⊕ Fin 0) o b)
    (P : Pins.ProcessorFields L) (f : BroadcastFrame) (A : AdviceLayout) (rp : ReferencePacket w d)
    (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8) (bank : Bank w) (m : Memory w)
    (word : Fin reserve → Bool) (declarations : List Bool) (tally extra : ℕ) (claims : Fin teams → Fin tallyDim → ℕ)
    (post : ProfileOperands P f A rp pub (padded (evaluation (List.ofFn word++declarations) tally claims) extra) m)
    (D : Packing.Directory.Layout) (head free team : ℕ) (boot : Stripe) (bootBits : List Bool)
    (strings : Fin D.entries → Fin D.description → Bool) (fresh off ell : ℕ) (old : Fin 81 → Word w) :
    let ok := GeometryOutput.validBit t (Sum.elim word Fin.elim0)=true
    ProfileAllocation P f rp pub D head free team boot bootBits strings t fresh off ell old →
    PinClear L 0 P.header.length → PinClear L (pub 0).val 112 →
    PinClear L f.dst (padded (evaluation (List.ofFn word++declarations) tally claims) extra).length →
    L.width ≤ L.count → Pins.LoopFits w L →
    ProfilePaths pinGeometry L.guessWidth pub mac bank m ok
      ((pinSetup.slots+17*L.count+1)+GeometryAdviceRate.ticks t.size reserve o b w)
      (Allocation.dest fresh reserve t.size o b) (nativeTableWords t word)
      (fun g after => ∀ i < fresh, after i = Pins.preparedMemory L (Pins.extendGuess g) m L.count i) := by
  intro ok alloc ci cf ch width loops
  obtain ⟨pins,pinMem,run₀⟩ := pin_geometry_table_runs t P f A rp pub mac bank m word declarations tally extra
    claims post D head free team boot bootBits strings fresh off ell old alloc ci cf ch width loops
  obtain ⟨accept,paths⟩ := pinGeometry_paths pins ok fresh (Allocation.dest fresh reserve t.size o b)
    (pinSetup.slots+17*L.count+1) (GeometryAdviceRate.ticks t.size reserve o b w)
    (nativeTableWords t word) run₀
  refine ⟨accept,fun valid => ?_,fun z g zg => ?_⟩
  · obtain ⟨E,hE⟩ := paths valid
    exact ⟨E,fun g => ⟨(hE g).1,(hE g).2.1,(hE g).2.2.1,(hE g).2.2.2.1⟩⟩
  · obtain ⟨E,hE⟩ := paths (accept.mp ⟨z⟩)
    obtain ⟨b,rfl⟩ := E.surjective z
    obtain rfl : b = g := List.ofFn_injective ((hE b).1.symm.trans zg)
    exact fun i hi => ((hE b).2.2.2.2 i hi).trans (congrFun (pinMem b) i)

variable {σ S V : Type*} [Fintype σ] [Fintype S] [Fintype V] {active reserve o b w : ℕ}

/-- The fixed gate ceiling determines the physical word bases even when the
packet circuit contains those absolute addresses. Acceptance, original rows,
sign, choices and untouched memory follow through the real pin and geometry
entry point on exactly the original branch. -/
theorem profile_paths_reserved {d teams tallyDim : ℕ} {L : Pins.Layout}
    (history : Frame (σ ⊕ S) (V ⊕ Unit)) (order : S ≃ Fin active) (fit : active ≤ reserve)
    (emit : Frame ((σ ⊕ Fin reserve) ⊕ V) (Fin o × Fin b)) (x : σ → Bool)
    (ceiling : ℕ) (gateRoom : (geometryTable history order fit emit x).size ≤ ceiling)
    (P : Pins.ProcessorFields L) (f : BroadcastFrame) (A : AdviceLayout) (rp : ReferencePacket w d)
    (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8) (bank : Bank w) (m : Memory w)
    (word : Fin reserve → Bool) (declarations : List Bool) (tally extra : ℕ) (claims : Fin teams → Fin tallyDim → ℕ)
    (post : ProfileOperands P f A rp pub (padded (evaluation (List.ofFn word++declarations) tally claims) extra) m)
    (D : Packing.Directory.Layout) (head free team : ℕ) (boot : Stripe) (bootBits : List Bool)
    (strings : Fin D.entries → Fin D.description → Bool) (fresh off ell : ℕ) (old : Fin 81 → Word w) :
    let t := reservedGeometryTable history order fit emit x ceiling
    let ok := validProfile order fit (fun g => history.eval (Sum.elim x g) (.inr ()) = true) word
    ProfileAllocation P f rp pub D head free team boot bootBits strings t fresh off ell old →
    PinClear L 0 P.header.length → PinClear L (pub 0).val 112 →
    PinClear L f.dst (padded (evaluation (List.ofFn word++declarations) tally claims) extra).length →
    L.width ≤ L.count → Pins.LoopFits w L →
    ProfilePaths pinGeometry L.guessWidth pub mac bank m ok
      ((pinSetup.slots+17*L.count+1)+GeometryAdviceRate.ticks ceiling reserve o b w)
      (Allocation.dest fresh reserve ceiling o b) (emittedWords history order fit emit x word)
      (fun g after => ∀ i < fresh, after i = Pins.preparedMemory L (Pins.extendGuess g) m L.count i) := by
  intro t ok alloc ci cf ch width loops
  have size : t.size=ceiling := (geometryTable history order fit emit x).reserve_size ceiling gateRoom
  obtain ⟨guard,words⟩ := reserved_semantics history order fit emit x ceiling word
  change (GeometryOutput.validBit t (Sum.elim word Fin.elim0)=true ↔ ok) at guard
  change nativeTableWords t word=emittedWords history order fit emit x word at words
  simpa only [size,guard,words] using profile_paths_table t P f A rp pub mac bank m word declarations tally extra claims
    post D head free team boot bootBits strings fresh off ell old alloc ci cf ch width loops

end PackedHistoryCircuit

end BorderVNP
end Computability
end OAI
