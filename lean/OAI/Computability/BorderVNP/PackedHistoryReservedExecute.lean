import OAI.Computability.BorderVNP.GeometryTableReservation
import OAI.Computability.BorderVNP.PackedHistoryPinGeometry

/-! # Executing a concretely supplied table at its reserved geometry addresses

The profile directory stores the supplied AND/NOT program. The public decoder
reads its actual guard and all its output references. This formulation accepts
a table padded to a fixed gate ceiling without recomputing any addresses.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit

open VPVNP BurstRAM RoutingISA TeamContraction ProcessorSlots JointHeader GeometryAdvice GeometryFrameEncoding
open VerifierNetwork DiagonalResidueRAM

variable {reserve o b w : ℕ}

/-- The values of all the gate references actually gathered after executing a
native multi-output table on its public profile. -/
def nativeTableWords (t : Table (Fin reserve ⊕ Fin 0) o b) (word : Fin reserve → Bool) (i : Fin o) : ℕ :=
  let x := Sum.elim word Fin.elim0
  ParseBatchSort.value fun j => (t.bit i j).read id x (t.program.run x)

set_option maxRecDepth 4000 in
/-- Read the true jointly installed table, return exactly its rows, and preserve
all lower input banks. Rejected profiles have no returning path. -/
theorem checked_profile_table_runs {d teams tallyDim : ℕ} {L : Pins.Layout}
    (t : Table (Fin reserve ⊕ Fin 0) o b) (P : Pins.ProcessorFields L)
    (f : BroadcastFrame) (A : AdviceLayout) (rp : ReferencePacket w d)
    (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8) (bank : Bank w) (m : Memory w)
    (word : Fin reserve → Bool) (declarations : List Bool) (tally extra : ℕ) (claims : Fin teams → Fin tallyDim → ℕ)
    (post : ProfileOperands P f A rp pub (padded (evaluation (List.ofFn word++declarations) tally claims) extra) m)
    (D : Packing.Directory.Layout) (head free team : ℕ) (boot : Stripe) (bootBits : List Bool)
    (strings : Fin D.entries → Fin D.description → Bool) (fresh off ell : ℕ) (old : Fin 81 → Word w)
    (alloc : ProfileAllocation P f rp pub D head free team boot bootBits strings t fresh off ell old) :
    let ok := GeometryOutput.validBit t (Sum.elim word Fin.elim0)=true
    ((∃ es guesses, TeamRAM.execute (reconstruct.program.fetch pub mac) ⟨0,bank⟩ m guesses = some es) ↔ ok) ∧
      (ok → ∃ es after result, GeometryReturn pub mac bank m fresh (Allocation.dest fresh reserve t.size o b)
        (GeometryAdviceRate.ticks t.size reserve o b w) (nativeTableWords t word) es after result) := by
  let st := Allocation.stripe fresh reserve t.size o b off ell
  let l := Allocation.output fresh reserve t.size o b w
  let packed := Allocation.packed fresh reserve t.size o b w
  let src := profileSources (reserve := reserve) f
  obtain ⟨space,place,input⟩ := profile_geometry_input P f A rp pub m word declarations tally extra claims post
    D head free team boot bootBits strings t fresh off ell old alloc.broadcast alloc.image alloc.extension
    alloc.headerAfter alloc.profileEnd alloc.width alloc.positive alloc.literal alloc.capacity alloc.stop
  have valid := reconstruct_runs pub mac bank m f st L P l fresh packed src t word alloc.broadcast space place input
  have bad := @reconstruct_invalid _ _ _ _ pub mac bank m f st L P l fresh packed src t word alloc.broadcast space place input
  intro ok
  constructor
  · constructor
    · rintro ⟨es,bs,h⟩
      by_contra invalid
      have no : GeometryOutput.validBit t (Sum.elim word Fin.elim0)=false := Bool.eq_false_iff.mpr invalid
      obtain ⟨⟨z,mz,r⟩,_⟩ := (Code.execute_iff_runs (by decide : reconstruct.withoutAccept=true)).mp h
      exact bad no r
    · intro good
      obtain ⟨es,z,mz,run,_,_,_⟩ := valid good
      exact ⟨es,_,run.execute⟩
  · intro good
    obtain ⟨es,z,mz,run,time,choices,image⟩ := valid good
    have plain := plain_return reconstruct (by decide) run
    refine ⟨es,z,mz,run,?_,?_,?_,⟨plain.1,plain.2,choices⟩,?_⟩
    · simpa only [cost,GeometryOutput.stagedTicks,GeometryOutput.packetCount,
        GeometryAdviceRate.ticks,GeometryAdviceRate.packetWords,Nat.add_assoc] using time
    · intro i
      exact (congrArg Fin.val (image.words i)).trans (word_val w _ ((ParseBatchSort.value_lt _).trans_le
        (Nat.pow_le_pow_right (by decide) alloc.width)))
    · intro a below
      have low : a<l.temp ∧ a<l.dest ∧ a<packed ∧ a<st.dense := by
        dsimp [l,packed,st,Allocation.output,Allocation.packed,Allocation.dense,Allocation.dest,Allocation.temp,Allocation.stripe]
        omega
      exact (image.outside a (Or.inl below) (Or.inl low.2.2.1) (Or.inl low.1) (Or.inl low.2.1)).trans
        (st.image_outside m (Or.inl low.2.2.2))
    · intro bs fs
      rw [Code.execute_iff_runs (by decide : reconstruct.withoutAccept=true)]
      constructor
      · rintro ⟨⟨_,_,other⟩,order⟩
        obtain ⟨rfl,_,_⟩ := unique_returns (c:=reconstruct) (by decide) run other
          (tail:=fs.flatMap TeamRAM.Event.choices) (tail':=[]) (by rw [choices]; simp)
        exact ⟨rfl,order.symm⟩
      · rintro ⟨rfl,rfl⟩
        exact ⟨⟨z,mz,run⟩,rfl⟩

variable {σ S V : Type*} [Fintype σ] [Fintype S] [Fintype V] {active : ℕ}
    (hist : Frame (σ ⊕ S) (V ⊕ Unit)) (ord : S ≃ Fin active) (fit : active≤reserve)
    (emit : Frame ((σ ⊕ Fin reserve) ⊕ V) (Fin o × Fin b)) (x : σ → Bool)

/-- Fixed-address table used by the physical profile evaluator. -/
noncomputable def reservedGeometryTable (ceiling : ℕ) := (geometryTable hist ord fit emit x).reserve ceiling

/-- The original lowered table has the recursive guard and the emitter's
actual numerical outputs on the given broadcast. -/
theorem geometry_semantics (word : Fin reserve → Bool) :
    let t := geometryTable hist ord fit emit x
    (GeometryOutput.validBit t (Sum.elim word Fin.elim0)=true ↔ validProfile ord fit
      (fun g => hist.eval (Sum.elim x g) (.inr ())=true) word) ∧
      nativeTableWords t word=emittedWords hist ord fit emit x word := by
  intro t
  constructor
  · change GeometryOutput.validBit (GeometryFrameEncoding.compile _ _) _=true ↔ _
    rw [GeometryOutput.compiled_valid,profilePins_eval]
    exact exportRows_valid hist ord fit emit x word
  · funext i
    unfold nativeTableWords
    apply congrArg ParseBatchSort.value
    funext j
    exact (bit_eval (exportRows hist ord fit emit) (profilePins x) i j (Sum.elim word Fin.elim0)).trans
      ((profilePins_eval x word).symm ▸ exportRows_bit hist ord fit emit x word (i,j))

/-- The reserved table retains the actual geometry guard and the true original
emitter words for every possible physical broadcast. -/
theorem reserved_semantics (ceiling : ℕ) (word : Fin reserve → Bool) :
    let t := reservedGeometryTable hist ord fit emit x ceiling
    (GeometryOutput.validBit t (Sum.elim word Fin.elim0)=true ↔ validProfile ord fit
      (fun g => hist.eval (Sum.elim x g) (.inr ())=true) word) ∧
      nativeTableWords t word=emittedWords hist ord fit emit x word := by
  intro t
  obtain ⟨guard,rows⟩ := geometry_semantics hist ord fit emit x word
  constructor
  · rw [show GeometryOutput.validBit t (Sum.elim word Fin.elim0)=_ from (geometryTable hist ord fit emit x).reserve_valid ..]
    exact guard
  · apply Eq.trans _ rows
    funext i
    unfold nativeTableWords
    apply congrArg ParseBatchSort.value
    exact funext fun j => (geometryTable hist ord fit emit x).reserve_bit ceiling _ i j

end PackedHistoryCircuit

end BorderVNP
end Computability
end OAI
