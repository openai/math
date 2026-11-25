import OAI.Computability.BorderVNP.PackedHistoryGeometryPaths

/-! # Native profile acceptance and output for each actual outer pack history

The bounded-state verifier checks the original dependent history index on its reachable
subsystem. The copied word is a bijective code for that index. For this word the native pin
and geometry prefix has exactly one path per substituted-index guess, and its outputs are
computed from a representation of the original terminal pack.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit

open VPVNP BurstRAM RoutingISA RoutingISA.Evaluator TeamContraction ProcessorSlots JointHeader GeometryAdvice
open VerifierNetwork DiagonalResidueRAM Packing Shortening.Adaptive

/-- Accepted chronological paths and their precise physical geometry outputs. -/
structure ProfilePaths {w o : ℕ} (body : Code) (k : ℕ) (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
    (bank : Bank w) (mem : Memory w) (ok : Prop) (time dest : ℕ) (words : Fin o → ℕ)
    (resident : (Fin k → Bool) → Memory w → Prop := fun _ _ => True) : Prop where
  /-- All malformed words reject, and all valid words have a returning execution. -/
  passes : Nonempty (Returns body pub mac bank mem) ↔ ok
  /-- For a valid word all histories are indexed by their actual fresh private pin bits. -/
  outputs : ok → ∃ E : (Fin k → Bool) ≃ Returns body pub mac bank mem, ∀ g,
    (E g).val.1.flatMap TeamRAM.Event.choices = List.ofFn g ∧ traceCost (E g).val.1 ≤ time ∧
    signedWeight (E g).val.1 = 1 ∧ ∀ i, readings (E g).val.2.2 (dest+i.val) = words i

  /-- The actual terminal memory has the specified resident data for the very same private choice. -/
  memory (z : Returns body pub mac bank mem) (g : Fin k → Bool) :
    z.val.1.flatMap TeamRAM.Event.choices = List.ofFn g → resident g z.val.2.2

variable {σ S V : Type*} [Fintype σ] [Fintype S] [Fintype V] {active reserve o b w : ℕ}

/-- Apply the concrete pin preparation, true joint-input reads and fixed native geometry
table to the actual copied profile word. -/
theorem profile_paths {d teams tallyDim : ℕ} {L : Pins.Layout}
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
    ProfilePaths pinGeometry L.guessWidth pub mac bank m ok
      ((pinSetup.slots+17*L.count+1)+GeometryAdviceRate.ticks t.size reserve o b w)
      (Allocation.dest fresh reserve t.size o b) (emittedWords history order fit emit x word)
      (fun g after => ∀ i < fresh, after i = Pins.preparedMemory L (Pins.extendGuess g) m L.count i) := by
  intro t ok alloc ci cf ch width loops
  obtain ⟨pins,pinMem,run⟩ := pin_geometry_runs history order fit emit x P f A rp pub mac bank m word declarations tally extra
    claims post D head free team boot bootBits strings fresh off ell old alloc ci cf ch width loops
  obtain ⟨accept,paths⟩ := pinGeometry_paths pins ok fresh (Allocation.dest fresh reserve t.size o b)
    (pinSetup.slots+17*L.count+1) (GeometryAdviceRate.ticks t.size reserve o b w)
    (emittedWords history order fit emit x word) run
  refine ⟨accept,fun valid => ?_,fun z g zg => ?_⟩
  · obtain ⟨E,hE⟩ := paths valid
    exact ⟨E,fun g => ⟨(hE g).1,(hE g).2.1,(hE g).2.2.1,(hE g).2.2.2.1⟩⟩
  · obtain ⟨E,hE⟩ := paths (accept.mp ⟨z⟩)
    obtain ⟨b,rfl⟩ := E.surjective z
    obtain rfl : b = g := List.ofFn_injective ((hE b).1.symm.trans zg)
    exact fun i hi => ((hE b).2.2.2.2 i hi).trans (congrFun (pinMem b) i)

variable {K T : ℕ} {A : ℕ → Type*} {W G : ℕ → Type} [∀ j, Fintype (W j)] [∀ j, Fintype (G j)]

/-- Genuine physical pack histories are exactly the public words on which the native table
returns. Its written rows are evaluated on a state representing that history's true pack
and integral routes. The correspondence separates choices even when two final packs agree. -/
theorem bounded_history_paths (epoch : ∀ j, (Fin K → A j) → ProfileSum (A (j+1)))
    (good : ∀ j, A j → Prop) (closed : Capacity.Closed (outerSystem T epoch) good)
    (leaf : {a // good 0 a}) (C : Codec (Capacity.restrict (outerSystem T epoch) good closed) G)
    (rep : Represents A W) (steps : Steps K T W G) (correct : LocalCorrect C (fun j z a => rep j z a.val) steps)
    (bottom : Frame σ (W 0)) (x : σ → Bool) (base : rep 0 (bottom.eval x) leaf.val)
    (width : ℕ → ℕ) (order : ∀ j, G j ≃ Fin (width j)) (fit : broadcastWidth K width T ≤ reserve)
    (emit : Frame ((σ ⊕ Fin reserve) ⊕ W T) (Fin o × Fin b))
    (body : Code) (k : ℕ) (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8) (bank : Bank w) (mem : Memory w)
    (time dest : ℕ) (word : Fin reserve → Bool) {resident : (Fin k → Bool) → Memory w → Prop} :
    let f := compile steps T le_rfl (repeatLeaf K bottom T)
    let ord := broadcastOrder K width order T
    let ok := validProfile ord fit (fun g => f.eval (Sum.elim x g) (.inr ()) = true) word
    let checked := acceptedOuterBounded epoch good closed leaf C rep steps correct bottom x base
    let E := acceptedBroadcastOfEquiv ord fit _ checked
    ProfilePaths body k pub mac bank mem ok time dest (emittedWords f ord fit emit x word) resident →
    (Nonempty (Returns body pub mac bank mem) ↔ ∃! q, (E q).val = word) ∧
    ∀ q, (E q).val = word → ∃ z : W T → Bool, rep T z ((packHistory leaf.val epoch T).term q) ∧
      ∃ R : (Fin k → Bool) ≃ Returns body pub mac bank mem, ∀ g,
        (R g).val.1.flatMap TeamRAM.Event.choices = List.ofFn g ∧ traceCost (R g).val.1 ≤ time ∧
        signedWeight (R g).val.1 = 1 ∧ ∀ i : Fin o, readings (R g).val.2.2 (dest+i.val) =
          ParseBatchSort.value (fun j => emit.eval (Sum.elim (Sum.elim x word) z) (i,j)) := by
  intro f ord ok checked E paths
  have iffWord : ok ↔ ∃! q, (E q).val = word := by
    constructor
    · intro h
      let q := E.symm ⟨word,h⟩
      have eq := congrArg Subtype.val (E.apply_symm_apply ⟨word,h⟩)
      exact ⟨q,eq,fun r hr => E.injective (Subtype.ext (hr.trans eq.symm))⟩
    · rintro ⟨q,h,_⟩
      dsimp only [ok]; rw [← h]; exact (E q).property
  refine ⟨paths.passes.trans iffWord,fun q eq => ?_⟩
  let y := readProfile ord fit word
  let z := output steps T le_rfl (repeatLeaf K bottom T) x y
  have rd : y = (checked q).val := by
    change readProfile ord fit word = _
    rw [← eq]
    exact readProfile_of_broadcast ord fit _ checked q
  have state : rep T z ((packHistory leaf.val epoch T).term q) := by
    dsimp only [z]; rw [rd]; exact acceptedOuterBounded_state epoch good closed leaf C rep steps correct bottom x base q
  have pass : ok := by dsimp only [ok]; rw [← eq]; exact (E q).property
  exact ⟨z,state,paths.outputs pass⟩

end PackedHistoryCircuit

end BorderVNP
end Computability
end OAI
