import OAI.Computability.VPVNP.RankCoordinateArgumentStage
import OAI.Computability.VPVNP.RankCoordinateSelectedMinor
import OAI.Computability.VPVNP.RankCoordinateTargetRead

/-! # Dynamic input ports of the selected Cramer minors

The numerator first selects original rows and columns. Its ordinary entry
reader shares a sum bank with the powered target reader. Installing the
four argument words reaches exactly the replacement index and the target
reader's three live fields through these nested selectors.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RankQuery.Stack.Coordinate.ArgumentStage

open RAMTape UniversalCountStack SliceArithmetic NativeReader
open RadicalCertificate.MonomialIndex

variable {K Base D H A T : Type} {p e : ℕ}

/-- Stack labels for a selected minor that can read both original matrix entries and entries of
the replacement row. -/
abbrev SelectedHost (K Base : Type) := SelectedMinor.Host K (Base ⊕ TargetRead.Work)

/-- Mount the powered reader as the right-hand direct scalar reader. -/
def targetMount : TargetRead.Work ↪ SelectedHost K Base :=
  ⟨ThreeBanks.right ∘ Sum.inr, ThreeBanks.right_injective.comp Sum.inr_injective⟩

/-- Place the three live target arguments inside the numerator reader's stack bank. -/
def selectedSlot : Fin 3 ↪ SelectedHost K Base := TargetRead.slot.trans targetMount

variable [DecidableEq K]

/-- Initialize the selected-minor reader with pivot stacks, the original-entry reader, and the
powered-target reader. -/
noncomputable def selectedRaw (w v n m : ℕ) (c : Vector p e) (pivot : Stacks K)
    (base : Stacks Base) (d : PairCall.Inputs) (constants : Bool → List Bool) : Stacks (SelectedHost K Base) :=
  SelectedMinor.initial w v n m c pivot (Sum.elim base (TargetRead.bank w d constants))

/-- Updating the target inside the selected-minor workspace preserves the
two pivot banks and the ordinary scalar reader at every stack. -/
theorem selected_after (w v n m : ℕ) (c : Vector p e) (pivot : Stacks K)
    (base : Stacks Base) (d : PairCall.Inputs) (constants : Bool → List Bool) (source scale mark : ℕ) :
    installStacks selectedSlot (selectedRaw w v n m c pivot base d constants) (TargetRead.words w source scale mark) =
      selectedRaw w v n m c pivot base (TargetRead.setDynamic d source scale mark) constants := by
  change installStacks (targetMount ∘ TargetRead.slot) _ _ = _
  rw [target_bank_after targetMount w d constants source scale mark _ rfl]
  apply installStacks_frame targetMount.injective
  · intro _
    rfl
  · rintro (i | j | k | l) h
    · rfl
    · rfl
    · rfl
    · exact (h l rfl).elim

/-- Each template destination is already a binary address word, so the
clearing stage has the same height bound as the four incoming values. -/
theorem selected_destination_length (w v n m r : ℕ) (c : Vector p e)
    (host : RootInit.RootHost D (Num (SelectedHost K Base)) ↪ H)
    (den : Stacks D) (pivot : Stacks K) (base : Stacks Base) (d : PairCall.Inputs)
    (constants : Bool → List Bool) (old : ℕ) (work : Stacks H)
    (hhost : ∀ i, work (host i) = RootInit.template c r w v den
      (Replacement.workBank w (digits w old) (Submatrix.workBank [] [] (selectedRaw w v n m c pivot base d constants))) i)
    (f : Field) : (work (destination host selectedSlot f)).length = w := by
  change (work (host (RootInit.readerPort (.inr (numSlot selectedSlot f))))).length = w
  rw [hhost]
  rcases f with ⟨⟩ | j
  · exact length_digits w old
  · fin_cases j <;> exact length_digits w _

/-- The final root host, after all four physical writes, is the canonical
template for the selected minor at the live replacement row and monomial. -/
theorem selected_host_after (w v n m r : ℕ) (c : Vector p e)
    (host : RootInit.RootHost D (Num (SelectedHost K Base)) ↪ H)
    (den : Stacks D) (pivot : Stacks K) (base : Stacks Base) (d : PairCall.Inputs)
    (constants : Bool → List Bool) (old replace source scale mark : ℕ) (work : Stacks H)
    (hhost : ∀ i, work (host i) = RootInit.template c r w v den
      (Replacement.workBank w (digits w old) (Submatrix.workBank [] [] (selectedRaw w v n m c pivot base d constants))) i)
    (i : RootInit.RootHost D (Num (SelectedHost K Base))) :
    installStacks (destination host selectedSlot) work
      (Sum.elim (fun _ : Unit ↦ digits w replace) (TargetRead.words w source scale mark)) (host i) =
      RootInit.template c r w v den (Replacement.workBank w (digits w replace) (Submatrix.workBank [] []
        (selectedRaw w v n m c pivot base (TargetRead.setDynamic d source scale mark) constants))) i := by
  rw [host_after c r w v host selectedSlot den _ _ _ _ work hhost i, selected_after]

/-- A runtime argument transport in the full selected minor. Its output
describes both the enclosing work bank and the canonical paired root. -/
theorem selected_machine_bounded [DecidableEq A] [DecidableEq H]
    (w v n m r cap : ℕ) (c : Vector p e) (host : RootInit.RootHost D (Num (SelectedHost K Base)) ↪ H)
    (src : Field → Bus A H) (scratch : H)
    (den : Stacks D) (pivot : Stacks K) (base : Stacks Base) (d : PairCall.Inputs)
    (constants : Bool → List Bool) (old replace source scale mark : ℕ)
    (label current next result : List Bool) (advice : Stacks A) (work : Stacks H)
    (apart : ∀ f g, src f ≠ workPort (destination host selectedSlot g))
    (hs : ∀ f, src f ≠ workPort scratch) (hd : ∀ f, destination host selectedSlot f ≠ scratch)
    (empty : work scratch = [])
    (live : ∀ f, state label current next result advice work (src f) =
      Sum.elim (fun _ : Unit ↦ digits w replace) (TargetRead.words w source scale mark) f)
    (hhost : ∀ i, work (host i) = RootInit.template c r w v den
      (Replacement.workBank w (digits w old) (Submatrix.workBank [] [] (selectedRaw w v n m c pivot base d constants))) i)
    (room : ∀ k, (state label current next result advice work k).length ≤ cap) :
    ∃ ticks ≤ clock w, ∃ out : Stacks H, out scratch = [] ∧
      (∀ i, out (host i) = RootInit.template c r w v den (Replacement.workBank w (digits w replace)
        (Submatrix.workBank [] [] (selectedRaw w v n m c pivot base (TargetRead.setDynamic d source scale mark) constants))) i) ∧
      (machine host selectedSlot src scratch).BoundedRun (cap+clock w) ticks
        (state label current next result advice work) (state label current next result advice out) := by
  let words := Sum.elim (fun _ : Unit ↦ digits w replace) (TargetRead.words w source scale mark)
  have small (f : Field) : (words f).length ≤ w := by
    rcases f with ⟨⟩ | j
    · exact (length_digits w replace).le
    · fin_cases j <;> exact (length_digits w _).le
  obtain ⟨ticks, bound, run⟩ := machine_bounded host selectedSlot src scratch w cap label current next result
    advice work words apart hs hd empty live small
    (fun f => (selected_destination_length w v n m r c host den pivot base d constants old work hhost f).le) room
  exact ⟨ticks, bound, _, (installStacks_outside work words hd).trans empty,
    selected_host_after w v n m r c host den pivot base d constants old replace source scale mark work hhost, run⟩

variable [Fact p.Prime]

/-- The two updated root inputs meet their exact readiness predicates. On the
direct-reader sum, the base reader is ready and the powered reader has its
specified monomial, scale, and mark. -/
theorem selected_root_ready (w v n m r : ℕ) (c : Vector p e) (hr : r < 2^w)
    {denReady : Stacks D → Prop} {baseReady : Stacks Base → Prop} (den : Stacks D) (hden : denReady den)
    (pivot : Stacks K) (base : Stacks Base) (hbase : baseReady base)
    (d : PairCall.Inputs) (replace source scale mark : ℕ) :
    let dyn := TargetRead.setDynamic d source scale mark
    let raw := selectedRaw w v n m c pivot base dyn (TargetRead.literal c v)
    let directReady (s : Stacks (Base ⊕ TargetRead.Work)) :=
      baseReady (s ∘ Sum.inl) ∧ TargetRead.Ready c w v dyn (s ∘ Sum.inr)
    let num := Replacement.workBank w (digits w replace) (Submatrix.workBank [] [] raw)
    GramEngine.Ready w v r r c denReady (GramEngine.initial w v r r c den) ∧
    GramEngine.Ready w v r r c (Replacement.Ready w replace (Submatrix.Ready (SelectedMinor.Ready w v n m c pivot directReady)))
      (GramEngine.initial w v r r c num) := by
  apply root_ready c r w v hr den hden
  apply SelectedMinor.initial_ready
  exact ⟨hbase, rfl⟩

end RankQuery.Stack.Coordinate.ArgumentStage

end VPVNP
end Computability
end OAI
