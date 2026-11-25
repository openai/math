import OAI.Computability.BorderVNP.TeamTapeSortingFields
import OAI.Computability.VPVNP.RAMTapeSuccessorRecord

/-! # Named-stack canonicality checks on the two boundary records

Before running the existing complete sort/scan, the processor copies each five-word
boundary payload to the physical comparator's two operand stacks. Its equality verifier
then checks every word against the canonical record format, retaining the verdict on the
same flag stack inspected by the terminal pass. Every copy and scan is timed on arbitrary
input bits, including malformed tags and nonzero padding.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamTapeSorting

open VPVNP BurstRAM RAMTape RAMBoundary SuccessorFields

/-- Physical named ports for the boundary guards and the sorting/terminal routine. -/
abbrev Port := Sorter.Port ⊕ SitePost.Port

/-- Decidable equality on the two sets of named ports. -/
@[implicit_reducible] def portDecidableEq : DecidableEq Port :=
  @instDecidableEqSum Sorter.Port SitePost.Port inferInstance inferInstance

attribute [local instance] portDecidableEq

private def guardPort : Sorter.Port → Port
  | .valid => .inr SitePost.flagPort
  | k => .inl k

private theorem guardPort_inj : Function.Injective guardPort := by
  intro i j he
  cases i <;> cases j <;> simp_all [guardPort]

/-- Copy one five-word field to both operand stacks, then use the fixed raw equality verifier. -/
def checkBoundary (src : SitePost.Port) : FiniteRoutine Port :=
  (prependCopy (.inr src) (.inl .left) (.inl .tmp)).followedBy
    ((prependCopy (.inr src) (.inl .right) (.inl .tmp)).followedBy (Sorter.verify.onPorts guardPort))

/-- Stage the unary word width and check both physical boundary fields. -/
def guard : FiniteRoutine Port :=
  (prependCopy (.inr SitePost.widthPort) (.inl .width) (.inl .tmp)).followedBy
    ((checkBoundary SitePost.previousPort).followedBy (checkBoundary SitePost.sentPort))

/-- Complete named-stack checker. The post-pass consumes the canonicality flags. -/
def program : FiniteRoutine Port :=
  guard.followedBy (SitePost.complete.onPorts Sum.inr)

/-- At entry the original data occupies the post-pass ports and all auxiliary ports are empty. -/
def inputBank (p : Stacks SitePost.Port) : Stacks Port := Sum.elim (fun _ => []) p

private def bank (p : Stacks SitePost.Port) (w : ℕ) (left right : List Bool) : Stacks Port
  | .inr k => p k
  | .inl .left => left
  | .inl .right => right
  | .inl .width => List.replicate w true
  | .inl _ => []

private theorem checkBoundary_runs {w : ℕ} (src : SitePost.Port) (a : RawSlot w)
    (p : Stacks SitePost.Port) (ha : p src = Boundary.recordBytes a) :
    (checkBoundary src).Runs (100*w+22) (bank p w [] [])
      (bank (Function.update p SitePost.flagPort (Sorter.verifyOK a a :: p SitePost.flagPort)) w [] []) := by
  let bs := Boundary.recordBytes a
  have copyLeft : (prependCopy (.inr src) (.inl .left) (.inl .tmp)).Runs (25*w+2)
      (bank p w [] []) (bank p w bs []) := by
    have h := prependCopy_runs (K := Port) (.inr src) (.inl .left) (.inl .tmp)
      (by simp) (by simp) (by decide) (bank p w [] []) rfl
    rw [show bank p w [] [] (.inr src) = bs from ha, Boundary.length_recordBytes] at h
    convert h using 1
    · omega
    · funext k
      rcases k with k | k
      · cases k <;> simp [bank, Function.update]
      · simp [bank, Function.update]
  have copyRight : (prependCopy (.inr src) (.inl .right) (.inl .tmp)).Runs (25*w+2)
      (bank p w bs []) (bank p w bs bs) := by
    have h := prependCopy_runs (.inr src : Port) (.inl .right) (.inl .tmp)
      (by simp) (by simp) (by decide) (bank p w bs []) rfl
    rw [show bank p w bs [] (.inr src) = bs from ha, Boundary.length_recordBytes] at h
    convert h using 1
    · omega
    · funext k
      rcases k with k | k
      · cases k <;> simp [bank, Function.update]
      · simp [bank, Function.update]
  let z : Sorter.Bank := ⟨[],[],[],[],[],[],[],[],p SitePost.flagPort⟩
  let q := Function.update p SitePost.flagPort (Sorter.verifyOK a a :: p SitePost.flagPort)
  have verify : (Sorter.verify.onPorts guardPort).Runs (50*w+18) (bank p w bs bs) (bank q w [] []) := by
    apply Sorter.verify.runs_onPorts_framed guardPort_inj (Sorter.verify_runs a a z)
    · intro k; cases k <;> first | rfl | simp [bank, guardPort, Sorter.ready, Sorter.Bank.stacks, bs, z]
    · intro k; cases k <;> rfl
    · intro k hk
      rcases k with k | k
      · cases k <;> first | rfl | exact (hk .left rfl).elim | exact (hk .right rfl).elim
      · exact Function.update_of_ne (fun e => hk .valid (congrArg Sum.inr e.symm)) ..
  simpa only [checkBoundary, show 25*w+2+(25*w+2+(50*w+18)) = 100*w+22 by omega]
    using copyLeft.followedBy (copyRight.followedBy verify)

private theorem initWidth_runs (p : Stacks SitePost.Port) (w : ℕ)
    (hw : p SitePost.widthPort = List.replicate w true) :
    (prependCopy (.inr SitePost.widthPort) (.inl .width) (.inl .tmp)).Runs (5*w+2)
      (inputBank p) (bank p w [] []) := by
  have h := prependCopy_runs (.inr SitePost.widthPort : Port) (.inl .width) (.inl .tmp)
    (by decide) (by decide) (by decide) (inputBank p) rfl
  rw [show inputBank p (.inr SitePost.widthPort) = List.replicate w true from hw, List.length_replicate] at h
  convert h using 1
  funext k
  rcases k with k | k
  · cases k <;> simp [bank, inputBank, Function.update]
  · simp [bank, inputBank, Function.update]

private theorem replaceFlags {h d w : ℕ} (v : Word d) (prev sent : RawSlot w)
    (x : SortReplay.State h w) (tail flags : List Bool) :
    Function.update (SitePost.prestate v prev sent x tail) SitePost.flagPort flags =
      SitePost.prestate v prev sent (x.1, flags) tail := by
  simp only [SitePost.prestate_eq_raw]
  funext p
  rcases p with (c | (((r|e)|o)|u)) | extra
  · cases c <;> rfl
  · cases r <;> rfl
  · cases e <;> rfl
  · cases o <;> rfl
  · cases u; rfl
  · cases extra <;> rfl

/-- Both checks read the actual retained edge records and return before sorting,
contributing a verdict bit each. No well-formedness premise is needed. -/
theorem guard_runs {h d w : ℕ} (v : Word d) (prev sent : RawSlot w)
    (x : SortReplay.State h w) (tail : List Bool) :
    let flags := Sorter.verifyOK sent sent :: Sorter.verifyOK prev prev :: x.2
    ∃ out, guard.Runs (205*w+46) (inputBank (SitePost.prestate v prev sent x tail)) out ∧
      out ∘ Sum.inr = SitePost.prestate v prev sent (x.1, flags) tail := by
  let p := SitePost.prestate v prev sent x tail
  let q := Function.update p SitePost.flagPort (Sorter.verifyOK prev prev :: p SitePost.flagPort)
  let z := Function.update q SitePost.flagPort (Sorter.verifyOK sent sent :: q SitePost.flagPort)
  have a := initWidth_runs p w rfl
  have b := checkBoundary_runs SitePost.previousPort prev p rfl
  have c := checkBoundary_runs SitePost.sentPort sent q rfl
  refine ⟨bank z w [] [], ?_, ?_⟩
  · simpa only [guard, show 5*w+2+(100*w+22+(100*w+22)) = 205*w+46 by omega]
      using a.followedBy (b.followedBy c)
  · change Function.update q SitePost.flagPort _ = _
    simp only [q, Function.update_self, Function.update_idem]
    exact replaceFlags ..

end TeamTapeSorting

end BorderVNP
end Computability
end OAI
