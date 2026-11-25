import OAI.Computability.BorderVNP.FiniteEvaluatorCubeTripleNative
import OAI.Computability.BorderVNP.CubeTeamPrivateKeysPath
import OAI.Computability.BorderVNP.DiagonalNativeSignedTags

/-! # Unique physical assignment recovered from actual owned-group returns

With the shared selector and crossing streams fixed, all teams' genuine
chronological private words determine one assignment. Re-executing that
assignment gives precisely the observed histories, final register banks and
memories, hence the physical lookup inputs for its private demand and supply
bits. A team owning both ends of a cut still executes both directed rows.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FiniteEvaluator.CubeTriple

open BorderVNP.Cube BorderVNP.Cube.Physical BorderVNP.Cube.TeamRows BorderVNP.Cube.TeamRowSources
open BorderVNP.Cube.Padding.Banks BorderVNP.Cube.Scatter
open VPVNP.BurstRAM RoutingISA RoutingISA.Owned DiagonalResidueRAM
open private owned_native from OAI.Computability.BorderVNP.DiagonalNativeSignedTags
open scoped Classical

variable {w n d blocks b h K s : ℕ} {Team : Type*} [DecidableEq Team]
variable {axis : Fin (n+1)} {select : Packet n d blocks → Selector n K h} {owner : Fin d → Team}

/-- Changing private words keeps the returned public setup valid, including all
routed crossing suffixes and both incident views, provided the common rows agree. -/
theorem setup_assignment {l : TeamRowPrepare.Layout} {select : Packet n l.d blocks → Selector n K h}
    {owner : Fin l.d → Team} {f₀ f : Assignment.Choices b s select axis owner} (code : Team ↪ ℕ)
    (packet single power base stop actual claimed : ℕ) (rows : Sym2 (Fin l.d) → Fin (n+1) → ℕ)
    (pub : Arg → Word w) (initial : Memory w)
    (P : PhysicalSetup (l := l) (Assignment.bankData f₀ packet single) (code ∘ owner) power base stop actual claimed rows pub initial)
    (shared : ((nativeWordsEquiv b s select axis owner) f).1 = ((nativeWordsEquiv b s select axis owner) f₀).1) :
    PhysicalSetup (l := l) (Assignment.bankData f packet single) (code ∘ owner) power base stop actual claimed rows pub initial := by
  let A := Assignment.bankData f packet single
  have cross (a : Assignment.Choices b s select axis owner) (p : Symbols l.d) :
      (((nativeWordsEquiv b s select axis owner) a).1 p).val =
        commonCrossings b axis p select (Assignment.supplies a) (fun z => (Assignment.bankData a packet single).value z.1.val z.2) := by
    rw [nativeWordsEquiv_shared a p]
    exact congrArg (commonCrossings b axis p select (Assignment.supplies a))
      (funext (fun z => (SingleRowData.extendSlots_apply (fun k => Assignment.lookup a (.inl k)) z).symm))
  have seed : Seed A l power pub initial := ⟨P.seed.frame,P.seed.alphabet,P.seed.axis,P.seed.selectorCount,P.seed.loaded,P.seed.labels,P.seed.singles⟩
  have alloc : Allocation A l power base stop w := ⟨P.allocation.packets,P.allocation.singles,P.allocation.orderPackets,
    P.allocation.orderSingles,P.allocation.endFit,P.allocation.frame,P.allocation.header,P.allocation.declaration,
    P.allocation.owners,P.allocation.powers,P.allocation.views⟩
  refine ⟨seed,alloc,P.fits,P.fields,P.directory,P.owners,P.capacity,P.image,P.authentic,P.checker,P.labelsFit,
    P.packetFit,P.capFit,P.afterScratch,P.checkSafe,P.selectorWords,?_⟩
  intro p high own
  have equal := (cross f p).symm.trans ((congrArg (fun words : StrictCrossWords b s select axis => (words p).val) shared).trans (cross f₀ p))
  exact equal.symm ▸ P.crossingWords p high own

/-- Use all other public layout fields supplied by the team while fixing the
two shared dimensions required by its ownership enumeration. -/
def teamLayout (layout : Team → TeamRowPrepare.Layout) (code : Team ↪ ℕ) (d : ℕ) (t : Team) :=
  {layout t with d := d, teamID := code t}

variable (code : Team ↪ ℕ) (layout : Team → TeamRowPrepare.Layout)
variable (packet single power base stop actual claimed : Team → ℕ)
variable (rows : Sym2 (Fin d) → Fin (n+1) → ℕ) (pub : Team → Arg → Word w)
variable (mac : Team → TeamOpcode.Macros w 8) (initialRegs : Team → Bank w) (initial : Team → Memory w)
variable (events : Team → List (TeamRAM.Event w)) (lastRegs : Team → Bank w) (lastMem : Team → Memory w)

/-- For fixed observed shared words, every tuple of actual returning owned-group
histories realizes exactly one distributed private assignment. All of its lookup
operands and private endpoint words occur in the actually returned memories. -/
theorem unique_assignment (observed : Assignment.Choices b s select axis owner)
    (setup : ∀ t, PhysicalSetup (l := teamLayout layout code d t) (Assignment.bankData observed (packet t) (single t))
      (code ∘ owner) (power t) (base t) (stop t) (actual t) (claimed t) rows (pub t) (initial t))
    (runs : ∀ t, Runs (pub t) (mac t) (ownedGroups n b h K s) (initialRegs t) (initial t) (events t) (lastRegs t) (lastMem t)) :
    ∃! f : Assignment.Choices b s select axis owner,
      ((nativeWordsEquiv b s select axis owner) f).1 = ((nativeWordsEquiv b s select axis owner) observed).1 ∧
        ∀ t, ((((nativeWordsEquiv b s select axis owner) f).2 t).val = (events t).flatMap TeamRAM.Event.choices) ∧
          Readback (l := teamLayout layout code d t) (Assignment.bankData f (packet t) (single t))
            (code ∘ owner) (power t) (base t) (stop t) (initial t) (lastMem t) := by
  let e := nativeWordsEquiv b s select axis owner
  let script (t : Team) := (events t).flatMap TeamRAM.Event.choices
  let length (t : Team) := (teamPrivateKeys b s select axis owner t).length
  let choices : TeamPrivateWords b s select axis owner := fun t =>
    ⟨ChoiceTape.segment (ChoiceTape.extend (script t)) 0 (length t),by simp [ChoiceTape.segment,length]⟩
  let f := e.symm ((e observed).1,choices)
  have ef : e f=((e observed).1,choices) := e.apply_symm_apply _
  have common := congrArg Prod.fst ef
  have each (t : Team) : ((e f).2 t).val=script t ∧
      Readback (l := teamLayout layout code d t) (Assignment.bankData f (packet t) (single t)) (code ∘ owner)
        (power t) (base t) (stop t) (initial t) (lastMem t) := by
    let L := teamLayout layout code d t
    let A := Assignment.bankData f (packet t) (single t)
    have geometry := setup_assignment (l := L) code (packet t) (single t) (power t) (base t) (stop t) (actual t) (claimed t)
      rows (pub t) (initial t) (setup t) common
    obtain ⟨xs,u,mu,canon,bits,_,read⟩ := native_run geometry (mac t) (initialRegs t)
    have tape := nativeWordsEquiv_teamRows code f t L rfl rfl (packet t) (single t)
    have hit := congrArg (fun z : StrictCrossWords b s select axis × TeamPrivateWords b s select axis owner => (z.2 t).val) ef
    have spelled : xs.flatMap TeamRAM.Event.choices = (choices t).val := bits.2.1.trans (tape.symm.trans hit)
    obtain ⟨rest,extra,agree⟩ := ChoiceTape.compatible (script t) (length t)
    have same := (congrArg (· ++ rest) spelled).trans agree
    obtain ⟨equal,_,terminal⟩ := unique_returns ((ownedGroups n b h K s).program_tag_native (owned_native ..)) canon (runs t) same
    exact ⟨tape.trans (bits.2.1.symm.trans (congrArg (List.flatMap TeamRAM.Event.choices) equal)),terminal ▸ read⟩
  refine ⟨f,⟨common,each⟩,?_⟩
  intro other yes
  exact e.injective (Prod.ext (yes.1.trans common.symm) (funext fun t => Subtype.ext ((yes.2 t).1.trans (each t).1.symm)))

end FiniteEvaluator.CubeTriple

end BorderVNP
end Computability
end OAI
