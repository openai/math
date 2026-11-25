import OAI.Computability.BorderVNP.FiniteEvaluatorCubeJointChoices
import OAI.Computability.BorderVNP.DiagonalNativeSequence

/-! # Equivalence between complete owned-group return tuples and private assignments

The shared row words are fixed first. The actual choices of every physical
team then determine exactly one routed assignment, and each assignment is
executed by precisely one tuple of returning native histories within the real
per-team tick bounds.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FiniteEvaluator.CubeTriple

open BorderVNP.Cube BorderVNP.Cube.Physical BorderVNP.Cube.TeamRows BorderVNP.Cube.Scatter
open VPVNP.BurstRAM RoutingISA RoutingISA.Owned DiagonalResidueRAM
open private owned_native from OAI.Computability.BorderVNP.DiagonalNativeSignedTags
open scoped Classical

variable {w n d blocks b h K s : ℕ} {Team : Type*} [DecidableEq Team]
variable {axis : Fin (n+1)} {select : Packet n d blocks → Selector n K h} {owner : Fin d → Team}

variable (code : Team ↪ ℕ) (layout : Team → TeamRowPrepare.Layout)
variable (packet single power base stop actual claimed : Team → ℕ)
variable (rows : Sym2 (Fin d) → Fin (n+1) → ℕ) (pub : Team → Arg → Word w)
variable (mac : Team → TeamOpcode.Macros w 8) (initialRegs : Team → Bank w) (initial : Team → Memory w)
variable (observed : Assignment.Choices b s select axis owner)

local notation "encoding" => nativeWordsEquiv b s select axis owner

/-- Assignment fiber for the observed common crossing suffixes. -/
abbrev Fiber := {f : Assignment.Choices b s select axis owner // (encoding f).1=(encoding observed).1}

/-- A complete tuple of actual native returns, retaining each team's
chronology, final bank and final memory. -/
abbrev Histories (n b h K s : ℕ) := (t : Team) →
  Evaluator.Returns (ownedGroups n b h K s) (pub t) (mac t) (initialRegs t) (initial t)

/-- The authenticated length-only setup and the actual common rows give the
full field-diagonal branch dictionary at the owned-group stage. Each private
assignment has its exact native tape, final lookup data and measured clock. -/
theorem assignment_dictionary
    (setup : ∀ t, PhysicalSetup (l := teamLayout layout code d t) (Assignment.bankData observed (packet t) (single t))
      (code ∘ owner) (power t) (base t) (stop t) (actual t) (claimed t) rows (pub t) (initial t)) :
    ∃ E : Fiber observed ≃ Histories pub mac initialRegs initial n b h K s, ∀ f t,
      let L := teamLayout layout code d t
      let a := Assignment.bankData f.val (packet t) (single t)
      let out := E f t
      TraceOK out.val.1 (((encoding f.val).2 t).val) out.val.1.length ∧
        traceCost out.val.1 ≤ 4+(ticks L (wordOwner (code ∘ owner)) (physicalCostAt L blocks b h K s axis)+11) ∧
        Readback (l := L) a (code ∘ owner) (power t) (base t) (stop t) (initial t) out.val.2.2 := by
  let Y := Histories pub mac initialRegs initial n b h K s
  have one (f : Fiber observed) (t : Team) :
      ∃ y : Evaluator.Returns (ownedGroups n b h K s) (pub t) (mac t) (initialRegs t) (initial t),
        let L := teamLayout layout code d t
        TraceOK y.val.1 (((encoding f.val).2 t).val) y.val.1.length ∧
          traceCost y.val.1 ≤ 4+(ticks L (wordOwner (code ∘ owner)) (physicalCostAt L blocks b h K s axis)+11) ∧
          Readback (l := L) (Assignment.bankData f.val (packet t) (single t)) (code ∘ owner) (power t) (base t) (stop t) (initial t) y.val.2.2 := by
    let L := teamLayout layout code d t
    have P := setup_assignment (l := L) code (packet t) (single t) (power t) (base t) (stop t) (actual t)
      (claimed t) rows (pub t) (initial t) (setup t) f.property
    obtain ⟨es,u,mu,run,ok,cost,read⟩ := native_run P (mac t) (initialRegs t)
    have tape := nativeWordsEquiv_teamRows code f.val t L rfl rfl (packet t) (single t)
    exact ⟨⟨(es,u,mu),run⟩,tape.symm ▸ ok,cost,read⟩
  choose send property using one
  have inj : Function.Injective send := by
    intro f g e
    apply Subtype.ext
    apply (encoding).injective
    apply Prod.ext (f.property.trans g.property.symm)
    funext t
    apply Subtype.ext
    have same := congrArg (fun z : Y => (z t).val.1.flatMap TeamRAM.Event.choices) e
    exact (property f t).1.2.1.symm.trans (same.trans (property g t).1.2.1)
  have onto : Function.Surjective send := by
    intro y
    obtain ⟨f,⟨common,scripts⟩,_⟩ := unique_assignment code layout packet single power base stop actual claimed rows pub mac
      initialRegs initial (fun t => (y t).val.1) (fun t => (y t).val.2.1) (fun t => (y t).val.2.2) observed setup (fun t => (y t).property)
    let a : Fiber observed := ⟨f,common⟩
    refine ⟨a,funext fun t => ?_⟩
    have word := (property a t).1.2.1.trans (scripts t).1
    obtain ⟨es,reg,mem⟩ := unique_returns ((ownedGroups n b h K s).program_tag_native (owned_native ..))
      (send a t).property (y t).property (congrArg (· ++ []) word)
    exact Subtype.ext (Prod.ext es (Prod.ext reg mem))
  exact ⟨Equiv.ofBijective send ⟨inj,onto⟩,property⟩

end FiniteEvaluator.CubeTriple

end BorderVNP
end Computability
end OAI
