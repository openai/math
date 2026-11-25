import OAI.Computability.BorderVNP.FiniteProcessorFrames
import OAI.Computability.BorderVNP.FiniteProcessorWeightContraction
import OAI.Computability.BorderVNP.TeamContractionPhysical

/-! # Reindexing the actual field processor leaves by adaptive native RAM paths -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FieldProcessor

open VPVNP RAMTape UniversalMachine TeamSite TeamContraction TeamSiteConsistency TeamSiteEvents
open TeamSiteTraversal TeamTapeHandoff Filter
open scoped BigOperators Classical
open private elapsed from OAI.Computability.BorderVNP.TeamContractionPhysical

variable {R teams t d link inner n p r k a e w m g : ℕ} {Q Γ : Type} [Fintype Q] {F : Type*} [Field F] [Fintype F]
variable (M : Setup teams w p r k a e) (lib : Fin a → Macro Q Γ m g) (weights : Returns Q Γ F m a)
variable (G : Wiring R teams t d link inner n (Wires.Edge teams r w e (w+1)))
variable (pin : Fin d → Bool) (ext : Exterior R teams link → Bool) (u : Fin (R+1))

/-- Source-side field value of the initialized, charged RAM. The source state
reconstructs each routine identifier before applying its returned field element. -/
noncomputable def nativeSum (fuel : ℕ) : F :=
  letI := Fintype.ofFinite M.Paths
  ∑ z : M.Paths, pathProduct M.program M.pub lib weights fuel M.start z.val

/-- Actual field leaves for passing, nonzero-signed rows at this physical layout. -/
def RowValues (fuel : ℕ) : Prop :=
  ∀ int j f, Reads (Wires.edgeEquiv int).1 M.first j f → ∀ es out,
    EndpointRow M.program M.pub M.lib M.block M.limit M.cap f es out →
    Writes (Wires.edgeEquiv int).1 j out → sorted M.width M.sorter M.input int j f es →
    (chunkSign (some false) es).isSome = true →
    (chunkBits es,rowProduct M.program M.pub lib weights fuel f es) ∈
      FieldReplay.leaves (code M.program lib weights) (FieldStack.productOutput (factor lib weights) terminal)
        (n^36) (Processor.start,Fintype.equivFin F 1)
        (StackCompiler.labeledInput Layout.input (G.input pin ext int u j))

omit [Fintype Q] in
/-- The row values and the original physical/signed path dictionary identify each
entire team's field product with the actual finite-field RAM path sum. -/
theorem witnesses_sum (fuel : ℕ) (hlib : M.lib = macros lib fuel) (hclock : max 1 (fuel-1) ≤ M.privateClock)
    (dictionary : RowDictionary M G lib pin ext u) (values : RowValues M lib weights G pin ext u fuel) :
    (∑ s : SiteWitness G M.program lib pin ext u, ∏ j, leafValue M.program lib weights G pin ext s.1 u j (s.2 j)) =
      nativeSum M lib weights fuel := by
  let b := dictionary.bijection fuel hlib hclock
  let := Fintype.ofFinite M.Paths
  have sumNZ : nativeSum M lib weights fuel =
      ∑ z : NonzeroPath M.machine M.limit.val M.cap.val M.privateClock, pathProduct M.program M.pub lib weights fuel M.start z.val.val := by
    unfold nativeSum
    rw [← Fintype.sum_subtype_add_sum_subtype (fun z : M.Paths => pathWeight z.val ≠ 0)
      (fun z => pathProduct M.program M.pub lib weights fuel M.start z.val)]
    apply add_eq_left.mpr
    apply Finset.sum_eq_zero
    intro z _
    have zero : pathWeight z.val.val = 0 := not_ne_iff.mp z.property
    have loc := (TeamRAM.execute_spec z.val.property.1).1
    change TeamRAM.Local (M.program.fetch M.pub M.lib) M.start z.val.val at loc
    rw [hlib] at loc
    rw [pathProduct_eq _ _ _ _ _ _ _ loc,zero,Int.cast_zero,zero_mul]
  rw [sumNZ]
  apply Finset.sum_equiv b.nativeEquiv (by simp)
  intro s _
  let z := b.rawEquiv s
  have spelled := b.spells_equiv s
  let raw := z.val.val
  obtain ⟨rows,last,frames,owners⟩ := (M.endpointChecks_iff_fuel raw lib fuel hlib hclock).mpr z.val.property
  let ins := predecessor M.first raw.frames
  have site (j : Fin teams) : leafValue M.program lib weights G pin ext s.1 u j (s.2 j) =
      rowProduct M.program M.pub lib weights fuel (ins j) (raw.blocks j) := by
    have f := frame_conditions (Wires.edgeEquiv raw.links).1 M.first ins raw.frames frames last j
    have checked := (sorted_iff_global M.width M.sorter M.input raw.links raw.blocks j (ins j)
      (elapsed M rows j)).mpr (owners j)
    have good := (rawWeight_ne_zero_iff raw).mp z.property j
    have native := values raw.links j (ins j) f.1 (raw.blocks j) (raw.frames j) (rows j) f.2 checked good
    have linkEq : s.1 = raw.links := spelled.links
    have tapeEq : chunkBits (raw.blocks j) = (s.2 j).val.1 := spelled.bits j
    rw [← linkEq,tapeEq] at native
    let E := FieldStack.leafEquiv (Processor.code M.program lib) (factor lib weights) terminal Processor.negative (n^36)
      Processor.start (StackCompiler.labeledInput Layout.input (G.input pin ext s.1 u j)) 1
    exact FieldReplay.output_unique _ _ _ _ _ (s.2 j).val.1 (E (s.2 j)).property native
  have all := (endpointRows_iff_pointwise ..).mpr rows
  rw [hlib] at all
  exact (Finset.prod_congr rfl fun j _ => site j).trans (product_rows M.program M.pub lib weights fuel M.pcs
    M.block M.limit M.cap M.start raw.blocks raw.frames all)

variable {Edge : Type}

/-- The physical team sum is over the same finite set of signed-site witnesses,
with the field output supplied by each unique instrumented replay. -/
theorem eventually_witnesses (P : TeamOpcode.Program p r k a) (lib : Fin a → Macro Q Γ m g) (weights : Returns Q Γ F m a) :
    ∀ᶠ n : ℕ in atTop, ∀ (R teams t d link inner : ℕ) (Edge : Type) [Fintype Edge]
      (G : Wiring R teams t d link inner n Edge), G.program = programPrefix (machine P lib weights) → ∀ pin ext u,
      FieldTeam.fieldValue G F pin ext u = ∑ s : SiteWitness G P lib pin ext u, ∏ j, leafValue P lib weights G pin ext s.1 u j (s.2 j) := by
  filter_upwards [FieldTeam.eventually_replay_value Layout.input 36 (by decide) (by decide)
    (code P lib weights) (FieldStack.productOutput (factor lib weights) terminal) (Processor.start,Fintype.equivFin F 1)] with n hn
  intro R teams t d link inner Edge _ G h pin ext u
  rw [hn _ _ _ _ _ _ _ G h]
  refine Eq.trans ?_ (Fintype.sum_sigma' (fun (int : Edge → Bool) (xs : (j : Fin teams) → ↥(physicalLeaves G
    Layout.input (Processor.code P lib) Processor.negative Processor.start 36 pin ext int u j)) =>
      ∏ j, leafValue P lib weights G pin ext int u j (xs j))).symm
  apply Finset.sum_congr rfl
  intro int _
  let E := Equiv.piCongrRight (fun j : Fin teams => FieldStack.leafEquiv (Processor.code P lib) (factor lib weights)
    terminal Processor.negative (n^36) Processor.start (StackCompiler.labeledInput Layout.input (G.input pin ext int u j)) 1)
  exact (E.sum_comp (fun xs => ∏ j, (xs j).val.2)).symm

end FieldProcessor

end BorderVNP
end Computability
end OAI
