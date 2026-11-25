import OAI.Computability.BorderVNP.TeamContractionSiteEquiv
import OAI.Computability.BorderVNP.TeamSiteTraversalSort

/-! # From the actual row replay dictionary to the whole signed team

The real register wires are traversed in processor order. Their typed states fix the
timestamps used by each local emitted sorting row. All the validated rows together
recover a unique native execution on the original shared memory.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction

open VPVNP RAMTape TeamSiteConsistency TeamContraction.Wires TeamSite TeamSiteEvents TeamTapeHandoff TeamSiteTraversal
open scoped Classical

variable {R teams t d link inner n p regs pub a e w m g : ℕ} {Q Γ : Type}
variable (M : Setup teams w p regs pub a e) (G : Wiring R teams t d link inner n (Edge teams regs w e (w+1)))
    (lib : Fin a → Macro Q Γ m g) (pin : Fin d → Bool) (ext : Exterior R teams link → Bool) (team : Fin (R+1))

/-- The single-site dictionary on the true physical assignment. It is tested only for
a canonical predecessor already present on the incident wires, exactly as at startup. -/
def RowDictionary : Prop :=
  ∀ links j incoming, Reads (edgeEquiv links).1 M.first j incoming → ∀ (bits : List Bool) (neg : Bool),
    (bits,neg) ∈ physicalLeaves G Layout.input (Processor.code M.program lib) Processor.negative Processor.start
      36 pin ext links team j ↔
    ∃ es out, EndpointRow M.program M.pub M.lib M.block M.limit M.cap incoming es out ∧
      Writes (edgeEquiv links).1 j out ∧ sorted M.width M.sorter M.input links j incoming es ∧
      bits = chunkBits es ∧ chunkSign (some false) es = some neg

private theorem elapsed {blocks : Fin teams → List (TeamRAM.Event w)} {outs : Fin teams → Frame w regs}
    (row : ∀ j, EndpointRow M.program M.pub M.lib M.block M.limit M.cap (predecessor M.first outs j) (blocks j) (outs j))
    (j : Fin teams) : (predecessor M.first outs j).elapsed.val+1 = 1+blockOffset blocks j := by
  have rows := (endpointRows_iff_pointwise ..).mpr row
  have eq := rows.predecessor_elapsed j
  change (predecessor M.first outs j).elapsed.val = 0+blockOffset blocks j at eq
  omega

variable {M G lib pin ext team}

/-- Recover a complete checked history from any collection of actual local leaves on
one shared assignment. Replaying the exact finite branch bits makes this history unique. -/
theorem RowDictionary.history (localLaw : RowDictionary M G lib pin ext team)
    (fuel : ℕ) (hlib : M.lib = macros lib fuel) (clock : max 1 (fuel-1) ≤ M.privateClock)
    (s : SiteWitness G M.program lib pin ext team) : ∃! z : M.Histories, Spells z.val s := by
  let R' (j : Fin teams) (f : Frame w regs) (es : List (TeamRAM.Event w)) (out : Frame w regs) :=
    EndpointRow M.program M.pub M.lib M.block M.limit M.cap f es out ∧
    sorted M.width M.sorter M.input s.1 j f es ∧ chunkBits es = (s.2 j).val.1 ∧
      chunkSign (some false) es = some (s.2 j).val.2
  have find (j : Fin teams) (f : Frame w regs) (input : Reads (edgeEquiv s.1).1 M.first j f) :
      ∃ es out, R' j f es out ∧ Writes (edgeEquiv s.1).1 j out := by
    obtain ⟨es,out,row,guard,sort,bs,sign⟩ :=
      (localLaw s.1 j f input (s.2 j).val.1 (s.2 j).val.2).mp (s.2 j).property
    exact ⟨es,out,⟨row,sort,bs.symm,sign⟩,guard⟩
  obtain ⟨bs,input,out,frames,rows,last⟩ := collect (edgeEquiv s.1).1 M.first R' find
  obtain rfl : input = predecessor M.first out := (frameChecks_iff.mp frames).2
  let z : RawHistory teams regs w e := ⟨bs,out,s.1⟩
  have checks : M.EndpointChecks z := by
    refine ⟨fun j => (rows j).1,last,frames,?_⟩
    intro j
    exact (sorted_iff_global M.width M.sorter M.input s.1 bs j (predecessor M.first out j)
      (elapsed M (fun j => (rows j).1) j)).mp (rows j).2.1
  let hist : M.Histories := ⟨z,(M.endpointChecks_iff_fuel z lib fuel hlib clock).mp checks⟩
  have spelled : Spells hist.val s := ⟨rfl,fun j => (rows j).2.2.1,fun j => (rows j).2.2.2⟩
  refine ⟨hist,spelled,?_⟩
  intro other hother
  exact histories_unique_fuel M lib fuel hlib clock other hist (hother.links.symm.trans spelled.links)
    (fun j => (hother.bits j).trans (spelled.bits j).symm)

/-- Conversely, each nonzero genuine checked history contributes its prescribed raw
links, sign and script to the actual leaf set on every real processor. -/
theorem RowDictionary.witness (localLaw : RowDictionary M G lib pin ext team)
    (fuel : ℕ) (hlib : M.lib = macros lib fuel) (clock : max 1 (fuel-1) ≤ M.privateClock)
    (z : M.NonzeroHistories) : ∃ s : SiteWitness G M.program lib pin ext team, Spells z.val.val s := by
  apply (spells_exists_iff z.val.val z.property).mpr
  have checks := (M.endpointChecks_iff_fuel z.val.val lib fuel hlib clock).mpr z.val.property
  obtain ⟨rows,last,frames,owners⟩ := checks
  intro j
  let f := predecessor M.first z.val.val.frames j
  have both := frame_conditions (edgeEquiv z.val.val.links).1 M.first _ _ frames last j
  apply (localLaw _ j f both.1 ..).mpr
  refine ⟨_,_,rows j,both.2,(sorted_iff_global M.width M.sorter M.input _ _ j f (elapsed M rows j)).mpr (owners j),rfl,?_⟩
  have good := (rawWeight_ne_zero_iff z.val.val).mp z.property j
  cases eq : chunkSign (some false) (z.val.val.blocks j) with
  | none => simp [eq] at good
  | some b => rfl

/-- The actual local replay dictionary suffices for the global signed identification.
The native shared-memory execution, scheduler and link uniqueness all follow from
the physical endpoint, frame and sorter checks. -/
theorem RowDictionary.bijection (localLaw : RowDictionary M G lib pin ext team)
    (fuel : ℕ) (hlib : M.lib = macros lib fuel) (clock : max 1 (fuel-1) ≤ M.privateClock) :
    SpellingBijection M G lib pin ext team :=
  ⟨localLaw.history fuel hlib clock,localLaw.witness fuel hlib clock⟩

end TeamContraction

end BorderVNP
end Computability
end OAI
