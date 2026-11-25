import OAI.Computability.BorderVNP.TeamContractionPhysical
import OAI.Computability.BorderVNP.TeamSiteProcessorRowIff

/-! # The unique physical extension of every native team path

The signed sum only observes nonzero accepting leaves. The processor also has
an unmasked memory-check verdict before it reports its path contribution. Using
that verdict includes valid paths whose private factors multiply to zero. The
bijection below retains all physical link bits, all exact local choices and all
three possible local weights.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction

open VPVNP RAMTape TeamSite TeamSiteEvents TeamSiteConsistency TeamSiteTraversal TeamContraction.Wires
open TeamPrivateFragment TeamTapeHandoff

variable {R r t d link inner n p regs k a e w m g : ℕ} {Q Γ : Type}

/-- One concrete team assignment, with the exact choices and path factor at each site. -/
structure LocalScripts (r : ℕ) (E : Type*) where
  /-- Physically shared interior bits. -/
  links : E → Bool
  /-- Ordered native and probe choices at each site. -/
  bits : Fin r → List Bool
  /-- Signed local contribution; `none` is an absorbed zero. -/
  sign : Fin r → Option Bool

variable (M : Setup r w p regs k a e) (G : Wiring R r t d link inner n (Edge r regs w e (w+1)))
    (lib : Fin a → Macro Q Γ m g) (pin : Fin d → Bool) (team : Fin (R+1))

/-- The physical run reaches the successful unmasked sorting terminal of the full
processor code, with no surplus binary choices. Its local coefficient can be zero. -/
def checkedSite (ext : Exterior R r link → Bool) (int : Edge r regs w e (w+1) → Bool)
    (j : Fin r) (bits : List Bool) (sign : Option Bool) : Prop :=
  ∃ h < n^36, ∃ q b, StackRuns (replay (Processor.code M.program lib)) h (Processor.start,bits)
    (StackCompiler.labeledInput Layout.input (G.input pin ext int team j)) (q,[]) b ∧ Processor.Row.Checked q sign

/-- A legitimate distributed path tests its physical output frame and all memory
messages, including after a zero private weight. -/
def FullyChecked (ext : Exterior R r link → Bool) (s : LocalScripts r (Edge r regs w e (w+1))) : Prop :=
  ∀ j, checkedSite M G lib pin team ext s.links j (s.bits j) (s.sign j)

/-- Dictionary for the unmasked physical verdict on every supplied canonical predecessor. -/
def CheckedDictionary (ext : Exterior R r link → Bool) : Prop :=
  ∀ int j f, Reads (edgeEquiv int).1 M.first j f → ∀ bits sign,
    checkedSite M G lib pin team ext int j bits sign ↔
      ∃ es out, EndpointRow M.program M.pub M.lib M.block M.limit M.cap f es out ∧
        Writes (edgeEquiv int).1 j out ∧ sorted M.width M.sorter M.input int j f es ∧
        bits = chunkBits es ∧ chunkSign (some false) es = sign

/-- Complete physical spelling determined by the native history. -/
def scripts (z : RawHistory r regs w e) : LocalScripts r (Edge r regs w e (w+1)) :=
  ⟨z.links,fun j => chunkBits (z.blocks j),fun j => chunkSign (some false) (z.blocks j)⟩

private theorem history_elapsed (z : RawHistory r regs w e)
    (rows : ∀ j, EndpointRow M.program M.pub M.lib M.block M.limit M.cap
      (predecessor M.first z.frames j) (z.blocks j) (z.frames j)) (j : Fin r) :
    (predecessor M.first z.frames j).elapsed.val+1 = 1+blockOffset z.blocks j := by
  have hh := ((endpointRows_iff_pointwise ..).mpr rows).predecessor_elapsed j
  change _ = 0+blockOffset z.blocks j at hh
  omega

variable {M G lib pin team}
variable {extBits : Exterior R r link → Bool}

/-- Physical validity of a complete tuple is equivalent to being the exact spelling
of a native-equivalent history. The implication from a physical witness traverses
the real register wires from the public first frame. -/
theorem CheckedDictionary.checked_iff (dict : CheckedDictionary M G lib pin team extBits) (fuel : ℕ)
    (hlib : M.lib = macros lib fuel) (bound : max 1 (fuel-1) ≤ M.privateClock)
    (s : LocalScripts r (Edge r regs w e (w+1))) :
    FullyChecked M G lib pin team extBits s ↔ ∃ z : M.Histories, scripts z.val = s := by
  constructor
  · intro checked
    let row (j : Fin r) (f : Frame w regs) (es : List (TeamRAM.Event w)) (out : Frame w regs) :=
      EndpointRow M.program M.pub M.lib M.block M.limit M.cap f es out ∧
        sorted M.width M.sorter M.input s.links j f es ∧ s.bits j = chunkBits es ∧
        chunkSign (some false) es = s.sign j
    have found (j : Fin r) (f : Frame w regs) (input : Reads (edgeEquiv s.links).1 M.first j f) :
        ∃ es out, row j f es out ∧ Writes (edgeEquiv s.links).1 j out := by
      obtain ⟨es,out,h,frame,sort,bits,sign⟩ := (dict _ _ _ input ..).mp (checked j)
      exact ⟨es,out,⟨h,sort,bits,sign⟩,frame⟩
    obtain ⟨bs,ins,outs,frames,rows,last⟩ := collect _ _ row found
    obtain rfl : ins = predecessor M.first outs := (frameChecks_iff.mp frames).2
    let z : RawHistory r regs w e := ⟨bs,outs,s.links⟩
    have valid : M.EndpointChecks z := by
      refine ⟨fun j => (rows j).1,last,frames,?_⟩
      intro j
      apply (sorted_iff_global M.width M.sorter M.input s.links bs j _
        (history_elapsed M z (fun i => (rows i).1) j)).mp (rows j).2.1
    refine ⟨⟨z,(M.endpointChecks_iff_fuel z lib fuel hlib bound).mp valid⟩,?_⟩
    rcases s with ⟨links,bits,sign⟩
    exact congrArg₂ (LocalScripts.mk links) (funext fun j => (rows j).2.2.1.symm) (funext fun j => (rows j).2.2.2)
  · rintro ⟨z,rfl⟩ j
    have valid := (M.endpointChecks_iff_fuel z.val lib fuel hlib bound).mpr z.property
    obtain ⟨rows,last,frames,owners⟩ := valid
    let f := predecessor M.first z.val.frames j
    have frame := frame_conditions _ _ _ _ frames last j
    apply (dict z.val.links j f frame.1 ..).mpr
    exact ⟨z.val.blocks j,z.val.frames j,rows j,frame.2,
      (sorted_iff_global M.width M.sorter M.input z.val.links z.val.blocks j f (history_elapsed M z.val rows j)).mpr (owners j),
      rfl,rfl⟩

/-- The exact assignment and finite choice spelling form a bijection between checked
physical scripts and the semantic histories with canonical frame and sorting fields. -/
noncomputable def CheckedDictionary.scriptEquiv (dict : CheckedDictionary M G lib pin team extBits)
    (fuel : ℕ) (hlib : M.lib = macros lib fuel) (bound : max 1 (fuel-1) ≤ M.privateClock) :
    M.Histories ≃ {s // FullyChecked M G lib pin team extBits s} := by
  let embed (z : M.Histories) : {s // FullyChecked M G lib pin team extBits s} :=
    ⟨scripts z.val,(dict.checked_iff fuel hlib bound _).mpr ⟨z,rfl⟩⟩
  apply Equiv.ofBijective embed
  constructor
  · intro x y he
    have same : scripts x.val = scripts y.val := congrArg Subtype.val he
    exact histories_unique_fuel M lib fuel hlib bound x y (congrArg LocalScripts.links same)
      (congrFun (congrArg LocalScripts.bits same))
  · intro s
    obtain ⟨z,h⟩ := (dict.checked_iff fuel hlib bound s.val).mp s.property
    exact ⟨z,Subtype.ext h⟩

/-- The native path has precisely one complete physically checked extension, even
when one of its local subroutines returns zero. -/
noncomputable def CheckedDictionary.physicalEquiv (dict : CheckedDictionary M G lib pin team extBits)
    (fuel : ℕ) (hlib : M.lib = macros lib fuel) (bound : max 1 (fuel-1) ≤ M.privateClock) :
    {s // FullyChecked M G lib pin team extBits s} ≃ M.Paths :=
  (dict.scriptEquiv fuel hlib bound).symm.trans M.rawEquivNative

/-- The actual coefficient contributed by the local halts. -/
def LocalScripts.weight {E : Type*} (s : LocalScripts r E) : ℤ :=
  ∏ j, (TeamPrivateCall.sign (s.sign j)).value

/-- Every factor in the product of the physical site weights agrees with the native
execution, including an absorbed zero. -/
theorem CheckedDictionary.physicalEquiv_weight (dict : CheckedDictionary M G lib pin team extBits)
    (fuel : ℕ) (hlib : M.lib = macros lib fuel) (bound : max 1 (fuel-1) ≤ M.privateClock)
    (s : {s // FullyChecked M G lib pin team extBits s}) :
    s.val.weight = pathWeight ((dict.physicalEquiv fuel hlib bound) s).val := by
  obtain ⟨z,rfl⟩ := (dict.scriptEquiv fuel hlib bound).surjective s
  simp only [physicalEquiv,Equiv.trans_apply,Equiv.symm_apply_apply]
  change (scripts z.val).weight = _
  exact (rawWeight_prod z.val).symm.trans (M.rawEquivNative_weight z)

/-- Pathwise uniqueness and equality of the native and physical weights, independently
of whether that weight survives the signed sum. -/
theorem CheckedDictionary.existsUnique_extension (dict : CheckedDictionary M G lib pin team extBits)
    (fuel : ℕ) (hlib : M.lib = macros lib fuel) (bound : max 1 (fuel-1) ≤ M.privateClock)
    (p : M.Paths) :
    ∃! s : {s // FullyChecked M G lib pin team extBits s},
      (dict.physicalEquiv fuel hlib bound) s = p ∧ s.val.weight = pathWeight p.val := by
  let E := dict.physicalEquiv fuel hlib bound
  refine ⟨E.symm p,⟨E.apply_symm_apply p,?_⟩,fun s h => E.injective (h.1.trans (E.apply_symm_apply p).symm)⟩
  have eq := dict.physicalEquiv_weight fuel hlib bound (E.symm p)
  rw [show (dict.physicalEquiv fuel hlib bound) (E.symm p) = p from E.apply_symm_apply p] at eq
  exact eq

end TeamContraction

end BorderVNP
end Computability
end OAI
