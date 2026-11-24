import OAI.Computability.VPVNP.PairNativeLeafSetupTable
import OAI.Computability.VPVNP.PairVertexSiteSegments

/-! # Installing the combined geometry and cache in the terminal vertex image

The segment uses the caller's saved header, role, and histogram registers.
Its two instruction ranges and its two private register ranges are disjoint.
Renaming the arithmetic and operand flows preserves both instruction counts.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.VertexGeometry

open BurstRAM PrivateRAM LiveProgram PrimedInputRAM NativeOperands VertexImage
open scoped Fin.CommRing

attribute [local irreducible] NativeOperands.capacity NativeOperands.saved

variable (c : Constants) (degree a b : ℕ)

/-- Geometry instruction count before relocation. -/
def frameCount := 2 + (NativeFrame.reads.length + (NativeFrame.arithmetic degree).length) + 29
/-- Instruction count of the finite cache computation and its 38 stores. -/
def cacheCount := (NativeCache.block c a b).length + 2*NativeCacheTable.count + 2
/-- Total number of program-counter slots used by the geometry segment. -/
def count := frameCount degree + cacheCount c a b
/-- Size of the segment's private register bank. -/
abbrev regs := 24 + NativeCache.bankSize c

variable {p r : ℕ}

/-- The first 24 private registers, used by the geometry reader. -/
def workBank (rs : Fin (regs c) ↪ Fin r) := (Fin.castAddEmb (NativeCache.bankSize c)).trans rs
/-- Private registers following the geometry reader's register bank. -/
def cacheBank (rs : Fin (regs c) ↪ Fin r) := (Fin.natAddEmb 24).trans rs

private theorem frame_length (ws : Fin 24 ↪ Fin r) (head role : Fin r) :
    NativeFrame.Table.size (NativeFrame.prelude degree ws head role) = frameCount degree := by
  simp only [NativeFrame.Table.size,NativeFrame.prelude,Flow.length,PrimedCounter.rename_length,frameCount]

private theorem cache_length (cs : Fin (NativeCache.bankSize c) ↪ Fin r) :
    NativeCacheTable.size (NativeCache.code c a b cs) = cacheCount c a b := by
  simp only [NativeCacheTable.size,NativeCache.code,NativeCache.relocated,PrimedCounter.rename_length,cacheCount]

variable (pc : Fin (count c degree a b) → Fin p) (bank : Saved ↪ Fin r) (rs : Fin (regs c) ↪ Fin r)
  (finish : Fin p)

private abbrev f := NativeFrame.prelude degree (workBank c rs) (bank header) (bank roleOffset)
private abbrev cacheCode := NativeCache.code c a b (cacheBank c rs)

private theorem length_eq : NativeFrame.Table.size (f c degree bank rs) + NativeCacheTable.size (cacheCode c a b rs)
    = count c degree a b := by rw [frame_length,cache_length,count]

/-- Two-bit opcodes are padded to the vertex image's five-bit literal type. -/
def text (j : Fin (count c degree a b)) : Instr 5 p r 11 :=
  let F := f c degree bank rs
  let C := cacheCode c a b rs
  let address := pc ∘ Fin.cast (length_eq c degree a b bank rs)
  let front (i : Fin (NativeFrame.Table.size F)) := address (i.castAdd (NativeCacheTable.size C))
  let tail (i : Fin (NativeCacheTable.size C)) := address (i.natAdd (NativeFrame.Table.size F))
  let start := tail (NativeCacheTable.label C C.entry)
  let dest := (cacheBank c rs) (saved (NativeCache.args c))
  let transfer : Instr 2 p r 11 := .jumpEq dest dest start start
  let ret : Instr 2 p r 11 := .jumpEq (bank histBase) (bank histBase) finish finish
  let emit : Fin (NativeFrame.Table.size F + NativeCacheTable.size C) → Instr 2 p r 11 :=
    Fin.addCases (NativeFrame.Table.row F (workBank c rs) (bank histBase) dest front transfer)
    (NativeCacheTable.row C (NativeCache.storeSrc c (cacheBank c rs)) (NativeCache.ptr c (cacheBank c rs))
      (NativeCache.one c (cacheBank c rs)) tail ret)
  (emit (Fin.cast (length_eq c degree a b bank rs).symm j)).resize 5

/-- Geometry component installed between the ordinal guard and the root gather. -/
def segment : Segment where
  count := count c degree a b
  privateRegs := regs c
  entry := ⟨0,by unfold count frameCount; omega⟩
  row pc _ bank rs finish := text c degree a b pc bank rs finish

private theorem disjoint {S : Part → Segment} {p r : ℕ} (A : VertexImage.Placement S p r)
    (s : Saved) (i : Fin (S Part.geometry).privateRegs) :
    A.saved s ≠ A.localRegs Part.geometry i := by
  change A.reg (.inr (.inl s)) ≠ A.reg (.inr (.inr (.inr ⟨.geometry,i⟩)))
  exact A.reg.injective.ne (by simp)

variable {rootFields leaf shrink refresh : Segment}
local notation "S" => segments (segment c degree a b) rootFields leaf shrink refresh
variable (A : VertexImage.Placement (segments (segment c degree a b) rootFields leaf shrink refresh) p r)

private theorem allocated : (S .geometry).privateRegs = regs c := rfl
private theorem labels : (S .geometry).count = count c degree a b := rfl

attribute [local irreducible] segments segment

/-- The combined geometry and cache registers in the actual linked vertex image. -/
noncomputable def bankFor : Fin (regs c) ↪ Fin r :=
  (Fin.castLEEmb (allocated (rootFields := rootFields) (leaf := leaf) (shrink := shrink) (refresh := refresh)
    c degree a b).ge).trans (A.localRegs .geometry)

/-- Locate a geometry opcode in the enclosing vertex program. -/
noncomputable def labelsFor (j : Fin (count c degree a b)) : Fin p :=
  A.stage .geometry (j.cast (labels (rootFields := rootFields) (leaf := leaf) (shrink := shrink) (refresh := refresh)
    c degree a b).symm)

/-- Construct the native initialization block from disjoint saved and private registers. -/
def placedBlock (banks : ∀ s j, bank s ≠ rs j) : NativeLeafSetup.Block c r where
  degree := degree
  numerator := a
  denominator := b
  frame := ⟨workBank c rs, bank header, bank roleOffset, bank histBase,
    (cacheBank c rs) (saved (NativeCache.args c)), banks _ _, banks _ _, banks _ _⟩
  cache := cacheBank c rs
  basePort := rfl
  histogramPort := by rintro ⟨j,hj⟩; exact banks _ _ hj.symm

/-- Initialization block with the actual caller's header, role and histogram registers. -/
noncomputable def block : NativeLeafSetup.Block c r :=
  placedBlock c degree a b A.saved (bankFor c degree a b A) (fun s j =>
    disjoint A s ((Fin.castLEEmb (allocated (rootFields := rootFields) (leaf := leaf)
      (shrink := shrink) (refresh := refresh) c degree a b).ge) j))

local notation "K" => block c degree a b A

/-- Physical address of an instruction in the combined native block. -/
noncomputable def placement (j : Fin (NativeLeafSetup.size K)) : Fin p :=
  labelsFor c degree a b A (Fin.cast (length_eq c degree a b A.saved (bankFor c degree a b A)) j)

theorem entry_eq : placement c degree a b A (NativeLeafSetup.entry K) = A.entry .geometry := by
  apply congrArg (A.stage .geometry)
  apply Fin.ext
  unfold segments segment
  rfl

/-- Unconditional jump from the last cache instruction to the root-field gather. -/
noncomputable def ret : Instr 2 p r 11 := .jumpEq (A.saved histBase) (A.saved histBase) (A.returns .geometry) (A.returns .geometry)

variable {w : ℕ} (M : Machine w p r 11)

private theorem resize (op : Instr 2 p r 11) : (op.resize 5).resize w = op.resize w := by
  cases op <;> try rfl
  case constant _ val _ => simp only [Instr.resize, resize_literal (by decide : 2 ≤ 5)]

attribute [local irreducible] NativeFrame.Table.row NativeCacheTable.row NativeFrame.prelude PrimedCounter.renameFlow NativeOperands.vector

private theorem text_at (banks : ∀ s j, bank s ≠ rs j)
    (j : Fin (NativeLeafSetup.size (placedBlock c degree a b bank rs banks))) :
    text c degree a b pc bank rs finish (Fin.cast (length_eq c degree a b bank rs) j) =
      (NativeLeafSetup.row (placedBlock c degree a b bank rs banks)
        (pc ∘ Fin.cast (length_eq c degree a b bank rs))
        (.jumpEq (bank histBase) (bank histBase) finish finish) j).resize 5 := by
  unfold text NativeLeafSetup.row
  rfl

attribute [local irreducible] text count frameCount cacheCount

private theorem transfer {T : Part → Segment} (V : VertexImage.Placement T p r)
    (N : Machine w p r 11) (hi : Contains V N) (seg : Segment) (he : T .geometry = seg)
    (j : Fin seg.count) :
    N.code (V.stage .geometry (j.cast (congrArg Segment.count he).symm)) =
      (seg.row (fun i => V.stage .geometry (i.cast (congrArg Segment.count he).symm))
        V.dfs V.saved ((Fin.castLEEmb (congrArg Segment.privateRegs he).ge).trans (V.localRegs .geometry))
        (V.returns .geometry) j).resize w := by
  subst seg
  exact stage_linked V N hi .geometry j

attribute [local semireducible] segment

private theorem text_link (h : Contains A M) (j : Fin (count c degree a b)) :
    M.code (labelsFor c degree a b A j) =
      (text c degree a b (labelsFor c degree a b A) A.saved (bankFor c degree a b A)
        (A.returns .geometry) j).resize w := by
  have he : (S .geometry) = segment c degree a b := by unfold segments; rfl
  have hrow := transfer A M h (segment c degree a b) he
  have e : labelsFor c degree a b A =
      fun j => A.stage .geometry (j.cast (congrArg Segment.count he).symm) := rfl
  rw [e]
  simpa only [segment,bankFor] using hrow j

/-- Actual opcode at every geometry and cache PC in the full linked image. -/
theorem linked (h : Contains A M) (j : Fin (NativeLeafSetup.size K)) :
    M.code (placement c degree a b A j) =
      (NativeLeafSetup.row K (placement c degree a b A) (ret c degree a b A) j).resize w := by
  change M.code (labelsFor c degree a b A _) = _
  rw [text_link c degree a b A M h, text_at c degree a b (labelsFor c degree a b A) A.saved
    (bankFor c degree a b A) (A.returns .geometry) (fun s j => disjoint A s _) j, resize]
  rfl

end PairSimulation.VertexGeometry

end VPVNP
end Computability
end OAI
