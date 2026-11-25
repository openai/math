import OAI.ThreeFlat.Diagonal.CompressorSweepImage
import OAI.ThreeFlat.Diagonal.CompressorNodeRecipe
import OAI.ThreeFlat.Diagonal.SlotImage

namespace OAI
/-! # Materialization of the shrinking successor by the real native passes -/
namespace ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkStage
open Computability.VPVNP.Compression Computability.VPVNP.BurstRAM Computability.VPVNP.BurstRAM.PrivateRAM RAM RAM.DescriptorScan
open scoped Fin.NatCast
variable {w : ℕ}

/-- An actual installed span reads its two bounds from this particular memory.
Its row equation is required against all writes confined to its own output. -/
structure FileSpec (current : Word w) (pub : Fin 1 → Word w) (f : Template.F) (low len : ℕ)
    (m : Memory w) (start count : ℕ) (file : ℕ → Word w) : Prop where
  fit : start+count<2^w
  lowWord : (headerRead m current low).val=start
  lenWord : (headerRead m current len).val=count
  values : ∀ a : Word w, ∀ alt,start≤a.val → a.val<start+count →
    agreesOutside start (start+count) alt m →
    (Template.emit current f).eval pub alt (fun _=>a)=file a.val

theorem FileSpec.image {current : Word w} {pub f low len m start count file}
    (h : FileSpec current pub f low len m start count file) :
    (((Recipe.one f low len).install current).execute current pub m).2 =
      fillSegment start count file m :=
  one_image ⟨Template.emit current f, low, len⟩ current pub m start count file h.fit h.lowWord h.lenWord h.values

/-- Compose two installed memory images without unfolding their row expressions. -/
private theorem seq_image (first second : Recipe) (current : Word w) (pub : Fin 1 → Word w)
    (m mid out : Memory w)
    (hfirst : ((first.install current).execute current pub m).2=mid)
    (hsecond : ((second.install current).execute current pub mid).2=out) :
    (((Recipe.seq first second).install current).execute current pub m).2=out := by
  change ((second.install current).execute current pub ((first.install current).execute current pub m).2).2=out
  exact (congrArg (fun x : Memory w=>((second.install current).execute current pub x).2) hfirst).trans hsecond

namespace PostImage
variable {B L : Type*} {N Z d : ℕ}
variable (G : LiftedSlots B d L) (base : B ≃ Fin N) (lane : L ≃ Fin Z)
variable (width : SlotImage.Edge B L d → ℕ) (C : SlotImage.Columns)

def graphMem (m : Memory w) (g : ℕ → Word w) := fillSegment C.graph (6*C.rows) g m
def keyMem (m : Memory w) (keys : ℕ) (g id : ℕ → Word w) := fillSegment keys C.rows id (graphMem C m g)
def widthMem (m : Memory w) (keys : ℕ) (g id out : ℕ → Word w) (lanes : ℕ) :=
  fillSegment C.widths (C.rows*lanes) out (keyMem C m keys g id)

private theorem cell_mem (rows : C.rows=N*d) (p : B × Fin d) (rev : Bool) (f : Fin 3) :
    C.graph≤SlotImage.cell C base p rev f ∧ SlotImage.cell C base p rev f<C.graph+6*C.rows := by
  have ix : SlotImage.ordinal base p<C.rows := by rw [rows]; exact SlotImage.ordinal_lt base p
  have cf : SlotImage.column rev f <6 := by
    cases rev <;> have := f.isLt <;> simp [SlotImage.column] <;> omega
  have mul := Nat.mul_le_mul_left C.rows cf
  rw [Nat.mul_succ] at mul
  unfold SlotImage.cell
  omega

/-- The graph is emitted, followed by its key file and selected width file.
The conclusion uses the exact memory produced by `post.execute`. -/
theorem stored (S : Graph.Stage) (current : Word w) (pub : Fin 1 → Word w) (m : Memory w)
    (keyBase : ℕ) (g id out : ℕ → Word w) (rows : C.rows=N*d)
    (keyStart : C.graph+6*C.rows≤keyBase) (widthStart : keyBase+C.rows≤C.widths)
    (graph : FileSpec current pub (Template.graph S false) nextGraph graphWords m C.graph (6*C.rows) g)
    (keysRun : FileSpec current pub (Template.graph S true) keys nextSlots (graphMem C m g) keyBase C.rows id)
    (widthRun : FileSpec current pub (Template.output S) nextWidths widthWords
      (keyMem C m keyBase g id) C.widths (C.rows*Z) out)
    (gv : ∀ p rev f,(g (SlotImage.cell C base p rev f)).val = SlotImage.fields G base lane p rev f)
    (wv : ∀ e,(out (C.widths+SlotImage.edgeOrdinal base lane e)).val=width e) :
    SlotImage.Stored G base lane C (fun x=>(((post current S).execute current pub m).2 x).val) width := by
  have material : ((post current S).execute current pub m).2 = widthMem C m keyBase g id out Z := by
    let graphPass:=Recipe.one (Template.graph S false) nextGraph graphWords
    let keyPass:=Recipe.one (Template.graph S true) keys nextSlots
    let widthPass:=Recipe.one (Template.output S) nextWidths widthWords
    have afterKeys : (((Recipe.seq keyPass widthPass).install current).execute current pub (graphMem C m g)).2=
        widthMem C m keyBase g id out Z :=
      seq_image keyPass widthPass current pub (graphMem C m g) (keyMem C m keyBase g id)
        (widthMem C m keyBase g id out Z) keysRun.image widthRun.image
    exact seq_image graphPass (.seq keyPass widthPass) current pub m (graphMem C m g)
      (widthMem C m keyBase g id out Z) graph.image afterKeys
  rw [material]
  refine ⟨rows,?_,?_⟩
  · intro p rev f
    have bounds := cell_mem base C rows p rev f
    have wno : ¬ C.widths≤SlotImage.cell C base p rev f := by omega
    have kno : ¬ keyBase≤SlotImage.cell C base p rev f := by omega
    simpa [widthMem,keyMem,graphMem,fillSegment,wno,kno,bounds.1,bounds.2] using gv p rev f
  · intro e
    have br := SlotImage.edgeOrdinal_lt base lane e
    rw [←rows] at br
    have hi := Nat.add_lt_add_left br C.widths
    simpa [widthMem,fillSegment,hi] using wv e

end PostImage
end ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkStage

end OAI
