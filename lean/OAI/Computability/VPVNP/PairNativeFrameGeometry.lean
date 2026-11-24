import OAI.Computability.VPVNP.PairNativeFrameArithmetic
import OAI.Computability.VPVNP.PairNativeFrameTable
import OAI.Computability.VPVNP.PairSimulationLeafArena

/-! # Terminal header words and the private address layout of the leaf verifier -/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.NativeFrame
open BurstRAM BurstRAM.PrivateRAM PrimedStackRAM
open scoped Fin.CommRing

variable {w : ℕ}

/-- The exclusive node bound uses the entire address interval, including
the cells below the first absolute descriptor address. -/
def regions (degree n firstRow rowWords labels : ℕ) : LeafArena.Regions :=
  ⟨⟨n,2*degree*n+1⟩,firstRow+rowWords,labels,n^5⟩

/-- Private leaf layout reconstructed from the terminal row base and row word count, the public
input length and label count, and the fixed degree. -/
def fromHeader (degree : ℕ) (pub : Fin 11 → Word w) (header : Word w) (m : Memory w) :=
  regions degree (pub 6).val (m (header+4).val).val (m (header+5).val).val (pub 9).val

/-- First address after the private histogram, where the terminal vertex installs its geometry
fields. -/
def frameBase (A : LeafArena.Regions) := A.histBase+A.histWords

/-- Offsets 0 through 5 serve the leaf decoder. Offsets 6 through 8
supply the argument and cache addresses for leaf preparation. -/
def fields (degree : ℕ) (pub : Fin 11 → Word w) (header role : Word w) (m : Memory w) :
    Fin 12 → Word w :=
  let A := fromHeader degree pub header m
  ![m (header+4).val, m (header+15).val, m (header+18).val, m (header+19).val,
    pub 3, m (header+20).val, pub 6, (A.arguments.stride : Word w), (A.cacheBase : Word w),
    pub 6, role, (A.histBase : Word w)]

private theorem nat_word (x : Word w) : (x.val : Word w) = x := Fin.ext (Nat.mod_eq_of_lt x.isLt)

private theorem stride_cast (degree : ℕ) (pub : Fin 11 → Word w) (header : Word w) (m : Memory w) :
    ((fromHeader degree pub header m).arguments.stride : Word w) = argumentStride pub degree := by
  simp only [fromHeader,regions,argumentStride,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one,nat_word]

private theorem hist_cast (degree : ℕ) (pub : Fin 11 → Word w) (header : Word w) (m : Memory w) (rs : Regs w 24) :
    ((fromHeader degree pub header m).histBase : Word w) = histWord pub (loaded header m rs) degree := by
  change (((pub 6).val + ((m (header+4).val).val + (m (header+5).val).val) *
    (fromHeader degree pub header m).arguments.stride : ℕ) : Word w) =
    pub 6 + argumentStride pub degree * (m (header+4).val + m (header+5).val)
  simp only [Nat.cast_add,Nat.cast_mul,nat_word,stride_cast,mul_comm]

private theorem graph_cast (degree : ℕ) (pub : Fin 11 → Word w) (header : Word w) (m : Memory w) (rs : Regs w 24) :
    (frameBase (fromHeader degree pub header m) : Word w) = graphWord pub (loaded header m rs) degree := by
  simp only [frameBase,Nat.cast_add,hist_cast degree pub header m rs,graphWord]
  rw [show (fromHeader degree pub header m).histWords = (pub 9).val from rfl,nat_word]

private theorem cache_cast (degree : ℕ) (pub : Fin 11 → Word w) (header : Word w) (m : Memory w) (rs : Regs w 24) :
    ((fromHeader degree pub header m).cacheBase : Word w) = graphWord pub (loaded header m rs) degree + (pub 6)^5 := by
  change ((frameBase (fromHeader degree pub header m)+(pub 6).val^5 : ℕ) : Word w) = _
  simp only [Nat.cast_add,Nat.cast_pow,graph_cast degree pub header m rs,nat_word]

/-- Values required by the thirteen private stores. The frame starts
immediately after the histogram and ends before the scalar operand cache. -/
structure Ready {r : ℕ} (reg : R ↪ Fin r) (pub : Fin 11 → Word w)
    (degree : ℕ) (header role : Word w) (m : Memory w) (out : Regs w r) : Prop where
  graph : out (reg 2) = (frameBase (fromHeader degree pub header m) : Word w)
  cursor : out (reg 18) = (frameBase (fromHeader degree pub header m) : Word w)
  unit : out (reg 15) = 1
  field : ∀ i, out (reg (fieldReg i)) = fields degree pub header role m i

theorem arithmetic_ready (degree : ℕ) (pub : Fin 11 → Word w) (header : Word w) (m : Memory w) (rs : Regs w 24) :
    Ready (Function.Embedding.refl _) pub degree header (rs 1) m
      (arithmeticBank pub (loaded header m rs) degree) := by
  have h := arithmetic_values pub (loaded header m rs) degree (show loaded header m rs 15 = 1 from rfl)
  have hg := (graph_cast degree pub header m rs).symm
  refine ⟨h.graph.trans hg,h.cursor.trans hg,h.preserved 15 (by decide),?_⟩
  intro i
  fin_cases i
  · exact h.preserved 3 (by decide)
  · exact h.preserved 4 (by decide)
  · exact h.preserved 5 (by decide)
  · exact h.preserved 6 (by decide)
  · exact h.shadow
  · exact h.preserved 8 (by decide)
  · exact h.length
  · exact h.iterations.trans (stride_cast degree pub header m).symm
  · exact h.cache.trans (cache_cast degree pub header m rs).symm
  · exact h.copyLength
  · exact h.role
  · exact h.histogram.trans (hist_cast degree pub header m rs).symm

end PairSimulation.NativeFrame

end VPVNP
end Computability
end OAI
