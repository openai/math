import OAI.Computability.VPVNP.PairNativeFrameReads
import OAI.Computability.VPVNP.PrimedStackRAMNodeTable

/-!
# Word arithmetic for the terminal vertex's pair frame

After the six descriptor reads, the native program computes the histogram
base, graph arena, cache base and remaining frame fields. Each equality is
in the machine's word ring, so the code equations also hold when an
intermediate wraps.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.NativeFrame
open BurstRAM PrivateRAM PrimedInputRAM PrimedStackRAM
open scoped Fin.CommRing

variable {w : ℕ}

private def degreeCode : ℕ → Code
  | 0 => .line (.constant 16 0)
  | d+1 => .seq (degreeCode d) (.line (.binary .add 16 16 15))

private theorem degree_run (pub : Fin 11 → Word w) (st : Word w) (m : Memory w) (rs : Regs w 24)
    (one : rs 15 = 1) (d : ℕ) :
    Flow.Exec pub st (degreeCode d) rs m (List.replicate (d+1) .tick) (Function.update rs 16 (d : Word w)) m := by
  induction d with
  | zero => exact .line rfl
  | succ d ih =>
    let t := Function.update rs (16 : R) (d : Word w)
    have h : Flow.Exec pub st (.line (.binary .add 16 16 15)) t m [.tick]
        (Function.update rs 16 ((d+1 : ℕ) : Word w)) m := by
      apply Flow.Exec.line
      simp [Op.effect,BinaryOp.eval,t,one]
    simpa only [degreeCode,List.replicate_succ',List.replicate_one] using ih.seq h

private def tailCode : Code := straight (.publicWord 7 3) [
  .publicWord 9 6, .publicWord 19 9, .copy 12 9, .copy 13 1,
  .binary .add 10 16 16, .binary .mul 10 10 9, .binary .add 10 10 15,
  .binary .add 14 3 17, .binary .mul 14 10 14, .binary .add 14 9 14,
  .binary .add 2 14 19, .copy 18 2,
  .binary .mul 11 9 9, .binary .mul 11 11 11, .binary .mul 11 11 9, .binary .add 11 2 11]

/-- Native program that constructs the fixed degree in register 16 and uses the loaded header
words to compute the private frame addresses. -/
def arithmetic (degree : ℕ) : Code := .seq (degreeCode degree) tailCode

/-- Word distance between consecutive node argument packets, equal to twice the degree times
the public input length plus one. -/
def argumentStride (pub : Fin 11 → Word w) (degree : ℕ) : Word w :=
  2*(degree : Word w)*pub 6+1

/-- Histogram base as a machine word, obtained by skipping one argument packet per address
below the exclusive end of the node rows. -/
def histWord (pub : Fin 11 → Word w) (rs : Regs w 24) (degree : ℕ) : Word w :=
  pub 6 + argumentStride pub degree * (rs 3 + rs 17)

/-- Base word of the graph arena and its geometry frame, immediately after the histogram's
public number of label slots. -/
def graphWord (pub : Fin 11 → Word w) (rs : Regs w 24) (degree : ℕ) : Word w :=
  histWord pub rs degree + pub 9

private def tailBank (pub : Fin 11 → Word w) (s : Regs w 24) : Regs w 24 :=
  let n := pub 6
  let square := n*n
  let degree2 := s 16+s 16
  let stride := degree2*n+s 15
  let rows := s 3+s 17
  let hist := n+stride*rows
  let G := hist+pub 9
  let fields : List (R × Word w) := [(7,pub 3),(9,n),(19,pub 9),(12,n),(13,s 1),
    (10,degree2),(10,degree2*n),(10,stride),
    (14,rows),(14,stride*rows),(14,hist),(2,G),(18,G),
    (11,square),(11,square*square),(11,square*square*n),(11,G+square*square*n)]
  fields.foldl (fun rs j => Function.update rs j.1 j.2) s

/-- Register bank obtained by installing the degree in register 16 and carrying out the frame
arithmetic updates in instruction order. -/
def arithmeticBank (pub : Fin 11 → Word w) (rs : Regs w 24) (degree : ℕ) :=
  tailBank pub (Function.update rs 16 (degree : Word w))

/-- The fixed post-read program emits only ticks, for an exact cost of the
degree plus eighteen native instructions. -/
theorem arithmetic_run (pub : Fin 11 → Word w) (st : Word w) (m : Memory w)
    (rs : Regs w 24) (degree : ℕ) (one : rs 15 = 1) :
    Flow.Exec pub st (arithmetic degree) rs m (List.replicate (degree+18) .tick)
      (arithmeticBank pub rs degree) m := by
  let s := Function.update rs (16 : R) (degree : Word w)
  have tail : Flow.Exec pub st tailCode s m (List.replicate 17 .tick) (tailBank pub s) m :=
    (Flow.once_sound pub st false _ s m rfl).1
  rw [show degree+18 = (degree+1)+17 by omega,List.replicate_add]
  exact (degree_run pub st m rs one degree).seq tail

/-- Register equations after address computation, including the graph, histogram and cache
bases, the frame fields, and preservation of the loaded descriptor registers. -/
structure ArithmeticValues (pub : Fin 11 → Word w) (rs : Regs w 24) (degree : ℕ) (out : Regs w 24) : Prop where
  graph : out 2 = graphWord pub rs degree
  shadow : out 7 = pub 3
  length : out 9 = pub 6
  iterations : out 10 = 2*(degree : Word w)*(pub 6)+1
  cache : out 11 = graphWord pub rs degree + (pub 6)^5
  copyLength : out 12 = pub 6
  role : out 13 = rs 1
  histogram : out 14 = histWord pub rs degree
  cursor : out 18 = graphWord pub rs degree
  preserved : ∀ i ∈ ([0,1,3,4,5,6,8,15,17] : List R), out i = rs i

theorem arithmetic_values (pub : Fin 11 → Word w) (rs : Regs w 24) (degree : ℕ) (one : rs 15 = 1) :
    ArithmeticValues pub rs degree (arithmeticBank pub rs degree) := by
  let stride := ((degree : Word w)+degree)*pub 6+rs 15
  let histogram := pub 6 + stride*(rs 3+rs 17)
  let graph := histogram+pub 9
  have hs : stride = argumentStride pub degree := by simp only [stride,argumentStride,one,two_mul]
  have hh : histogram = histWord pub rs degree := by simp only [histogram,histWord,hs]
  have hg : graph = graphWord pub rs degree := by simp only [graph,graphWord,hh]
  refine ⟨hg,rfl,rfl,hs,?_,rfl,rfl,hh,hg,?_⟩
  · change graph + (pub 6*pub 6)*(pub 6*pub 6)*pub 6 = _
    rw [hg]; ring
  · intro i hi
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl

end PairSimulation.NativeFrame

end VPVNP
end Computability
end OAI
