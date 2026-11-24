import OAI.Computability.VPVNP.LivePublicExpr
import OAI.Computability.VPVNP.PrimedCounterData

/-!
# Reconstructing the public words of the primed pair parser

In Section 14 the live evaluator reproduces the auxiliary machine's finite
table. Its last eighteen public words specify scratch addresses, parser
dimensions and schedule endpoints. Their expressions below use the first
sixteen public words together with the prescribed grammar-state count and
root. They use only length data and fixed arithmetic, independently of
pair-specific cut lengths, exterior bits and nominations.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveProgram.ParserPublic

open BurstRAM PrimedInputRAM PrimedStackRAM PrimedCounter
open scoped Fin.CommRing

/-- Length expressions for the assembler's public operands, the grammar state count, and the
root state. -/
structure Inputs where
  /-- The sixteen public operands of the primed input assembler. -/
  assembler : Fin 16 → PublicExpr
  /-- Public expression for the number of grammar states. -/
  states : PublicExpr
  /-- Public expression for the grammar's root state ordinal. -/
  root : PublicExpr

namespace Inputs

variable (x : Inputs)

/-- Input length recovered from the assembler's second operand. -/
def n := x.assembler 1
/-- Number of sites per group recovered from the assembler's third operand. -/
def R := x.assembler 2
/-- Total number of input cells for both groups, taken from the assembler's first operand. -/
def rectangle := x.assembler 0
/-- Base of the second-pass assembled input rectangle, immediately after the first-pass choice
rectangle. -/
def base := (x.assembler 6).add x.rectangle
/-- Base of the parser's degree stack, immediately after the assembled input rectangle. -/
def degreeBase := x.base.add x.rectangle
/-- Base of the parser's state stack, one input length past the degree stack base. -/
def stateBase := x.degreeBase.add x.n
/-- Base of the terminal-position mark array, one input length past the state stack base. -/
def markBase := x.stateBase.add x.n
/-- Base of the label histogram, one input length past the mark array base. -/
def histBase := x.markBase.add x.n
/-- Largest zero-based degree index for the full-degree grammar, the input length minus one. -/
def degree := x.n.sub (.lit 1)
/-- Number of positive binary degree splits over degrees through the input length. -/
def triangle := (x.n.mul x.degree).divConst 2
/-- Number of terminal production labels, with one for each state, input position, and Boolean
bit. -/
def terminal := (x.states.mul x.n).mul (.lit 2)
/-- Number of binary production labels, with one for each degree split and ordered triple of
states. -/
def binary := ((x.triangle.mul x.states).mul x.states).mul x.states
/-- Total number of terminal and binary production labels checked by the parser. -/
def labels := x.terminal.add x.binary
/-- First word beyond the reserved primed header, after three length words, two group indices,
advice, and two cut capacities. -/
def headerEnd := (((PublicExpr.lit 3).add ((.lit 2 : PublicExpr).mul (x.assembler 9))).add
  (x.assembler 10)).add ((.lit 2 : PublicExpr).mul (x.assembler 11))
/-- Number of calls across the two rectangular input assembly passes. -/
def assembly := x.rectangle.add x.rectangle
/-- Number of parser calls for each site, three times the input length. -/
def rowSpan := (PublicExpr.lit 3).mul x.n
/-- Total site rows in the two groups, twice the number of sites per group. -/
def rows := (PublicExpr.lit 2).mul x.R
/-- First call cursor of the histogram comparison phase after input assembly and all per-site
parser calls. -/
def compareStart := x.assembly.add (x.rows.mul x.rowSpan)
/-- Total number of scheduled calls through the last label comparison. -/
def total := x.compareStart.add x.labels

/-- The fourteen parser parameters in the auxiliary machine's order. -/
def parser : Fin 14 → PublicExpr :=
  Fin.append ![x.degreeBase,x.stateBase,x.markBase,x.histBase,x.histBase.add x.labels,
    x.n,x.n,x.states,x.base,x.terminal,x.labels] ![x.degree,x.root,x.headerEnd]

/-- The four bounds partition the absolute cursor into assembly, site and
final histogram-comparison calls. -/
def schedule : Fin 4 → PublicExpr := ![x.assembly,x.rowSpan,x.compareStart,x.total]

/-- Assemble the 34 public words in order from the sixteen assembler operands, the parser
operands, and the schedule operands. -/
def table : Fin 34 → PublicExpr := Fin.append x.assembler (Fin.append x.parser x.schedule)

variable {L : Lengths} {n r H w s : ℕ} {Q : Layout L n r H w}

/-- Numerical inputs to the suffix construction, before word packing. -/
structure Values (x : Inputs) (g : Geometry) (D : PrimedCounter.Data Q s) : Prop where
  assembler (j) : (x.assembler j).eval g = Opcodes.pubNat Q j
  states : x.states.eval g = s
  root : x.root.eval g = D.root.val

private theorem span_eq (n : ℕ) (hn : 0 < n) : Cursor.span n (2*n-1) = 3*n := by
  unfold Cursor.span
  omega

/-- Re-evaluating the expressions gives the native auxiliary table exactly. -/
theorem table_eval (g : Geometry) (D : PrimedCounter.Data Q s) (h : x.Values g D)
    (hd : D.degree.val+1 = n) (j : Fin 34) :
    Fin.ofNat (2 ^ w) ((x.table j).eval g) = D.pub j := by
  have hn : 0 < n := by omega
  have hdeg : n-1 = D.degree.val := by omega
  have hlabels : x.labels.eval g = D.labels := by
    simp only [labels, terminal, binary, triangle, degree, Inputs.n, PublicExpr.eval,
      h.assembler, h.states, Opcodes.pubNat, PrimedCounter.Data.labels, labelCount, Nat.choose_two_right]
    rfl
  refine Fin.addCases (m := 16) (n := 18) (fun i ↦ ?_) (fun i ↦ ?_) j
  · rw [table, Fin.append_left, h.assembler]
    change Opcodes.pubWord Q i = _
    exact (Program.public_input (Opcodes.pubWord Q) D.parserPub D.assembly (2*2^r) n (2*n-1) D.labels i).symm
  · rw [table, Fin.append_right]
    refine Fin.addCases (m := 14) (n := 4) (fun p ↦ ?_) (fun p ↦ ?_) i
    · rw [Fin.append_left]
      change _ = D.pub (Program.parserPub p)
      rw [PrimedCounter.Data.pub, Program.public_parser, PrimedCounter.Data.parserPub, parser]
      refine Fin.addCases (m := 11) (n := 3) (fun u ↦ ?_) (fun u ↦ ?_) p
      · rw [Fin.append_left, Fin.append_left]
        fin_cases u <;> simp [publicData, base, degreeBase, stateBase, markBase, histBase, Inputs.n,
          rectangle, terminal, hlabels, PublicExpr.eval, h.assembler, h.states, Opcodes.pubNat]
      · rw [Fin.append_right, Fin.append_right]
        fin_cases u <;> simp [degree,Inputs.n,headerEnd,PublicExpr.eval,h.assembler,h.root,Opcodes.pubNat,
          hdeg,Header.count]
    · rw [Fin.append_right]
      have hs := Program.public_schedule (Opcodes.pubWord Q) D.parserPub D.assembly (2*2^r) n (2*n-1) D.labels
      have he : ∀ u : Fin 4, D.pub ((u.natAdd 14).natAdd 16) =
          (![↑D.assembly, ↑(Cursor.span n (2*n-1)),
            ↑(Cursor.compareStart D.assembly (2*2^r) n (2*n-1)), ↑D.total] : Fin 4 → Word w) u := by
        intro u; fin_cases u <;> first | exact hs.1 | exact hs.2.1 | exact hs.2.2.1 | exact hs.2.2.2
      rw [he]
      fin_cases p <;> simp [schedule,assembly,rectangle,rowSpan,Inputs.n,rows,R,compareStart,total,
        Cursor.compareStart, PrimedCounter.Data.total, Cursor.calls, span_eq n hn, hlabels,
        PublicExpr.eval,h.assembler,Opcodes.pubNat, Nat.add_assoc]

/-- The existing parser bounds imply that every intermediate computation of
the suffix is word-sized. In particular, the numerator of the triangular
label count fits before it is divided by two. -/
theorem table_fits (g : Geometry) (D : PrimedCounter.Data Q s) (h : x.Values g D) (hf : D.Fits)
    (ha : ∀ i, (x.assembler i).Fits g (2 ^ w)) (hs : x.states.Fits g (2 ^ w))
    (hr : x.root.Fits g (2 ^ w)) (j : Fin 34) : (x.table j).Fits g (2 ^ w) := by
  let F := PublicExpr.Fits g (2 ^ w)
  have addF {a b : PublicExpr} (fa : F a) (fb : F b) (hb : a.eval g + b.eval g < 2^w) :
      F (.add a b) := ⟨hb,fa,fb⟩
  have mulF {a b : PublicExpr} (fa : F a) (fb : F b) (hb : a.eval g * b.eval g < 2^w) :
      F (.mul a b) := ⟨hb,fa,fb⟩
  have hn : 0 < n := (Nat.zero_le _).trans_lt D.degree.isLt
  have hpos : 0 < s := (Nat.zero_le _).trans_lt D.root.isLt
  have hR : 0 < 2^r := Nat.two_pow_pos _
  have hnV : x.n.eval g = n := h.assembler 1
  have hRV : x.R.eval g = 2 ^ r := h.assembler 2
  have hrectV : x.rectangle.eval g = positions n r := h.assembler 0
  have hbaseV : x.base.eval g = Q.scratchBase + positions n r := by
    change (x.assembler 6).eval g + x.rectangle.eval g = _; rw [h.assembler,hrectV]; rfl
  have hdegV : x.degree.eval g = n - 1 := by change x.n.eval g - 1 = _; rw [hnV]
  have htriV : x.triangle.eval g = n.choose 2 := by
    change x.n.eval g * x.degree.eval g / 2 = _; rw [hnV,hdegV,Nat.choose_two_right]
  have htermV : x.terminal.eval g = s * n * 2 := by
    change x.states.eval g * x.n.eval g * 2 = _; rw [h.states,hnV]
  have hbinV : x.binary.eval g = n.choose 2 * s * s * s := by
    change x.triangle.eval g * x.states.eval g * x.states.eval g * x.states.eval g = _
    rw [htriV,h.states]
  have hlabelV : x.labels.eval g = D.labels := by
    change x.terminal.eval g + x.binary.eval g = _; rw [htermV,hbinV]; rfl
  have hdepth : D.base + positions n r + n + n + n + D.labels < 2^w := by
    have hh := hf.scratch
    change D.base + (positions n r + (n + (n + (n + (D.labels + 1))))) ≤ 2^w at hh
    omega
  have htotal : (positions n r + positions n r) + ((2 * 2^r) * (3*n) + D.labels) < 2^w := by
    have hh := hf.cursor
    change (positions n r + positions n r) + ((2 * 2^r) * Cursor.span n (2*n-1) + D.labels) < _ at hh
    rwa [span_eq n hn] at hh
  have hhend := hf.headers
  have hheader : 3 + 2*L.index + L.advice + 2*L.cutCapacity < 2^w := by
    change (3 + 2*L.index + L.advice + 2*L.cutCapacity) + D.labels ≤ Q.scratchBase at hhend
    change Q.scratchBase + positions n r + positions n r + n + n + n + D.labels < _ at hdepth
    omega
  have f1 : F (.lit 1) := ⟨by change 1 < _; omega, trivial⟩
  have f2 : F (.lit 2) := ⟨hf.word,trivial⟩
  have f3 : F (.lit 3) := ⟨by change 3 < _; omega, trivial⟩
  have fn : F x.n := ha 1
  have fR : F x.R := ha 2
  have frect : F x.rectangle := ha 0
  have fbase : F x.base := addF (ha 6) frect (by
    change x.base.eval g < _; rw [hbaseV]; change D.base < _; omega)
  have fdBase : F x.degreeBase := addF fbase frect (by rw [hbaseV,hrectV]; change D.base + _ < _; omega)
  have fdV : x.degreeBase.eval g = D.base + positions n r := by change x.base.eval g + _ = _; rw [hbaseV,hrectV]
  have fsBase : F x.stateBase := addF fdBase fn (by rw [fdV,hnV]; omega)
  have fsV : x.stateBase.eval g = D.base + positions n r + n := by change x.degreeBase.eval g + _ = _; rw [fdV,hnV]
  have fmBase : F x.markBase := addF fsBase fn (by rw [fsV,hnV]; omega)
  have fmV : x.markBase.eval g = D.base + positions n r + n + n := by change x.stateBase.eval g + _ = _; rw [fsV,hnV]
  have fhBase : F x.histBase := addF fmBase fn (by rw [fmV,hnV]; omega)
  have fhV : x.histBase.eval g = D.base + positions n r + n + n + n := by change x.markBase.eval g + _ = _; rw [fmV,hnV]
  have fd : F x.degree := ⟨by rw [hdegV]; omega,fn,f1⟩
  have hnum : n*(n-1) < 2^w := (Nat.mul_lt_mul_of_pos_left (by omega : n-1 < n) hn).trans_le
    (by simpa [pow_two] using hf.triangle)
  have fnum := mulF fn fd (by rw [hnV,hdegV]; exact hnum)
  have ftri : F x.triangle := ⟨htriV ▸ ((Nat.choose_two_right n) ▸ ((Nat.div_le_self _ _).trans_lt hnum)),
    fnum, hf.word⟩
  have ht : s*n*2 ≤ D.labels := Nat.le_add_right ..
  have hb : n.choose 2*s*s*s ≤ D.labels := Nat.le_add_left ..
  have hlfit : D.labels < 2^w := by omega
  have hss : n.choose 2*s ≤ n.choose 2*s*s := Nat.le_mul_of_pos_right _ hpos
  have hsss : n.choose 2*s*s ≤ n.choose 2*s*s*s := Nat.le_mul_of_pos_right _ hpos
  have fterm : F x.terminal := mulF (mulF hs fn (by rw [h.states,hnV]; omega)) f2
    (by change x.terminal.eval g < _; rw [htermV]; omega)
  have fs₁ := mulF ftri hs (by rw [htriV,h.states]; omega)
  have fs₂ := mulF fs₁ hs (by change x.triangle.eval g*x.states.eval g*x.states.eval g < _; rw [htriV,h.states]; omega)
  have fbin : F x.binary := mulF fs₂ hs (by change x.binary.eval g < _; rw [hbinV]; omega)
  have flabel : F x.labels := addF fterm fbin (by change x.labels.eval g < _; rw [hlabelV]; exact hlfit)
  have fdepth := addF fhBase flabel (by rw [fhV,hlabelV]; exact hdepth)
  have fiV : (x.assembler 9).eval g = L.index := h.assembler 9
  have faV : (x.assembler 10).eval g = L.advice := h.assembler 10
  have fcV : (x.assembler 11).eval g = L.cutCapacity := h.assembler 11
  have fi := mulF f2 (ha 9) (by change 2 * _ < _; rw [fiV]; omega)
  have fc := mulF f2 (ha 11) (by change 2 * _ < _; rw [fcV]; omega)
  have fh₁ := addF f3 fi (by change 3 + 2 * _ < _; rw [fiV]; omega)
  have fh₂ := addF fh₁ (ha 10) (by change 3 + 2*(x.assembler 9).eval g + _ < _; rw [fiV,faV]; omega)
  have fheader : F x.headerEnd := addF fh₂ fc
    (by change 3 + 2*(x.assembler 9).eval g + (x.assembler 10).eval g + 2*(x.assembler 11).eval g < _
        rw [fiV,faV,fcV]; exact hheader)
  have hrow := Nat.le_mul_of_pos_left (3*n) (by omega : 0 < 2 * 2^r)
  have hsites := Nat.le_mul_of_pos_right (2*2^r) (by omega : 0 < 3*n)
  have fspan : F x.rowSpan := mulF f3 fn (by change 3 * _ < _; rw [hnV]; omega)
  have frows : F x.rows := mulF f2 fR (by change 2 * _ < _; rw [hRV]; omega)
  have fassembly : F x.assembly := addF frect frect (by rw [hrectV]; omega)
  have fvisits := mulF frows fspan (by change (2*x.R.eval g)*(3*x.n.eval g) < _; rw [hRV,hnV]; omega)
  have fcompare : F x.compareStart := addF fassembly fvisits
    (by change x.rectangle.eval g+x.rectangle.eval g+(2*x.R.eval g)*(3*x.n.eval g) < _; rw [hrectV,hRV,hnV]; omega)
  have ftotal : F x.total := addF fcompare flabel (by
    change x.rectangle.eval g+x.rectangle.eval g+(2*x.R.eval g)*(3*x.n.eval g)+x.labels.eval g < _
    rw [hrectV,hRV,hnV,hlabelV]; omega)
  refine Fin.addCases (m := 16) (n := 18) (fun i ↦ ?_) (fun i ↦ ?_) j
  · simpa only [table, Fin.append_left] using ha i
  · rw [table, Fin.append_right]
    refine Fin.addCases (m := 14) (n := 4) (fun p ↦ ?_) (fun p ↦ ?_) i
    · rw [Fin.append_left, parser]
      refine Fin.addCases (m := 11) (n := 3) (fun u ↦ ?_) (fun u ↦ ?_) p
      · rw [Fin.append_left]; fin_cases u <;> assumption
      · rw [Fin.append_right]; fin_cases u <;> assumption
    · rw [Fin.append_right]; fin_cases p <;> assumption

end Inputs
end LiveProgram.ParserPublic

end VPVNP
end Computability
end OAI
