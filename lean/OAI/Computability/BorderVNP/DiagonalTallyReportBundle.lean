import OAI.Computability.BorderVNP.DiagonalTallyReportDriver

/-! # Executing the complete native kernel for a delivered bottom bundle -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace DiagonalTallyCellReports

open VPVNP.BurstRAM RoutingISA DiagonalResidueRAM DiagonalTallyPacketEmit
open DiagonalTallyBits TallySidecar
open Packing.BottomReports
open private decoded_field from OAI.Computability.BorderVNP.PackedReportWriterDecoded

/-- Chronological write of the packed metadata, the private checker bindings, and the
actual reference and descriptor tables for all copies of the marked positions. -/
def bundleImage {w : ℕ} (m : Memory w) (f : DiagonalTallyOperandArray.Frame) (g : Writer.Frame)
    (H : ℕ) (ps : List Position) (rel : ℕ → ℕ) : ℕ → ℕ :=
  f.image .unary (Writer.write (readings (outputMemory m g.side (words H ps))) g.dst
    (((g.rows rel ps.length)++[g.zeroRow ps.length]).flatMap CellSparse.Packet.record))

/-- All output cursors of the current bundle, including the private-stack report cursor. -/
structure BundleResult (f : DiagonalTallyOperandArray.Frame) (g : Writer.Frame)
    (n : ℕ) (r : Reg → ℕ) : Prop where
  /-- Persistent decoded metadata immediately after the count and triples. -/
  packed : r 20=f.side+1+3*n
  /-- Compact external use-report pointer after all marked copies. -/
  external : r 22=f.external+f.nrefs .unary
  /-- Corresponding use cursor inside the private macro assignment. -/
  privateUse : r 24=g.useStart+n*g.copies
  /-- Supplemental checker packet cursor, including the zero-padding row. -/
  supplement : r 28=g.dst+9*n+6
  /-- Number of supplemental records, including the padding record. -/
  supplementCount : r 29=g.previousRows+n+1
  /-- Next five-word operand descriptor. -/
  descriptors : r 30=f.descriptors+5*f.nrows .unary
  /-- Next indirect bit-address vector. -/
  refs : r 31=f.refs+f.nrefs .unary
  /-- Accumulated local operand count. -/
  operands : r 32=f.prior+f.nrows .unary

/-- Exact physical execution on a genuine decoded box, with no table of selected rows
in the common advice. The number of copies affects the operand writer and the lane
strides, while the sidecar is read just once per bottom bundle. -/
theorem bundleKernel_runs {w : ℕ} (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
    (s : Bank w) (m : Memory w) (f : DiagonalTallyOperandArray.Frame) (g : Writer.Frame)
    (p H : ℕ) (ps : List Position) (rel : ℕ → ℕ)
    (load : f.Loaded (readings s)) (lg : g.loaded (.ofWords s m))
    (fit : f.Fits .unary w) (fg : g.Fits w ps.length rel)
    (marks : f.marked=ps.length) (hp : (s 16).val=p) (hh : (s 17).val=H) (hw : H ≤ w)
    (rawRoom : p+(1+3*ps.length)*H<2^w) (sideRoom : g.side+(1+3*ps.length)<2^w)
    (separate : p+(1+3*ps.length)*H ≤ g.side ∨ g.side+(1+3*ps.length) ≤ p)
    (valid : Fits H ps) (raw : WordsAt m p (words H ps))
    (rows : ∀ i (hi : i<ps.length), rel i=ps[i].stagedReportRel)
    (refSep : f.side<f.refs) (descSep : f.side<f.descriptors) :
    ∃ es t mt, Runs pub mac bundleKernel s m es t mt ∧
      traceCost es ≤ TallySidecar.headerSetup.slots+DiagonalTallyBits.ticks 1 H+rowsSetup.slots+
        DiagonalTallyBits.ticks (3*ps.length) H+(28*ps.length+23)+f.cost .unary+advancePacked.slots ∧
      readings mt=bundleImage m f g H ps rel ∧ BundleResult f g ps.length (readings t) := by
  have side : f.side=g.side := load.side.symm.trans lg.1.2.1
  obtain ⟨a,t₁,m₁,r₁,c₁,h₁⟩ := Writer.decode_write_runs pub mac s m g p H ps rel lg fg hp hh hw
    rawRoom sideRoom separate valid raw rows
  have l₁ : f.Loaded (readings t₁) := by
    obtain ⟨a,b,c,d,e,h,i,j,k,l⟩ := load
    constructor <;> first | exact (congrArg Fin.val (r₁.keepsReg (by decide))).trans a
                          | exact (congrArg Fin.val (r₁.keepsReg (by decide))).trans b
                          | exact (congrArg Fin.val (r₁.keepsReg (by decide))).trans c
                          | exact (congrArg Fin.val (r₁.keepsReg (by decide))).trans d
                          | exact (congrArg Fin.val (r₁.keepsReg (by decide))).trans e
                          | exact (congrArg Fin.val (r₁.keepsReg (by decide))).trans h
                          | exact (congrArg Fin.val (r₁.keepsReg (by decide))).trans i
                          | exact (congrArg Fin.val (r₁.keepsReg (by decide))).trans j
                          | exact (congrArg Fin.val (r₁.keepsReg (by decide))).trans k
                          | exact (congrArg Fin.val (r₁.keepsReg (by decide))).trans l
  let before := readings (outputMemory m g.side (words H ps))
  let rows' := ((g.rows rel ps.length)++[g.zeroRow ps.length]).flatMap CellSparse.Packet.record
  have out₁ : readings m₁=Writer.write before g.dst rows' := h₁.image
  have len : rows'.length=9*ps.length+6 := by
    simp [rows',List.flatMap_append,g.rows_words_length,Writer.Frame.zeroRow,CellSparse.Packet.record,CellSparse.Packet.port]
  have hdr₁ : (m₁ f.side).val=f.marked := by
    change readings m₁ f.side=_
    rw [out₁,side,Writer.write_outside _ _ _ _ (by rw [len]; have := fg.disjoint; omega),marks]
    have hd := decoded_field m g.side H ps hw valid 0 (by simp [fields])
    simpa [before,readings,fields] using hd
  obtain ⟨b,t₂,m₂,r₂,c₂,h₂,ext,desc,refs,oper⟩ :=
    DiagonalTallyOperandArray.writer_runs f .unary pub mac t₁ m₁ l₁ fit hdr₁
  have img : readings m₂=bundleImage m f g H ps rel := by rw [h₂,out₁]; rfl
  have hdr₂ : (m₂ f.side).val=f.marked := by
    change readings m₂ f.side=_
    rw [h₂,DiagonalTallyOperandArray.Frame.image,written_before _ _ _ descSep,written_before _ _ _ refSep]
    exact hdr₁
  have ptr : (t₂ 20).val=f.side := (congrArg Fin.val (r₂.keepsReg (by decide))).trans l₁.side
  have hs := fit.sideEnd
  have hm := fit.small
  have hwpos : w≠0 := by rintro rfl; simp at hm
  have safe : advancePacked.safeReadOnly w (readings pub) (readings m₂) (readings t₂) := by
    simp [advancePacked,Code.block,Code.safeReadOnly,Code.evalNat,Function.update,addressOpFits,addressOp,
      readings,ptr,hdr₂,hwpos]; omega
  obtain ⟨c,t₃,r₃,c₃,e₃⟩ := advancePacked.runReadOnly pub mac m₂ t₂ safe
  have pack : readings t₃ 20=f.side+1+3*ps.length := by
    rw [e₃]
    simp [advancePacked,Code.block,Code.evalNat,Function.update,addressOp,readings,ptr,hdr₂,marks]; omega
  refine ⟨_,_,_,r₁.seq (r₂.seq r₃),?_,img,?_⟩
  · unfold traceCost
    simp only [VPVNP.RAMBuckets.cost_append]
    change traceCost a+(traceCost b+traceCost c) ≤ _
    omega
  · have keep (j : Reg) (h : advancePacked.keeps j=true) := congrArg Fin.val (r₃.keepsReg h)
    have keep' (j : Reg) (h : (DiagonalTallyOperandArray.writer .unary).keeps j=true) :=
      congrArg Fin.val (r₂.keepsReg h)
    exact ⟨pack,(keep 22 (by decide)).trans ext,
      (keep 24 (by decide)).trans ((keep' 24 (by decide)).trans h₁.useLane),
      (keep 28 (by decide)).trans ((keep' 28 (by decide)).trans h₁.output),
      (keep 29 (by decide)).trans ((keep' 29 (by decide)).trans h₁.count),
      (keep 30 (by decide)).trans desc,(keep 31 (by decide)).trans refs,(keep 32 (by decide)).trans oper⟩

end DiagonalTallyCellReports

end BorderVNP
end Computability
end OAI
