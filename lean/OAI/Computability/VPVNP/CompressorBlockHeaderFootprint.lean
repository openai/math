import OAI.Computability.VPVNP.CompressorBlockHeaderRun
import OAI.Computability.VPVNP.CompressorFormulaFootprint

/-!
# Read and write addresses of the compressor's header visits

All reads of the initial scalar publisher come from the immutable cursor
bank in level zero. The relabel and successor workers read the old header.
The head publisher reads the new level's dimensions and level zero's
capacity. Their report logs can therefore be replayed on memories agreeing
from the first level header onwards.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.BlockHeaderFootprint

open BurstRAM Compression PhaseRecipe DescriptorSpace BlockHeaderRun SourceTransport
open scoped Fin.CommRing
open private fields nextVertices from OAI.Computability.VPVNP.CompressorDescriptorScalars
open private loadAt rowCount capacity firstColumn from OAI.Computability.VPVNP.CompressorDescriptorHeads

variable {w a b c : ℕ} {k : Type*} [_root_.Field k] {S : BlockSchedule k} {B : S.Templates}
  {R : Type*} [CommRing R] {f : B.Entry → R} {hf : B.IsSolution f}

/-- External addresses at or above the first level header, where descriptor data are read and
written. -/
abbrev Data (L : Layout) (address : ℕ) := levelStart L 0 ≤ address

private theorem room (L : Layout) (i : Fin L.levels) (fit : endAddress L < 2^w) :
    levelStart L i+levelHeaderWords L < 2^w := by
  have h := level_room L fit i
  have eqn : levelStart L (i.val+1) = levelStart L i + levelWords L := by
    simp [levelStart,Nat.succ_mul,Nat.add_assoc]
  rw [eqn] at h
  unfold levelWords at h
  omega

private theorem data_cell (L : Layout) (i : Fin L.levels) (fit : endAddress L < 2^w)
    {j : ℕ} (hj : j < levelHeaderWords L) : Data L (header w L i + (j : Word w)).val := by
  have h := room L i fit
  change levelStart L 0 ≤ (((levelStart L i : ℕ) : Word w)+(j : Word w)).val
  rw [← Nat.cast_add,Fin.val_natCast,Nat.mod_eq_of_lt (by omega)]
  exact (levelStart_mono L (Nat.zero_le i.val)).trans (Nat.le_add_right ..)

private theorem header_from (L : Layout) (base : Word w) (pub : Fin 5 → Word w) (m : Memory w)
    (j : ℕ) (h : Data L (base+(j : Word w)).val) : (Expr.header j).ReadsFrom (Data L) pub base m :=
  ⟨⟨trivial,trivial⟩,h⟩

private theorem fields_from (p : Scalars.Pass a b) (x y z : Expr) (data : ℕ → Prop)
    (pub : Fin 5 → Word w) (s : Word w) (m : Memory w)
    (hx : x.ReadsFrom data pub s m) (hy : y.ReadsFrom data pub s m) (hz : z.ReadsFrom data pub s m)
    (j : Fin 6) : (fields p x y z j).ReadsFrom data pub s m := by
  fin_cases j <;> simp [fields,Expr.div,Expr.ReadsFrom,hx,hy,hz]

private theorem scalar_writes (L : Layout) (i : Fin L.levels) (fit : endAddress L < 2^w)
    (six : 6 ≤ L.shape.scalarFields) (src : Word w) (m : Memory w) (row : FormulaRow 3)
    (dest : row.dest = .publicWord 0) :
    Writes (Data L) (scalarReport row src (header w L i) m).events := by
  apply row.report_writes
  intro j
  rw [dest]
  change Data L (header w L i+(j.val : Word w)).val
  exact data_cell L i fit (by have := j.isLt; unfold levelHeaderWords; omega)

theorem initial_scalar (L : Layout) (nonempty : 0 < L.levels) (fourteen : 14 ≤ L.shape.scalarFields)
    (fit : endAddress L < 2^w) (p : Scalars.Pass a b) (m : Memory w) :
    let base := header w L 0
    let es := (scalarReport (Scalars.initialRow p) (base+6) base m).events
    Reads (Data L) es ∧ Writes (Data L) es := by
  let z : Fin L.levels := ⟨0,nonempty⟩
  let base := header w L 0
  let pub := scalarPorts base
  have load (j : ℕ) (hj : j < 8) : (Expr.header j).ReadsFrom (Data L) pub (base+6) m := by
    apply header_from
    rw [show base+6+(j : Word w) = header w L 0+((6+j : ℕ) : Word w) by simp [base,add_assoc]]
    exact data_cell L z fit (by unfold levelHeaderWords; omega)
  constructor
  · apply (Scalars.initialRow p).report_reads
    · trivial
    · intro j
      exact fields_from p ((Expr.header 3).mul (.header 4)) (.header 2) (.header 5) (Data L) pub (base+6) m
        ⟨load 3 (by decide),load 4 (by decide)⟩
        (load 2 (by decide)) (load 5 (by decide)) j
  · exact scalar_writes L z fit (by omega) (base+6) m _ rfl

theorem advance_scalar (L : Layout) (i j : Fin L.levels) (six : 6 ≤ L.shape.scalarFields)
    (fit : endAddress L < 2^w) (p : Scalars.Pass a b) (q : Scalars.Pass b c) (m : Memory w) :
    let es := (scalarReport (Scalars.advanceRow p q) (header w L i) (header w L j) m).events
    Reads (Data L) es ∧ Writes (Data L) es := by
  let pub := scalarPorts (header w L j)
  let src := header w L i
  have load (x : ℕ) (hx : x < 6) : (Expr.header x).ReadsFrom (Data L) pub src m :=
    header_from L src pub m x (data_cell L i fit (by unfold levelHeaderWords; omega))
  have count : (nextVertices p).ReadsFrom (Data L) pub src m := by
    cases p with
    | shrink => exact ⟨load 0 (by decide),trivial⟩
    | refresh => exact ⟨load 0 (by decide),load 1 (by decide)⟩
    | terminal => exact load 0 (by decide)
  constructor
  · apply (Scalars.advanceRow p q).report_reads
    · trivial
    · exact fields_from q _ _ _ _ pub src m count (load 4 (by decide)) (load 3 (by decide))
  · exact scalar_writes L j fit six src m _ rfl

theorem heads (L : Layout) (i : Fin L.levels) (six : 6 ≤ L.shape.scalarFields) (fit : endAddress L < 2^w)
    (m : Memory w) : Reads (Data L) (headReport L i m).events ∧ Writes (Data L) (headReport L i m).events := by
  let z : Fin L.levels := ⟨0, by have := i.isLt; omega⟩
  let pub := headPorts (header w L i) (header w L 0)
  have old (j : ℕ) (hj : j < 3) : (loadAt 0 j).ReadsFrom (Data L) pub 0 m :=
    ⟨⟨trivial,trivial⟩,data_cell L i fit (by unfold levelHeaderWords; omega)⟩
  have first (j : ℕ) (hj : j < 3) : (loadAt 1 j).ReadsFrom (Data L) pub 0 m :=
    ⟨⟨trivial,trivial⟩,data_cell L z fit (by unfold levelHeaderWords; omega)⟩
  have nr : rowCount.ReadsFrom (Data L) pub 0 m := ⟨⟨old 0 (by decide),old 2 (by decide)⟩,old 1 (by decide)⟩
  have nc : (capacity L.shape).ReadsFrom (Data L) pub 0 m := ⟨⟨first 0 (by decide),first 2 (by decide)⟩,trivial⟩
  have col : (firstColumn L.shape).ReadsFrom (Data L) pub 0 m := ⟨trivial,trivial⟩
  constructor
  · apply (DescriptorHeads.publisher L.shape).report_reads
    · exact ⟨trivial,trivial⟩
    · intro j
      change (if j.val < 6 then _ else _ : Expr).ReadsFrom (Data L) pub 0 m
      by_cases hj : j.val < 6
      · rw [ite_eq_left hj]; exact ⟨col,⟨trivial,nr⟩⟩
      · rw [ite_eq_right hj]; exact ⟨⟨col,⟨trivial,nc⟩⟩,⟨trivial,⟨nc,trivial⟩⟩⟩
  · apply (DescriptorHeads.publisher L.shape).report_writes
    intro j
    change Data L (header w L i+(L.shape.scalarFields : Word w)+(j.val : Word w)).val
    rw [show header w L i+(L.shape.scalarFields : Word w)+(j.val : Word w) =
      header w L i+((L.shape.scalarFields+j.val : ℕ) : Word w) by simp [add_assoc]]
    exact data_cell L i fit (by unfold levelHeaderWords; have := j.isLt; omega)

private theorem join_reads {data : ℕ → Prop} {xs ys : List (Event w)} (hx : Reads data xs) (hy : Reads data ys) :
    Reads data (xs++ys) := fun a v h ↦ (List.mem_append.mp h).elim (hx a v) (hy a v)

private theorem join_writes {data : ℕ → Prop} {xs ys : List (Event w)} (hx : Writes data xs) (hy : Writes data ys) :
    Writes data (xs++ys) := fun a v h ↦ (List.mem_append.mp h).elim (hx a v) (hy a v)

/-- The complete three-report header log is confined to the descriptor data
suffix, including reads used to compute array capacities from level zero. -/
theorem substep (v : SelectedLevel B f hf) (L : Layout) (i j : Fin L.levels)
    (six : 6 ≤ L.shape.scalarFields) (fit : endAddress L < 2^w) (m : Memory w) :
    Reads (Data L) (eventLog (reports v L i j m)) ∧ Writes (Data L) (eventLog (reports v L i j m)) := by
  have h₁ := advance_scalar L i i six fit (.terminal v.inputExponent) (Scalars.ofOrigin v.origin) m
  have h₂ := advance_scalar L i j six fit (Scalars.ofOrigin v.origin) (.terminal v.outputExponent)
    (inputMemory v L i m)
  have h₃ := heads L j six fit (outputMemory v L i j m)
  simp only [reports,eventLog,List.flatMap_cons,List.flatMap_nil,List.append_nil]
  exact ⟨join_reads h₁.1 (join_reads h₂.1 h₃.1), join_writes h₁.2 (join_writes h₂.2 h₃.2)⟩

theorem initial (L : Layout) (nonempty : 0 < L.levels) (fourteen : 14 ≤ L.shape.scalarFields)
    (fit : endAddress L < 2^w) (a : ℕ) (m : Memory w) :
    let start := header w L 0
    let es := eventLog [scalarReport (Scalars.initialRow (.terminal a)) (start+6) start m,
      headReport L 0 (initialMemory a L m)]
    Reads (Data L) es ∧ Writes (Data L) es := by
  have h₁ := initial_scalar L nonempty fourteen fit (.terminal a) m
  have h₂ := heads L ⟨0,nonempty⟩ (by omega) fit (initialMemory a L m)
  simp only [eventLog,List.flatMap_cons,List.flatMap_nil,List.append_nil]
  exact ⟨join_reads h₁.1 h₂.1,join_writes h₁.2 h₂.2⟩

end CompressorRecords.BlockHeaderFootprint

end VPVNP
end Computability
end OAI
