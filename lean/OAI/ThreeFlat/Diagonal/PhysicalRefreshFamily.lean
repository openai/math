import OAI.ThreeFlat.Diagonal.PhysicalRecordFamily
import OAI.ThreeFlat.Diagonal.PhysicalRecordAlphabet
import OAI.ThreeFlat.Diagonal.PhysicalCardinalTransport
import OAI.ThreeFlat.Diagonal.PhysicalRefreshCopies

namespace OAI
/-! # Refresh branches in the exact native row and symbol order -/

namespace ThreeFlat.Diagonal.PhysicalStage

open Computability.VPVNP.Compression CompressorPacking MotifOuterTerms
open scoped Classical BigOperators
noncomputable section

variable {F : Type} [Field F] {s rem h pad : ℕ} {c : Fin (2^s) → Fin (2^s) → ℕ} {C γ : ℝ}
  (T : RefreshMotif.Table F c (1+h+pad) C) (A : State (2^s) (s+rem))

/-- Native rows use the old base ordinal as the high coordinate and the
remaining binary lane as the low coordinate. -/
def refreshBlockOrder : A.Base × BitWord rem ≃ Fin (Fintype.card A.Base*2^rem) :=
  (A.order.prodCongr (Native.tagOrdinal rem)).trans finProdFinEquiv

theorem refreshBlockOrder_val (z : A.Base × BitWord rem) :
    (refreshBlockOrder A z).val=(A.order z.1).val*2^rem+(Native.tagOrdinal rem z.2).val := by
  change _+_*_=_*_+_
  ac_rfl

abbrev refreshBinaryInput := refreshInput A (splitWord s rem) (Native.tagOrdinal s).symm
abbrev refreshBinaryGraph := changeLanes A.graph (splitWord s rem)
abbrev refreshBinaryEntry (z : A.Base × BitWord rem) :=
  T.entry (refreshBinaryGraph A) (Native.tagOrdinal s).symm (refreshBinaryInput A) z
abbrev refreshBinaryCopies (z : A.Base × BitWord rem) :=
  T.repeats (refreshBinaryGraph A) (Native.tagOrdinal s).symm (refreshBinaryInput A) z
abbrev refreshBinaryBranches := refreshBranches T A (splitWord s rem) (Native.tagOrdinal s).symm

variable (hm : 2≤2^s) (hh : 0<h) (sym : ∀ i j,c i j=c j i) (rows : ∀ i,∑ j,c i j=h)
  (zero : ∀ i,c i i=0) (conn : Expander.Bound (Expander.transition c h) ℝ γ)

open private refreshRules_count from OAI.ThreeFlat.Diagonal.PhysicalStageRefresh in
theorem refreshBinaryBranchCount :
    (refreshBinary T A hm hh sym rows zero conn).rules.count = Fintype.card (refreshBinaryBranches T A) := by
  calc
    _ = _ := refreshRules_count T A (splitWord s rem) (Native.tagOrdinal s).symm hm hh sym rows zero conn
    _ = _ := congrArg (fun inst : Fintype (refreshBinaryBranches T A) => @Fintype.card _ inst)
      (Subsingleton.elim _ _)

/-- The ordinal of the selected physical refresh row, expressed in the native branch coordinates. -/
def refreshBinaryBranchOrder :
    Fin (refreshBinary T A hm hh sym rows zero conn).rules.count ≃ refreshBinaryBranches T A :=
  (finCongr (refreshBinaryBranchCount T A hm hh sym rows zero conn)).trans
    (Fintype.equivFin (refreshBinaryBranches T A)).symm

def refreshBinaryFamily : RecordFamily (refreshBinary T A hm hh sym rows zero conn).rules.count where
  motifs := Fintype.card A.Base*2^rem
  alphabet i := (refreshBinaryEntry T A ((refreshBlockOrder A).symm i)).Alphabet
  finiteAlphabet _ := inferInstance
  copies i := refreshBinaryCopies T A ((refreshBlockOrder A).symm i)
  order := (refreshBinaryBranchOrder T A hm hh sym rows zero conn).trans
    (Equiv.piCongrLeft' (fun z=>Histogram (refreshBinaryEntry T A z).Alphabet (refreshBinaryCopies T A z))
      (refreshBlockOrder A))

local notation "R" => refreshBinaryFamily T A hm hh sym rows zero conn

@[simp] theorem refreshBinaryFamily_motifs : (R).motifs=Fintype.card A.Base*2^rem := rfl

theorem refreshBinaryFamily_entry (i : Fin (R).motifs) :
    (R).alphabet i = (refreshBinaryEntry T A ((refreshBlockOrder A).symm i)).Alphabet := rfl

@[simp] theorem refreshBinaryFamily_copies (i : Fin (R).motifs) :
    (R).copies i=refreshBinaryCopies T A ((refreshBlockOrder A).symm i) := rfl

/-- Every symbol count installed by the stage record comes from the
same histogram that indexes the physical successor label. -/
theorem refreshBinaryFamily_order (j : Fin (refreshBinary T A hm hh sym rows zero conn).rules.count)
    (i : Fin (R).motifs) :
    (R).order j i=(refreshBinaryBranchOrder T A hm hh sym rows zero conn j) ((refreshBlockOrder A).symm i) := rfl

theorem refreshBinaryFamily_symbol (j : Fin (refreshBinary T A hm hh sym rows zero conn).rules.count)
    (i : Fin (R).motifs) (b : Fin (Fintype.card ((R).alphabet i))) :
    (((R).order j i).val ((Fintype.equivFin ((R).alphabet i)).symm b)).val =
      (((refreshBinaryBranchOrder T A hm hh sym rows zero conn j) ((refreshBlockOrder A).symm i)).val
        ((Fintype.equivFin ((R).alphabet i)).symm b)).val := rfl

theorem refreshBinaryFamily_symbols (i : Fin (R).motifs) :
    Fintype.card ((R).alphabet i)≤refreshSymbolBound T :=
  Finset.le_sup (s:=Finset.univ) (f:=fun j=>Fintype.card (T.block j).Alphabet) (Finset.mem_univ _)

theorem refreshBinaryFamily_fits {K W : ℕ} (symbols : refreshSymbolBound T≤K)
    (word : (1+2*(2^s)*(2^s))*(1+A.maxWidth)<2^W) : (R).Fits K W :=
  ⟨fun i => (refreshBinaryFamily_symbols T A hm hh sym rows zero conn i).trans symbols,
   fun i => (refreshCopies_le T A (splitWord s rem) (Native.tagOrdinal s).symm
     ((refreshBlockOrder A).symm i)).trans_lt word⟩

theorem refreshBinaryFamily_width {K W : ℕ} (fit : (R).Fits K W) :
    ((R).record fit).width=(Fintype.card A.Base*2^rem)*K*W := rfl

theorem refreshBinaryFamily_words {K W : ℕ} (fit : (R).Fits K W)
    (j : Fin (refreshBinary T A hm hh sym rows zero conn).rules.count)
    (i : Fin (R).motifs) (v : (R).alphabet i) :
    (HistogramRegister.words ((R).rows fit) ((R).sequence fit j) i
      ((Fintype.equivFin _ v).castLE (fit.1 i))).val =
      (((refreshBinaryBranchOrder T A hm hh sym rows zero conn j) ((refreshBlockOrder A).symm i)).val v).val :=
  (R).words_val fit j i v

/-- Parsing the chronological raw register bits identifies precisely the
same refresh branch as the tensor rewrite, including zero padding. -/
theorem refreshBinaryFamily_decode {K W : ℕ} (fit : (R).Fits K W)
    (raw : HistogramRegister.Words (R).motifs K W)
    (j : Fin (refreshBinary T A hm hh sym rows zero conn).rules.count) :
    ((R).record fit).read (List.ofFn (HistogramRegister.bitTable raw))=some j ↔
      raw=HistogramRegister.words ((R).rows fit) ((R).sequence fit j) := by
  constructor
  · intro h
    have eqn := ((R).record fit).write_read _ _ h
    apply HistogramRegister.bitTable.injective
    apply List.ofFn_inj.mp
    exact eqn.symm
  · rintro rfl
    exact ((R).record fit).read_write j

end
end ThreeFlat.Diagonal.PhysicalStage

end OAI
