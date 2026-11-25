import OAI.ThreeFlat.Diagonal.PhysicalShrinkPre
import OAI.ThreeFlat.Diagonal.CompressorChartPublication

namespace OAI
/-! # The complete guard precondition from the actual stored old graph and untrusted histogram bits -/
namespace ThreeFlat.Diagonal.PhysicalStage
open Computability.VPVNP.BurstRAM PrivateRAM RAM RAM.DescriptorScan Computability.VPVNP.Compression CompressorPacking
open Native Native.ShrinkStage Native.ShrinkStage.Resident Native.Placement
open NavigationDirectory NavigationPass PhysicalShrink ShrinkStageNav MotifIntegerChoice
open scoped Classical Fin.NatCast
noncomputable section
private theorem palette_two (degree : ℕ) : 2≤2*(2^degree)+1 := by
  have := Nat.two_pow_pos degree
  omega

variable {F : Type} [Field F] (T : ShrinkMotif.Table F) (s D rem : ℕ) (hD : 0<D)
variable (small : ((2^(2*(2^s)+1)*(2^s)*(2^s):ℕ):ℝ)/D≤1/1024) (A : State (2^s) (shrinkCharge s+rem))
local notation "M" => shrinkBinary T s D rem hD small A
local notation "Q" => shrinkBinaryFamily T s D rem hD small A
local notation "P" => shrinkRecordPacking s rem A
local notation "ord" => shrinkRecordOrder s rem A
local notation "b" => State.order (shrinkRecordState s rem A)
local notation "N" => Fintype.card (State.Base (shrinkRecordState s rem A))
local notation "d" => (2^s : ℕ)
local notation "hc" => palette_two s
local notation "S" => shrinkStage s D
local notation "x" => dims S N (tagBits d) rem
local notation "prior" => shrinkRecordWidth s rem A
local notation "du" => PhysicalShrink.b P prior (shrinkRecordCode s rem A) hc
variable {W K : ℕ} (cur : Word W) (m : Memory W) (c : Cursor)
local notation "p" => pointers K c x
local notation "C" => incoming S N p

def shrinkChoiceTicks (rows : ℕ) :=
  let size:=fun j=>Fintype.card (T.block (T.row j)).Alphabet
  11+3*rows*(2*(RAM.HeaderScan.closed (w:=W) (choiceWords cur (T.base ∘ T.row) size)).binds+4)

structure ShrinkPrefix (fit : (Q).Fits K W) (raw : HistogramRegister.Words (Q).motifs K W) : Prop where
  oldFits : (shrinkOld cur s D).fits m
  chart : Chart S P b p cur prior ((shrinkOld cur s D).run m).2
  choicesFit : (shrinkChoices cur T).fits ((shrinkOld cur s D).run m).2
  choiceClocks : ((shrinkChoices cur T).run ((shrinkOld cur s D).run m).2).1=shrinkChoiceTicks T cur (Q).motifs
  cursor : CursorSpace cur ((shrinkChoices cur T).run ((shrinkOld cur s D).run m).2).2 c K x
  bank : AdmissionBank.Fits cur.val K ((shrinkChoices cur T).run ((shrinkOld cur s D).run m).2).2 ∧
    HistogramRegister.BankLayout cur.val ((Q).rows fit) raw ((shrinkChoices cur T).run ((shrinkOld cur s D).run m).2).2
  tiles : ∀i:Fin (Q).motifs,(((shrinkChoices cur T).run ((shrinkOld cur s D).run m).2).2 (c.heap+i.val*3+1)).val=
    (RefreshDemandRows.tileNumber (du ((ord).symm i)) (T.base ∘ T.row)).val
  oldFrame : agreesOutside (p).demands (p).newGraph ((shrinkOld cur s D).run m).2 m
  choiceFrame : agreesOutside c.heap (c.heap+3*(Q).motifs) ((shrinkChoices cur T).run ((shrinkOld cur s D).run m).2).2
    ((shrinkOld cur s D).run m).2
  entryCursor : CursorSpace cur m c K x
  demandWords : ∀ a : (P).Motif,∀ j : Fin 2,
    (((shrinkOld cur s D).run m).2 ((p).demands+(ord a).val*2+j.val)).val=du a j

theorem shrink_prefix (fit : (Q).Fits K W) (raw : HistogramRegister.Words (Q).motifs K W)
    (space : CursorSpace cur m c K x) (stored : SlotImage.Stored A.graph A.order (tagOrdinal _) C (fun i=>(m i).val) A.width)
    (dense : ∀(i : Fin (Q).motifs) (j : Fin K),m (c.dense+K*i.val+j.val)=raw i j)
    (caps : ShrinkOldCaps s rem W) (totals : ∀a:(P).Motif,thickWidth P prior ((P).bundle a)<2^W)
    (table : T.more.length+1≤2^W) (budget : ∀a j e,sentinel (du a)+T.base (T.row j) e<2^W) :
    ShrinkPrefix T s D rem hD small A cur m c fit raw := by
  let v:=((shrinkOld cur s D).run m).2
  have prep:=native_shrink_old s D rem A cur m c space stored caps totals
  have fs:=space.fresh
  have ⟨e0,e1,e2,e3,e4,e5,e6,e7,e8,e9⟩:=space.allocated
  have motifs : (Q).motifs = (x).motifs := rfl
  have low : c.dense + K*(Q).motifs ≤ c.heap := space.counts
  have demandLow : c.heap ≤ (p).demands := by omega
  have mid := shrink_cursor_frame s D rem A cur m c space v prep.2.1
  have raw_mid (i : Fin (Q).motifs) (j : Fin K) : v (c.dense+K*i.val+j.val)=raw i j := by
    have row:=Nat.mul_le_mul_left K i.isLt
    rw [Nat.mul_succ] at row
    have col:=j.isLt
    rw [show v (c.dense+K*i.val+j.val)=m _ from prep.2.1 _ (.inl (by omega))]
    exact dense i j
  have pairs (a : (P).Motif) (j : Fin 2) : (v ((p).demands+(ord a).val*2+j.val)).val=du a j := by
    have word : v ((p).demands+(ord a).val*2+j.val) = (du a j : Word W) :=
      (congrArg (fun n : ℕ => v ((p).demands+n+j.val)) (Nat.mul_comm (ord a).val 2)).trans
        (prep.2.2.2 a j)
    have hj : du a j ≤ ∑ e, du a e :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
    have H:=budget a 0 0
    unfold sentinel at H
    have room : du a j < 2^W := by omega
    exact (congrArg Fin.val word).trans (Fin.val_cast_of_lt room)
  have choices:=native_shrink_choice T s D rem hD small A cur v c mid fit raw raw_mid pairs
    (by have:=caps.eight;omega) table budget
  have endChoice : c.heap+3*(Q).motifs≤cur.val := by
    rw [motifs]
    have := fs.high
    omega
  have head:=ShrinkStageNav.header_frame cur v mid.header choices.2.2.2.2.2 (.inr endChoice) (.inl space.earlier)
  exact ⟨prep.1,prep.2.2.1,choices.1,choices.2.1,{mid with header:=head},⟨choices.2.2.1,choices.2.2.2.1⟩,
    choices.2.2.2.2.1,prep.2.1,choices.2.2.2.2.2,space,pairs⟩

theorem shrink_table_of_read (fit : (Q).Fits K W) (raw : HistogramRegister.Words (Q).motifs K W) (term : Fin (M).rules.count)
    (accepted : ((Q).record fit).read (List.ofFn (HistogramRegister.bitTable raw))=some term) :
    HistogramRegister.words ((Q).rows fit) ((Q).sequence fit term)=raw :=
  HistogramRegister.bitTable.injective (List.ofFn_inj.mp (((Q).record fit).write_read _ _ accepted))


end
end ThreeFlat.Diagonal.PhysicalStage

end OAI
