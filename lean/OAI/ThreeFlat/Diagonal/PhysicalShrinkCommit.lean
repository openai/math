import OAI.ThreeFlat.Diagonal.PhysicalShrinkPrefix
import OAI.ThreeFlat.Diagonal.ShrinkDescriptorSpan

namespace OAI
/-! # The canonical accepted word bank, true chosen layout and resident graph input -/
namespace ThreeFlat.Diagonal.PhysicalStage
open Computability.VPVNP.BurstRAM PrivateRAM RAM RAM.DescriptorScan Computability.VPVNP.Compression CompressorPacking
open Native Native.ShrinkStage Native.ShrinkStage.Resident Native.Placement
open NavigationDirectory NavigationPass PhysicalShrink ShrinkStageNav MotifIntegerChoice
open scoped Classical Fin.NatCast
noncomputable section
open private palette_two from OAI.ThreeFlat.Diagonal.PhysicalShrinkPrefix
set_option quotPrecheck false
variable {F : Type} [Field F] (T : ShrinkMotif.Table F) (s D rem : ℕ) (hD : 0<D)
variable (small : ((2^(2*(2^s)+1)*(2^s)*(2^s):ℕ):ℝ)/D≤1/1024) (A : State (2^s) (shrinkCharge s+rem))
local notation "M" => shrinkBinary T s D rem hD small A
local notation "Q" => shrinkBinaryFamily T s D rem hD small A
local notation "P" => shrinkRecordPacking s rem A
local notation "ord" => shrinkRecordOrder s rem A
local notation "b" => (shrinkRecordState s rem A).order
local notation "N" => Fintype.card (shrinkRecordState s rem A).Base
local notation "d" => (2^s : ℕ)
local notation "hc" => palette_two s
local notation "S" => shrinkStage s D
local notation "x" => dims S N (tagBits d) rem
local notation "prior" => shrinkRecordWidth s rem A
local notation "du" => PhysicalShrink.b P prior (shrinkRecordCode s rem A) hc
variable {W K : ℕ} (cur : Word W) (m : Memory W) (c : Cursor)
local notation "p" => pointers K c x
local notation "mid" => ((shrinkChoices cur T).run ((shrinkOld cur s D).run m).2).2
local notation "E" => shrinkCostScans T cur K
local notation "z" => ((E).run mid).2

def shrinkDataTicks {w : ℕ} (cell : Word w) (alphabet rows : ℕ) :=
  let sizes:=fun j=>Fintype.card (T.block (T.row j)).Alphabet
  let issue:=widthWords cell alphabet sizes (fun j=>(T.block (T.row j)).bits)
    (fun j a e=>(T.block (T.row j)).output ((Fintype.equivFin _).symm a) e)
  (11+8*rows*(2*(RAM.HeaderScan.closed (w:=w) issue).binds+4))+
    ((11+2*(rows+1)*(2*(RAM.HeaderScan.closed (w:=w) (prefixWords cell)).binds+4))+
     (11+(2*(RAM.HeaderScan.closed (w:=w) (layoutWord cell)).binds+4)))

structure ShrinkCommitted (term : Fin (M).rules.count) : Prop where
  fits : (E).fits mid
  clocks : ((E).run mid).1=shrinkDataTicks T cur K (Q).motifs
  ready : Input S P b hc (ShrinkMotif.chooseWidths (shrinkIssuedWords T s D rem hD small A term)) p cur prior
    (shrinkIssuedWords T s D rem hD small A term) z
  elected : RAM.HeaderScan.Scans.Header cur z c.header 63
    (DescriptorSpan.fields K c x (ShrinkMotif.chooseWidths (shrinkIssuedWords T s D rem hD small A term)))
  keep : ∀ i,i≠c.header+27 → (i<(p).costs ∨ (p).costs+2*((Q).motifs+1)≤ i) →
    (i<(p).supply ∨ (p).supply+8*(Q).motifs≤ i) → z i=mid i

theorem shrink_commit {fit : (Q).Fits K W} {raw : HistogramRegister.Words (Q).motifs K W}
    (prep : ShrinkPrefix T s D rem hD small A cur m c fit raw)
    (separated : c.header+64≤c.graph ∧ c.header+64≤c.width)
    (term : Fin (M).rules.count) (accepted : ((Q).record fit).read (List.ofFn (HistogramRegister.bitTable raw))=some term)
    (eight : 8<2^W) (count : T.more.length+1≤2^W) (alph : ∀ j,Fintype.card (T.block (T.row j)).Alphabet≤K)
    (B : ℕ) (wBound : ∀ a e,shrinkIssuedWords T s D rem hD small A term a e≤B)
    (widthFits : B<2^W) (scoreFits : 80*(Q).motifs*B^2<2^W) :
    ShrinkCommitted (K:=K) T s D rem hD small A cur m c term := by
  let f:=prep.cursor
  have table:=shrink_table_of_read T s D rem hD small A fit raw term accepted
  have bank:=prep.bank.2
  rw [←table] at bank
  have chosen:=native_shrink_commit T s D rem hD small A cur mid c f fit term bank prep.tiles
    eight count alph B wBound widthFits scoreFits
  have keep:=chosen.2.2.2.2
  obtain ⟨r0,r1,r2,r3,r4,r5,r6,r7,r8,r9⟩:=f.allocated
  have motifs : (Q).motifs = (x).motifs := rfl
  have graph:=f.graph
  have widths:=f.widths
  have head:=f.earlier
  have left:=separated.1
  have right:=separated.2
  have lim:=f.end_lt
  have saved (i) (h : ChartRead x p i) :
      z i=((shrinkOld cur s D).run m).2 i := by
    apply Eq.trans (keep i ?_ (.inl ?_) ?_) (prep.choiceFrame i ?_)
    all_goals cases h with
    | graph h => rcases h with ⟨lo,hi⟩;change c.graph≤ i at lo;change i<c.graph+6*(x).oldEdges at hi;omega
    | widths h => rcases h with ⟨lo,hi⟩;change c.width≤ i at lo;change i<c.width+(x).oldEdges*(x).originalLanes at hi;omega
    | aux h => rcases h with ⟨lo,hi⟩;omega
  have elapsed:=(native_shrink_supply T s D rem hD small A cur mid c f fit term bank prep.tiles eight count alph).2.2
  have time : ((E).run mid).1=shrinkDataTicks T cur K (Q).motifs := by rw [chosen.2.1,elapsed]; rfl
  refine ⟨chosen.1,time,prep.chart.publish f.fresh chosen.2.2.1 (by omega) chosen.2.2.2.1 saved,?_,keep⟩
  apply DescriptorSpan.elected_header K c x _ cur z f.header chosen.2.2.1
  intro i low high
  exact keep _ (by omega) (.inl (by omega)) (.inl (by omega))


end
end ThreeFlat.Diagonal.PhysicalStage

end OAI
