import OAI.ThreeFlat.Diagonal.PhysicalShrinkPublished
import OAI.ThreeFlat.Diagonal.ProgramDirectory
import OAI.ThreeFlat.Diagonal.ShrinkRecordBase

namespace OAI
/-! # Admission and publication for a complete physical binary shrinking stage -/
namespace ThreeFlat.Diagonal.PhysicalStage
open Computability.VPVNP.BurstRAM PrivateRAM RAM RAM.DescriptorScan Computability.VPVNP.Compression CompressorPacking
open Native Native.ShrinkStage Native.ShrinkStage.Resident Native.Placement
open NavigationDirectory NavigationPass PhysicalShrink ShrinkStageNav
open scoped Classical Fin.NatCast BigOperators
noncomputable section
set_option quotPrecheck false
private theorem thick_read_bound {colors degree maxWidth wordBits extra : ℕ}
    {V H Tag L : Type*} [AddCommGroup H] [AddCommGroup Tag] [AddCommGroup L]
    [Fintype V] [Fintype H] [Fintype Tag] [Fintype L]
    (packing : PackingData V H Tag L degree colors) (width : Arc V H Tag L degree colors → ℕ)
    (bounded : ∀ e, width e ≤ maxWidth)
    (room : 1+2*(widthMultiplicity colors degree*maxWidth)+extra < 2^wordBits)
    (point : Site V Tag L × Fin degree) : thickWidth packing width point < 2^wordBits := by
  have mass : thickWidth packing width point ≤ (2^(colors-2)*degree)*maxWidth := by
    calc
      thickWidth packing width point ≤ ∑ _a : ThickAt packing point, maxWidth :=
        Finset.sum_le_sum fun e _ => bounded e.val
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, card_thickAt, nsmul_eq_mul, Nat.cast_id]
  unfold widthMultiplicity at room
  rw [Nat.add_mul, Nat.one_mul] at room
  omega

variable {F : Type} [Field F] (T : ShrinkMotif.Table F) (s D rem : ℕ) (hD : 0<D)
variable (small : ((2^(2*(2^s)+1)*(2^s)*(2^s):ℕ):ℝ)/D≤1/1024) (A : State (2^s) (shrinkCharge s+rem))
local notation "M" => shrinkBinary T s D rem hD small A
local notation "Q" => shrinkBinaryFamily T s D rem hD small A
local notation "N" => Fintype.card (shrinkRecordState s rem A).Base
local notation "oldPacking" => shrinkRecordPacking s rem A
local notation "d" => (2^s : ℕ)
local notation "k" => (2*d+1 : ℕ)
local notation "S" => shrinkStage s D
local notation "stageDims" => dims S N (CompressorPacking.tagBits d) rem
local notation "top" => shrinkMotifWidthFactor T k d*(1+A.maxWidth)
variable {W K : ℕ}

def shrinkBudget (K : ℕ) (cur : Word W) (c : Cursor) :=
  let pre:=DescriptorSpan.recipeTicks (DescriptorSpan.fields K c stageDims false) (before S (CompressorPacking.tagBits d))
  pre+(shrinkChoiceTicks T cur (Q).motifs+((6+(Q).motifs*(2*AdmissionBank.cost 0 K+4))+
    shrinkPublishBudget T s D rem hD small A cur K c))

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
theorem shrink_admission (field : FieldCode F W) (word : 0<W) (cur : Word W) (input : Memory W) (c : Cursor)
    (space : CursorSpace cur input c K stageDims)
    (old : SlotImage.Stored A.graph A.order (tagOrdinal _) (incoming S N (pointers K c stageDims))
      (fun i=>(input i).val) A.width)
    (sep : c.header+64≤c.graph ∧ c.header+64≤c.width)
    (fit : (Q).Fits K W) (raw : HistogramRegister.Words (Q).motifs K W)
    (stream : ∀i j,input (c.dense+K*i.val+j.val)=raw i j)
    (oldCap : ShrinkOldCaps s rem W) (extra : ShrinkOutputCaps s D N W)
    (tiles : T.more.length+1≤2^W) (alphabet : shrinkSymbolBound T≤K)
    (room : 1+2*(widthMultiplicity k d*A.maxWidth)+shrinkBaseBound T<2^W)
    (widthFits : top<2^W) (scoreFits : 80*(Q).motifs*top^2<2^W) :
    let body:=NavigationPass.shrink cur K s D T
    let bits:=List.ofFn (HistogramRegister.bitTable raw)
    TickStageSpec.Admission field body.block body.publicData (fun m=>m=input) (fun _=>(((Q).record fit).read bits).isSome)
      (fun _ out=>∃ branch:Fin (M).rules.count,((Q).record fit).read bits=some branch ∧
        ShrinkOutput (K:=K) T s D rem hD small A cur input c branch out)
      (shrinkBudget T s D rem hD small A K cur c) := by
  let bits:=List.ofFn (HistogramRegister.bitTable raw)
  let mid:=((shrinkChoices cur T).run ((shrinkOld cur s D).run input).2).2
  have oldBound (a : (oldPacking).Motif) : thickWidth oldPacking (shrinkRecordWidth s rem A) ((oldPacking).bundle a)<2^W := by
    exact thick_read_bound oldPacking (shrinkRecordWidth s rem A) (prior_width_le s rem A)
      room ((oldPacking).bundle a)
  have prep:=shrink_prefix T s D rem hD small A cur input c fit raw space old stream oldCap oldBound tiles
    (by
      apply shrink_choice_room (T:=T) (s:=s) (D:=D) (rem:=rem) (A:=A)
      all_goals assumption)
  have alph (j) : Fintype.card (T.block (T.row j)).Alphabet≤K :=
    (Finset.le_sup (s:=Finset.univ) (f:=fun j:T.Row=>Fintype.card (T.block j).Alphabet) (Finset.mem_univ _)).trans alphabet
  have post (branch : Fin (M).rules.count) (accepted : ((Q).record fit).read bits=some branch) := by
    let wd:=shrink_issued_room T s D rem hD small A branch
    let committed:=shrink_commit T s D rem hD small A cur input c prep sep branch accepted oldCap.eight tiles alph
      top wd widthFits scoreFits
    exact shrink_published T s D rem hD small A cur input c prep branch accepted committed oldCap extra top wd widthFits
  let body := NavigationPass.shrink cur K s D T
  let finalMemory := ((shrinkPublish cur K s D T).run mid).2
  let clock := ((shrinkOld cur s D).run input).1 +
    (((shrinkChoices cur T).run ((shrinkOld cur s D).run input).2).1 +
      ((6+(Q).motifs*(2*AdmissionBank.cost 0 K+4))+shrinkPublishBudget T s D rem hD small A cur K c))
  have guard : TickStageSpec.Admission field body.block body.publicData (fun m => m=input)
      (fun _ => (((Q).record fit).read bits).isSome) (fun _ out => out=finalMemory) clock :=
    shrink_native field word cur K s D T ((Q).rows fit) ((Q).sequence fit) raw input
      (shrinkPublishBudget T s D rem hD small A cur K c) prep.oldFits prep.choicesFit prep.bank (by
      change (((Q).record fit).read bits).isSome = true →
        (shrinkPublish cur K s D T).fits mid ∧
          ((shrinkPublish cur K s D T).run mid).1 ≤ shrinkPublishBudget T s D rem hD small A cur K c
      intro ok
      obtain ⟨branch,valid⟩:=Option.isSome_iff_exists.mp ok
      exact ⟨(post branch valid).1,(post branch valid).2.1⟩)
  have boot : RAM.HeaderScan.Scans.Header cur input c.header 63 (DescriptorSpan.fields K c stageDims false) := by
    rw [DescriptorSpan.fields_false];exact space.header
  have preTime := (DescriptorSpan.pre_run S K c stageDims false cur (fun _=>0) input boot space.earlier space.controls (CompressorPacking.tagBits d)).clocks
  dsimp only
  intro np nr nk machine
  refine TickStageSpec.Admission.mono (b:=body.block) (data:=body.publicData)
    (pre:=fun m => m=input) (good:=fun _ => (((Q).record fit).read bits).isSome)
    (post:=fun _ out => out=finalMemory) (t:=clock)
    guard (fun _ h => h) (fun _ _ => Iff.rfl) ?_ ?_ machine
  · intro _ out _ ok same
    obtain ⟨branch,valid⟩:=Option.isSome_iff_exists.mp ok
    refine ⟨branch,valid,?_⟩
    rw [same]
    exact (post branch valid).2.2
  · change ((shrinkOld cur s D).run input).1+(_+_)≤_
    rw [prep.choiceClocks]
    unfold shrinkBudget
    change (((before S (CompressorPacking.tagBits d)).install cur).execute cur (fun _=>0) input).1+_≤_
    rw [preTime]



/-- The per-call upper budget read by the chronological composer uses precisely the
same spans as the physical theorem, with the current base cardinal supplied by the directory. -/
def shrinkAbsoluteTicks (K : ℕ) (cur : Word W) (c : Cursor) (v r : ℕ) :=
  let x := dims S v (CompressorPacking.tagBits d) r
  let pre := DescriptorSpan.recipeTicks (DescriptorSpan.fields K c x false) (before S (CompressorPacking.tagBits d))
  let post := fun b=>DescriptorSpan.recipeTicks (DescriptorSpan.fields K c x b) (NodeRecipe.after S K 1)
  pre+(shrinkChoiceTicks T cur x.motifs+((6+x.motifs*(2*AdmissionBank.cost 0 K+4))+
    (shrinkDataTicks T cur K x.motifs+max (post false) (post true)+6)))

theorem shrinkBudget_absolute (K : ℕ) (cur : Word W) (c : Cursor) :
    shrinkBudget T s D rem hD small A K cur c=shrinkAbsoluteTicks T s D K cur c (Fintype.card A.Base) rem := by
  rw [←shrink_record_base s rem A]
  rfl

private theorem shrink_tick_sum (front back choices issued rows work control multiplier budget scale : ℕ)
    (scans : front+back ≤ budget*(1+scale))
    (calls : choices+issued ≤ 44+work*(rows+1))
    (count : rows+1 ≤ multiplier*(1+scale)) :
    front+(choices+((6+rows*control)+(issued+back+6))) ≤
      (budget+(work+control)*multiplier+56)*(1+scale) := by
  have dataBound := Nat.mul_le_mul_left work count
  have controlBound := Nat.mul_le_mul_left control ((Nat.le_succ rows).trans count)
  nlinarith only [scans,calls,dataBound,controlBound,Nat.zero_le scale]

theorem shrink_absolute_time (K : ℕ) :
    ∃ B : ℕ,∀ (W : ℕ) (cur : Word W) (c : Cursor) (r v : ℕ),
      shrinkAbsoluteTicks T s D K cur c v r≤B*(1+v*2^(shrinkCharge s+r)) := by
  let size := fun j=>Fintype.card (T.block (T.row j)).Alphabet
  let bits := fun j=>(T.block (T.row j)).bits
  let pool := fun j (i : Fin (size j)) e=>(T.block (T.row j)).output ((Fintype.equivFin _).symm i) e
  obtain ⟨C,linear⟩ := calls_linear (T.base ∘ T.row) size bits pool K
  let recipes := (before S (CompressorPacking.tagBits d)).cost+(NodeRecipe.after S K 1).cost
  let g := 2*AdmissionBank.cost 0 K+4
  let heap := 22*(8*d+6*D+6)+(7+6*(8*d^2*2^k)+8*D)+2
  refine ⟨(3+heap)*recipes+(C+g)*(3*d+1)+56,?_⟩
  intro W cur csr r v
  let x := dims S v (CompressorPacking.tagBits d) r
  let z := v*2^(shrinkCharge s+r)
  have P := Program.shrink_positions s 0 r v
  have orig : x.originalSites=z := P.1
  have dep : x.outputSites≤x.originalSites := by
    have p : x.outputSites*4≤x.originalSites := P.2
    omega
  have n : x.motifs≤3*d*z := by
    rw [←orig]
    change x.motifs≤3*x.oldDegree*x.originalSites
    unfold Dimensions.motifs Dimensions.upperBlocks Dimensions.oldEdges Dimensions.originalSites Dimensions.originalLanes
    have pw : 2^(x.colorBits-2)≤2^x.colorBits := Nat.pow_le_pow_right (by decide) (Nat.sub_le ..)
    calc
      _ ≤ (x.oldBase*x.oldDegree*x.residual*x.tagRadix*x.oldDegree)*(3*2^x.colorBits) := by gcongr
      _ = _ := by ring
  have heaplim : (NavigationDirectory.Stage.shrink x).heapWords≤2+heap*z := by
    rw [←orig]
    exact shrink_heap_le x (Nat.two_pow_pos _) (Nat.two_pow_pos _) (Nat.two_pow_pos _) dep
  have pr := DescriptorSpan.recipe_charge S K csr x (CompressorPacking.tagBits d) 1
  have rc :
      DescriptorSpan.recipeTicks (DescriptorSpan.fields K csr x false) (before S (CompressorPacking.tagBits d))+
        max (DescriptorSpan.recipeTicks (DescriptorSpan.fields K csr x false) (NodeRecipe.after S K 1))
          (DescriptorSpan.recipeTicks (DescriptorSpan.fields K csr x true) (NodeRecipe.after S K 1)) ≤
        ((3+heap)*recipes)*(1+z) := by
    apply pr.trans
    change (_+1)*recipes≤_
    calc
      _ ≤ (2+heap*z+1)*recipes := Nat.mul_le_mul_right _ (Nat.add_le_add_right heaplim 1)
      _ ≤ _ := by nlinarith only [Nat.zero_le (recipes*z),Nat.zero_le (heap*recipes)]
  have num : shrinkChoiceTicks T cur x.motifs+shrinkDataTicks T cur K x.motifs ≤44+C*(x.motifs+1) := by
    simpa only [shrinkChoiceTicks,shrinkDataTicks,Nat.add_assoc] using linear W cur x.motifs
  have nm : x.motifs+1≤(3*d+1)*(1+z) := by nlinarith only [n,Nat.zero_le d,Nat.zero_le z]
  exact shrink_tick_sum
    (DescriptorSpan.recipeTicks (DescriptorSpan.fields K csr x false) (before S (CompressorPacking.tagBits d)))
    (max (DescriptorSpan.recipeTicks (DescriptorSpan.fields K csr x false) (NodeRecipe.after S K 1))
      (DescriptorSpan.recipeTicks (DescriptorSpan.fields K csr x true) (NodeRecipe.after S K 1)))
    (shrinkChoiceTicks T cur x.motifs) (shrinkDataTicks T cur K x.motifs) x.motifs C g
    (3*d+1) ((3+heap)*recipes) z rc num nm



/-- All fixed graph and grid terms, the raw admission guard and the terminal pointer
advance are included in the runtime coefficient of the installed shrink stage. -/
theorem shrink_return_time (K : ℕ) :
    ∃ B : ℕ,∀ (W : ℕ) (cur : Word W) (c : Cursor) (r : ℕ) (a : State d (shrinkCharge s+r)),
      shrinkBudget T s D r hD small a K cur c≤B*(1+Fintype.card a.Base*2^(shrinkCharge s+r)) := by
  obtain ⟨B,fit⟩ := shrink_absolute_time T s D K
  refine ⟨B,?_⟩
  intro W cur c r a
  rw [shrinkBudget_absolute]
  exact fit W cur c r (Fintype.card a.Base)


end
end ThreeFlat.Diagonal.PhysicalStage

end OAI
