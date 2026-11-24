import OAI.Computability.VPVNP.CompressorShrinkInputTerms
import OAI.Computability.VPVNP.CompressorRecordsSelectedPreimages
import OAI.Computability.VPVNP.CompressorShrinkOutputAllocation
import OAI.Computability.VPVNP.CompressorSliceIndexedStarts
import OAI.Computability.VPVNP.CompressorShrinkResidentLayout

/-!
# Linear external address ranges of a selected shrinking level

Each coefficient uses the fixed input and output degree exponents. The areas
for demand slices, surviving slices, and sorted slots can be assigned their
own table heads. The bound for the contiguous construction starts the supply
and slot arrays after the selected child-preimage rows.
-/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section

namespace CompressorRecords.ShrinkLevelSpace

open BurstRAM Compression Compression.PackingData Compression.ShrinkMotif
open SlotLevel ShrinkSlots

variable {a b g w : ℕ} (X : State a (packingLaneBits a g))

private theorem positions_eq :
    Fintype.card X.Base*2^(packingLaneBits a g) = X.positions := by
  simp only [State.positions,Fintype.card_prod,Fintype.card_congr (bitWordFinEquiv
    (packingLaneBits a g)),Fintype.card_fin]

private theorem packed_le : ShrinkPreimages.newCount X ≤ X.positions := by
  rw [← positions_eq X]
  change Fintype.card X.Base*(2^(Shrink.J a)*2^g) ≤ Fintype.card X.Base*2^(packingLaneBits a g)
  apply Nat.mul_le_mul_left
  rw [← Nat.pow_add]
  exact Nat.pow_le_pow_right Nat.zero_lt_two (by unfold packingLaneBits Shrink.J; omega)

private theorem absolute_eq : ShrinkOutput.absoluteCount X = X.positions*2^a :=
  (DemandRAM.count_eq X).symm.trans (congrArg (·*2^a) (positions_eq X))

private theorem motif_le : ShrinkOutput.motifCount X ≤ X.positions*(2^a*ShrinkRankSpace.cap a) := by
  change ShrinkPreimages.newCount X*2^a*ShrinkRankSpace.cap a ≤ _
  rw [Nat.mul_assoc]; exact Nat.mul_le_mul_right _ (packed_le X)

private theorem selected_motifs : SelectedArena.motifs X = ShrinkOutput.motifCount X :=
  (Fintype.card_congr (ShrinkMotifOrder.stateNumber X)).trans (Fintype.card_fin _)

/-- Per-position words for the six greedy scans, old placement and both dense rank/width banks. -/
def inputRate (a : ℕ) :=
  let d := 2^a
  11+10*d+4*Greedy.WalkLayout.tagCount d+10*d*ShrinkRankSpace.cap a

theorem input_stop (start : ℕ) : ShrinkInput.stop X start ≤ start+X.positions*inputRate a := by
  let d := 2^a
  let Q := ShrinkRankSpace.cap a
  let t := Greedy.WalkLayout.tagCount d
  let P := X.positions
  let V := Fintype.card X.Base
  let B := ShrinkPreimages.newCount X*d
  have hV : V ≤ P := by
    change Fintype.card X.Base ≤ X.positions
    rw [← positions_eq X]
    exact Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _)
  have hb : B ≤ P*d := Nat.mul_le_mul_right _ (packed_le X)
  have hbase : ShrinkInput.placementBase X start = start+V*(6+3*d+4*t)+1 :=
    GreedyArena.greedyStop_eq ..
  have hrank : ShrinkInput.rankBase X start = ShrinkInput.placementBase X start+4*P :=
    congrArg (fun n => ShrinkInput.placementBase X start+4*n) (positions_eq X)
  let r := ShrinkInput.plan X start
  have ha : r.A = P*d := congrArg (·*d) (positions_eq X)
  have eqn : ShrinkInput.stop X start =
      ShrinkInput.rankBase X start + 3*r.A + 4*B + 10*B*Q := by
    change (((((ShrinkInput.rankBase X start+2*r.A)+2*B)+(2*B)*Q)+(2*B)*Q)+r.A)+6*(B*Q)+2*B = _
    ring
  rw [eqn,hrank,hbase,ha]
  change _ ≤ start+P*(11+10*d+4*t+10*d*Q)
  linarith only [Nat.mul_le_mul_right (6+3*d+4*t) hV,Nat.mul_le_mul_right Q hb,hb,X.positions_pos]

/-- Per-old-position space bound through the term descriptors, allowing for the input
workspace, two demand words per motif and a descriptor of the given stride. -/
def termRate (a stride : ℕ) := inputRate a + (2+stride)*(2^a*ShrinkRankSpace.cap a)

theorem term_end (start stride : ℕ) :
    ShrinkInput.termEnd X start stride ≤ start+X.positions*termRate a stride := by
  let M := ShrinkOutput.motifCount X
  change ShrinkInput.stop X start+2*M+M*stride ≤ _
  have hm : M ≤ X.positions*(2^a*ShrinkRankSpace.cap a) := motif_le X
  unfold termRate
  linarith only [input_stop X start,hm,Nat.mul_le_mul_right stride hm]

/-- Selected scores, role columns and both child-preimage arrays after the term table. -/
def selectedRate (a : ℕ) := 9+4*2^a

theorem selected_stop (term stride : Word w) :
    SelectedFinish.stop X term stride ≤ term.val+ShrinkOutput.motifCount
      X*stride.val+X.positions*selectedRate a := by
  change term.val+SelectedArena.motifs X*stride.val+3+4*(Fintype.card X.Base*2^(packingLaneBits
    a g))+
    4*ShrinkOutput.absoluteCount X+ShrinkPreimages.newCount
      X+(Fintype.card X.Base*2^(packingLaneBits a g)) ≤ _
  rw [selected_motifs X,positions_eq X,absolute_eq X,selectedRate]
  linarith only [X.positions_pos,packed_le X]

/-- The end of table zero with the actual allocated word head. Modulo conversion of
the head or stride can only decrease its natural value. -/
theorem table_zero (start stride : ℕ) :
    SelectedFinish.stop X (ShrinkInput.termHead (w := w) X start) (Fin.ofNat (2^w) stride) ≤
      start+X.positions*(termRate a stride+selectedRate a) := by
  let term := ShrinkInput.termHead (w := w) X start
  let step := Fin.ofNat (2^w) stride
  let M := ShrinkOutput.motifCount X
  have ht : term.val ≤ ShrinkInput.stop X start+2*M := Nat.mod_le ..
  have hs : step.val ≤ stride := Nat.mod_le ..
  have he := term_end X start stride
  change ShrinkInput.stop X start+2*M+M*stride ≤ _ at he
  have hc := selected_stop X term step
  change SelectedFinish.stop X term step ≤ term.val+M*step.val+X.positions*selectedRate a at hc
  linarith only [he,hc,ht,Nat.mul_le_mul_left M hs]

/-- Per-position capacity of the separate AB interval banks. -/
def abRate (a : ℕ) := 2^a*IndexedStarts.capacity (2^(Shrink.colors a)*2^a/4) (ShrinkRankSpace.cap a)

theorem ab_end (first : ℕ) :
    first+ShrinkTermSelection.bundles X*IndexedStarts.capacity (2^(Shrink.colors a)*2^a/4)
      (ShrinkRankSpace.cap a)
      ≤ first+X.positions*abRate a := by
  apply Nat.add_le_add_left
  change (ShrinkPreimages.newCount X*2^a)*_ ≤ X.positions*(2^a*_)
  rw [Nat.mul_assoc]; exact Nat.mul_le_mul_right _ (packed_le X)

/-- Total number of subdivisions over the four supply types for a shrink from degree exponent
`a` to exponent `b`. -/
def subdivisionSum (a b : ℕ) :=
  ∑ t, subdivisions (2^a) (Shrink.colors a) (2^b) t

/-- Width and interval banks of the four surviving supply roles. -/
def survivingRate (a b : ℕ) :=
  let d := 2^a
  let S := subdivisionSum a b
  4*d*S+4*d*ShrinkRankSpace.cap a*(5+7*S)

theorem surviving_end (width : ℕ) :
    ShrinkOutput.slotsBase X width (levelShape (b := b) X) ≤ width+X.positions*survivingRate a
      b := by
  let S := subdivisionSum a b
  change width+(ShrinkOutput.absoluteCount X*4)*S+(ShrinkOutput.motifCount X*4)*(5+7*S) ≤ _
  rw [absolute_eq X]
  unfold survivingRate
  change _ ≤ width+X.positions*(4*2^a*S+4*2^a*ShrinkRankSpace.cap a*(5+7*S))
  linarith only [Nat.mul_le_mul_right (4*(5+7*S)) (motif_le X)]

/-- Slot inputs, counters, sorted owner rows, inversion and six output incidence columns. -/
def slotRate (a b : ℕ) :=
  let d := 2^a
  let c := Shrink.colors a
  let k := 4*d*(2^c*d)*subdivisionSum a b
  let pad := 2^b-survivingDegree d c (subdivisions d c (2^b))
  15+6*(k+pad)+(8+2*(k+pad))*2^b

theorem slot_end (role start : ℕ) :
    let s := levelShape (b := b) X
    finish s (ShrinkOutput.heads s role start) ≤ start+X.positions*slotRate a b := by
  intro s
  let P := sites s
  let U := 4*s.oldDegree*(2^s.colors*s.oldDegree)*(∑ t,s.subdivisions t)
  let J := U+pad s
  have hg : genuineCount s = P*(2*U) := by dsimp [P,genuineCount,sites,Slots.keyCount,U]; ring
  have hd : dummyCount s = P*(2*pad s) := by dsimp [P,dummyCount,sites]; ring
  have hf : fields s = P*(2*J) := by rw [← counts_add,hg,hd]; dsimp [J]; ring
  have ho : owners s = 2*P := Nat.mul_comm ..
  have hl : 1 ≤ s.lanes := Nat.two_pow_pos g
  have hb : baseArcs s ≤ P*s.newDegree := by
    change s.bases*s.tags*s.newDegree ≤ s.bases*(s.tags*s.lanes)*s.newDegree
    rw [← Nat.mul_assoc]; exact Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_right _ hl)
  have hp : 0 < P := Nat.mul_pos Fintype.card_pos (Nat.mul_pos (Nat.two_pow_pos _)
    (Nat.two_pow_pos _))
  apply le_trans _ (Nat.add_le_add_left (Nat.mul_le_mul_right (slotRate a b) (packed_le X)) start)
  change _ ≤ start+P*(15+6*J+(8+2*J)*s.newDegree)
  change start+8+P+4+fields s+(owners s+fields s)+(owners s+fields s)*s.newDegree+fields s+
    baseArcs s+baseArcs s+baseArcs s+P*s.newDegree+P*s.newDegree+P*s.newDegree ≤ _
  rw [hf,ho]
  linarith only [hb,hp]

/-- The ordinary contiguous output build starts its new width arrays after every
retained input, then allocates its ordered slots. -/
theorem output_end (term stride : Word w) :
    let role := SelectedArena.roleBase X term stride
    let retained := SelectedFinish.stop X term stride
    ShrinkOutput.stop (b := b) X term.val stride.val role retained ≤
      retained+X.positions*(survivingRate a b+slotRate a b) := by
  intro role retained
  have hs : term.val+ShrinkOutput.motifCount X*stride.val ≤ role := by
    change _ ≤ term.val+SelectedArena.motifs X*stride.val+3+4*SelectedArena.positions X
    rw [selected_motifs X]; omega
  have hr : role+4*ShrinkOutput.absoluteCount X ≤ retained := by
    change _ ≤ role+4*ShrinkOutput.absoluteCount X+ShrinkPreimages.newCount
      X+ShrinkPreimages.oldCount X
    omega
  have hmax : ShrinkOutput.widthBase X term.val stride.val role retained = retained := by
    unfold ShrinkOutput.widthBase
    rw [max_eq_right hr,max_eq_right ((hs.trans (Nat.le_add_right ..)).trans hr)]
  let width := ShrinkOutput.widthBase X term.val stride.val role retained
  let slot := ShrinkOutput.slotsBase X width (levelShape (b := b) X)
  have hw := surviving_end (b := b) X width
  have hc := slot_end (b := b) X role slot
  change ShrinkOutput.stop (b := b) X term.val stride.val role retained ≤
    slot+X.positions*slotRate a b at hc
  change slot ≤ width+X.positions*survivingRate a b at hw
  change width = retained at hmax
  linarith only [hc,hw,hmax]

/-- Both resident directories, including their owner columns, counters and
bounded append rows for the four hidden wires and six local maps per motif. -/
def residentRate (a : ℕ) := 2+20*2^a*ShrinkRankSpace.cap a

theorem resident_end (first : ℕ) :
    (ShrinkResidentLayout.layout X first).endAddr ≤ first+X.positions*residentRate a := by
  let P := ShrinkPreimages.newCount X
  change first+SelectedArena.motifs X*4+P+SelectedArena.motifs X*4+SelectedArena.motifs
    X*6+P+SelectedArena.motifs X*6 ≤ _
  rw [selected_motifs X,residentRate]
  dsimp only [P]; linarith only [packed_le X,motif_le X]

/-- Capacity for all live shrinking arenas, chosen from the fixed transition. -/
def levelRate (a b : ℕ) :=
  termRate a 10+selectedRate a+abRate a+survivingRate a b+slotRate a b+residentRate a

variable {k : Type*} [_root_.Field k]

/-- Uniform rate chosen before the input, the number of remaining lanes and the
selected term. It works for separate table arenas and the contiguous output layout. -/
def tableFactor (S : BlockSchedule k) :=
  Finset.univ.sup fun i : Fin S.steps ↦ levelRate (S.degreeExponent i.castSucc)
    (S.degreeExponent i.succ)

theorem levelRate_le_tableFactor (S : BlockSchedule k) (i : Fin S.steps) :
    levelRate (S.degreeExponent i.castSucc) (S.degreeExponent i.succ) ≤ tableFactor S :=
  Finset.le_sup (f := fun j : Fin S.steps => levelRate (S.degreeExponent j.castSucc)
    (S.degreeExponent j.succ)) (Finset.mem_univ i)

/-- The contiguous shrinking branch is housed in a single linear-capacity arena.
The same uniform factor also bounds each of the separate slice and slot tables. -/
theorem packed_ends (S : BlockSchedule k) (i : Fin S.steps) {g : ℕ}
    (X : State (S.degreeExponent i.castSucc) (packingLaneBits (S.degreeExponent i.castSucc) g))
    (start ab supply slots : ℕ) (w : ℕ) :
    let a := S.degreeExponent i.castSucc
    let b := S.degreeExponent i.succ
    let s := levelShape (b := b) X
    let term := ShrinkInput.termHead (w := w) X start
    let stride := Fin.ofNat (2^w) 10
    let role := SelectedArena.roleBase X term stride
    let selected := SelectedFinish.stop X term stride
    let size := X.positions*tableFactor S
    ShrinkInput.stop X start ≤ start+size ∧ ShrinkInput.termEnd X start 10 ≤ start+size ∧
      selected ≤ start+size ∧ ShrinkOutput.stop (b := b) X term.val stride.val role selected ≤
        start+size ∧
      ab+ShrinkTermSelection.bundles X*IndexedStarts.capacity (2^(Shrink.colors a)*2^a/4)
        (ShrinkRankSpace.cap a) ≤ ab+size ∧
      ShrinkOutput.slotsBase X supply s ≤ supply+size ∧ finish s
        (ShrinkOutput.heads s role slots) ≤ slots+size := by
  intro a b s term stride role selected size
  have hi := input_stop X start
  have ht := term_end X start 10
  have hp := table_zero (w := w) X start 10
  have ho := output_end (b := b) X term stride
  have ha := ab_end X ab
  have hs := surviving_end (b := b) X supply
  have hw := slot_end (b := b) X role slots
  have hf : X.positions*levelRate a b ≤ size := Nat.mul_le_mul_left _ (levelRate_le_tableFactor S i)
  change selected ≤ start+X.positions*(termRate a 10+selectedRate a) at hp
  change ShrinkOutput.stop (b := b) X term.val stride.val role selected ≤
    selected+X.positions*(survivingRate a b+slotRate a b) at ho
  unfold levelRate at hf
  have input : inputRate a ≤ termRate a 10 := Nat.le_add_right ..
  have inputWords := Nat.mul_le_mul_left X.positions input
  dsimp only [a,b,s] at *
  simp only [Nat.mul_add] at hf hp ho
  exact ⟨by omega,by omega,by omega,by omega,by omega,by omega,by omega⟩

/-- The resident arrays may follow the chosen preimage rows in table zero or
occupy their own table. The fixed schedule rate covers either address convention. -/
theorem resident_table (S : BlockSchedule k) (i : Fin S.steps) {g : ℕ}
    (X : State (S.degreeExponent i.castSucc) (packingLaneBits (S.degreeExponent i.castSucc) g))
    (start separate w : ℕ) :
    let term := ShrinkInput.termHead (w := w) X start
    let stride := Fin.ofNat (2^w) 10
    let next := SelectedFinish.stop X term stride
    let size := X.positions*tableFactor S
    (ShrinkResidentLayout.layout X next).endAddr ≤ start+size ∧
      (ShrinkResidentLayout.layout X separate).endAddr ≤ separate+size := by
  intro term stride next size
  have h := table_zero (w := w) X start 10
  change next ≤ _ at h
  have hr := resident_end X next
  have hs := resident_end X separate
  have hf := Nat.mul_le_mul_left X.positions (levelRate_le_tableFactor S i)
  unfold levelRate at hf
  change _ ≤ size at hf
  simp only [Nat.mul_add] at hf h
  exact ⟨by omega,by omega⟩

end CompressorRecords.ShrinkLevelSpace

end

end VPVNP
end Computability
end OAI
