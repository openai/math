import OAI.Hierarchy.TraceNativePorts
import OAI.Hierarchy.PhysicalTracePlan
import OAI.Hierarchy.TraceRecordScale
import OAI.Hierarchy.TraceRecordInput
import OAI.Hierarchy.TraceRegisterGuard
import OAI.ThreeFlat.Diagonal.PhysicalProgramRecords
import OAI.ThreeFlat.Diagonal.PhysicalHistogramRows

namespace OAI
/-! # Histogram records for the repeated physical compression schedule

At each move the previous widths select the actual motif rows and their permitted
multiplicities. The number of such rows, and hence the number of raw histogram words,
is determined by the public stage directory before the input or shared bits are read.
-/

noncomputable section
namespace Hierarchy.TraceAdmission

open ThreeFlat Diagonal Diagonal.PhysicalStage
open TraceDistribution Filter
open scoped BigOperators Classical

variable {F : Type} [Field F] (B : Block F)

def stageCounts (s axes : ℕ) : List ℕ :=
  (((B.repeat s).directory (axes-(B.repeat s).charge) axes).map NavigationDirectory.Stage.motifs)

private theorem charge_split {axes s : ℕ} (fits : B.blockCharge*s ≤ axes) :
    axes = (B.repeat s).charge+(axes-(B.repeat s).charge) := by
  rw [B.charge_repeat]
  omega

private theorem width_cast {d l l' : ℕ} (h : l=l') (A : State d l) :
    (h ▸ A : State d l').maxWidth = A.maxWidth := by cases h; rfl

/-- The concrete register for the same recast physical run that computes the trace.
Its padded letter count depends only on the fixed compressor. -/
def physicalTable {k : ℕ} (hk : 2≤k+1) (low offsets slots s W : ℕ)
    (fits : B.blockCharge*s≤k+1)
    (enough : B.repeatFactor*((B.cursorState hk low offsets slots).maxWidth+1)*
      B.widthBase^s < 2^W) :
    Program.RecordTable (Physical.run B hk low offsets slots s fits) B.alphabetCap W
      (stageCounts B s (k+1)) := by
  let P := B.repeat s
  let rem := k+1-P.charge
  let A := B.cursorState hk low offsets slots
  have split : k+1=P.charge+rem := charge_split B fits
  let A' : State (2^B.exponent 0) (P.charge+rem) := split ▸ A
  have widths : A'.maxWidth = A.maxWidth := width_cast split A
  have base : @Fintype.card A'.Base A'.finiteBase = k+1 :=
    (Program.baseCast split A).trans (Fintype.card_fin (k+1))
  have budget : B.repeatFactor*((A'.maxWidth+1)*B.widthBase^s) < 2^W := by
    rw [widths, ←Nat.mul_assoc]
    exact enough
  let table := B.recordTable B.alphabetCap W s rem A' le_rfl budget
  exact (Program.changeTable split A _ table).changeSizes (by simp only [base, stageCounts, rem, P])

/-- Every valid stage history has the single representation checked by the parser,
and parsing leaves its arbitrary shared-wire suffix untouched. -/
theorem physical_record_codec {k : ℕ} (hk : 2≤k+1) (low offsets slots s W : ℕ)
    (fits : B.blockCharge*s≤k+1)
    (enough : B.repeatFactor*((B.cursorState hk low offsets slots).maxWidth+1)*
      B.widthBase^s < 2^W) :
    let r := Physical.run B hk low offsets slots s fits
    let q := physicalTable B hk low offsets slots s W fits enough
    ∀ h : r.plan.History,
      (r.plan.write q.codes h).length = (stageCounts B s (k+1)).sum*B.alphabetCap*W ∧
      (∀ tail, r.plan.read q.codes (r.plan.write q.codes h ++ tail) = some (h,tail)) ∧
      (∀ raw tail, r.plan.read q.codes raw = some (h,tail) → raw = r.plan.write q.codes h ++ tail) := by
  intro r q h
  exact ⟨q.write_size h, r.plan.read_write q.codes h, fun raw tail => r.plan.write_read q.codes raw h tail⟩

theorem stage_count_sum_le (s axes : ℕ) (fits : B.blockCharge*s≤axes) :
    (stageCounts B s axes).sum ≤ (B.levels+1)*s*B.costFactors.sum*(axes*2^axes) := by
  have rows := (B.repeat s).histogram_rows B.costFactors.sum (B.factor_bound s)
    (axes-(B.repeat s).charge) axes
  rw [B.length_repeat, ←charge_split B fits] at rows
  exact rows

/-- The public tape contains sixty-four header words per real move. Its dense-word
and descriptor heap pointers bound the exact regions touched by the repeated schedule. -/
theorem schedule_footprint (s axes : ℕ) (fits : B.blockCharge*s ≤ axes)
    (cursor : NavigationDirectory.Cursor) :
    let steps := (B.repeat s).directory (axes-(B.repeat s).charge) axes
    let last := NavigationDirectory.finish B.alphabetCap steps cursor
    (NavigationDirectory.tape B.alphabetCap steps cursor).length = 64*((B.levels+1)*s) ∧
      last.dense = cursor.dense+B.alphabetCap*(stageCounts B s axes).sum ∧
      last.heap ≤ cursor.heap+(B.levels+1)*s*B.allocations.sum*(1+axes*2^axes) := by
  intro steps last
  refine ⟨?_, NavigationDirectory.dense_finish .., ?_⟩
  · rw [Program.header_length, B.length_repeat]
  · have bound := B.heap_usage s (axes-(B.repeat s).charge) axes B.alphabetCap cursor
    rw [B.length_repeat, ←charge_split B fits] at bound
    exact bound

/-- The source cell widths of every trace grid in a polynomially bounded offset/slot
window give valid words for the actual table, uniformly in the number of admitted blocks. -/
theorem physical_word_room {u s : ℕ → ℕ} (scale : Scale u s)
    (offsets slots : ℕ → ℕ) (a b : ℕ)
    (ports : ∀ᶠ w : ℕ in atTop, offsets w * slots w * 3 ≤ a*(w+1)^b) :
    ∀ᶠ w : ℕ in atTop, ∀ {k : ℕ} (hk : 2≤k+1),
      B.repeatFactor*((B.cursorState hk (w/2) (offsets w) (slots w)).maxWidth+1)*
        B.widthBase^(s w) < 2^(64*w) := by
  filter_upwards [ports, multiplicity_room scale B.repeatFactor a b B.widthBase]
    with w size room
  intro k hk
  have bound : (B.cursorState hk (w/2) (offsets w) (slots w)).maxWidth ≤
      2^(w/2)*(a*(w+1)^b) :=
    (B.cursorState hk (w/2) (offsets w) (slots w)).maxWidth_le fun i => by
      rw [B.cursorState_width]
      exact Nat.mul_le_mul_left _ size
  rw [Nat.mul_assoc]
  exact lt_of_le_of_lt (Nat.mul_le_mul_left _
    (Nat.mul_le_mul_right _ (Nat.add_le_add_right bound 1))) room

/-- Instantiate the width budget at the actual, machine-dependent trace table. -/
theorem native_table_word_room [Fintype F] {u s : ℕ → ℕ} (scale : Scale u s) :
    ∀ᶠ w : ℕ in atTop, ∀ {pc regs words : ℕ}, pc≤64*w → regs≤64*w → words≤64*w → ∀ {k : ℕ} (hk : 2≤k+1) (_axes : k+1=u w+1-w/2)
      (M : Computability.VPVNP.BurstRAM.PrivateRAM.Machine (64*w) pc regs words) {N base fuel : ℕ}
      (fit : NativeTrace.Fits M N base ((k+1)+w/2) fuel)
      (q : Fintype.card F ≤ 2^(64*w)) (st : Computability.VPVNP.BurstRAM.Word (64*w)),
      let slots := (TraceStaticRow.gateTable q fit.width fit.labels base fuel st regs words
        ((k+1)+w/2)).cells
      let offsets := 1+(((k+1)+w/2)+((k+1)+w/2))
      B.repeatFactor*((B.cursorState hk (w/2) offsets slots).maxWidth+1)*B.widthBase^(s w)
        < 2^(64*w) := by
  let a := 3*5*10^26*65^14
  filter_upwards [multiplicity_room scale B.repeatFactor a 15 B.widthBase,
    eventual_native_port_count (F:=F) scale] with w room ports
  intro pc regs words pcBound regBound wordBound k hk axes M N base fuel fit q st slots offsets
  have cols := ports pcBound regBound wordBound axes M fit q st
  have bound := (B.cursorState hk (w/2) offsets slots).maxWidth_le
    fun e => (B.cursorState_width hk (w/2) offsets slots e).le.trans
      (Nat.mul_le_mul_left _ cols)
  rw [Nat.mul_assoc]
  exact lt_of_le_of_lt (Nat.mul_le_mul_left _
    (Nat.mul_le_mul_right _ (Nat.add_le_add_right bound 1))) room

/-- The full public padded record fits at the paper's scale, for all physical
histories and at the actual `64*w` word width. -/
theorem eventual_record_length {u s : ℕ → ℕ} (scale : Scale u s) :
    ∀ᶠ w : ℕ in atTop, ∀ _hw : B.blockCharge*s w ≤ u w+1-w/2,
      (stageCounts B (s w) (u w+1-w/2)).sum*B.alphabetCap*(64*w) ≤ 2^(3*w/5) := by
  filter_upwards [record_room scale ((B.levels+1)*B.costFactors.sum*B.alphabetCap)] with w bound
  intro fits
  let axes := u w+1-w/2
  have rows := stage_count_sum_le B (s w) axes fits
  calc
    _ ≤ ((B.levels+1)*s w*B.costFactors.sum*(axes*2^axes))*B.alphabetCap*(64*w) :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ rows)
    _ = ((B.levels+1)*B.costFactors.sum*B.alphabetCap)*s w*(axes*2^axes)*(64*w) := by ring
    _ ≤ ((B.levels+1)*B.costFactors.sum*B.alphabetCap)*(s w+1)*(1+axes*2^axes)*(64*w+1) := by
      gcongr <;> omega
    _ ≤ _ := bound

/-- Sum of the instruction counts of the actual guards, including their constant
cost on a stage with no rows. -/
def guardsTime (K : ℕ) (counts : List ℕ) :=
  (counts.map fun rows => 6+rows*(2*RAM.AdmissionBank.cost 0 K+4)).sum

private theorem guardsTime_eq (K : ℕ) (counts : List ℕ) :
    guardsTime K counts=6*counts.length+counts.sum*(2*RAM.AdmissionBank.cost 0 K+4) := by
  induction counts with
  | nil => simp [guardsTime]
  | cons a l ih =>
    unfold guardsTime at *
    simp only [List.map_cons,List.sum_cons,List.length_cons, ih]
    ring

theorem eventual_guards_time {u s : ℕ → ℕ} (scale : Scale u s) :
    ∀ᶠ w : ℕ in atTop, ∀ _fits : B.blockCharge*s w ≤ u w+1-w/2,
      guardsTime B.alphabetCap (stageCounts B (s w) (u w+1-w/2)) ≤ 2^(3*w/5) := by
  let ticks := 2*RAM.AdmissionBank.cost 0 B.alphabetCap+4
  let A := (B.levels+1)*(6+B.costFactors.sum*ticks)
  filter_upwards [record_room scale A] with w bound
  intro fits
  let axes := u w+1-w/2
  let stages := (B.levels+1)*s w
  let volume := axes*2^axes
  have count : (stageCounts B (s w) axes).length=stages := by
    rw [stageCounts,List.length_map,Program.directory_length,B.length_repeat]
  have rows := stage_count_sum_le B (s w) axes fits
  rw [guardsTime_eq,count]
  calc
    _ ≤ 6*stages + stages*B.costFactors.sum*volume*ticks :=
      Nat.add_le_add_left (Nat.mul_le_mul_right _ rows) _
    _ ≤ A*(s w+1)*(1+volume) := by
      have lo : s w ≤ s w+1 := Nat.le_succ _
      have high : volume ≤ 1+volume := by omega
      calc
        _ ≤ 6*(B.levels+1)*(s w+1)*(1+volume) +
            (B.levels+1)*(s w+1)*B.costFactors.sum*(1+volume)*ticks := by
          apply Nat.add_le_add
          · dsimp [stages]
            exact (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ lo)).trans (by
              rw [←Nat.mul_assoc]
              exact Nat.le_mul_of_pos_right _ (by omega))
          · dsimp [stages]
            gcongr
        _ = _ := by dsimp [A]; ring
    _ ≤ A*(s w+1)*(1+volume)*(64*w+1) := Nat.le_mul_of_pos_right _ (by omega)
    _ ≤ _ := bound

/-- Reading raw bits into every padded histogram word takes five instructions
per bit plus a constant per word. This charges the actual input mount. -/
theorem eventual_pack_time {u s : ℕ → ℕ} (scale : Scale u s) :
    ∀ᶠ w : ℕ in atTop, ∀ _fits : B.blockCharge*s w ≤ u w+1-w/2,
      ((stageCounts B (s w) (u w+1-w/2)).sum*B.alphabetCap)*(5*(64*w)+6)+6 ≤ 2^(3*w/5) := by
  let C := (B.levels+1)*B.costFactors.sum*B.alphabetCap
  filter_upwards [record_room scale (6*(C+1))] with w room
  intro fits
  let axes := u w+1-w/2
  let vol := axes*2^axes
  have count := stage_count_sum_le B (s w) axes fits
  have stages : (stageCounts B (s w) axes).sum*B.alphabetCap ≤ C*s w*vol := by
    calc
      _ ≤ (B.levels+1)*s w*B.costFactors.sum*vol*B.alphabetCap := Nat.mul_le_mul_right _ count
      _ = _ := by dsimp [C];ring
  have price : 5*(64*w)+6≤6*(64*w+1) := by omega
  calc
    _ ≤ C*s w*vol*(6*(64*w+1))+6 := Nat.add_le_add_right (Nat.mul_le_mul stages price) _
    _ ≤ (6*(C+1))*(s w+1)*(1+vol)*(64*w+1) := by
      ring_nf
      omega
    _ ≤ _ := room

/-- At the actual verification grid there is a single physical record codec,
fixed before the input. Its accepted prefixes exhaust exactly the histories
and every accepted prefix has the required three-fifths length. -/
theorem native_history_codec [Fintype F] {u s : ℕ→ℕ} (scale : Scale u s) :
    ∀ᶠ w : ℕ in atTop, ∀ {pc regs words : ℕ}, pc≤64*w → regs≤64*w → words≤64*w → ∀ {k : ℕ} (hk : 2≤k+1) (_axes : k+1=u w+1-w/2)
      (M : Computability.VPVNP.BurstRAM.PrivateRAM.Machine (64*w) pc regs words) {N base fuel : ℕ}
      (fit : NativeTrace.Fits M N base ((k+1)+w/2) fuel)
      (q : Fintype.card F≤2^(64*w)) (st : Computability.VPVNP.BurstRAM.Word (64*w))
      (passes : B.blockCharge*s w≤k+1),
      let slots := (TraceStaticRow.gateTable q fit.width fit.labels base fuel st regs words ((k+1)+w/2)).cells
      let offsets := 1+(((k+1)+w/2)+((k+1)+w/2))
      let r := Physical.run B hk (w/2) offsets slots (s w) passes
      ∃ table : Program.RecordTable r B.alphabetCap (64*w) (stageCounts B (s w) (k+1)),
        ∀ h : r.plan.History, (r.plan.write table.codes h).length≤2^(3*w/5) ∧
          (∀ tail,r.plan.read table.codes (r.plan.write table.codes h++tail)=some (h,tail)) ∧
          (∀ raw tail,r.plan.read table.codes raw=some (h,tail)→ raw=r.plan.write table.codes h++tail) := by
  filter_upwards [native_table_word_room B scale,eventual_record_length B scale] with w fits length
  intro pc regs words pcBound regBound wordBound k hk axes M N base fuel fit q st passes slots offsets r
  let enough := fits pcBound regBound wordBound hk axes M fit q st
  let table := physicalTable B hk (w/2) offsets slots (s w) (64*w) passes enough
  refine ⟨table,fun h=>?_⟩
  obtain ⟨size,read,write⟩ := physical_record_codec B hk (w/2) offsets slots (s w) (64*w) passes enough h
  exact ⟨size.le.trans (by rw [axes];exact length (axes ▸ passes)),read,write⟩


end Hierarchy.TraceAdmission

end
end OAI
