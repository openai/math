import OAI.Computability.MultitapeWeakETH.ShrinkHiddenRecipe
import OAI.Computability.VPVNP.PairShrinkRolePackedHidden

/-! # Demand and payload records of a resident shrinking map -/

namespace OAI.Computability.MultitapeWeakETH.ShrinkMap

open VPVNP BurstRAM BurstRAM.PrivateRAM Compression Compression.ShrinkMotif
open CompressorRecords DescriptorSpace PhaseRecipe PairSimulation ShrinkBlockInputs MapResidentRows
open scoped Classical Fin.CommRing
noncomputable section

/-- The selected owner row lists motif-party pairs in directory order. -/
def key (a : ℕ) : Expr :=
  .load (((Expr.header 35).add ((Expr.publicWord 0).mul (.lit (capacity a)))).add (.publicWord 1))

def party (a : ℕ) := (key a).mod (.lit 6)
def ordinal (a : ℕ) := (key a).div (.lit 6)

/-- The demand and payload expressions only need the public level header and motif ordinal. -/
def inputs (a : ℕ) : ShrinkCallFields.Inputs :=
  ⟨.state,ordinal a,.lit 0,.lit 0,.lit 0,.lit 0,fun _ => .lit 0⟩

variable {k : Type} [_root_.Field k] {S : BlockSchedule k} (B : S.Templates) (i : Fin S.steps)
  {g w : ℕ} (X : State (a i) (packingLaneBits (a i) g))
  (sel : SelectedScore.Selection B X) (base : Word w) (positions blocks n cur : ℕ)
  (mem : Memory w)
local notation "L" => BlockProgram.layout B base.val positions blocks
local notation "head" => levelStart L cur
local notation "first" => tableBase L cur (5 : Fin 6)
local notation "cut" => tableBase L cur (0 : Fin 6)
local notation "side" => SelectedFinish.chosen B X sel

set_option maxHeartbeats 2000000 in
/-- Decode a row by its owner and local index, and identify both parts of its ID. -/
theorem item_read (stored : CompiledResident.ShrinkPayload B base positions blocks n cur i X sel mem)
    (v : Site X) (j : Fin (order X side v).length) (p : Fin 5 → Word w)
    (owner : p 0 = ((siteIndex X v).val : Word w)) (index : p 1 = (j.val : Word w)) :
    let ev := Expr.eval p (head : Word w) mem
    let e := entry X side v j
    ev (ordinal (a i)) = ((ShrinkMotifOrder.stateNumber X e.1).val : Word w) ∧
      ev (party (a i)) = (e.2.val : Word w) := by
  intro ev e
  let H := ShrinkResidentLayout.layout X first
  let t := H.params (a i) true w
  have fit : H.endAddr < 2^w := stored.bounds.residentEnd.trans_lt
    ((levelStart_mono L stored.bounds.nextLive.le).trans_lt stored.bounds.room)
  have headerRoom := stored.words.oldRoom
  have headCell : ev (.header 35) = (H.rows true : Word w) := by
    change mem (((head : Word w) + ((35 : ℕ) : Word w)).val) = _
    rw [← Nat.cast_add,Fin.val_cast_of_lt (by omega)]
    exact stored.words.residentHeads 5
  have rows : MapResidentRows.Directory X side t mem := stored.sources.residents true
  let num := (ShrinkMotifOrder.stateNumber X e.1).val
  have rbase : (t 5).val = H.rows true := (ShrinkResidentLayout.frame X first true fit).2.2.2.2.2.2
  have endFit : (t 5).val + (siteIndex X v).val * capacity (a i) + capacity (a i) < 2^w :=
    (MapResidentRows.directory_fit X first v fit).2
  have localIdx : j.val < capacity (a i) := j.isLt.trans_eq (length_eq X side v)
  have posFit : (t 5).val + (siteIndex X v).val * capacity (a i) + j.val < 2^w := by omega
  have raw : (ev (key (a i))).val = num*6 + e.2.val := by
    change (mem (ev (.header 35) + p 0 * (capacity (a i) : Word w) + p 1).val).val = _
    rw [headCell,← rbase,owner,index,← Nat.cast_mul,← Nat.cast_add,← Nat.cast_add,Fin.val_cast_of_lt posFit]
    exact allocated_id X first fit rows v j
  have six : (6 : Word w).val = 6 := Nat.mod_eq_of_lt (show 6 < 2^w by omega)
  have hj := e.2.isLt
  constructor
  · change Fin.ofNat _ ((ev (key (a i))).val/(6 : Word w).val) = _
    rw [six,raw,show (num*6+e.2.val)/6 = num by omega]
    rfl
  · change Fin.ofNat _ ((ev (key (a i))).val%(6 : Word w).val) = _
    rw [six,raw,show (num*6+e.2.val)%6 = e.2.val by omega]
    rfl

set_option maxHeartbeats 1800000 in
/-- Read both demand widths, all eight payload widths and the repetition count from
the term belonging to this occurrence. -/
theorem item_fields (stored : CompiledResident.ShrinkPayload B base positions blocks n cur i X sel mem)
    (v : Site X) (j : Fin (order X side v).length) (p : Fin 5 → Word w)
    (owner : p 0 = ((siteIndex X v).val : Word w)) (index : p 1 = (j.val : Word w)) :
    let ev := Expr.eval p (head : Word w) mem
    let motif := (entry X side v j).1
    let demand := X.packingData.shrinkDemandWidths X.shrinkNumber X.packingWidth motif
    (∀ d, ev ((inputs (a i)).demand d) = (demand d : Word w)) ∧
      (∀ e, ev ((inputs (a i)).payload e) = ((sel motif).val e : Word w)) ∧
      ev (inputs (a i)).copies = ((MotifConversion.repetitions B.shrink demand : ℕ) : Word w) := by
  intro ev motif demand
  let term := ShrinkInput.termHead (w:=w) X cut
  let dense := ShrinkInput.demandHead (w:=w) X cut
  let scratch : ShrinkCallFields.Scratch := ⟨0,0,0,0⟩
  have id := (item_read B i X sel base positions blocks n cur mem stored v j p owner index).1
  have h : ShrinkCallFields.Stored p (head : Word w) mem X motif (inputs (a i)) scratch term dense 10 side (fun _ => 0) :=
    ⟨id,rfl,rfl,rfl,rfl,stored.words.level.termHead,stored.words.level.termStride,stored.words.level.layout,
      stored.words.level.demandHead,fun _ => rfl⟩
  let M := ShrinkTermSelection.bundles X * ShrinkTermSelection.ranks (a i)
  have room := stored.bounds.termRoom
  change ShrinkInput.stop X cut + 2*M + M*10 < 2^w at room
  have mfit : (ShrinkMotifOrder.stateNumber X motif).val < M := (ShrinkMotifOrder.stateNumber X motif).isLt
  have tval : term.val = ShrinkInput.stop X cut + 2*M := Nat.mod_eq_of_lt (by omega)
  have dval : dense.val = ShrinkInput.stop X cut := Nat.mod_eq_of_lt (by omega)
  have result := ShrinkCallFields.fields_eval (inputs (a i)) scratch term dense 10 side (fun _ => 0) h
    stored.sources.pairs (stored.sources.terms motif) (by rw [dval]; omega) (by rw [tval]; omega) (0 : Fin 6)
  exact ⟨fun d => result (.demand d),fun e => result (.payload e),result .copies⟩

end
end OAI.Computability.MultitapeWeakETH.ShrinkMap
