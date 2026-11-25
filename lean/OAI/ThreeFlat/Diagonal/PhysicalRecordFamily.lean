import OAI.ThreeFlat.Diagonal.HistogramRegister
import OAI.ThreeFlat.Diagonal.PhysicalReadHistory
import OAI.ThreeFlat.Diagonal.BlockEnergyPotential
import OAI.ThreeFlat.Diagonal.CompressorWordEncoding

namespace OAI
/-! # The physical motif table determining one chronological binary record -/

namespace ThreeFlat.Diagonal.PhysicalStage
open MotifOuterTerms HistoryContraction
open scoped Classical BigOperators
noncomputable section

/-- The number and order of rows come from the displayed native graph. Each selected
grid tile supplies its own finite alphabet and repeat count. -/
structure RecordFamily (n : ℕ) where
  motifs : ℕ
  alphabet : Fin motifs → Type
  [finiteAlphabet : ∀ i,Fintype (alphabet i)]
  copies : Fin motifs → ℕ
  order : Fin n ≃ (∀ i : Fin motifs,Histogram (alphabet i) (copies i))

attribute [instance] RecordFamily.finiteAlphabet

namespace RecordFamily
variable {n : ℕ} (Q : RecordFamily n)

def Fits (K W : ℕ) : Prop :=
  (∀ i,Fintype.card (Q.alphabet i)≤K) ∧ (∀ i,Q.copies i<2^W)

def rows {K W : ℕ} (h : Q.Fits K W) : HistogramRegister.Rows Q.motifs K W :=
  ⟨fun i=>Fintype.card (Q.alphabet i),Q.copies,h.1,h.2⟩

def sequence {K W : ℕ} (h : Q.Fits K W) : Fin n ≃ HistogramRegister.Choices (Q.rows h) :=
  Q.order.trans (HistogramRegister.reindex (Q.rows h) (Equiv.refl _) (fun i=>(Fintype.equivFin (Q.alphabet i)).symm))

def record {K W : ℕ} (h : Q.Fits K W) : Record n := HistogramRegister.record (Q.rows h) (Q.sequence h)

@[simp] theorem record_width {K W : ℕ} (h : Q.Fits K W) : (Q.record h).width=Q.motifs*K*W := rfl

theorem words_val {K W : ℕ} (h : Q.Fits K W) (t : Fin n) (i : Fin Q.motifs)
    (v : Q.alphabet i) :
    (HistogramRegister.words (Q.rows h) (Q.sequence h t) i
        (((Fintype.equivFin _ v).castLE (h.1 i)))).val = ((Q.order t i).val v).val := by
  refine (HistogramRegister.words_active (Q.rows h) (Q.sequence h t) i (Fintype.equivFin _ v)).trans ?_
  change ((Q.order t i).val ((Fintype.equivFin _).symm (Fintype.equivFin _ v))).val = _
  rw [Equiv.symm_apply_apply]

end RecordFamily
namespace Run
variable {F : Type} [Field F]

def Families : {d l : ℕ} → {A : State d l} → Run F A → Type 1
  | _,_,_,.done _ => PUnit
  | _,_,_,.step R next => RecordFamily R.rules.count × (∀ t,(next t).Families)

def FamiliesFit (K W : ℕ) : {d l : ℕ} → {A : State d l} → (r : Run F A) → r.Families → Prop
  | _,_,_,.done _,_ => True
  | _,_,_,.step _ next,Q => Q.1.Fits K W ∧ ∀ t,(next t).FamiliesFit K W (Q.2 t)

def familyRecords (K W : ℕ) : {d l : ℕ} → {A : State d l} → (r : Run F A) →
    (Q : r.Families) → r.FamiliesFit K W Q → r.Records
  | _,_,_,.done _,_,_ => ()
  | _,_,_,.step _ next,Q,h => (Q.1.record h.1,fun t=>(next t).familyRecords K W (Q.2 t) (h.2 t))

def rowCounts : {d l : ℕ} → {A : State d l} → (r : Run F A) → r.Families → r.plan.History → List ℕ
  | _,_,_,.done _,_,_ => []
  | _,_,_,.step R next,Q,h =>
    Q.1.motifs :: (next h.1).rowCounts (Q.2 h.1) (tailHistory R next h)

private theorem write_cast {S T : Shape} (e : S=T) (P : Plan F S) (Q : P.Codes)
    (h : (e ▸ P : Plan F T).History) :
    (e ▸ P : Plan F T).write (castCodes e P Q) h = P.write Q (historyOfCast e P h) := by cases e; rfl

/-- The first n physical row records are admitted. The number consumed is measured in
stages; the data length at each step is the width of its actual selected finite family. -/
def PrefixOK : ℕ → {d l : ℕ} → {A : State d l} → (r : Run F A) → r.Records → List Bool → Prop
  | 0,_,_,_,_,_,_ => True
  | _+1,_,_,_,.done _,_,_ => False
  | n+1,_,_,_,.step _ next,E,s => ∃ i,E.1.read (s.take E.1.width)=some i ∧
      PrefixOK n (next i) (E.2 i) (s.drop E.1.width)

theorem PrefixOK.shorten {i j : ℕ} (le : i≤j) {d l : ℕ} {A : State d l}
    (r : Run F A) (E : r.Records) (s : List Bool) :
    PrefixOK j r E s → PrefixOK i r E s := by
  induction i generalizing j d l s with
  | zero => exact fun _=>trivial
  | succ i ih =>
    obtain ⟨j,rfl⟩:=Nat.exists_eq_succ_of_ne_zero (show j≠0 by omega)
    cases r with
    | done _ => exact id
    | step R next =>
      rintro ⟨t,h,tail⟩
      exact ⟨t,h,ih (Nat.le_of_succ_le_succ le) (next t) (E.2 t) _ tail⟩

/-- An index is a genuine number of physical stages on every branch of this run. -/
def StageLength : {d l : ℕ} → {A : State d l} → Run F A → ℕ → Prop
  | _,_,_,.done _,n => n=0
  | _,_,_,.step _ _,0 => False
  | _,_,_,.step _ next,n+1 => ∀ i,(next i).StageLength n

theorem read_cast_some {S T : Shape} (e : S=T) (P : Plan F S) (Q : P.Codes)
    (s : List Bool) :
    ((e ▸ P : Plan F T).read (castCodes e P Q) s).isSome ↔ (P.read Q s).isSome := by cases e; rfl

theorem read_cast_eq {S T : Shape} (e : S=T) (P : Plan F S) (Q : P.Codes)
    (s rest : List Bool) (h : (e ▸ P : Plan F T).History) :
    (e ▸ P : Plan F T).read (castCodes e P Q) s=some (h,rest) ↔
      P.read Q s=some (historyOfCast e P h,rest) := by cases e;rfl

theorem read_step_eq {d l D L : ℕ} {A : State d l} (R : Move F A D L)
    (next : ∀ t,Run F (R.next t)) (E : (Run.step R next).Records)
    (s rest : List Bool) (h : (Run.step R next).plan.History) :
    (Run.step R next).plan.read ((Run.step R next).codes E) s=some (h,rest) ↔
      E.1.read (s.take E.1.width)=some h.1 ∧
      (next h.1).plan.read ((next h.1).codes (E.2 h.1)) (s.drop E.1.width)=
        some (tailHistory R next h,rest) := by
  let P := (Run.step R next).plan
  let rs := (Run.step R next).codes E
  let T := (next h.1).plan
  let C := (next h.1).codes (E.2 h.1)
  have write : P.write rs h = E.1.write h.1 ++ T.write C (tailHistory R next h) := by
    exact congrArg (fun bits => E.1.write h.1 ++ bits)
      (write_cast (R.target_eq h.1).symm T C h.2)
  have length := E.1.write_length h.1
  constructor
  · intro parsed
    have eq := P.write_read rs s h rest parsed
    rw [write,List.append_assoc] at eq
    rw [eq,←length]
    simpa [E.1.read_write] using T.read_write C (tailHistory R next h) rest
  · rintro ⟨first,later⟩
    have head := E.1.write_read _ _ first
    have tail := T.write_read C _ _ rest later
    have joined : s=P.write rs h++rest := by
      calc
        s = s.take E.1.width++s.drop E.1.width := (List.take_append_drop ..).symm
        _ = E.1.write h.1 ++ (T.write C (tailHistory R next h)++rest) := by rw [←head,tail]
        _ = _ := by rw [write,List.append_assoc]
    rw [joined]
    exact P.read_write rs h rest

/-- The parser of the physical run tests this stage's actual finite histogram and then tests
the unique remaining physical computation selected by that record. -/
theorem read_step_some {d l D L : ℕ} {A : State d l} (R : Move F A D L)
    (next : ∀ t,Run F (R.next t)) (records : (Run.step R next).Records) (s : List Bool) :
    ((Run.step R next).plan.read ((Run.step R next).codes records) s).isSome ↔
      ∃ t,records.1.read (s.take records.1.width)=some t ∧
        ((next t).plan.read ((next t).codes (records.2 t)) (s.drop records.1.width)).isSome := by
  cases first : records.1.read (s.take records.1.width) with
  | none => simp [plan,codes,Plan.read,first]
  | some t =>
    simp only [plan,codes,Plan.read,first,Option.some.injEq,exists_eq_left']
    have keep {α β : Type} (v : Option α) (f : α → β) :
        (v.bind (fun x=>some (f x))).isSome = v.isSome := by cases v <;> rfl
    let e := (R.target_eq t).symm
    let P := (next t).plan
    let C := (next t).codes (records.2 t)
    let tail := (e ▸ P : Plan F (R.rules.target t)).read (castCodes e P C) (s.drop records.1.width)
    let wrap (hs : (e ▸ P : Plan F (R.rules.target t)).History × List Bool) :
        (Run.step R next).plan.History × List Bool := (⟨t,hs.1⟩,hs.2)
    change (tail.bind (fun hs=>some (wrap hs))).isSome = true ↔ (P.read C (s.drop records.1.width)).isSome = true
    exact (iff_of_eq (congrArg (fun b : Bool => b=true) (keep tail wrap))).trans
      (read_cast_some e P C _)

theorem PrefixOK.complete {n d l : ℕ} {A : State d l} (r : Run F A)
    (len : r.StageLength n) (E : r.Records) (s : List Bool) :
    PrefixOK n r E s ↔ (r.plan.read (r.codes E) s).isSome := by
  induction r generalizing n s with
  | done A =>
    change n=0 at len
    subst n
    simp [PrefixOK,plan,codes,Plan.read]
  | step R next ih =>
    cases n with
    | zero => exact False.elim len
    | succ n =>
      rw [read_step_some]
      change (∃ t,_ ∧ PrefixOK n (next t) _ _) ↔ _
      exact exists_congr fun t=>and_congr_right fun _=>ih t (len t) _ _

theorem write_length {d l K W : ℕ} {A : State d l} (r : Run F A) (Q : r.Families)
    (fit : r.FamiliesFit K W Q) (h : r.plan.History) :
    (r.plan.write (r.codes (r.familyRecords K W Q fit)) h).length =
      (r.rowCounts Q h).sum*K*W := by
  induction r with
  | done A => simp [plan,Plan.write,rowCounts]
  | step R next ih =>
    change ((Q.1.record fit.1).write h.1 ++
      (((R.target_eq h.1).symm ▸ (next h.1).plan : Plan F (R.rules.target h.1)).write
        (castCodes _ _ ((next h.1).codes ((next h.1).familyRecords K W (Q.2 h.1) (fit.2 h.1)))) h.2)).length = _
    rw [write_cast,List.length_append,(Q.1.record fit.1).write_length,RecordFamily.record_width]
    change _ + ((next h.1).plan.write _ (tailHistory R next h)).length =
      (Q.1.motifs :: (next h.1).rowCounts (Q.2 h.1) (tailHistory R next h)).sum * K * W
    rw [ih]
    simp [Nat.add_mul]
end Run

namespace State
open Computability.VPVNP.Compression
variable {d l : ℕ} (A : State d l)

abbrev edgeCount := (Fintype.card A.Base*d)*2^l

/-- Physical outgoing wire order in the flat terminal width array. -/
def wireOrder : (A.Base×Fin d)×BitWord l ≃ Fin A.edgeCount :=
  (((A.order.prodCongr (Equiv.refl _)).trans finProdFinEquiv).prodCongr
    (CompressorPacking.Native.tagOrdinal l)).trans finProdFinEquiv

theorem wireOrder_val (v : A.Base) (p : Fin d) (lane : BitWord l) :
    (A.wireOrder ((v,p),lane)).val =
      ((A.order v).val*d+p.val)*2^l+(CompressorPacking.Native.tagOrdinal l lane).val := by
  change _ + 2^l*(p.val+d*(A.order v).val) = _
  ac_rfl

def wireWidth (i : Fin A.edgeCount) := A.width (A.wireOrder.symm i)

theorem wireWidth_sum : (∑ i,A.wireWidth i)=A.widthSum := A.wireOrder.symm.sum_comp A.width

def bitAddress (i : Fin A.edgeCount) (j : Fin (A.wireWidth i)) : Fin A.widthSum :=
  (finCongr A.wireWidth_sum) (finSigmaFinEquiv ⟨i,j⟩)

theorem bitAddress_val (i : Fin A.edgeCount) (j : Fin (A.wireWidth i)) :
    (A.bitAddress i j).val = (∑ k : Fin i.val,A.wireWidth (Fin.castLE i.isLt.le k))+j.val :=
  finSigmaFinEquiv_apply _

/-- Follow the physical edge order and the actual little-endian width of each edge;
the two incidences of a self-loop read the same shared word. -/
def boundaryBits : A.shape.Boundary ≃ (Fin A.widthSum → Bool) :=
  (((Equiv.piCongrLeft (fun e => Fin (2^A.width e)) A.wireOrder.symm).symm.trans
    (Equiv.piCongrRight fun i=>(MotifBinaryPacking.word (A.wireWidth i)).symm)).trans
      (MotifBinaryPacking.flatten A.wireWidth)).trans
        (Equiv.arrowCongr (finCongr A.wireWidth_sum) (Equiv.refl Bool))

theorem boundaryBits_at (z : A.shape.Boundary) (i : Fin A.edgeCount) (j : Fin (A.wireWidth i)) :
    A.boundaryBits z (A.bitAddress i j) =
      (MotifBinaryPacking.word (A.wireWidth i)).symm (z (A.wireOrder.symm i)) j := by
  let bits (a : Fin A.edgeCount) :=
    (MotifBinaryPacking.word (A.wireWidth a)).symm (z (A.wireOrder.symm a))
  let readBit (p : (a : Fin A.edgeCount) × Fin (A.wireWidth a)) := bits p.1 p.2
  change (MotifBinaryPacking.flatten A.wireWidth bits)
    ((finCongr A.wireWidth_sum).symm ((finCongr A.wireWidth_sum) (finSigmaFinEquiv ⟨i,j⟩))) =
      readBit ⟨i,j⟩
  rw [Equiv.symm_apply_apply]
  exact congrArg readBit (finSigmaFinEquiv.symm_apply_apply ⟨i,j⟩)

theorem bitAddress_read (z : Fin A.widthSum → Bool) (i : Fin A.edgeCount) (j : Fin (A.wireWidth i)) :
    ((A.boundaryBits.symm z) (A.wireOrder.symm i)).val.testBit j.val=z (A.bitAddress i j) := by
  obtain ⟨y,rfl⟩ := A.boundaryBits.surjective z
  rw [Equiv.symm_apply_apply,A.boundaryBits_at]
  rfl

end State

namespace Run
variable {F : Type} [Field F]

/-- At the terminal visit retain the actual typed word array together with the folds
needed to relate its wire count and displayed shape to the chronological plan. -/
structure WireLayer where
  degree : ℕ
  lanes : ℕ
  state : State degree lanes

def terminalLayer {d l : ℕ} {A : State d l} (r : Run F A) (h : r.plan.History) : WireLayer :=
  r.readTerminal (fun {d l} a=>⟨d,l,a⟩) h

def EndsAt {d l : ℕ} {A : State d l} (r : Run F A) (E : r.Records) (raw : List Bool)
    (v : WireLayer) (tail : List Bool) : Prop := ∃ h : r.plan.History,
  r.plan.read (r.codes E) raw=some (h,tail) ∧ r.terminalLayer h=v

def historyToCast {X Y : Shape} (e : X=Y) (P : Plan F X) (h : P.History) :
    (e ▸ P : Plan F Y).History := by cases e;exact h

theorem historyOfToCast {X Y : Shape} (e : X=Y) (P : Plan F X) (h : P.History) :
    historyOfCast e P (historyToCast e P h)=h := by cases e;rfl

theorem endsAt_step {d l D L : ℕ} {A : State d l} (R : Move F A D L) (next : ∀ j,Run F (R.next j))
    (E : (Run.step R next).Records) (raw : List Bool) (j : Fin R.rules.count)
    (head : E.1.read (raw.take E.1.width)=some j) (v : WireLayer) (tail : List Bool) :
    (Run.step R next).EndsAt E raw v tail ↔ (next j).EndsAt (E.2 j) (raw.drop E.1.width) v tail := by
  constructor
  · rintro ⟨⟨i,h⟩,parsed,layer⟩
    obtain ⟨first,second⟩:=(read_step_eq R next E _ _ ⟨i,h⟩).mp parsed
    dsimp only at first
    have eq : j=i:=Option.some.inj (head.symm.trans first)
    subst i
    exact ⟨tailHistory R next ⟨j,h⟩,second,layer⟩
  · rintro ⟨h,parsed,layer⟩
    let e:=(R.target_eq j).symm
    let all : (Run.step R next).plan.History:=⟨j,historyToCast e (next j).plan h⟩
    have t : tailHistory R next all=h:=historyOfToCast e _ _
    refine ⟨all,(read_step_eq R next E _ _ all).mpr ⟨head,by simpa only [t] using parsed⟩,?_⟩
    change (next j).terminalLayer (tailHistory R next all)=v
    rwa [t]

private theorem read_map {α β : Type*} (f : ∀ {d l},State d l → α) (g : α → β)
    {d l : ℕ} {A : State d l} (r : Run F A) (h : r.plan.History) :
    g (r.readTerminal f h) = r.readTerminal (fun X=>g (f X)) h := by
  induction r with
  | done => rfl
  | step R next ih => exact ih h.1 (tailHistory R next h)

theorem terminalLayer_shape {d l : ℕ} {A : State d l} (r : Run F A) (h : r.plan.History) :
    (r.terminalLayer h).state.shape = r.plan.finish h :=
  (read_map (fun {d l} a=>(⟨d,l,a⟩ : WireLayer)) (fun v=>v.state.shape) r h).trans (r.terminal_shape h)

theorem terminalLayer_width {d l : ℕ} {A : State d l} (r : Run F A) (h : r.plan.History) :
    (r.terminalLayer h).state.widthSum = r.readTerminal (fun X=>X.widthSum) h :=
  read_map (fun {d l} a=>(⟨d,l,a⟩ : WireLayer)) (fun v=>v.state.widthSum) r h

def terminalLabels {d l : ℕ} {A : State d l} (r : Run F A) (h : r.plan.History) :
    (Fin ((r.terminalLayer h).state.widthSum) → Bool) ≃ (r.plan.finish h).Boundary :=
  ((r.terminalLayer h).state.boundaryBits.symm).trans
    (Equiv.cast (congrArg Shape.Boundary (r.terminalLayer_shape h)))

end Run
end
end ThreeFlat.Diagonal.PhysicalStage

end OAI
