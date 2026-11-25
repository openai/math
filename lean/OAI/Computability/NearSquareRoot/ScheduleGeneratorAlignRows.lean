import OAI.Computability.NearSquareRoot.ScheduleGeneratorPublicRoute
import OAI.Computability.NearSquareRoot.CommonAlphabetPublicNumbering

/-! # Effective rows of the output-head alignment wrapper -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Generator.Alignment

open CommonAlphabet IntegerMultiplication TM Routing

variable {A I : Type} (a : Numbering A) (i : Numbering I)

private abbrev Reads := i.option.arrow a
private abbrev OldOps := i.arrow (a.prod Numbering.move)
private abbrev Ops := i.option.arrow (a.prod Numbering.move)

/-- `false` and `true` are digits zero and one in the sign field. -/
private def bval (b : Bool) := (Numbering.bool.equiv b).val

private def runTag (q b : ℕ) := b + 2*q + 2
private def unwindTag (q b : ℕ) := q*2 + b + 2

private theorem run_rank {Q : Type} (q : Numbering Q) (s : Q) (b : Bool) :
    (q.align.equiv (.run s b)).val = runTag (q.equiv s).val (bval b) := rfl
private theorem rewind_rank {Q : Type} (q : Numbering Q) (b : Bool) :
    (q.align.equiv (.rewind b)).val = unwindTag q.size (bval b) := rfl

private def readOld := lookup (Reads a i) fun r => ((i.arrow a).equiv (fun k => r (some k))).val

private def stationary (r : Option I → A) (k : I) : A × Move := (r (some k),.stay)

private def staying := lookup (Reads a i) fun r => ((Ops a i).equiv
    (Align.banks (stationary r) (r none,.stay))).val
private def booting (marker : A) := lookup (Reads a i) fun r => ((Ops a i).equiv
    (Align.banks (stationary r) (marker,.stay))).val

private def signedRead (r b : ℕ) := b + 2*r

private theorem signedRead_rank (r : Option I → A) (b : Bool) :
    signedRead ((Reads a i).equiv r).val (bval b) =
      (((Reads a i).prod Numbering.bool).equiv (r,b)).val := rfl

private def tagged [DecidableEq A] (marker : A) := lookup (Reads a i) fun r =>
  if r none = marker then 1 else 0

private def unwindAction [DecidableEq I] [DecidableEq A] (out : I) (blank marker : A) :=
  lookup ((Reads a i).prod Numbering.bool) fun (r,b) =>
    ((Ops a i).equiv (if r none = marker then Align.banks (stationary r) (blank,.stay)
      else Align.banks (fun j => (r (some j), if j=out then Align.toward b else .stay)) (r none,.left))).val

private def newSign [DecidableEq A] (out : I) (marker : A) :=
  lookup₂ ((Reads a i).prod Numbering.bool) (OldOps a i) fun (r,b) o =>
    bval (Align.foldSign (decide (r none = marker)) b (o out).2)

private def newAction [DecidableEq A] (out : I) (marker : A) :=
  lookup₂ ((Reads a i).prod Numbering.bool) (OldOps a i) fun (r,b) o =>
    ((Ops a i).equiv (Align.banks o (r none, Align.foldMove (decide (r none = marker)) b (o out).2))).val

variable [DecidableEq I] [DecidableEq A] (out : I) (blank marker : A)

/-- A row of the extended machine. The input and output tuples include its folded distance tape. -/
def rows (size entry : ℕ → ℕ) (orig : Rows) : Rows := fun j (p,r) =>
  let k := (p-2)/2
  let b := (p-2)%2
  let rb := signedRead r b
  if p=0 then some (runTag (entry j) 0, booting a i marker r)
  else if p=1 then none
  else if k < size j then
    some (((orig j (k, readOld a i r)).map (fun (q,o) =>
      (runTag q (newSign a i out marker rb o), newAction a i out marker rb o))).getD
        (unwindTag (size j) b, staying a i r))
  else some (if tagged a i marker r = 1 then 1 else unwindTag (size j) b,
    unwindAction a i out blank marker rb)

theorem rows_correct {Q : ℕ → Type} (q : ∀ j, Numbering (Q j)) (entry : ∀ j, Q j)
    (m : ∀ j, Rule A (Q j) I) (orig : Rows)
    (correct : ∀ j s r, orig j (((q j).equiv s).val, ((i.arrow a).equiv r).val) =
      (m j s r).map fun z => (((q j).equiv z.1).val, ((OldOps a i).equiv z.2).val))
    (j : ℕ) (s : Align.Phase (Q j)) (r : Option I → A) :
    rows a i out blank marker (fun t => (q t).size) (fun t => ((q t).equiv (entry t)).val) orig
      j (((q j).align.equiv s).val, ((Reads a i).equiv r).val) =
      (Align.rule out blank marker (entry j) (m j) s r).map fun z =>
        (((q j).align.equiv z.1).val, ((Ops a i).equiv z.2).val) := by
  cases s with
  | boot => simp only [rows, show ((q j).align.equiv .boot).val = 0 from rfl, ↓reduceIte,
                       booting, lookup_rank, Align.rule, Option.map_some]; rfl
  | done => rfl
  | rewind b =>
    have hb : bval b < 2 := (Numbering.bool.equiv b).isLt
    have h0 : unwindTag (q j).size (bval b) ≠ 0 := by unfold unwindTag; omega
    have h1 : unwindTag (q j).size (bval b) ≠ 1 := by unfold unwindTag; omega
    have hu : (unwindTag (q j).size (bval b) - 2) / 2 = (q j).size := by unfold unwindTag; omega
    have hv : (unwindTag (q j).size (bval b) - 2) % 2 = bval b := by unfold unwindTag; omega
    simp only [rows, rewind_rank, h0,h1,hu,hv,Nat.lt_irrefl,↓reduceIte,signedRead_rank,
      unwindAction,tagged,lookup_rank,Align.rule]
    by_cases h : r none = marker <;> simp [h,rewind_rank,show ((q j).align.equiv .done).val = 1 from rfl]
    rfl
  | run s b =>
    have hb : bval b < 2 := (Numbering.bool.equiv b).isLt
    let k := ((q j).equiv s).val
    have hk : k < (q j).size := ((q j).equiv s).isLt
    have h0 : runTag k (bval b) ≠ 0 := by unfold runTag; omega
    have h1 : runTag k (bval b) ≠ 1 := by unfold runTag; omega
    have hu : (runTag k (bval b) - 2) / 2 = k := by unfold runTag; omega
    have hv : (runTag k (bval b) - 2) % 2 = bval b := by unfold runTag; omega
    dsimp only [k] at h0 h1 hu hv hk
    simp only [rows,run_rank,h0,h1,hu,hv,hk,↓reduceIte,readOld,lookup_rank,signedRead_rank]
    rw [correct]
    cases h : m j s (fun u => r (some u)) with
    | none =>
      simp [Align.rule,h,rewind_rank,staying,lookup_rank]
      rfl
    | some z =>
      obtain ⟨q',o⟩ := z
      simp [Align.rule,h,run_rank,newSign,newAction,lookup₂_rank]

private theorem ifDec {X Y : Type} [Primcodable X] [Primcodable Y]
    {p : X → Prop} [DecidablePred p] {f g : X → Y}
    (hp : Computable fun x => decide (p x)) (hf : Computable f) (hg : Computable g) :
    Computable fun x => if p x then f x else g x :=
  (Computable.cond hp hf hg).of_eq fun x => by by_cases h : p x <;> simp [h]

private theorem primrec_runTag : Primrec₂ runTag :=
  Primrec.nat_add.comp (Primrec.nat_add.comp Primrec.snd
    (Primrec.nat_mul.comp (Primrec.const 2) Primrec.fst)) (Primrec.const 2)

private theorem primrec_unwindTag : Primrec₂ unwindTag :=
  Primrec.nat_add.comp (Primrec.nat_add.comp
    (Primrec.nat_mul.comp Primrec.fst (Primrec.const 2)) Primrec.snd) (Primrec.const 2)

theorem computable_rows {size entry : ℕ → ℕ} {orig : Rows}
    (hs : Computable size) (he : Computable entry) (ho : Computable₂ orig) :
    Computable₂ (rows a i out blank marker size entry orig) := by
  let X := ℕ × ℕ × ℕ
  let j (v : X) := v.1
  let p (v : X) := v.2.1
  let r (v : X) := v.2.2
  let k (v : X) := (p v-2)/2
  let b (v : X) := (p v-2)%2
  let rb (v : X) := signedRead (r v) (b v)
  have hj : Computable j := Computable.fst
  have hp : Computable p := Computable.fst.comp Computable.snd
  have hr : Computable r := Computable.snd.comp Computable.snd
  have sub := Primrec.nat_sub.to_comp.comp hp (Computable.const 2)
  have hk : Computable k := Primrec.nat_div.to_comp.comp sub (Computable.const 2)
  have hb : Computable b := Primrec.nat_mod.to_comp.comp sub (Computable.const 2)
  have hrb : Computable rb := Primrec.nat_add.to_comp.comp hb (Primrec.nat_mul.to_comp.comp (Computable.const 2) hr)
  have hsize := hs.comp hj
  have uw := primrec_unwindTag.to_comp.comp hsize hb
  let rop := newAction a i out marker
  let rsign := newSign a i out marker
  have ops : Computable₂ rop := (primrec_lookup₂ _ _ _).to_comp
  have sgn : Computable₂ rsign := (primrec_lookup₂ _ _ _).to_comp
  have old := ho.comp hj (hk.pair ((primrec_lookup _ _).to_comp.comp hr :
    Computable fun v => readOld a i (r v)))
  change Computable fun v : X => if p v = 0 then _ else if p v = 1 then _ else if k v < size (j v) then _ else _
  apply ifDec (Primrec.eq.decide.to_comp.comp hp (Computable.const 0))
  · exact Computable.option_some.comp ((primrec_runTag.to_comp.comp (he.comp hj) (Computable.const 0)).pair
      ((primrec_lookup _ _).to_comp.comp hr))
  apply ifDec (Primrec.eq.decide.to_comp.comp hp (Computable.const 1)) (Computable.const none)
  apply ifDec (Primrec.nat_lt.decide.to_comp.comp hk hsize)
  · apply Computable.option_some.comp
    apply Computable.option_getD (Computable.option_map old ?_)
    · exact uw.pair ((primrec_lookup _ _).to_comp.comp hr)
    · exact (primrec_runTag.to_comp.comp (Computable.fst.comp Computable.snd)
        (sgn.comp (hrb.comp Computable.fst) (Computable.snd.comp Computable.snd))).pair
        (ops.comp (hrb.comp Computable.fst) (Computable.snd.comp Computable.snd))
  · apply Computable.option_some.comp
    apply Computable.pair
    · exact ifDec (Primrec.eq.decide.to_comp.comp ((primrec_lookup _ _).to_comp.comp hr)
        (Computable.const 1)) (Computable.const 1) uw
    · exact (primrec_lookup _ _).to_comp.comp hrb

end Generator.Alignment

end NearSquareRoot
end Computability
end OAI
