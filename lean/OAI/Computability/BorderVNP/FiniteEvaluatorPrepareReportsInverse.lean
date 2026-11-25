import OAI.Computability.BorderVNP.FiniteEvaluatorPrepareReportsMemory
import OAI.Computability.BorderVNP.FiniteDiagonalCellTraceCopied

/-! # Recovering every actual finite report-preparation branch

Replay an arbitrary observed tape with trailing padding. The deterministic
clocked traversal consumes exactly the declared scalar positions and ends at
the same memory and bank. The physical bit-major matrix is uniquely readable
from those bits, including the empty case.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FiniteEvaluator.Reports

open VPVNP.BurstRAM RoutingISA DiagonalResidueRAM TeamRAM

/-- Required number of fresh bits in all the owned rows. -/
def capacity (rows : List Row) := (rows.flatMap Row.bits).length

/-- Split a chronological choice stream at the actual row boundaries. -/
def rebit : List Row → List Bool → List Row
  | [],_ => []
  | r::rs,t => {r with bits := t.take r.bits.length} :: rebit rs (t.drop r.bits.length)

@[simp] theorem rebit_length (rows : List Row) (t : List Bool) : (rebit rows t).length=rows.length := by
  induction rows generalizing t <;> simp [rebit, *]

/-- Shapes and addresses of two row records coincide. -/
def Row.SameShape (a b : Row) :=
  a.number=b.number ∧ a.base=b.base ∧ a.canonical=b.canonical ∧ a.bits.length=b.bits.length

private theorem capacity_cons (r : Row) (rs : List Row) : capacity (r::rs)=r.bits.length+capacity rs := by
  simp [capacity]

/-- All physical report cost is constant per row plus six ticks per supplied bit. -/
theorem ticks_eq (rows : List Row) :
    ticks rows=1+rows.length*(beginCell.slots+publish.slots+7)+6*capacity rows := by
  induction rows with
  | nil => simp [ticks,capacity]
  | cons r rs ih => rw [ticks,ih,capacity_cons,List.length_cons]; ring

private theorem shape (rs : List Row) (t : List Bool) (room : capacity rs ≤ t.length)
    (i : Fin rs.length) : rs[i].SameShape ((rebit rs t)[i.val]'(by simp)) := by
  induction rs generalizing t with
  | nil => exact Fin.elim0 i
  | cons r rs ih =>
    rw [capacity_cons] at room
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [rebit,Row.SameShape,List.length_take_of_le (by omega : r.bits.length ≤ t.length)]
    · exact ih (t.drop r.bits.length) (by simp [List.length_drop]; omega) j

private theorem bits_rebit (rs : List Row) (t : List Bool) :
    (rebit rs t).flatMap Row.bits = t.take (capacity rs) := by
  induction rs generalizing t with
  | nil => simp [rebit,capacity]
  | cons r rs ih => simp only [rebit,List.flatMap_cons,capacity_cons,ih,List.take_add]

private theorem shape_ticks {rs : List Row} {t : List Bool} (room : capacity rs ≤ t.length) :
    ticks (rebit rs t)=ticks rs := by
  induction rs generalizing t with
  | nil => rfl
  | cons r rs ih =>
    rw [capacity_cons] at room
    simp only [rebit,ticks,List.length_take_of_le (by omega : r.bits.length ≤ t.length)]
    rw [ih (by simp [List.length_drop]; omega)]

private theorem rebit_exact (rs : List Row) (t : List Bool) (room : capacity rs ≤ t.length) :
    rebit rs ((rebit rs t).flatMap Row.bits) = rebit rs t := by
  induction rs generalizing t with
  | nil => rfl
  | cons r rs ih =>
    rw [capacity_cons] at room
    let first := t.take r.bits.length
    let rest := t.drop r.bits.length
    let bs := (rebit rs rest).flatMap Row.bits
    have len : first.length=r.bits.length := List.length_take_of_le (by omega)
    have tk : (first++bs).take r.bits.length=first := by simpa only [len] using (List.take_left (l₁:=first) (l₂:=bs))
    have dr : (first++bs).drop r.bits.length=bs := by simpa only [len] using (List.drop_left (l₁:=first) (l₂:=bs))
    change {r with bits := (first++bs).take r.bits.length}::rebit rs ((first++bs).drop r.bits.length) = _
    rw [tk,dr,ih (t:=rest) (by simp [rest,List.length_drop]; omega)]
    rfl

private theorem rebit_inputs {w : ℕ} (l : Layout) (p : ℕ) (rows : List Row) (m : ℕ → ℕ) (t : List Bool)
    (long : capacity rows ≤ t.length) (headers : ∀ i : Fin rows.length, rows[i].Stored (p+6*i.val) m)
    (room : ∀ i : Fin rows.length, rows[i].Fits l w (p+6*i.val))
    (apart : ∀ i j : Fin rows.length, i<j → ∀ k : Fin 3, rows[i].Outside l (p+6*j.val+k.val)) :
    Inputs l w (rebit rows t) p m := by
  apply inputs_from_stored
  · intro i
    let j : Fin rows.length := Fin.cast (rebit_length rows t) i
    obtain ⟨hn,hb,hc,_⟩ := shape rows t long j
    have hr := headers j
    exact ⟨hr.1.trans hn,hr.2.1.trans hb,hr.2.2.trans hc⟩
  · intro i
    let j : Fin rows.length := Fin.cast (rebit_length rows t) i
    obtain ⟨hn,hb,hc,hl⟩ := shape rows t long j
    have hr := room j
    change (rebit rows t)[j.val].Fits l w (p+6*j.val)
    simpa only [Row.Fits,Row.start,← hn,← hb,← hc,← hl] using hr
  · intro i j lt k
    let a := Fin.cast (rebit_length rows t) i
    let b := Fin.cast (rebit_length rows t) j
    obtain ⟨hn,hb,hc,hl⟩ := shape rows t long a
    have old := apart a b lt k
    change (rebit rows t)[a.val].Outside l (p+6*b.val+k.val)
    simpa only [Row.Outside,Row.start,← hn,← hb,← hc,← hl] using old

/-- Exhaustive inverse for any real report-preparation run. Both the physical
memory image and native trace cost are forced by its exact observed choice
string. Only initial headers, numerical bounds and actual write separation
are needed. -/
theorem prepare_cover {w : ℕ} (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8) (s : Bank w) (m : Memory w)
    (l : Layout) (rows : List Row) (ptr : (pub 0).val=l.frame) (seed : l.Seed rows.length (readings m))
    (frame : l.frame+92 < 2^w) (control : l.control+27 < 2^w) (space : l.headers+6*rows.length < 2^w)
    (headers : ∀ i : Fin rows.length, rows[i].Stored (l.headers+6*i.val) (readings m))
    (room : ∀ i : Fin rows.length, rows[i].Fits l w (l.headers+6*i.val))
    (apart : ∀ i j : Fin rows.length, i<j → ∀ k : Fin 3, rows[i].Outside l (l.headers+6*j.val+k.val))
    {es u mu} (run : Runs pub mac prepareReports s m es u mu) :
    let choices := es.flatMap Event.choices
    choices.length=capacity rows ∧ TraceOK es choices es.length ∧ traceCost es ≤ setup.slots+ticks rows ∧
      readings mu=image l (rebit rows choices) (readings m) := by
  intro choices
  let t := choices++List.replicate (capacity rows) false
  have long : capacity rows ≤ t.length := by simp [t]
  let fresh := rebit rows t
  have length : fresh.length=rows.length := rebit_length ..
  have input := rebit_inputs l l.headers rows (readings m) t long headers room apart
  obtain ⟨fs,v,mv,rr,tr,cost,mem⟩ := prepare_run pub mac s m l fresh ptr (length ▸ seed) frame control (length ▸ space) input
  have tape : choices++List.replicate (capacity rows) false=(fs.flatMap Event.choices)++t.drop (capacity rows) := by
    rw [tr.2.1,bits_rebit]
    exact (List.take_append_drop _ t).symm
  obtain ⟨rfl,rfl,rfl⟩ := unique_returns (c:=prepareReports) (by decide) run rr tape
  have chosen : choices=fresh.flatMap Row.bits := tr.2.1
  refine ⟨?_,?_,?_,?_⟩
  · rw [chosen,bits_rebit,List.length_take_of_le long]
  · exact ⟨rfl,rfl,tr.2.2⟩
  · exact cost.trans_eq (congrArg (setup.slots+·) (shape_ticks long))
  · rw [chosen,rebit_exact rows t long]
    exact mem

open private reportBits_eq from OAI.Computability.BorderVNP.FiniteDiagonalCellTraceCopied

/-- Every physical bit stream of the prescribed length is the bit-major encoding
of exactly one field report matrix, even at zero width. -/
theorem decode_unique (F : Type*) [Fintype F] (digits : ℕ) (bs : List Bool) (hlen : bs.length=digits*Fintype.card F) :
    ∃! c : Fin (Fintype.card F) → Fin digits → Bool, FiniteScalarRounds.stream F c=bs := by
  let get := fun j : Fin (digits*Fintype.card F) => bs[j.val]'(by rw [hlen]; exact j.isLt)
  let c := fun (v : Fin (Fintype.card F)) (i : Fin digits) => get (finProdFinEquiv (i,v))
  have formula (r : Fin (Fintype.card F) → Fin digits → Bool) :
      FiniteScalarRounds.stream F r = List.ofFn fun j : Fin (digits*Fintype.card F) =>
        r (finProdFinEquiv.symm j).2 (finProdFinEquiv.symm j).1 := reportBits_eq r
  have read (r : Fin (Fintype.card F) → Fin digits → Bool) (h : FiniteScalarRounds.stream F r=bs) :
      ∀ i v, r v i=c v i := by
    rw [formula] at h
    intro i v
    let j := finProdFinEquiv (i,v)
    have hj := congrArg (fun l : List Bool => l[j.val]?) h
    rw [List.getElem?_ofFn,dite_eq_left j.isLt,List.getElem?_eq_getElem (by rw [hlen]; exact j.isLt)] at hj
    exact (congrArg (fun p : Fin digits × Fin (Fintype.card F) => r p.2 p.1) (finProdFinEquiv.symm_apply_apply (i,v))).symm.trans
      (Option.some.inj hj)
  refine ⟨c,?_,fun r h => funext fun v => funext fun i => read r h i v⟩
  change FiniteScalarRounds.stream F c=bs
  rw [formula]
  have eq : (fun j : Fin (digits*Fintype.card F) => c (finProdFinEquiv.symm j).2 (finProdFinEquiv.symm j).1)=get := by
    funext j
    exact congrArg get (finProdFinEquiv.apply_symm_apply j)
  rw [eq]
  apply List.ext_getElem (by simp [hlen])
  intro i h₁ h₂
  rw [List.getElem_ofFn]

end FiniteEvaluator.Reports

end BorderVNP
end Computability
end OAI
