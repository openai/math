import OAI.ThreeFlat.Diagonal.TickLocalMatrix
import OAI.ThreeFlat.RAM.TickTransferWeight
import OAI.ThreeFlat.RAM.TickChunkTransfer

namespace OAI
/-! # Identifying the installed one-tick team with the chronological scalar -/

noncomputable section
namespace ThreeFlat.Diagonal.TickPhaseModel

open HistoryContraction TickChronology TickAuxiliary PackedChunkTransfer RotatedChunkGuards
open RAM.TickActiveROM RAM.Contraction RAM.BitLayout RAM
open scoped Classical BigOperators
variable {F : Type*} [Field F] [Fintype F] {S : Shape} {P : Plan F S} {E : P.Codes} {bits : P.History → ℕ}
  {A : RAM.TickActiveROM.Layout} {c : Clock} {R : GroupRegister P E bits A.bits} (B : Data R c)
  {p H J w teams : ℕ} {fit : Fits (TickWeightedBank.shape F p H J) w}

theorem branch_layout (t : ℕ) (oa na : Aux A.bits) (x : CellInput A c fit) :
    branch x.aux (c.phase t) oa na = branch R.base (c.phase t) oa na := rfl

theorem scan_agrees (t : ℕ) (x : CellInput A c fit) (v : Plan.Terminal P bits)
    (oa oc nc : Aux A.bits)
    (codes : ∀ i : Fin A.bits, TickChunkCheck.codeAt (TickGroupScanBank.layout A.scan x.lo x.group)
      x.intervals i.val = B.code v (c.group t) (chunk c t) i)
    (op : x.before = atIndex (before B v (c.group t) oa))
    (np : x.after = atIndex (after B v (c.group t) oa)) :
    TickChunkCheck.valid true (TickGroupScanBank.layout A.scan x.lo x.group) x.intervals x.before x.after
      (chunkView A x.lo x.group oc) (chunkView A x.lo x.group nc) ↔
      guard (B.code v (c.group t) (chunk c t)) (atIndex (before B v (c.group t) oa))
        (atIndex (after B v (c.group t) oa)) oc nc := by
  rw [TickChunkTransfer.valid_iff_guard,op,np]
  let e := finCongr (TickGroupScanBank.size A.scan x.lo x.group)
  let condition (i : Fin A.bits) (word : ℕ) : Prop :=
    if word = 0 then oc i = nc i else
      oc i = atIndex (before B v (c.group t) oa) (word-1) ∧
      nc i = atIndex (after B v (c.group t) oa) (word-1)
  constructor
  · intro ok i
    have read := ok (e.symm i)
    exact Eq.mp (congrArg (condition i) (codes i)) read
  · intro ok j
    have read := ok (e j)
    exact Eq.mpr (congrArg (condition (e j)) (codes (e j))) read

/-- Reads beyond the advertised group length never participate in either check. -/
theorem scan_agrees_on_count (t : ℕ) (x : CellInput A c fit) (v : Plan.Terminal P bits)
    (oa oc nc : Aux A.bits)
    (codes : ∀ i : Fin A.bits, TickChunkCheck.codeAt (TickGroupScanBank.layout A.scan x.lo x.group)
      x.intervals i.val = B.code v (c.group t) (chunk c t) i)
    (bound : ∀ i : Fin A.bits, B.code v (c.group t) (chunk c t) i ≤ B.length v (c.group t))
    (op : ∀ i : Fin (B.length v (c.group t)), x.before i.val = before B v (c.group t) oa i)
    (np : ∀ i : Fin (B.length v (c.group t)), x.after i.val = after B v (c.group t) oa i) :
    TickChunkCheck.valid true (TickGroupScanBank.layout A.scan x.lo x.group) x.intervals x.before x.after
      (chunkView A x.lo x.group oc) (chunkView A x.lo x.group nc) ↔
      guard (B.code v (c.group t) (chunk c t)) (atIndex (before B v (c.group t) oa))
        (atIndex (after B v (c.group t) oa)) oc nc := by
  let y : CellInput A c fit := {x with before := atIndex (before B v (c.group t) oa), after := atIndex (after B v (c.group t) oa)}
  rw [← scan_agrees B t y v oa oc nc codes rfl rfl]
  unfold TickChunkCheck.valid
  apply forall_congr'
  intro j
  let i := Fin.cast (TickGroupScanBank.size A.scan x.lo x.group) j
  let n := B.code v (c.group t) (chunk c t) i
  have word : TickChunkCheck.codeAt (TickGroupScanBank.layout A.scan x.lo x.group) x.intervals j.val = n := codes i
  by_cases z : n=0
  · simp [y,word,z]
  · have inside : n-1 < B.length v (c.group t) := by have := bound i; change n≤_ at this; omega
    have first := op ⟨n-1,inside⟩
    have second := np ⟨n-1,inside⟩
    simp [y,word,z,atIndex,inside,first,second]

/-- The linked native execution provides one value per team member. Admission uses
the canonical decoder on the word selected by the phase; an admitted record
determines the actual AUX layout, external comparison map and selected network. -/
theorem installed_team {publicPins : ℕ} (t : ℕ) (pos : 0<teams) (N : BitNetwork F publicPins)
    (rawPins : Fin teams → Fin publicPins → Bool) (slotPins : Fin teams → Fin p → Bool)
    (oa na oc nc : Aux A.bits) (x : Fin teams → CellInput A c fit)
    (allow : Fin teams → Prop) [DecidablePred allow]
    (admission : ∀ k, allow k ↔ (decode P E bits R.base (if c.phase t=.opening then na else oa)).isSome)
    (run : ∀ k, N.eval (rawPins k) =
      if branch (x k).aux (c.phase t) oa na then
        if allow k then (x k).weight (c.phase t) oa na oc nc (slotPins k) else 0
      else if oa=(fun _=>false) ∧ na=(fun _=>false) ∧ oc=nc then 1 else 0)
    (hydrated : ∀ v, decode P E bits R.base (if c.phase t=.opening then na else oa)=some v →
      (∀ k, (x k).aux=layout B v (c.group t)) ∧
      (c.phase t=.scan → ∀ k,
        TickChunkCheck.valid true (TickGroupScanBank.layout A.scan (x k).lo (x k).group)
          (x k).intervals (x k).before (x k).after (chunkView A (x k).lo (x k).group oc)
            (chunkView A (x k).lo (x k).group nc) ↔
        guard (B.code v (c.group t) (chunk c t)) (atIndex (before B v (c.group t) oa))
          (atIndex (after B v (c.group t) oa)) oc nc) ∧
      (c.phase t=.evaluate → (∏ k, (x k).net.eval (slotPins k)) =
        B.weight v (c.group t) (before B v (c.group t) oa) (after B v (c.group t) oa) t)) :
    (∏ k, N.eval (rawPins k)) = localValue B t oc nc oa na := by
  let ph := c.phase t
  let g := c.group t
  let hist := decode P E bits R.base (if ph=.opening then na else oa)
  let idOk := oa=(fun _=>false) ∧ na=(fun _=>false) ∧ oc=nc
  have zeroBranch (ok : idOk) : branch R.base ph oa na=false := by
    obtain ⟨o,n,_⟩ := ok
    simp [branch,o,n]
  have yesBranch (v : Plan.Terminal P bits) (ok : (layout B v g).accepts ph true oa na) :
      branch R.base ph oa na=true := branch_eq_of_accepts (layout B v g) ph true oa na ok
  let action (v : Plan.Terminal P bits) :=
    if (layout B v g).accepts ph true oa na then
      if ph=.scan then
        if guard (B.code v g (chunk c t)) (atIndex (before B v g oa)) (atIndex (after B v g oa)) oc nc then (1:F) else 0
      else if oc=nc then if ph=.evaluate then B.weight v g (before B v g oa) (after B v g oa) t else 1 else 0
    else 0
  change (∏ k, N.eval (rawPins k)) = (if idOk then 1 else 0) + hist.elim 0 action
  have member (k : Fin teams) : N.eval (rawPins k) =
      if branch R.base ph oa na then
        if hist.isSome then (x k).weight ph oa na oc nc (slotPins k) else 0
      else if idOk then 1 else 0 := by
    rw [run k,branch_layout (R:=R)]
    simp only [admission k,ph,idOk,hist]
  simp_rw [member]
  by_cases tag : branch R.base ph oa na=true
  · have noId : ¬idOk := fun ok => Bool.noConfusion (tag.symm.trans (zeroBranch ok))
    simp only [tag,ite_true,ite_eq_right noId,zero_add]
    cases dec : hist with
    | none => simp [Nat.ne_of_gt pos]
    | some v =>
      obtain ⟨aux,scan,ev⟩ := hydrated v dec
      let ok := (layout B v g).accepts ph true oa na ∧
        (if ph=.scan then guard (B.code v g (chunk c t)) (atIndex (before B v g oa))
          (atIndex (after B v g oa)) oc nc else oc=nc)
      have common k : (x k).checked ph oa na oc nc ↔ ok := by
        by_cases sc : ph=.scan
        · simp only [CellInput.checked,ok,aux k,sc,ite_true,scan sc k,g]
        · simp only [CellInput.checked,ok,aux k,ite_eq_right sc,g]
      simpa only [Option.isSome_some,ite_true,Option.elim_some] using
        (team_product pos x ph oa na oc nc slotPins ok common).trans (by
          by_cases ac : (layout B v g).accepts ph true oa na <;> by_cases sc : ph=.scan <;>
            by_cases eval : ph=.evaluate <;> by_cases same : oc=nc <;>
            simp_all [action,ok]; exact ev eval)
  · have rej (v : Plan.Terminal P bits) : ¬(layout B v g).accepts ph true oa na :=
      fun h => tag (yesBranch v h)
    cases dec : hist <;> by_cases id : idOk <;>
      simp [tag,id,action,rej,Nat.ne_of_gt pos]


end ThreeFlat.Diagonal.TickPhaseModel

end
end OAI
