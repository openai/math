import OAI.ThreeFlat.Diagonal.RefreshCursorFrame

namespace OAI
/-! # Previously published arrays remain available to the selected-node compiler -/

namespace ThreeFlat.Diagonal.RefreshStageNav.CursorSpace

open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.Compression RAM RAM.HeaderScan NavigationDirectory
open RefreshDemandRows CompressorPacking.Native

variable {W v a t h pad K k : ℕ} {cur : Word W} {mem : Memory W} {c : Cursor}
    (u : CursorSpace cur mem c K v a t h pad)
set_option quotPrecheck false
local notation "m" => mPort a
local notation "d" => 1+h+pad
local notation "entry" => allocate K c (.refresh v m (2^t) h pad)
local notation "old" => fun i : ℕ=>i<c.heap ∨ (entry).next.heap≤ i

private theorem prefix_safe (p : Scans W) (upto : ℕ) {fields : ℕ → ℕ} {keep : ℕ → Prop}
    (live : p.every (Scans.Safe 63 fields keep)) (above : p.every (fun r => upto ≤ fields r.first)) :
    p.every (Scans.Safe 63 fields (fun i => keep i ∨ i < upto)) := by
  induction p with
  | one r =>
    obtain ⟨f,n,fit,apart⟩ := live
    exact ⟨f,n,fit,fun i q=>q.elim (apart i) (fun h=>Or.inl (h.trans_le above))⟩
  | next p q l r => exact ⟨l live.1 above.1,r live.2 above.2⟩

include u

theorem post_retains (E : SlotGraph (Fin m) h)
    (base : Fin (k+1) → (Bool × Fin m × Fin m) → ℕ)
    (size bits : Fin (k+1)→ℕ) (pool : ∀ j,Fin (size j)→Fin m→Fin h→ℕ)
    (i : ℕ) (lt : i<c.heap+3*(v*2^t)) :
    (publication cur E pad K base size bits pool).run mem i=mem i := by
  let p := postScans cur E pad K base size bits pool
  have first : p.every (fun r=>c.heap+3*(v*2^t)≤(entry).words r.first) := by
    obtain ⟨h1,h2,h3,h4,h5⟩ := ordered (c:=c) (K:=K) (v:=v) (a:=a) (t:=t) (h:=h) (pad:=pad)
    change c.heap+3*(v*2^t)≤(entry).words 14 ∧ c.heap+3*(v*2^t)≤(entry).words 19 ∧ c.heap+3*(v*2^t)≤(entry).words 3
    change _≤(nextColumns entry v m h pad).graph ∧ _≤(nextColumns entry v m h pad).widths ∧ _
    omega
  have safe := prefix_safe p _ (u.post_safe E base size bits pool) first
  have h := p.run_spec cur mem c.header 63 (entry).words _ u.header (.inl (.inr u.controls))
    (fun z hz=>.inl (u.start_live z hz)) safe
  exact h.2.2 i (.inr lt)

/-- The sparse copy ends at the split table. The graph and width scans
start beyond that table, so a party can reopen all three of its columns. -/
theorem post_retains_split (E : SlotGraph (Fin m) h)
    (base : Fin (k+1) → (Bool × Fin m × Fin m) → ℕ)
    (size bits : Fin (k+1)→ℕ) (pool : ∀ j,Fin (size j)→Fin m→Fin h→ℕ)
    (i : ℕ) (lo : (entry).words 12≤ i) (hi : i<(entry).words 12+3*(v*m)) :
    (publication cur E pad K base size bits pool).run mem i=mem i := by
  let p:=postScans cur E pad K base size bits pool
  let range:=fun j=>(entry).words 12≤j ∧ j<(entry).words 12+3*(v*m)
  have current:=u.post_safe E base size bits pool
  obtain ⟨_,sparseEnd,graphStart,widthStart,_⟩:=ordered (c:=c) (K:=K) (v:=v) (a:=a) (t:=t) (h:=h) (pad:=pad)
  let C:=nextColumns entry v m h pad
  have sparseN : (entry).words 20=v*2^t*m*h:=rfl
  have graphPtr : (entry).words 14=C.graph:=rfl
  have widthPtr : (entry).words 19=C.widths:=rfl
  have newStart : (entry).words 12+3*(v*m)=C.graph:=graphStart
  have newEnd : C.graph+6*C.rows=C.widths:=widthStart
  have widen (row : ScanRow W) (ok : Scans.Safe 63 (entry).words old row)
      (extra : ∀ j,range j→j<(entry).words row.first ∨ (entry).words row.first+(entry).words row.count≤j) :
      Scans.Safe 63 (entry).words (fun j=>old j ∨ range j) row :=
    ⟨ok.1,ok.2.1,ok.2.2.1,fun j e=>e.elim (ok.2.2.2 j) (extra j)⟩
  have safe:p.every (Scans.Safe 63 (entry).words (fun j=>old j ∨ range j)) := by
    refine ⟨widen _ current.1 ?_,widen _ current.2.1 ?_,widen _ current.2.2 ?_⟩
    · exact fun j h=>.inl (h.2.trans_le (newStart.trans graphPtr.symm).le)
    · intro j h
      exact .inl (h.2.trans_le (newStart.le.trans ((Nat.le_add_right ..).trans (newEnd.trans widthPtr.symm).le)))
    · intro j h
      apply Or.inr
      change (entry).words 3+(entry).words 20≤j
      rw [sparseN,sparseEnd]
      exact h.1
  exact (p.run_spec cur mem c.header 63 (entry).words _ u.header (.inl (.inr u.controls))
    (fun j hj=>.inl (u.start_live j hj)) safe).2.2 i (.inr ⟨lo,hi⟩)

theorem records_retain (i : ℕ) (lt : i<(entry).words 34) :
    (Records.pipeline cur m d K).run mem i=mem i := by
  let p := recordScans cur m d K
  have first : p.every (fun r=>(entry).words 34≤(entry).words r.first) := by
    obtain ⟨k,mot,hd,hs,l⟩ := record_layout (c:=c) (K:=K) (v:=v) (a:=a) (t:=t) (h:=h) (pad:=pad)
    let P := recordPointers entry
    change P.kernel≤P.kernel ∧ P.kernel≤P.motif ∧ P.kernel≤P.headers ∧ P.kernel≤P.halves
    have toMotif : P.kernel ≤ P.motif := (Nat.le_add_right _ _).trans_eq mot
    have toHeader : P.motif ≤ P.headers := (Nat.le_add_right _ _).trans_eq hd
    have toHalf : P.headers ≤ P.halves := (Nat.le_add_right _ _).trans_eq hs
    exact ⟨le_rfl, toMotif, toMotif.trans toHeader, (toMotif.trans toHeader).trans toHalf⟩
  have safe := prefix_safe p ((entry).words 34) u.recorder_safe first
  have h := p.run_spec cur mem c.header 63 (entry).words _ u.header (.inl (.inr u.controls))
    (fun z hz=>.inl (u.start_live z hz)) safe
  rw [← record_pipeline cur m d K]
  exact h.2.2 i (.inr lt)


end ThreeFlat.Diagonal.RefreshStageNav.CursorSpace

end OAI
