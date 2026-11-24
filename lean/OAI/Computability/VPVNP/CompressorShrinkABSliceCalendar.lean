import OAI.Computability.VPVNP.CompressorShrinkABSliceVisits

/-!
# Chronological realization of the fixed AB slice calendar

Every visit scans all bundles. The old and new ranks are fixed by the visit,
so each call computes its addresses from the current bundle ordinal. After
the count, interval and incidence visits, each bundle has its exact interval
frames and both compact endpoint lists in the common memory.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.ShrinkABSliceRecipe

open BurstRAM Compression Compression.PackingData PrimedStackRAM ShrinkSliceArrays
open ShrinkABSliceTable IndexedStarts

variable {w m n rows first : ℕ}

private theorem fin_walk {J : Type*} {source : J → Memory w → List (Report w) → Prop} {k : ℕ}
    (label : Fin k → J) (inv : ℕ → Memory w → Prop) (mem : Memory w) (start : inv 0 mem)
    (step : ∀ j : Fin k, ∀ mem, inv j.val mem →
      ∃ rs, source (label j) mem rs ∧ inv (j.val+1) (after mem (eventLog rs))) :
    ∃ rs, SourceWalk source ((List.finRange k).map label) mem rs ∧ inv k (after mem (eventLog rs)) := by
  let js := (List.finRange k).map label
  have len : js.length = k := by simp [js]
  have hstep (i : Fin js.length) (st : Memory w) (h : inv (0+i.val) st) :
      ∃ rs, source js[i.val] st rs ∧ inv (0+i.val+1) (after st (eventLog rs)) := by
    let j := i.cast len
    have he : js[i.val] = label j := by simp [js,j]; rfl
    rw [he,Nat.zero_add]
    exact step j st (by change inv i.val st; simpa only [Nat.zero_add] using h)
  simpa only [len,Nat.zero_add] using FlatRows.walk js inv 0 mem start hstep

open private before inputs from OAI.Computability.VPVNP.CompressorShrinkABSliceTable

variable (I : Inputs) (pub : Fin 5 → Word w) (state : Word w) (ref : Memory w)
variable {t p : Fin 5 → Word w} (L : Layout t p rows m n first) (D : Describes I pub state ref t p rows first)

include L D

/-- Exact worker runs for all field ordinals in the fixed catalog. The bank
and frame addresses are the same as the native row-major descriptor builder. -/
theorem run (old new : Fin rows → List ℕ) (om : ∀ i, (old i).length = m) (nm : ∀ i, (new i).length = n)
    (hs : ∀ i, (old i).sum < 2^w) (ht : ∀ i, (new i).sum < 2^w)
    (start : Memory w)
    (reads : ∀ i : Fin rows, SliceSchedule.Inputs (IndexedStarts.pair (columns t p i.val) (bank first m n i.val) m n)
      (old i) (new i) start)
    (cap : ℕ) (hcap : 95 ≤ cap) :
    ∃ rs, SourceWalk (Source I pub state ref rows cap) (phases m n) start rs ∧
      (∀ i : Fin rows, IndexedStarts.Stored (bank first m n i.val) (old i) (new i) (after start (eventLog rs))) ∧
      ∀ x, x < first ∨ first+rows*capacity m n ≤ x → after start (eventLog rs) x = start x := by
  let B (i : Fin rows) := bank (w := w) first m n i.val
  let src := Source (m := m) (n := n) I pub state ref rows cap
  let Shared (mem : Memory w) := ∀ x, x < first ∨ first+rows*capacity m n ≤ x → mem x = start x
  have shared : Shared start := fun _ _ => rfl
  have sp (i : Fin rows) : Space (columns t p i.val) (B i) (old i).length (new i).length :=
    by simpa only [om i,nm i] using ShrinkABSliceTable.space L i
  have retain (i : Fin rows) (mem out : Memory w) (h : Shared mem)
      (outside : ∀ x, ¬ BankAt (B i) m n x → out x = mem x) : Shared out := by
    intro x hx
    have hv := bank_val L i
    change (B i).val = _ at hv
    have hi := Nat.mul_le_mul_right (capacity m n) i.isLt
    rw [Nat.succ_mul] at hi
    exact (outside x (by dsimp only [BankAt]; omega)).trans (h x hx)
  have inp (i : Fin rows) (mem : Memory w) (h : Shared mem) :
      SliceSchedule.Inputs (IndexedStarts.pair (columns t p i.val) (B i) (old i).length (new i).length)
        (old i) (new i) mem := by
    rw [om i,nm i]
    have eqn (c : Fin 4) (j : ℕ) (hj : j < (if c.val < 2 then m else n)) :
        mem (((columns t p i.val) c).val+j) = start (((columns t p i.val) c).val+j) :=
      h _ (Or.inl (by have := before L i c; omega))
    constructor <;> intro j hj
    · exact (congrArg Fin.val (eqn 0 j (om i ▸ hj))).trans ((reads i).oldStart _ hj)
    · exact (congrArg Fin.val (eqn 1 j (om i ▸ hj))).trans ((reads i).oldWidth _ hj)
    · exact (congrArg Fin.val (eqn 2 j (nm i ▸ hj))).trans ((reads i).newStart _ hj)
    · exact (congrArg Fin.val (eqn 3 j (nm i ▸ hj))).trans ((reads i).newWidth _ hj)
  let C (k : ℕ) (i : Fin rows) (mem : Memory w) := Cleared (B i) k mem
  let F (k : ℕ) (i : Fin rows) (mem : Memory w) := Frames (B i) (old i) (new i) k mem
  let R (k : ℕ) (i : Fin rows) (mem : Memory w) := Dirs (B i) (old i) (new i) k mem
  let State (pred : Fin rows → Memory w → Prop) (mem : Memory w) := Shared mem ∧ ∀ i, pred i mem
  have ck {k} (hk : k ≤ m+n) (i : Fin rows) (mem out : Memory w) (h : C k i mem)
      (eqn : ∀ x, BankAt (B i) m n x → out x = mem x) : C k i out := h.keep hk eqn
  have fk {k} (hk : k ≤ m*n) (i : Fin rows) (mem out : Memory w) (h : F k i mem)
      (eqn : ∀ x, BankAt (B i) m n x → out x = mem x) : F k i out :=
    h.keep (om i ▸ nm i ▸ hk) (om i ▸ nm i ▸ eqn)
  have rk {k} (hk : k ≤ m*n) (i : Fin rows) (mem out : Memory w) (h : R k i mem)
      (eqn : ∀ x, BankAt (B i) m n x → out x = mem x) : R k i out :=
    h.keep (sp i) (om i ▸ nm i ▸ hk) (om i ▸ nm i ▸ eqn)
  have clearStep (j : Fin (m+n)) (mem : Memory w) (cur : State (C j.val) mem) :
      ∃ rs, src (.clear j) mem rs ∧ State (C (j.val+1)) (after mem (eventLog rs)) := by
    apply phase_run I pub state ref L D (.clear j) cap hcap Shared (C j.val) (C (j.val+1)) retain
      (ck j.isLt.le) (ck j.isLt) _ mem cur.1 cur.2
    intro i st _ prev
    let k : Fin ((old i).length+(new i).length) := ⟨j.val,by rw [om i,nm i]; exact j.isLt⟩
    obtain ⟨r,hr,he,hd,hframe⟩ := clear_one (sp i) k st prev
    exact ⟨r,hr,he ▸ rfl,hd,by simpa only [om i,nm i] using hframe⟩
  obtain ⟨clears,cr,cleared⟩ := fin_walk (Stage.clear (m := m) (n := n)) (fun k => State (C k)) start
    ⟨shared,fun _ _ hj => by omega⟩ clearStep
  let firstMem := after start (eventLog clears)
  let CF (k : ℕ) (i : Fin rows) (mem : Memory w) := C (m+n) i mem ∧ F k i mem
  have keepCF {k} (hk : k ≤ m*n) (i : Fin rows) (mem out : Memory w) (h : CF k i mem)
      (eqn : ∀ x, BankAt (B i) m n x → out x = mem x) : CF k i out :=
    ⟨ck le_rfl i _ _ h.1 eqn,fk hk i _ _ h.2 eqn⟩
  have pairStep (j : Fin (m*n)) (mem : Memory w) (cur : State (CF j.val) mem) :
      ∃ rs, src (.pair j) mem rs ∧ State (CF (j.val+1)) (after mem (eventLog rs)) := by
    apply phase_run I pub state ref L D (.pair j) cap hcap Shared (CF j.val) (CF (j.val+1)) retain
      (keepCF j.isLt.le) (keepCF j.isLt) _ mem cur.1 cur.2
    intro i st sh prev
    let k : Fin ((old i).length*(new i).length) := ⟨j.val,by rw [om i,nm i]; exact j.isLt⟩
    obtain ⟨r,hr,he,hd,hframe⟩ := frame_one (sp i) k st (hs i) (ht i) (inp i st sh)
      (om i ▸ nm i ▸ prev.1) prev.2
    dsimp only [k] at hr hd he
    rw [om i,nm i] at hr hframe
    exact ⟨r,hr,he ▸ rfl,⟨by simpa only [om i,nm i] using hd.1,hd.2⟩,hframe⟩
  obtain ⟨pairs,pr,framed⟩ := fin_walk (Stage.pair (m := m) (n := n)) (fun k => State (CF k)) firstMem
    ⟨cleared.1,fun i => ⟨cleared.2 i,fun _ hj => by omega,fun _ hj _ => by omega⟩⟩ pairStep
  let secondMem := after firstMem (eventLog pairs)
  let FR (k : ℕ) (i : Fin rows) (mem : Memory w) := F (m*n) i mem ∧ R k i mem
  have keepFR {k} (hk : k ≤ m*n) (i : Fin rows) (mem out : Memory w) (h : FR k i mem)
      (eqn : ∀ x, BankAt (B i) m n x → out x = mem x) : FR k i out :=
    ⟨fk le_rfl i _ _ h.1 eqn,rk hk i _ _ h.2 eqn⟩
  have refStep (j : Fin (m*n)) (mem : Memory w) (cur : State (FR j.val) mem) :
      ∃ rs, src (.refs j) mem rs ∧ State (FR (j.val+1)) (after mem (eventLog rs)) := by
    apply phase_run I pub state ref L D (.refs j) cap hcap Shared (FR j.val) (FR (j.val+1)) retain
      (keepFR j.isLt.le) (keepFR j.isLt) _ mem cur.1 cur.2
    intro i st _ prev
    let k : Fin ((old i).length*(new i).length) := ⟨j.val,by rw [om i,nm i]; exact j.isLt⟩
    obtain ⟨r,hr,he,hd,hframe⟩ := refs_one (sp i) k st (om i ▸ nm i ▸ prev.1) prev.2
    dsimp only [k] at hr hd he
    rw [om i,nm i] at hr hframe
    exact ⟨r,hr,he ▸ rfl,⟨by simpa only [om i,nm i] using hd.1,hd.2⟩,hframe⟩
  obtain ⟨refs,rr,final⟩ := fin_walk (Stage.refs (m := m) (n := n)) (fun k => State (FR k)) secondMem
    ⟨framed.1,fun i => ⟨(framed.2 i).2,Dirs.zero (sp i) (om i ▸ nm i ▸ (framed.2 i).1)⟩⟩ refStep
  have firstTwo := cr.append pr
  have second : after start (eventLog (clears++pairs)) = secondMem := SourceWalk.after_append ..
  have all := firstTwo.append (second ▸ rr)
  have replay : after start (eventLog ((clears++pairs)++refs)) = after secondMem (eventLog refs) := by
    rw [SourceWalk.after_append,second]
  refine ⟨(clears++pairs)++refs,all,?_,replay ▸ final.1⟩
  rw [replay]
  intro i
  obtain ⟨frames,dirs⟩ := final.2 i
  rw [← om i,← nm i] at frames dirs
  exact ⟨frames.lengths,frames.offsets,dirs.oldRows,dirs.newRows⟩

omit L D

section Graph

variable {V H Tag Lane : Type} {d c nv : ℕ}
variable [AddCommGroup H] [AddCommGroup Tag] [AddCommGroup Lane]
variable [Fintype V] [Fintype H] [Fintype Tag] [Fintype Lane]
variable [DecidableEq V] [DecidableEq Tag] [DecidableEq Lane]
variable (P : PackingData V H Tag Lane d c) (site : Site V Tag Lane ≃ Fin nv)
variable (width : Arc V H Tag Lane d c → ℕ) (dd : P.ThickNumbering) (cd : P.BundleNumbering)
local notation "ns" => 2^c*d/4
local notation "nt" => pieceCount d c
local notation "ord" => BundleLists.portIndex site (d := d)

/-- The native whole-level calendar on the width-and-start columns of the
selected shrinking branch. Each resulting endpoint directory and frame
is interpreted directly in the final memory of the actual calendar. -/
theorem graph_run (hc : 2 ≤ c) (hd : 0 < d) (t u p : Fin 5 → Word w) (initial : Memory w)
    (stored : DemandWidths.Stored P site width dd cd t u p initial)
    (layout : Layout t p (nv*d) ns nt first)
    (heads : Describes I pub state ref t p (nv*d) first)
    (fit : ∀ b, P.bundleWidth width b < 2^w) (cap : ℕ) (hcap : 95 ≤ cap) :
    ∃ rs, SourceWalk (Source I pub state ref (nv*d) cap) (phases ns nt) initial rs ∧
      (∀ b, IndexedStarts.Stored (bank first ns nt (ord b).val) (thickWidths P dd width b)
        (abWidths P cd width b) (after initial (eventLog rs))) ∧
      ∀ x, x < first ∨ first+(nv*d)*capacity ns nt ≤ x → after initial (eventLog rs) x = initial x := by
  let old := fun i => thickWidths P dd width ((ord).symm i)
  let new := fun i => abWidths P cd width ((ord).symm i)
  have hs (i) : (old i).sum < 2^w := (thickWidths_sum P dd width _).symm ▸ fit _
  have ht (i) : (new i).sum < 2^w := by
    dsimp only [new]
    rw [abWidths,orderedWidths,List.sum_ofFn,
      (cd _).symm.sum_comp (fun z : P.MotifFiber _ => P.abWidth cd width z.1),P.sum_abWidth hc hd cd width _]
    exact fit _
  obtain ⟨rs,walk,rows,outside⟩ := run I pub state ref layout heads old new (fun _ => List.length_ofFn)
    (fun _ => List.length_ofFn) hs ht initial (inputs P site width dd cd t u p initial stored layout) cap hcap
  exact ⟨rs,walk,fun b => by simpa only [old,new,Equiv.symm_apply_apply] using rows (ord b),outside⟩

end Graph

end CompressorRecords.ShrinkABSliceRecipe

end VPVNP
end Computability
end OAI
