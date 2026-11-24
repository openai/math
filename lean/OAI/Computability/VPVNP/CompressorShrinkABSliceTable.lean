import OAI.Computability.VPVNP.CompressorSliceIndexedStarts
import OAI.Computability.VPVNP.CompressorShrinkKernelSlices
import OAI.Computability.VPVNP.CompressorRecordsDemandWidths

/-!
# All AB copy slices in the shrinking graph

Each assigned bundle receives a contiguous bank. The three native scans
clear the endpoint counts, read both existing prefix columns to write
interval frames, and link positive frames into the two endpoint directories.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.ShrinkABSliceTable

open BurstRAM Compression Compression.PackingData BundleLists ShrinkSliceArrays
open IndexedStarts

variable {w : ℕ}

/-- Four source columns are packed by a common bundle ordinal, with
independent row strides for the old thick and the AB fields. -/
def columns (thick ab : Fin 5 → Word w) (i : ℕ) : Fin 4 → Word w :=
  ![Fin.ofNat _ ((thick 3).val+i*(thick 1).val), Fin.ofNat _ ((thick 2).val+i*(thick 1).val),
    Fin.ofNat _ ((ab 4).val+i*(ab 1).val), Fin.ofNat _ ((ab 3).val+i*(ab 1).val)]

/-- The starting word address of bundle `i` in the consecutive AB banks, using the capacity for
`m` old and `n` new fields. -/
def bank (first m n i : ℕ) : Word w := Fin.ofNat _ (first+i*capacity m n)

/-- The AB banks fit in machine addresses, the two row strides accommodate their field counts,
and all four input columns end before the banks. -/
structure Layout (thick ab : Fin 5 → Word w) (rows m n first : ℕ) : Prop where
  fits : first+rows*capacity m n < 2^w
  oldStride : m ≤ (thick 1).val
  newStride : n ≤ (ab 1).val
  oldWidths : (thick 2).val+rows*(thick 1).val ≤ first
  oldStarts : (thick 3).val+rows*(thick 1).val ≤ first
  newWidths : (ab 3).val+rows*(ab 1).val ≤ first
  newStarts : (ab 4).val+rows*(ab 1).val ≤ first

variable {thick ab : Fin 5 → Word w} {rows m n first : ℕ}
variable (L : Layout thick ab rows m n first)

private theorem mul_step {i stride : ℕ} (hi : i < rows) :
    i*stride+stride ≤ rows*stride := (Nat.succ_mul i stride) ▸ Nat.mul_le_mul_right stride hi

include L

theorem bank_val (i : Fin rows) : (bank (w := w) first m n i.val).val = first+i.val*capacity m n := by
  have := mul_step (stride := capacity m n) i.isLt
  exact Nat.mod_eq_of_lt (by have := L.fits; omega)

theorem columns_val (i : Fin rows) :
    let p := columns thick ab i.val
    (p 0).val = (thick 3).val+i.val*(thick 1).val ∧ (p 1).val = (thick 2).val+i.val*(thick 1).val ∧
    (p 2).val = (ab 4).val+i.val*(ab 1).val ∧ (p 3).val = (ab 3).val+i.val*(ab 1).val := by
  have := mul_step (stride := (thick 1).val) i.isLt
  have := mul_step (stride := (ab 1).val) i.isLt
  have := L.fits
  obtain ⟨_,_,_,h₀,h₁,h₂,h₃⟩ := L
  exact ⟨Nat.mod_eq_of_lt (by omega),Nat.mod_eq_of_lt (by omega),
    Nat.mod_eq_of_lt (by omega),Nat.mod_eq_of_lt (by omega)⟩

private theorem before (i : Fin rows) (t : Fin 4) :
    ((columns thick ab i.val) t).val+(if t.val < 2 then m else n) ≤ first := by
  have := mul_step (stride := (thick 1).val) i.isLt
  have := mul_step (stride := (ab 1).val) i.isLt
  obtain ⟨h₀,h₁,h₂,h₃⟩ := columns_val L i
  obtain ⟨_,s₀,s₁,b₀,b₁,b₂,b₃⟩ := L
  fin_cases t
  · change ((columns thick ab i.val) 0).val+m ≤ first
    rw [h₀]; omega
  · change ((columns thick ab i.val) 1).val+m ≤ first
    rw [h₁]; omega
  · change ((columns thick ab i.val) 2).val+n ≤ first
    rw [h₂]; omega
  · change ((columns thick ab i.val) 3).val+n ≤ first
    rw [h₃]; omega

theorem space (i : Fin rows) :
    Space (columns thick ab i.val) (bank first m n i.val) m n := by
  have := mul_step (stride := capacity m n) i.isLt
  have h := bank_val L i
  constructor
  · rw [h]; have := L.fits; omega
  · intro t; exact (before L i t).trans (by omega)

omit L

/-- Actual banks for all absolute bundle ordinals. -/
inductive Runs (thick ab : Fin 5 → Word w) (first m n : ℕ) :
    List (Fin rows) → Memory w → List (Report w) → Prop where
  | nil (mem) : Runs thick ab first m n [] mem []
  | cons {i is mem rs ds} :
      Native (columns thick ab i.val) (bank first m n i.val) m n mem rs →
      Runs thick ab first m n is (after mem (eventLog rs.all)) ds →
      Runs thick ab first m n (i::is) mem (rs.all++ds)

/-- Row data in the final table. Only the cells of this row's bank are
consulted when following either endpoint directory. -/
def Image (B : Word w) (old new : List ℕ) (out : Memory w) : Prop :=
  ∃ staged, IndexedStarts.Stored B old new staged ∧
    ∀ x, B.val ≤ x → x < B.val+capacity old.length new.length → out x = staged x

theorem Image.stored {B : Word w} {old new : List ℕ} {out : Memory w} {input : Fin 4 → Word w}
    (space : Space input B old.length new.length) (img : Image B old new out) :
    IndexedStarts.Stored B old new out := by
  obtain ⟨staged,stored,same⟩ := img
  exact stored.transfer space same

section Graph

variable {V H Tag Lanes : Type} {d c nv : ℕ}
variable [Fintype V] [Fintype H] [Fintype Tag] [Fintype Lanes]
variable [DecidableEq V] [DecidableEq Tag] [DecidableEq Lanes]
variable [AddCommGroup H] [AddCommGroup Tag] [AddCommGroup Lanes]
variable (P : PackingData V H Tag Lanes d c) (site : Site V Tag Lanes ≃ Fin nv)
variable (width : Arc V H Tag Lanes d c → ℕ) (dd : P.ThickNumbering) (cd : P.BundleNumbering)

local notation "ns" => 2^c*d/4
local notation "nt" => pieceCount d c
local notation "ord" => portIndex site (d := d)

set_option maxHeartbeats 600000 in
private theorem inputs (t u p : Fin 5 → Word w) (mem : Memory w)
    (h : DemandWidths.Stored P site width dd cd t u p mem)
    (l : Layout t p (nv*d) ns nt first) (i : Fin (nv*d)) :
    let b := (ord).symm i
    let src := thickWidths P dd width b
    let dst := abWidths P cd width b
    let B := bank (w := w) first ns nt i.val
    SliceSchedule.Inputs (pair (columns t p i.val) B ns nt) src dst mem := by
  intro b src dst B
  have hb : ord b = i := (ord).apply_symm_apply _
  have hm : src.length = ns := List.length_ofFn
  have hn : dst.length = nt := List.length_ofFn
  obtain ⟨s₀,w₀,s₁,w₁⟩ := columns_val l i
  let data := pair (columns t p i.val) B ns nt
  constructor
  · intro j hj
    let k : Fin ns := ⟨j,hm ▸ hj⟩
    let a := (dd b).symm k
    have read := h.thickStarts b a
    rw [hb,show dd b a = k from (dd b).apply_symm_apply k] at read
    have start := congrArg Field.start (fieldAt_ordered (dd b) (fun a : P.ThickFiber b => width a.1.1) a)
    rw [show dd b a = k from (dd b).apply_symm_apply k] at start
    change (src.take j).sum = _ at start
    change (mem (((columns t p i.val) 0).val+j)).val = _
    rw [s₀,start]; exact read
  · intro j hj
    let k : Fin ns := ⟨j,hm ▸ hj⟩
    have read := h.thickWidths b k
    rw [hb] at read
    change (mem (((columns t p i.val) 1).val+j)).val = _
    rw [w₀]; simp only [src,thickWidths,orderedWidths,List.getElem_ofFn]; exact read
  · intro j hj
    let k : Fin nt := ⟨j,hn ▸ hj⟩
    let a := (cd b).symm k
    have read := h.ab.starts b k
    rw [hb] at read
    have start := congrArg Field.start (fieldAt_ordered (cd b) (fun z : P.MotifFiber b => P.abWidth cd width z.1) a)
    rw [show cd b a = k from (cd b).apply_symm_apply k] at start
    change (dst.take j).sum = _ at start
    change (mem (((columns t p i.val) 2).val+j)).val = _
    rw [s₁,start]; exact read
  · intro j hj
    let k : Fin nt := ⟨j,hn ▸ hj⟩
    have read := h.ab.widths b k
    rw [hb] at read
    change (mem (((columns t p i.val) 3).val+j)).val = _
    rw [w₁]; simp only [dst,abWidths,orderedWidths,List.getElem_ofFn]; exact read

/-- Given the single snapshot produced by the native thick/CD and AB scans,
materialize every bundle's frame lengths, offsets and both endpoint directories
in a separate bank, leaving the complete input area intact. -/
theorem graph_run (hc : 2 ≤ c) (hd : 0 < d) (t u p : Fin 5 → Word w) (initial : Memory w)
    (h : DemandWidths.Stored P site width dd cd t u p initial)
    (l : Layout t p (nv*d) ns nt first) (fit : ∀ b, P.bundleWidth width b < 2^w) :
    ∃ rs, Runs t p first ns nt (List.finRange (nv*d)) initial rs ∧
      (∀ b, Image (bank first ns nt (ord b).val) (thickWidths P dd width b) (abWidths P cd width b)
        (after initial (eventLog rs))) ∧
      (∀ x, x < first ∨ first+(nv*d)*capacity ns nt ≤ x → after initial (eventLog rs) x = initial x) ∧
      rs.length = (nv*d)*(ns+nt+2*(ns*nt)) ∧
      (rs.map Report.probes).sum ≤ (nv*d)*(ns+nt+14*(ns*nt)) ∧
      (rs.map fun r => r.events.length+1).sum ≤ (nv*d)*(8*(ns+nt)+74*(ns*nt)) := by
  let old (i : Fin (nv*d)) := thickWidths P dd width ((ord).symm i)
  let new (i : Fin (nv*d)) := abWidths P cd width ((ord).symm i)
  let B (i : Fin (nv*d)) := bank (w := w) first ns nt i.val
  let Q := capacity ns nt
  have om (i) : (old i).length = ns := List.length_ofFn
  have nm (i) : (new i).length = nt := List.length_ofFn
  have outside (i : Fin (nv*d)) (x : ℕ) (hx : x < first ∨ first+(nv*d)*Q ≤ x) :
      x < (B i).val ∨ (B i).val+Q ≤ x := by
    have hv := bank_val l i
    change (B i).val = first+i.val*Q at hv
    have := mul_step (stride := Q) i.isLt
    omega
  have segment (is : List (Fin (nv*d))) (nd : is.Nodup) (mem : Memory w)
      (same : ∀ x < first, mem x = initial x) :
      ∃ rs, Runs t p first ns nt is mem rs ∧
        (∀ i ∈ is, Image (B i) (old i) (new i) (after mem (eventLog rs))) ∧
        (∀ x, (∀ i ∈ is, x < (B i).val ∨ (B i).val+Q ≤ x) → after mem (eventLog rs) x = mem x) ∧
        rs.length = is.length*(ns+nt+2*(ns*nt)) ∧
        (rs.map Report.probes).sum ≤ is.length*(ns+nt+14*(ns*nt)) ∧
        (rs.map fun r => r.events.length+1).sum ≤ is.length*(8*(ns+nt)+74*(ns*nt)) := by
    induction is generalizing mem with
    | nil => exact ⟨[],.nil _,by simp,fun _ _ => rfl,by simp,by simp,by simp⟩
    | cons i is ih =>
      let data := pair (columns t p i.val) (B i) ns nt
      have ready := inputs P site width dd cd t u p initial h l i
      have field (col : Fin 4) (j : ℕ) (hj : j < (if col.val < 2 then ns else nt)) :
          mem (((columns t p i.val) col).val+j) = initial (((columns t p i.val) col).val+j) := by
        have := before l i col
        exact same _ (by omega)
      have actual : SliceSchedule.Inputs data (old i) (new i) mem := by
        constructor <;> intro j hj
        · exact (congrArg Fin.val (field 0 j (om i ▸ hj))).trans (ready.oldStart j hj)
        · exact (congrArg Fin.val (field 1 j (om i ▸ hj))).trans (ready.oldWidth j hj)
        · exact (congrArg Fin.val (field 2 j (nm i ▸ hj))).trans (ready.newStart j hj)
        · exact (congrArg Fin.val (field 3 j (nm i ▸ hj))).trans (ready.newWidth j hj)
      have oldFit : (old i).sum < 2^w := (thickWidths_sum P dd width _).symm ▸ fit _
      have newFit : (new i).sum < 2^w := by
        change (abWidths P cd width _).sum < _
        rw [abWidths,orderedWidths,List.sum_ofFn,(cd _).symm.sum_comp (fun z : P.MotifFiber _ => P.abWidth cd width z.1),
          P.sum_abWidth hc hd cd width _]; exact fit _
      have sp : Space (columns t p i.val) (B i) (old i).length (new i).length := om i ▸ nm i ▸ space l i
      obtain ⟨r,run,image,frame,cl,cp,ci⟩ := IndexedStarts.build (old i) (new i) (columns t p i.val) (B i) mem
        sp oldFit newFit (om i ▸ nm i ▸ actual)
      rw [om i,nm i] at run frame cl cp ci
      let mid := after mem (eventLog r.all)
      have nd' := List.nodup_cons.mp nd
      obtain ⟨s,tail,images,tframe,tl,tp,ti⟩ := ih nd'.2 mid
        (fun x hx => (frame x (outside i x (Or.inl hx))).trans (same x hx))
      have replay : after mem (eventLog (r.all++s)) = after mid (eventLog s) := by
        simp only [mid,after,eventLog,List.flatMap_append,List.foldl_append]
      refine ⟨r.all++s,.cons run tail,?_,?_,?_,?_,?_⟩
      · intro j hj
        rw [replay]
        rcases List.mem_cons.mp hj with rfl | hj
        · refine ⟨mid,image,fun x hlo hhi => tframe x fun k hk => ?_⟩
          rw [om j,nm j] at hhi
          have ne : j.val ≠ k.val := fun e => nd'.1 ((Fin.ext e).symm ▸ hk)
          have hvj := bank_val l j
          have hvk := bank_val l k
          change (B j).val = first+j.val*Q at hvj
          change (B k).val = first+k.val*Q at hvk
          change x < (B j).val+Q at hhi
          rcases lt_or_gt_of_ne ne with hlt | hlt
          · have := mul_step (stride := Q) hlt; omega
          · have := mul_step (stride := Q) hlt; omega
        · exact images _ hj
      · intro x hx
        rw [replay,tframe x (fun k hk => hx k (List.mem_cons_of_mem _ hk))]
        exact frame x (hx i List.mem_cons_self)
      · rw [List.length_append,cl,tl,List.length_cons,Nat.add_mul,one_mul]; omega
      · rw [List.map_append,List.sum_append,List.length_cons,Nat.add_mul,one_mul]; omega
      · rw [List.map_append,List.sum_append,List.length_cons,Nat.add_mul,one_mul]; omega
  obtain ⟨rs,run,imgs,frame,cl,cp,ci⟩ := segment (List.finRange _) (List.nodup_finRange _) initial (fun _ _ => rfl)
  exact ⟨rs,run,fun b => by simpa only [old,new,Equiv.symm_apply_apply] using imgs (ord b) (by simp),
    fun x hx => frame x (fun i _ => outside i x hx),by simpa using cl,by simpa using cp,by simpa using ci⟩

/-- Follow the exact frame of the old wire and motif at either packed
endpoint. Its offsets characterize the demand bit bijection used by both
`localAWord` and `localBWord`. -/
theorem image_bits (hc : 2 ≤ c) (hd : 0 < d) (b : Port V Tag Lanes d) {B : Word w} {out : Memory w}
    (img : Image B (thickWidths P dd width b) (abWidths P cd width b) out)
    (a : P.ThickFiber b) (z : P.MotifFiber b) (x : Fin (width a.1.1))
    (y : Fin (P.abWidth cd width z.1)) :
    let id := (dd b a).val*nt+(cd b z).val
    let f := B.val+ns+nt+3*id
    P.demandBitEquiv hc hd cd dd width b ⟨z,y⟩ = ⟨a,x⟩ ↔
      ∃ k < (out (f+2)).val, x.val = (out f).val+k ∧ y.val = (out (f+1)).val+k := by
  intro id f
  obtain ⟨staged,h,same⟩ := img
  have om : (thickWidths P dd width b).length = ns := List.length_ofFn
  have nm : (abWidths P cd width b).length = nt := List.length_ofFn
  have hr : id < ns*nt := by
    calc
      _ < (dd b a).val*nt+nt := Nat.add_lt_add_left (cd b z).isLt _
      _ = ((dd b a).val+1)*nt := (Nat.succ_mul ..).symm
      _ ≤ _ := Nat.mul_le_mul_right _ (dd b a).isLt
  have hr' : id < (thickWidths P dd width b).length * (abWidths P cd width b).length := by
    simpa only [om,nm] using hr
  have eqn := ab_sliceAt P cd dd width b a z
  have sameFrame (j : ℕ) (hj : j < 3) : out (f+j) = staged (f+j) := by
    apply same
    · dsimp [f]; omega
    · rw [om,nm]; dsimp only [capacity,f]; omega
  have len := h.lengths id hr'
  rw [om,nm,eqn] at len
  change (staged (f+2)).val = _ at len
  rw [P.demandBitEquiv_eq_iff_slice cd dd width b hc hd,sameFrame 2 (by decide),len]
  dsimp only
  by_cases pos : 0 < (P.demandSlice cd dd width b a z).length
  · obtain ⟨hs,ht⟩ := h.offsets id hr' (eqn ▸ pos)
    rw [om,nm,eqn] at hs ht
    change (staged f).val = _ at hs
    change (staged (f+1)).val = _ at ht
    rw [show out f = staged f from sameFrame 0 (by decide),sameFrame 1 (by decide),hs,ht]
  · simp [show (P.demandSlice cd dd width b a z).length = 0 by omega]

end Graph

end CompressorRecords.ShrinkABSliceTable

end VPVNP
end Computability
end OAI
