import OAI.ThreeFlat.Diagonal.RefreshOwnerNative
import OAI.ThreeFlat.Diagonal.RefreshRetainedPrefix

namespace OAI
/-! # Retained child and owner arrays after the last two allocator scans -/

namespace ThreeFlat.Diagonal.RefreshNodeOwners

open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.Compression RAM RAM.HeaderScan RAM.DescriptorScan
open RefreshStageNav RefreshDemandRows NavigationDirectory CompressorPacking.Native
open scoped Fin.CommRing

variable {W v a t h pad K : ℕ} {cur : Word W} {mem : Memory W} {c : Cursor}
    (u : CursorSpace cur mem c K v a t h pad)
set_option quotPrecheck false
local notation "m" => mPort a
local notation "d" => 1+h+pad
local notation "n" => v*m*2^t
local notation "entry" => allocate K c (.refresh v m (2^t) h pad)
local notation "H" => fun i : ℕ=>i<c.heap ∨ (entry).next.heap≤ i
local notation "N" => fun i=>(mem i).val

include K v a t h pad c in
theorem owner_spans : (entry).words 42+n=(entry).words 44 ∧ (entry).words 44+n=(entry).next.heap ∧
    c.heap≤(entry).words 42 ∧ (entry).words 40+(entry).words 41=(entry).words 42 := by
  constructor
  · change _+(13+8*d)*n+n=_+(14+8*d)*n
    ring
  · refine ⟨rfl,?_,?_⟩
    · change c.heap ≤ c.heap + _ + _ + _ + _ + _ + _
      omega
    · change _+5*n+6*n+2*n+8*d*n=_+(13+8*d)*n
      ring

include u in
theorem safe : (both cur m).every (Scans.Safe 63 (entry).words H) := by
  obtain ⟨left,right,above,_⟩ := owner_spans (c:=c) (v:=v) (a:=a) (t:=t) (h:=h) (pad:=pad) (K:=K)
  have n43 : (entry).words 43=n := rfl
  have n45 : (entry).words 45=n := rfl
  exact ⟨u.span_safe _ _ _ (by decide) (by decide) above (by omega),
    u.span_safe _ _ _ (by decide) (by decide) (by omega) (by omega)⟩

def value (oldFirst ports lanes : ℕ) (b : Bool) (i : ℕ) :=
  if b then oldFirst+RefreshOwnership.child ports lanes i else RefreshOwnership.owner ports lanes i

include u in
private theorem single (b : Bool) (ports : m<2^W) (full : m*2^t<2^W) :
    let f := if b then 42 else 44
    ((scan cur m b).pipeline cur).run mem =
      fillSegment ((entry).words f) n (tableWord (Equiv.refl (Fin n)) ((entry).words f)
        (fun i=>(value c.node m (2^t) b i.val:Word W))) mem := by
  let f := if b then 42 else 44
  have hf : f≤44 := by cases b <;> decide
  have ln : (entry).words (f+1)=n := by cases b <;> rfl
  have spans := owner_spans (c:=c) (v:=v) (a:=a) (t:=t) (h:=h) (pad:=pad) (K:=K)
  have lo : c.heap≤(entry).words f := by
    cases b with
    | false => change c.heap ≤ (entry).words 44; omega
    | true => exact spans.2.2.1
  have hi : (entry).words f+n≤(entry).next.heap := by
    cases b with
    | false => exact spans.2.1.le
    | true => change (entry).words 42+n ≤ (entry).next.heap; omega
  have before : (mem cur.val).val+45<2^W := by rw [u.header.pointer]; have := u.header.fit; omega
  have reg := u.controls.trans_lt cur.isLt
  have id : (scan cur m b).pipeline cur=Pipeline.scan cur f (f+1) (HeaderScan.closed (expr cur.val m b)) := by
    cases b <;> simp only [scan, f, Bool.false_eq_true, eq_self, ite_true, ite_false, Scans.pipeline]
  rw [id]
  apply scan_table cur mem (Equiv.refl (Fin n)) (fun i => (value c.node m (2^t) b i.val:Word W))
    (HeaderScan.closed (expr cur.val m b)) f (f+1) ((entry).words f) (by omega)
    (u.read f (by omega)) ((u.read (f+1) (by omega)).trans ln) (by omega)
  intro i arg m' addr fr
  have keep (x) (z : x=cur.val ∨ c.header≤x ∧ x≤c.header+45) : m' x=mem x := by
    apply fr
    rcases z with eq|hu
    · rw [eq]
      right
      exact hi.trans u.controls
    · left
      have := u.earlier
      omega
  have ptr := keep cur.val (.inl rfl)
  have hdr (j : ℕ) (hj : j≤45) : (m' ((m' cur.val).val+j)).val=(entry).words j := by
    rw [ptr,u.header.pointer,keep (c.header+j) (.inr ⟨by omega,by omega⟩),u.header.values j (by omega)]
  have laneBound : m*(m' ((m' cur.val).val+8)).val<2^W := by
    rw [hdr 8 (by decide)]
    exact full
  have val := native cur m' arg m b (by rw [ptr]; omega) ports laneBound
  apply val.trans
  cases b with
  | false =>
    change arg.val = (entry).words 44+i.val at addr
    change (RefreshOwnership.owner m (m' ((m' cur.val).val+8)).val
      (arg.val-(m' ((m' cur.val).val+44)).val):Word W) = _
    rw [hdr 8 (by decide),hdr 44 (by decide),addr,Nat.add_sub_cancel_left]; rfl
  | true =>
    change arg.val = (entry).words 42+i.val at addr
    change (((m' ((m' cur.val).val+6)).val + RefreshOwnership.child m
      (m' ((m' cur.val).val+8)).val (arg.val-(m' ((m' cur.val).val+42)).val):ℕ):Word W) = _
    rw [hdr 6 (by decide),hdr 8 (by decide),hdr 42 (by decide),addr,Nat.add_sub_cancel_left]; rfl

private theorem pair_run (first second : Scans W) (ptr : Word W) (seed : Memory W) :
    ((first.next second).pipeline ptr).run seed =
      (second.pipeline ptr).run ((first.pipeline ptr).run seed) := rfl

private theorem adjacent_tables {size base tail : ℕ} (input middle output : Memory W)
    (child owner : Fin size → Word W) (adjacent : base + size = tail)
    (left : middle = fillSegment base size (tableWord (Equiv.refl _) base child) input)
    (right : output = fillSegment tail size (tableWord (Equiv.refl _) tail owner) middle) :
    (∀ i : Fin size, output (base + i.val) = child i) ∧
    (∀ i : Fin size, output (tail + i.val) = owner i) ∧
    (∀ i, i < base → output i = input i) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    have low : base + i.val < tail := by
      rw [← adjacent]
      exact Nat.add_lt_add_left i.isLt base
    rw [right, segment_other middle tail size _ _ (.inl low), left]
    exact scan_read input (Equiv.refl _) child base i
  · intro i
    rw [right]
    exact scan_read middle (Equiv.refl _) owner tail i
  · intro i hi
    have low : i < tail := by omega
    rw [right, segment_other middle tail size _ _ (.inl low), left,
      segment_other input base size _ _ (.inl hi)]

include u in
theorem image (ports : m<2^W) (full : m*2^t<2^W) :
    let out := ((both cur m).pipeline cur).run mem
    (∀ i : Fin n, out ((entry).words 42+i.val)=(value c.node m (2^t) true i.val:Word W)) ∧
    (∀ i : Fin n, out ((entry).words 44+i.val)=(value c.node m (2^t) false i.val:Word W)) ∧
    (∀ i,i<(entry).words 42 → out i=mem i) := by
  let mid := ((scan cur m true).pipeline cur).run mem
  have spec := (scan cur m true).run_spec cur mem c.header 63 (entry).words H
    u.header (.inr u.controls) u.start_live (safe u).1
  have next : CursorSpace cur mid c K v a t h pad := u.frame mid spec.2.2
  simp only [both, pair_run]
  exact adjacent_tables mem mid (((scan cur m false).pipeline cur).run mid)
    (fun i : Fin n => (value c.node m (2^t) true i.val : Word W))
    (fun i : Fin n => (value c.node m (2^t) false i.val : Word W))
    (owner_spans (c:=c) (v:=v) (a:=a) (t:=t) (h:=h) (pad:=pad) (K:=K)).1
    (single u true ports full) (single next false ports full)


end ThreeFlat.Diagonal.RefreshNodeOwners

end OAI
