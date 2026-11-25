import OAI.ThreeFlat.Diagonal.RefreshCursorTime
import OAI.ThreeFlat.Diagonal.RefreshRecordCursor

namespace OAI
/-! # All native refresh calls fit from the canonical chronological allocator -/

namespace ThreeFlat.Diagonal.RefreshStageNav.CursorSpace

open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.Compression RAM RAM.HeaderScan NavigationDirectory
open RefreshDemandRows CompressorPacking.Native
open scoped Fin.CommRing

variable {W v a t h pad K k : ℕ} {cur : Word W} {mem : Memory W} {c : Cursor}
    (u : CursorSpace cur mem c K v a t h pad)
set_option quotPrecheck false
local notation "m" => mPort a
local notation "d" => 1+h+pad
local notation "entry" => allocate K c (.refresh v m (2^t) h pad)
local notation "keep" => fun i : ℕ=>i<c.heap ∨ (entry).next.heap≤ i

include u

theorem span_safe (f n : ℕ) (r : RAM.DescriptorExpr.Term W 0 1) (hf : f≤63) (hn : n≤63)
    (lo : c.heap≤(entry).words f) (hi : (entry).words f+(entry).words n≤(entry).next.heap) :
    Scans.Safe 63 (entry).words keep ⟨f,n,r⟩ := by
  have cap := u.controls.trans_lt cur.isLt
  exact ⟨hf,hn,hi.trans_lt cap,fun i q=>q.imp (fun b=>b.trans_le lo) (fun b=>hi.trans b)⟩

theorem start_live (i : ℕ) (bound : i≤63) : keep (c.header+i) := by
  left
  have := u.earlier
  omega

theorem pre_safe (base : Fin (k+1) → (Bool × Fin m × Fin m) → ℕ) (size : Fin (k+1)→ℕ) :
    (preScans cur base size).every (Scans.Safe 63 (entry).words keep) := by
  obtain ⟨h1,h2,h3,h4,h5⟩ := ordered (c:=c) (K:=K) (v:=v) (a:=a) (t:=t) (h:=h) (pad:=pad)
  change (entry).words 12+3*(v*m)=_ at h3
  constructor
  · apply u.span_safe <;> first | decide | omega | (change _+3*(v*m)≤_; omega)
  · apply u.span_safe <;> first | decide | rfl | (change c.heap+3*(v*2^t)≤_; omega)

theorem post_safe (E : SlotGraph (Fin m) h)
    (base : Fin (k+1) → (Bool × Fin m × Fin m) → ℕ)
    (size bits : Fin (k+1)→ℕ) (pool : ∀ j,Fin (size j)→Fin m→Fin h→ℕ) :
    (postScans cur E pad K base size bits pool).every (Scans.Safe 63 (entry).words keep) := by
  obtain ⟨h1,h2,h3,h4,h5⟩ := ordered (c:=c) (K:=K) (v:=v) (a:=a) (t:=t) (h:=h) (pad:=pad)
  let fresh := nextColumns entry v m h pad
  have g : (entry).words 14=fresh.graph := rfl
  have w : (entry).words 19=fresh.widths := rfl
  have gl : (entry).words 16=6*fresh.rows := rfl
  have wl : (entry).words 17=v*m*d*2^t := rfl
  have sl : (entry).words 20=v*2^t*m*h := rfl
  dsimp only [fresh] at g w gl
  refine ⟨u.span_safe _ _ _ (by decide) (by decide) (by omega) (by omega),?_,?_⟩
  · exact u.span_safe _ _ _ (by decide) (by decide) (by omega) (by omega)
  · exact u.span_safe _ _ _ (by decide) (by decide) (by omega) (by omega)

theorem recorder_safe : (recordScans cur m d K).every (Scans.Safe 63 (entry).words keep) := by
  obtain ⟨h1,h2,h3,h4,h5⟩ := ordered (c:=c) (K:=K) (v:=v) (a:=a) (t:=t) (h:=h) (pad:=pad)
  obtain ⟨k0,m0,a0,e0,last⟩ := record_layout (c:=c) (K:=K) (v:=v) (a:=a) (t:=t) (h:=h) (pad:=pad)
  let P := recordPointers entry
  let N := v*m*2^t
  have f34 : (entry).words 34=P.kernel := rfl
  have f35 : (entry).words 35=N*5 := Nat.mul_comm 5 N
  have f36 : (entry).words 36=P.motif := rfl
  have f37 : (entry).words 37=N*6 := Nat.mul_comm 6 N
  have f38 : (entry).words 38=P.headers := rfl
  have f39 : (entry).words 39=N*2 := Nat.mul_comm 2 N
  have f40 : (entry).words 40=P.halves := rfl
  have f41 : (entry).words 41=N*(8*d) := Nat.mul_comm (8*d) N
  dsimp only [P,N] at f34 f35 f36 f37 f38 f39 f40 f41
  exact ⟨u.span_safe _ _ _ (by decide) (by decide) (by omega) (by omega),
    u.span_safe _ _ _ (by decide) (by decide) (by omega) (by omega),
    u.span_safe _ _ _ (by decide) (by decide) (by omega) (by omega),
    u.span_safe _ _ _ (by decide) (by decide) (by omega) (by omega)⟩

end ThreeFlat.Diagonal.RefreshStageNav.CursorSpace

end OAI
