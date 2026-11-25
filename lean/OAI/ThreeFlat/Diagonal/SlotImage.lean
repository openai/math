import OAI.Computability.VPVNP.SlotGraph
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic

namespace OAI
/-! # Common physical image of a numbered slot graph

A table has three outgoing columns and three incoming columns: neighbor
base ordinal, receiving slot, and source displacement. The incoming row
at a receiving slot records its unique source. The separate width array
uses outgoing source coordinates in base, slot, lane order.
-/

namespace ThreeFlat.Diagonal.SlotImage

open Computability.VPVNP.Compression

variable {B L : Type*} {v lanes d : ℕ}

structure Columns where
  graph : ℕ
  rows : ℕ
  widths : ℕ
  deriving DecidableEq

abbrev Edge (B L : Type*) (d : ℕ) := (B × Fin d) × L

def ordinal (base : B ≃ Fin v) (p : B × Fin d) := (base p.1).val*d+p.2.val

def siteOrdinal (base : B ≃ Fin v) (lane : L ≃ Fin lanes) (s : B × L) := (base s.1).val*lanes+(lane s.2).val

def edgeOrdinal (base : B ≃ Fin v) (lane : L ≃ Fin lanes) (e : Edge B L d) :=
  ordinal base e.1*lanes+(lane e.2).val

def oriented (G : LiftedSlots B d L) (back : Bool) (p : B × Fin d) : B × Fin d :=
  if back then G.base.target.symm p else G.base.target p

def shift (G : LiftedSlots B d L) (back : Bool) (p : B × Fin d) : L :=
  G.displacement (if back then G.base.target.symm p else p)

def column (back : Bool) (f : Fin 3) : ℕ := (if back then 3 else 0)+f.val

def cell (C : Columns) (base : B ≃ Fin v) (p : B × Fin d) (back : Bool) (f : Fin 3) :=
  C.graph+C.rows*column back f+ordinal base p

def fields (G : LiftedSlots B d L) (base : B ≃ Fin v) (lane : L ≃ Fin lanes) (p : B × Fin d)
    (back : Bool) : Fin 3 → ℕ :=
  ![(base (oriented G back p).1).val,(oriented G back p).2.val,(lane (shift G back p)).val]

/-- This single relation applies to the initial binary cursor and to every
numbered regularized shrink or refresh successor. -/
structure Stored (G : LiftedSlots B d L) (base : B ≃ Fin v) (lane : L ≃ Fin lanes)
    (C : Columns) (mem : ℕ → ℕ) (width : Edge B L d → ℕ) : Prop where
  rowCount : C.rows=v*d
  graph : ∀ p back f, mem (cell C base p back f)=fields G base lane p back f
  widthWord : ∀ e, mem (C.widths+edgeOrdinal base lane e)=width e

variable {G : LiftedSlots B d L} {base : B ≃ Fin v} {lane : L ≃ Fin lanes} {C : Columns}
  {mem : ℕ → ℕ} {width : Edge B L d → ℕ}

theorem Stored.neighbor (s : Stored G base lane C mem width) (p : B × Fin d) (back : Bool) :
    mem (cell C base p back 0)=(base (oriented G back p).1).val := s.graph p back 0

theorem Stored.mate (s : Stored G base lane C mem width) (p : B × Fin d) (back : Bool) :
    mem (cell C base p back 1)=(oriented G back p).2.val := s.graph p back 1

theorem Stored.displacement (s : Stored G base lane C mem width) (p : B × Fin d) (back : Bool) :
    mem (cell C base p back 2)=(lane (shift G back p)).val := s.graph p back 2

private theorem mixed {v n i j : ℕ} (hi : i<v) (hj : j<n) : i*n+j<v*n :=
  (Nat.add_lt_add_left hj _).trans_le (by simpa only [Nat.succ_mul] using Nat.mul_le_mul_right n hi)

theorem ordinal_lt (base : B ≃ Fin v) (p : B × Fin d) : ordinal base p<v*d :=
  mixed (base p.1).isLt p.2.isLt

theorem edgeOrdinal_lt (base : B ≃ Fin v) (lane : L ≃ Fin lanes) (e : Edge B L d) :
    edgeOrdinal base lane e<v*d*lanes := mixed (ordinal_lt base e.1) (lane e.2).isLt

theorem cell_range (s : Stored G base lane C mem width) (p : B × Fin d) (back : Bool) (f : Fin 3) :
    C.graph≤cell C base p back f ∧ cell C base p back f<C.graph+6*C.rows := by
  have idx : ordinal base p<C.rows := by rw [s.rowCount]; exact ordinal_lt base p
  have hc : column back f<6 := by cases back <;> dsimp [column] <;> have := f.isLt <;> omega
  have h := mixed hc idx
  unfold cell
  rw [Nat.mul_comm C.rows]
  omega

/-- Unrelated histogram, node or navigation writes preserve the physical image
once the allocator places both input spans outside their write interval. -/
theorem Stored.frame (s : Stored G base lane C mem width) {mem' : ℕ → ℕ}
    (edges : ∀ a, C.graph≤a → a<C.graph+6*C.rows → mem' a=mem a)
    (widths : ∀ a, C.widths≤a → a<C.widths+v*d*lanes → mem' a=mem a) :
    Stored G base lane C mem' width where
  rowCount := s.rowCount
  graph p back f := (edges _ (cell_range s p back f).1 (cell_range s p back f).2).trans (s.graph p back f)
  widthWord e := (widths _ (Nat.le_add_right ..) (Nat.add_lt_add_left (edgeOrdinal_lt base lane e) _)).trans (s.widthWord e)

end ThreeFlat.Diagonal.SlotImage

end OAI
