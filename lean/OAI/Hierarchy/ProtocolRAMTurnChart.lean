import OAI.Hierarchy.ProtocolRAMTurnRead
import OAI.Hierarchy.ProtocolRAMVisitColumns

namespace OAI
/-! # Orienting the immutable turn header from the actual old and paid words -/

namespace Hierarchy.ProtocolRAMTurnChart

open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure DescriptorExpr
open ProtocolRAM ProtocolRAMTurnItinerary
open scoped Fin.CommRing

/-- All six geometry words depend only on the unmodified commodity's type, ordinal
and raw boundary. For a permanent row the public seat word is ignored. -/
structure Geometry where
  item : ℕ
  origin : ℕ
  length : ℕ
  raw : ℕ
  permanent : Bool
  label : ℕ

def Geometry.field (u : Geometry) : Fin 6 → ℕ := ![u.item,u.origin,u.length,u.raw,u.permanent.toNat,u.label]

def bank (base bits : ℕ) (f : Fin 6) : Bank := ⟨base+f.val*2^bits,bits⟩

def get (base bits : ℕ) (f : Fin 6) : Expr := .lookup (bank base bits f) .row

/-- A literal read-only field-major header with zero padding. No visit site, direction,
permutation image, selected route incidence or final width is included. -/
def mount {W N : ℕ} (base bits : ℕ) (u : Fin N → Geometry) (m : Memory W) : Memory W :=
  fillSegment base (6*2^bits) (fun a =>
    if h : (a-base)/(2^bits) < 6 ∧ (a-base)%(2^bits) < N then
      ((u ⟨(a-base)%(2^bits),h.2⟩).field ⟨(a-base)/(2^bits),h.1⟩:Word W) else 0) m

def Loaded {W N : ℕ} (base bits : ℕ) (u : Fin N → Geometry) (m : Memory W) : Prop :=
  ∀ (f : Fin 6) (i : Fin N),(get base bits f).eval m (i.val:Word W)=((u i).field f:Word W)

theorem mounted {W N : ℕ} (base bits : ℕ) (u : Fin N → Geometry) (m : Memory W)
    (nRoom : N ≤ 2^bits) (words : N ≤ 2^W) : Loaded base bits u (mount base bits u m) := by
  intro f i
  have cap : i.val < 2^bits := i.isLt.trans_le nRoom
  have fit := i.isLt.trans_le words
  let page := 2^bits
  change i.val < page at cap
  have off : f.val*page+i.val < 6*page := by
    have ht := Nat.mul_le_mul_right page f.isLt
    rw [Nat.succ_mul] at ht
    omega
  have div : (f.val*page+i.val)/page=f.val := by
    simpa only [Nat.mul_comm page f.val,Nat.div_eq_of_lt cap,Nat.add_zero] using
      Nat.mul_add_div (by exact Nat.two_pow_pos bits : page > 0) f.val i.val
  have md : (f.val*page+i.val)%page=i.val := Nat.mul_add_mod_of_lt cap
  change mount base bits u m ((base+f.val*page)+(i.val:Word W).val%page)=_
  rw [Fin.val_cast_of_lt fit,Nat.mod_eq_of_lt cap]
  have order : (base+f.val*page)+i.val=base+(f.val*page+i.val) := Nat.add_assoc ..
  rw [order]
  simp [mount,fillSegment,show base+(f.val*page+i.val)<base+6*page by omega,←show page=2^bits from rfl,
    div,md,f.isLt,i.isLt]

structure Data where
  rawSource : Bank
  rawTarget : Bank
  oldWidth : Bank
  site : Bank
  sourceRole : Bank
  targetRole : Bank
  /-- Literal public table u ↦ u/2 on the fixed even role codes. -/
  half : Bank

def direction (item : Expr) (d : Data) : Expr :=
  .branch .lt (.lookup d.rawSource item) (.lookup d.rawTarget item) (.lit 0) (.lit 1)

def seat (item raw permanent label : Expr) (d : Data) : Expr :=
  .branch .eq permanent (.lit 0) label <| .lookup d.half
    (.branch .eq raw (.lit 0) (.lookup d.sourceRole item) (.lookup d.targetRole item))

def chart (base bits : ℕ) (d : Data) : Chart :=
  let item := get base bits 0
  let len := get base bits 2
  let raw := get base bits 3
  let reversal := direction item d
  ⟨item,get base bits 1,len,.branch .eq reversal (.lit 0) raw (.op .sub len raw),
    reversal,.lookup d.oldWidth item,.lookup d.site .row,seat item raw (get base bits 4) (get base bits 5) d⟩

def walk (base bits : ℕ) (d : Data) (edge tail head : Bank) : ProtocolRAMVisitColumns.Inputs :=
  ⟨get base bits 0,get base bits 1,get base bits 3,d.rawSource,edge,tail,head⟩

structure Words where
  rawSource : ℕ → ℕ
  rawTarget : ℕ → ℕ
  width : ℕ → ℕ
  sourceRole : ℕ → ℕ
  targetRole : ℕ → ℕ

def rev (v : Words) (i : ℕ) := decide (¬v.rawSource i < v.rawTarget i)

def record {N : ℕ} (u : Fin N → Geometry) (v : Words) (site : Fin N → ℕ) (i : Fin N) : Turn :=
  let x := u i
  ⟨x.item,x.origin,x.length,if rev v x.item then x.length-x.raw else x.raw,rev v x.item,v.width x.item,site i,
    if x.permanent then (if x.raw=0 then v.sourceRole x.item else v.targetRole x.item)/2 else x.label⟩

variable {W N : ℕ}

structure Data.Before (d : Data) (v : Words) (m : Memory W) (u : Fin N → Geometry) : Prop where
  rawSource : ∀ i,d.rawSource.read m ((u i).item:Word W)=(v.rawSource (u i).item:Word W)
  rawTarget : ∀ i,d.rawTarget.read m ((u i).item:Word W)=(v.rawTarget (u i).item:Word W)
  width : ∀ i,d.oldWidth.read m ((u i).item:Word W)=(v.width (u i).item:Word W)
  sourceRole : ∀ i,d.sourceRole.read m ((u i).item:Word W)=(v.sourceRole (u i).item:Word W)
  targetRole : ∀ i,d.targetRole.read m ((u i).item:Word W)=(v.targetRole (u i).item:Word W)
  halfSource : ∀ i,d.half.read m (v.sourceRole (u i).item:Word W)=((v.sourceRole (u i).item/2:ℕ):Word W)
  halfTarget : ∀ i,d.half.read m (v.targetRole (u i).item:Word W)=((v.targetRole (u i).item/2:ℕ):Word W)
  srcRoom : ∀ i,v.rawSource (u i).item < 2^W
  dstRoom : ∀ i,v.rawTarget (u i).item < 2^W

structure Data.Reads (d : Data) (v : Words) (m : Memory W) (u : Fin N → Geometry)
    (site : Fin N → ℕ) : Prop extends d.Before v m u where
  low : ∀ i,d.site.read m (i.val:Word W)=(site i:Word W)

theorem reads (base bits : ℕ) (d : Data) (u : Fin N → Geometry) (v : Words)
    (site : Fin N → ℕ) (m : Memory W) (header : Loaded base bits u m)
    (sources : d.Reads v m u site) (pos : ∀ i,(u i).raw ≤ (u i).length)
    (small : ∀i,(u i).length < 2^W) (one : 1 < 2^W) :
    (chart base bits d).Reads (record u v site) m := by
  have getAt (f : Fin 6) (i : Fin N) := header f i
  have ir (i : Fin N) : (get base bits 0).eval m (i.val:Word W)=((u i).item:Word W) := getAt 0 i
  have ln (i : Fin N) : (get base bits 2).eval m (i.val:Word W)=((u i).length:Word W) := getAt 2 i
  have raw (i : Fin N) : (get base bits 3).eval m (i.val:Word W)=((u i).raw:Word W) := getAt 3 i
  have pe (i : Fin N) : (get base bits 4).eval m (i.val:Word W)=((u i).permanent.toNat:Word W) := getAt 4 i
  have lab (i : Fin N) : (get base bits 5).eval m (i.val:Word W)=((u i).label:Word W) := getAt 5 i
  have nz : (1:Word W)≠0 := by
    intro same
    have hv:=congrArg Fin.val same
    change (1:Word W).val=0 at hv
    rw [show (1:Word W)=((1:ℕ):Word W) by rfl,Fin.val_cast_of_lt one] at hv
    omega
  have dir (i : Fin N) : (direction (get base bits 0) d).eval m (i.val:Word W)=((rev v (u i).item).toNat:Word W) := by
    have lt : ((v.rawSource (u i).item:Word W)<(v.rawTarget (u i).item:Word W)) ↔
        v.rawSource (u i).item<v.rawTarget (u i).item := by
      change (_:Word W).val<(_:Word W).val ↔ _
      rw [Fin.val_cast_of_lt (sources.srcRoom i),Fin.val_cast_of_lt (sources.dstRoom i)]
    by_cases h : v.rawSource (u i).item<v.rawTarget (u i).item
    · have hw := lt.mpr h
      simp [direction,Expr.eval,Comparison.test,ir,sources.rawSource,sources.rawTarget,hw,h,rev]
    · have hw : ¬((v.rawSource (u i).item:Word W)<(v.rawTarget (u i).item:Word W)) := fun bad=>h (lt.mp bad)
      simp [direction,Expr.eval,Comparison.test,ir,sources.rawSource,sources.rawTarget,hw,h,rev]
  refine ⟨ir,getAt 1,ln,?_,dir,?_,sources.low,?_⟩
  · intro i
    change (Expr.branch .eq (direction (get base bits 0) d) (.lit 0) _ _).eval m _=_
    cases hr : rev v (u i).item <;>
      simp [Expr.eval,Comparison.test,dir,hr,nz,ln,raw,RowOp.opcode,BinaryOp.eval,record,Nat.cast_sub (pos i)]
  · intro i
    exact (congrArg (d.oldWidth.read m) (ir i)).trans (sources.width i)
  · intro i
    have rz : (((u i).raw:Word W)=0) ↔ (u i).raw=0 := by
      rw [Fin.ext_iff,Fin.val_cast_of_lt ((pos i).trans_lt (small i)),Fin.val_zero]
    have divides : 2^W ∣ (u i).raw ↔ (u i).raw=0 :=
      ⟨fun h=>Nat.eq_zero_of_dvd_of_lt h ((pos i).trans_lt (small i)),fun h=>h ▸ dvd_zero _⟩
    cases hp : (u i).permanent <;> by_cases hs : (u i).raw=0 <;>
      simp [chart,seat,record,Expr.eval,Comparison.test,pe,raw,ir,lab,hp,hs,nz,rz,sources.sourceRole,
        sources.targetRole,sources.halfSource,sources.halfTarget]

end Hierarchy.ProtocolRAMTurnChart

end OAI
