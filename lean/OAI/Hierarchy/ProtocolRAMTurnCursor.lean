import OAI.Hierarchy.ProtocolRAMTurnChart

namespace OAI
/-! # The native segmented walk supplies the visit-site operand to the adjacent-turn publisher -/

namespace Hierarchy.ProtocolRAMTurnCursor

open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open ProtocolRAM ProtocolRAMTurnChart ProtocolRAMTurnItinerary
open scoped Fin.CommRing

variable {W N : ℕ}

structure Safe (d : Data) (W initial : ℕ) : Prop where
  rawSource : d.rawSource.Fits W initial
  rawTarget : d.rawTarget.Fits W initial
  oldWidth : d.oldWidth.Fits W initial
  sourceRole : d.sourceRole.Fits W initial
  targetRole : d.targetRole.Fits W initial
  half : d.half.Fits W initial

private theorem kept (b : Bank) (floor : ℕ) (m out : Memory W) (safe : b.Fits W floor)
    (frame : ∀ a < floor,out a=m a) (i : Word W) : b.read out i=b.read m i :=
  frame _ ((Nat.add_lt_add_left (Nat.mod_lt i.val safe.1) _).trans_le safe.2.2)

theorem before (d : Data) (v : Words) (m out : Memory W) (u : Fin N → Geometry) (floor : ℕ)
    (read : d.Before v m u) (safe : Safe d W floor) (frame : ∀a < floor,out a=m a) :
    d.Before v out u := by
  have keep (b : Bank) (h : b.Fits W floor) (i : Word W) := kept b floor m out h frame i
  exact
    ⟨fun i=>(keep _ safe.rawSource _).trans (read.rawSource i),
     fun i=>(keep _ safe.rawTarget _).trans (read.rawTarget i),
     fun i=>(keep _ safe.oldWidth _).trans (read.width i),
     fun i=>(keep _ safe.sourceRole _).trans (read.sourceRole i),
     fun i=>(keep _ safe.targetRole _).trans (read.targetRole i),
     fun i=>(keep _ safe.half _).trans (read.halfSource i),
     fun i=>(keep _ safe.half _).trans (read.halfTarget i),
     read.srcRoom,read.dstRoom⟩

theorem run (base bits initial : ℕ) (d : Data) (u : Fin N → Geometry) (v : Words)
    (edges tails heads : Bank) (site : Fin N → ℕ) (paid tail head : ℕ → ℕ) (m : Memory W)
    (header : Loaded base bits u m) (prior : d.Before v m u) (safe : Safe d W initial)
    (rom : ∀ f,(get base bits f).Fits W initial)
    (zeroFit : d.site.base=initial+1+2*N) (siteRoom : N ≤ d.site.size)
    (within : ∀i,(u i).raw ≤ (u i).length) (lenFit : ∀i,(u i).length < 2^W) (one : 1 < 2^W)
    (geo : ProtocolRAMVisitColumns.Geography (walk base bits d edges tails heads) m
      (fun i=>(u i).raw) (fun i=>(u i).origin) (fun i=>(u i).item) site
      paid v.rawSource tail head)
    (fit : ∀ e ∈ ProtocolRAMVisitColumns.terms initial (initial+1+2*N) (walk base bits d edges tails heads),e.Fits W initial)
    (space : initial+1+3*N < 2^W) :
    ∃ out,(ProtocolRAMVisitColumns.program W N initial (walk base bits d edges tails heads)).Exec
        m out (ProtocolRAMVisitColumns.ticks N initial (walk base bits d edges tails heads)) ∧
      (chart base bits d).Reads (record u v site) out ∧
      (∀a,a < initial ∨ initial+1+3*N ≤ a → out a=m a) := by
  obtain ⟨out,exec,visit,frame⟩ := ProtocolRAMVisitColumns.run initial (walk base bits d edges tails heads)
    m _ _ _ _ _ _ _ _ geo fit space
  have low (a : ℕ) (ha : a < initial) := frame a (.inl ha)
  have hdr : Loaded base bits u out := fun f i=>
    (eval_below (get base bits f) (i.val:Word W) m out (rom f) low).trans (header f i)
  have coords (i : Fin N) : d.site.read out (i.val:Word W)=(site i:Word W) := by
    change out (d.site.base+(i.val:Word W).val%d.site.size)=_
    rw [zeroFit,Fin.val_cast_of_lt (by have := i.isLt;omega),Nat.mod_eq_of_lt (i.isLt.trans_le siteRoom)]
    exact visit i
  exact ⟨out,exec,reads base bits d u v _ out hdr ⟨before d v m out u initial prior safe low,coords⟩
    within lenFit one,frame⟩

end Hierarchy.ProtocolRAMTurnCursor

end OAI
