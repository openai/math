import OAI.ThreeFlat.Diagonal.TraceNodeHeaderScan
import OAI.ThreeFlat.Diagonal.PhysicalNodeTape

namespace OAI
/-! # Native compaction from the actual mounted 64-word table -/

namespace ThreeFlat.Diagonal.NavigationPass.TraceNodeHeaders
open Computability.VPVNP.BurstRAM PrivateRAM RAM RAM.NavigationNodeRows PhysicalPinsExpr PhysicalProcedure
open NavigationDirectory NodePublication
open scoped Fin.CommRing Classical

theorem MountedAt.congr {K : ℕ} {old new : ℕ→ℕ} (ops : List Stage) (c : Cursor)
    (initial : MountedAt old K ops c)
    (agree : ∀ x, c.header ≤ x → x<c.header+64*ops.length → new x=old x) :
    MountedAt new K ops c := by
  induction ops generalizing c with
  | nil => trivial
  | cons op ops ih =>
    obtain ⟨first, tail⟩ := initial
    have step : (allocate K c op).next.header=c.header+64 := by cases op <;> rfl
    constructor
    · intro j hj same
      rw [agree (c.header+j) (by omega) (by simp only [List.length_cons]; omega)]
      exact first j hj same
    · apply ih _ tail
      intro x h₁ h₂
      rw [step] at h₁ h₂
      apply agree x (by omega)
      simp only [List.length_cons]
      omega

structure ScanRoom (W ctrl head src dst stages : ℕ) : Prop where
  ctrl : ctrl < dst
  head : head+12 < dst
  source : src+64*stages ≤ dst
  sourceFits : src+64*stages+44 < 2^W
  targetFits : dst+16*(stages+1) < 2^W

theorem compactScan_spec {W ctrl head K : ℕ} (a : NodeArchive) (ops : List Stage)
    (c : Cursor) (seed : Layer) (m : Memory W)
    (room : ScanRoom W ctrl head c.header a.headerBase ops.length)
    (pointer : (m ctrl).val=head)
    (fields : ∀ j<13,(m (head+j)).val=scanFields a.banks ops.length c.header a.headerBase seed j)
    (mounted : MountedAt (fun x=>(m x).val) K ops c) (live : ∀ op∈ops,0<successors op) :
    let rows:=nodeLayers K ops c seed
    (compactScan W ctrl).Spec (·=m)
      (fun _ out => out=fillSegment a.headerBase (16*rows.length) (tapeWord a rows) m)
      (11+16*rows.length*(2*(compactRow ctrl).work+4)) := by
  intro rows
  let n := ops.length
  let dst := a.headerBase
  have width := room.targetFits
  have ctl := room.ctrl
  have hdr := room.head
  have nrow : rows.length=n+1 := nodeLayers_length ..
  have ctlFits : ctrl < 2^W := by dsimp [dst,n] at *; omega
  have dstWord : (m head).val=dst := by simpa [scanFields,dst] using fields 0 (by decide)
  have sizeWord : (m (head+1)).val=16*rows.length := by
    simpa [scanFields,nrow,n] using fields 1 (by decide)
  have h0 : (HeaderScan.headerWord m (ctrl:Word W) 0).val=dst := by
    simpa [HeaderScan.headerWord,Fin.val_cast_of_lt ctlFits,pointer] using dstWord
  have h1 : (HeaderScan.headerWord m (ctrl:Word W) 1).val=16*rows.length := by
    unfold HeaderScan.headerWord
    rw [Fin.val_cast_of_lt ctlFits]
    have atHead : m ctrl=(head:Word W) := (Fin.cast_val_eq_self _).symm.trans (by rw [pointer])
    have addr : ((head:Word W)+((1:ℕ):Word W)).val = head+1 := by
      rw [←Nat.cast_add,Fin.val_cast_of_lt (show head+1<2^W by omega)]
    rw [atHead,addr]
    exact sizeWord
  rw [←HeaderScan.binds_closed (w:=W) (compactRow ctrl)]
  intro labels regs slots
  apply HeaderScan.prefix_spec _ _ _ _ _ _ _ _ (by rw [nrow]; exact width) h0 h1
  intro i hi
  let t:=i/16
  let j : Fin 16 := ⟨i%16,Nat.mod_lt _ (by decide)⟩
  have split : i=16*t+j.val := by dsimp [t,j]; omega
  have time : t≤n := by rw [nrow] at hi; dsimp [t]; omega
  let newMem:=fillSegment dst i (tapeWord a rows) m
  let raw:=fun x=>(newMem x).val
  have before (x) (hx : x<dst) : raw x=(m x).val := by
    simp [raw,newMem,fillSegment,Nat.not_le_of_lt hx]
  have hp : raw ctrl=head := (before _ ctl).trans pointer
  have hf (q : ℕ) (hq : q<13) : raw (head+q)=scanFields a.banks n c.header dst seed q :=
    (before _ (by omega)).trans (fields _ hq)
  have tables : MountedAt raw K ops c := MountedAt.congr ops c mounted (fun x _ hx =>
    before _ (hx.trans_le room.source))
  have eq := compactTape_exact a.banks raw K ops c dst seed tables live
  have got := compactTape_get a.banks raw c.header dst n seed t time j
  rw [show n=ops.length by rfl,eq] at got
  have ft := compactRow_fits a.banks raw seed t j time hp hf (fun x=>(newMem x).isLt)
    ctlFits (by omega) room.sourceFits room.targetFits.le
  have ev := (compactRow ctrl).value_eq_natural (fun _=>0) raw (fun _=>dst+16*t+j.val) ft
  have val := compactRow_natural (W:=W) a.banks raw seed t j hp hf
  rw [val] at ev
  rw [HeaderScan.eval_closed]
  change _=tapeWord a rows (dst+i)
  convert ev using 1
  · simp only [raw,Nat.cast_zero,Fin.cast_val_eq_self]
    rw [split]
    simp [dst,newMem,Nat.add_assoc]; rw [←split]
  · simp [tapeWord,rows,dst,split,got]; rfl


end ThreeFlat.Diagonal.NavigationPass.TraceNodeHeaders

end OAI
