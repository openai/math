import OAI.ThreeFlat.Diagonal.CompressorPreSweeps

namespace OAI
/-! # The ordered clear, color and offset passes publish the packing's actual chart -/
namespace ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkStage.Resident
open Computability.VPVNP.Compression Computability.VPVNP.BurstRAM Computability.VPVNP.BurstRAM.PrivateRAM RAM RAM.DescriptorScan
open scoped Fin.NatCast
variable {B H : Type} [DecidableEq B] [AddCommGroup H] {w N t l : ℕ} {S : Graph.Stage}
variable {P : PackingData B H (BitWord t) (BitWord l) S.degree S.colors}
variable {b : B ≃ Fin N} {p : Pointers} {cell : Word w} {m : Memory w}
variable {prior : Arc B H (BitWord t) (BitWord l) S.degree S.colors → ℕ}
local notation "C" => incoming S N p

def coloringRest (cell : Word w) (S : Graph.Stage) (t : ℕ) (pub : Fin 1→Word w) (old : Memory w) :=
  let a:=(one (.lit 0) colors oldBases cell).execute cell pub old
  let b:=(one (.lit 0) offsets oldBases cell).execute cell pub a.2
  let c:=(one (Template.color S.degree) colors oldBases cell).execute cell pub b.2
  (one (Template.offset S.degree t) offsets oldBases cell).execute cell pub c.2 |>.2

def coloringFits (cell : Word w) (S : Graph.Stage) (t : ℕ) (pub : Fin 1→Word w) (m : Memory w) : Prop :=
  let a:=one (.lit 0) colors oldBases cell
  let b:=one (.lit 0) offsets oldBases cell
  let c:=one (Template.color S.degree) colors oldBases cell
  let d:=one (Template.offset S.degree t) offsets oldBases cell
  let x:=(a.execute cell pub m).2
  let y:=(b.execute cell pub x).2
  let z:=(c.execute cell pub y).2
  a.fits cell pub m ∧ b.fits cell pub x ∧ c.fits cell pub y ∧ d.fits cell pub z

omit [AddCommGroup H] in
theorem Sliced.greedy (h : Sliced S P b p cell prior m) (s : Fresh (dims S N t l) p cell.val) (pub : Fin 1→Word w)
    (palette : 2*S.degree+1≤2^w) (tw : t≤w) (oneWord : (1:Word w)≠0)
    (col_eq : ∀v,(P.color v).val=(Ordered.colors P.slots b.symm v).val)
    (tag_eq : ∀v,P.offset v=Ordered.offsets P.slots (shift P) b.symm (tagOrdinal t).symm v) :
    let out:=coloringRest cell S t pub m
    coloringFits cell S t pub m ∧ agreesOutside p.colors (p.offsets+N) out m ∧ Sliced S P b p cell prior out ∧
      StoredColumns.Auxiliary P b C (extra p) out := by
  let a:=(one (.lit 0) colors oldBases cell).execute cell pub m |>.2
  let b0:=(one (.lit 0) offsets oldBases cell).execute cell pub a |>.2
  let c0:=(one (Template.color S.degree) colors oldBases cell).execute cell pub b0 |>.2
  let out:=coloringRest cell S t pub m
  have s0:=s.splitEnd
  have s1:=s.colorEnd
  have s2:=s.offsetEnd
  have s3:=s.high
  have limit:=cell.isLt
  have baseCount : (dims S N t l).oldBase = N := rfl
  have cfits : p.colors+N<2^w := by omega
  have tfits : p.offsets+N<2^w := by omega
  have native (y : Memory w) (hh : Header (dims S N t l) p false cell y) :
      (headerRead y cell colors).val=p.colors ∧ (headerRead y cell offsets).val=p.offsets ∧
        (headerRead y cell oldBases).val=N := by
    refine ⟨?_,?_,?_⟩
    · change (headerRead y cell (18 : Fin 34).val).val = p.colors
      rw [hh.native (18 : Fin 34)]
      change (p.colors : Word w).val = p.colors
      exact Fin.val_cast_of_lt (by omega)
    · change (headerRead y cell (19 : Fin 34).val).val = p.offsets
      rw [hh.native (19 : Fin 34)]
      change (p.offsets : Word w).val = p.offsets
      exact Fin.val_cast_of_lt (by omega)
    · change (headerRead y cell (10 : Fin 34).val).val = N
      rw [hh.native (10 : Fin 34)]
      change (N : Word w).val = N
      exact Fin.val_cast_of_lt (by omega)
  have A : a=fillSegment p.colors N (fun _=>0) m :=
    zero_sweep pub colors oldBases p.colors N cfits (native _ h.header).1 (native _ h.header).2.2
  have fa : agreesOutside p.colors (p.colors+N) a m := by rw [A]; exact fill_frame _ _
  have ha:=h.frame s s0 (by omega) fa
  have B : b0=fillSegment p.offsets N (fun _=>0) a :=
    zero_sweep pub offsets oldBases p.offsets N tfits (native _ ha.header).2.1 (native _ ha.header).2.2
  have fb : agreesOutside p.offsets (p.offsets+N) b0 a := by rw [B]; exact fill_frame _ _
  have hb:=ha.frame s (by omega) s2 fb
  have cc:=hb.color pub s palette oneWord (fun v=>by
    rw [fb _ (.inl (by have:=(b v).isLt;omega)),A]
    simp [fillSegment,(b v).isLt])
  have fc : agreesOutside p.colors (p.colors+N) c0 b0:=cc.2.1
  have hc:=hb.frame s s0 (by omega) fc
  have tt:=hc.offset pub s tw oneWord (fun v=>by
    rw [fc _ (.inr (by omega)),B]
    simp [fillSegment,(b v).isLt])
  have ft : agreesOutside p.offsets (p.offsets+N) out c0:=tt.2.1
  have ho:=hc.frame s (by omega) s2 ft
  have fits : coloringFits cell S t pub m := by
    refine ⟨?_,?_,cc.1,tt.1⟩
    · change (headerRead m cell colors).val+(headerRead m cell oldBases).val<2^w
      rwa [(native _ h.header).1,(native _ h.header).2.2]
    · change (headerRead a cell offsets).val+(headerRead a cell oldBases).val<2^w
      rwa [(native _ ha.header).2.1,(native _ ha.header).2.2]
  refine ⟨fits,?_,ho,?_,?_,ho.split,cfits.le,tfits.le,ho.splitFits,ho.graphFits⟩
  · intro z outside
    have ic : z<p.colors ∨ p.colors+N≤z := by rcases outside with lo|hi <;> omega
    have it : z<p.offsets ∨ p.offsets+N≤z := by rcases outside with lo|hi <;> omega
    exact (ft _ it).trans ((fc _ ic).trans ((fb _ it).trans (fa _ ic)))
  · intro v
    change (out (p.colors+(b v).val)).val = (P.color v).val
    have beforeOffsets : p.colors+(b v).val < p.offsets := by
      have := (b v).isLt
      omega
    have readColor : c0 (p.colors+(b v).val) = ((Ordered.colors P.slots b.symm v).val : Word w) :=
      cc.2.2 v
    rw [ft _ (.inl beforeOffsets), readColor, Fin.val_cast_of_lt ((Ordered.colors P.slots b.symm v).isLt.trans_le palette)]
    exact (col_eq v).symm
  · intro v
    change (out (p.offsets+(b v).val)).val = (tagOrdinal t (P.offset v)).val
    have readTag : out (p.offsets+(b v).val) = tagWord tw (Ordered.offsets P.slots (shift P) b.symm (tagOrdinal t).symm v) :=
      tt.2.2 v
    rw [readTag, tag_eq]
    rfl


end ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkStage.Resident

end OAI
