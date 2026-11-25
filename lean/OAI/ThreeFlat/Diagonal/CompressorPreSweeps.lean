import OAI.ThreeFlat.Diagonal.CompressorSplitImage
import OAI.ThreeFlat.Diagonal.CompressorGreedyRows

namespace OAI
/-! # Clear and populate each of the two evolving vertex tables in the actual chronological pass -/
namespace ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkStage.Resident
open Computability.VPVNP.Compression Computability.VPVNP.BurstRAM Computability.VPVNP.BurstRAM.PrivateRAM RAM RAM.DescriptorScan
open scoped Fin.NatCast
variable {w : ℕ} {m : Memory w} {cell : Word w} (pub : Fin 1→Word w)

def one (row : Template.F) (lo sz : ℕ) (cell : Word w) := (Recipe.one row lo sz).install cell

theorem one_sweep (row : Template.F) (lo sz start count : ℕ)
    (left : (headerRead m cell lo).val=start) (right : (headerRead m cell sz).val=count) :
    ((one row lo sz cell).execute cell pub m).2 =
      sweep (fun a z=>(Template.emit cell row).eval pub z (fun _=>a)) count (start:Word w) m := by
  change sweep _ (headerRead m cell sz).val (headerRead m cell lo) m=_
  have base : headerRead m cell lo=(start:Word w) := by rw [←left,Fin.cast_val_eq_self]
  rw [right,base]

theorem zero_sweep (lo sz start count : ℕ) (fit : start+count<2^w)
    (left : (headerRead m cell lo).val=start) (right : (headerRead m cell sz).val=count) :
    ((one (.lit 0) lo sz cell).execute cell pub m).2 = fillSegment start count (fun _=>0) m := by
  apply one_image _ cell pub m start count (fun _=>0) fit left right
  intro _ _ _ _ _
  rfl

section
variable {B H : Type} [DecidableEq B] [AddCommGroup H] {N t l : ℕ} {S : Graph.Stage}
variable {P : PackingData B H (BitWord t) (BitWord l) S.degree S.colors}
variable {b : B ≃ Fin N} {p : Pointers}
variable {prior : Arc B H (BitWord t) (BitWord l) S.degree S.colors → ℕ}
local notation "x" => dims S N t l
local notation "C" => incoming S N p

omit [AddCommGroup H] in
theorem Sliced.color (h : Sliced S P b p cell prior m) (s : Fresh (dims S N t l) p cell.val) (palette : 2*S.degree+1≤2^w)
    (oneWord : (1:Word w)≠0) (blank : ∀v,m (p.colors+(b v).val)=0) :
    let pass:=one (Template.color S.degree) colors oldBases cell
    let out:=(pass.execute cell pub m).2
    pass.fits cell pub m ∧ agreesOutside p.colors (p.colors+N) out m ∧
      ∀v,out (p.colors+(b v).val)=((Ordered.colors P.slots b.symm v).val:Word w) := by
  have s0:=s.splitEnd
  have s1:=s.colorEnd
  have s2:=s.offsetEnd
  have s3:=s.high
  have cap:=cell.isLt
  have baseCount : (dims S N t l).oldBase=N := rfl
  have fit : p.colors+N<2^w := by omega
  have lo : (headerRead m cell colors).val=p.colors := by
    change (headerRead m cell (18 : Fin 34).val).val=p.colors
    rw [h.header.native (18 : Fin 34)]
    change (p.colors:Word w).val=p.colors
    exact Fin.val_cast_of_lt (by omega)
  have len : (headerRead m cell oldBases).val=N := by
    change (headerRead m cell (10 : Fin 34).val).val=N
    rw [h.header.native (10 : Fin 34)]
    change (N:Word w).val=N
    exact Fin.val_cast_of_lt (by omega)
  dsimp only
  refine ⟨?_,?_⟩
  · change (headerRead m cell colors).val+(headerRead m cell oldBases).val<2^w
    rwa [lo,len]
  rw [one_sweep pub _ _ _ _ _ lo len]
  apply inPlace_scan b p.colors fit m (List.ofFn (Equiv.refl (Fin (2*S.degree+1)))) 0
    (Ordered.colorBan P.slots) (fun a=>(a.val:Word w)) (fun _=>0) _ blank
  intro alt table v frame native
  exact (h.frame s s0 (by omega) frame).toOld.colorStep pub v table palette oneWord fit.le native

omit [AddCommGroup H] in
theorem Sliced.offset (h : Sliced S P b p cell prior m) (s : Fresh (dims S N t l) p cell.val) (tw : t≤w)
    (oneWord : (1:Word w)≠0) (blank : ∀v,m (p.offsets+(b v).val)=0) :
    let pass:=one (Template.offset S.degree t) offsets oldBases cell
    let out:=(pass.execute cell pub m).2
    pass.fits cell pub m ∧ agreesOutside p.offsets (p.offsets+N) out m ∧
      ∀v,out (p.offsets+(b v).val)=tagWord tw (Ordered.offsets P.slots (shift P) b.symm (tagOrdinal t).symm v) := by
  have s0:=s.splitEnd
  have s1:=s.colorEnd
  have s2:=s.offsetEnd
  have s3:=s.high
  have cap:=cell.isLt
  have offsetEnd : p.offsets+N≤p.newGraph := s.offsetEnd
  have fit : p.offsets+N<2^w := (offsetEnd.trans s.high).trans_lt cell.isLt
  have lo : (headerRead m cell offsets).val=p.offsets := by
    have word : headerRead m cell offsets=(p.offsets:Word w) := h.header.native (19:Fin 34)
    rw [word,Fin.val_cast_of_lt (by omega)]
  have len : (headerRead m cell oldBases).val=N := by
    have word : headerRead m cell oldBases=(N:Word w) := h.header.native (10:Fin 34)
    rw [word,Fin.val_cast_of_lt (by omega)]
  dsimp only
  refine ⟨?_,?_⟩
  · change (headerRead m cell offsets).val+(headerRead m cell oldBases).val<2^w
    rwa [lo,len]
  rw [one_sweep pub _ _ _ _ _ lo len]
  apply inPlace_scan b p.offsets fit m (List.ofFn (tagOrdinal t).symm) 0
    (Ordered.tagBan P.slots (shift P)) (tagWord tw) (fun _=>0) _ (by simpa only [tagWord_zero] using blank)
  intro alt table v frame native
  exact (h.frame s (by omega) s2 frame).tagStep pub v table tw oneWord fit.le native

end
end ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkStage.Resident

end OAI
