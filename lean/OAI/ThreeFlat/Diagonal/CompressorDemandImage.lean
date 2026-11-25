import OAI.ThreeFlat.Diagonal.CompressorPreChart

namespace OAI
/-! # Linear-order materialization of the old AB/CD demand pair for every physical motif -/
namespace ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkStage.Resident
open Computability.VPVNP.Compression Computability.VPVNP.BurstRAM Computability.VPVNP.BurstRAM.PrivateRAM RAM RAM.DescriptorScan RAM.PhysicalPinsExpr Placement
open scoped Classical Fin.NatCast
variable {B H : Type} [AddCommGroup H] [Fintype B] [Fintype H] {w N t l : ℕ}
variable (S : Graph.Stage) (P : PackingData B H (BitWord t) (BitWord l) S.degree S.colors)
variable (b : B ≃ Fin N) (hc : 2≤S.colors)
local notation "num" => denseMotifRow P b (tagOrdinal t) (tagOrdinal l) hc

noncomputable def demandNumber : P.Motif × Fin 2 ≃ Fin (2*(dims S N t l).motifs) :=
  (((num).prodCongr (Equiv.refl _)).trans finProdFinEquiv).trans (finCongr (Nat.mul_comm (dims S N t l).motifs 2))

omit [Fintype B] [Fintype H] in
theorem demandNumber_val (a : P.Motif) (j : Fin 2) :
    (demandNumber S P b hc (a,j)).val=2*(num a).val+j.val := by
  change _+2*_ = 2*_+_
  ac_rfl

variable {S P b} {p : Pointers} {cell : Word w} {m : Memory w}
variable {prior : Arc B H (BitWord t) (BitWord l) S.degree S.colors → ℕ}
local notation "du" => demandWidth P prior (motifNumbers P (Demand.key P (baseNat b)) hc)

theorem Chart.demands (q : Chart S P b p cell prior m) (s : Fresh (dims S N t l) p cell.val) (pub : Fin 1→Word w)
    (E : Codec B w S.colors t l) (code : ∀v,E.base v=((b v).val:Word w))
    (add : ∀u v,slotCode (w:=w) P (u+v)=BinaryOp.bitXor.eval (slotCode P u) (slotCode P v))
    (sub : ∀u v,slotCode (w:=w) P (u-v)=BinaryOp.bitXor.eval (slotCode P u) (slotCode P v))
    (bits : 2^S.colors<2^w) (dimensions : S.degree<2^w ∧ 2^t<2^w ∧ 2^l<2^w)
    (size : 3*(2^S.colors*S.degree)/4<2^w)
    (sums : ∀a:P.Motif,thickWidth P prior (P.bundle a)<2^w) :
    let scan:=one (Template.input S) demand demandWords cell
    let out:=(scan.execute cell pub m).2
    scan.fits cell pub m ∧ agreesOutside p.demands (p.demands+2*(dims S N t l).motifs) out m ∧
      Chart S P b p cell prior out ∧
      ∀ (a : P.Motif) (j : Fin 2), out
        (p.demands+2*(denseMotifRow P b (tagOrdinal t) (tagOrdinal l) hc a).val+j.val)=
        (demandWidth P prior (motifNumbers P (Demand.key P (baseNat b)) hc) a j : Word w) := by
  let order:=demandNumber S P b hc
  let word:=fun u : P.Motif × Fin 2=>(du u.1 u.2:Word w)
  let file:=PostImage.file order word p.demands
  let out:=fillSegment p.demands (2*(dims S N t l).motifs) file m
  have endFit : p.demands+2*(dims S N t l).motifs<2^w := by
    have:=s.demandEnd;have:=s.splitEnd;have:=s.colorEnd;have:=s.offsetEnd;have:=s.high;have:=cell.isLt;omega
  have lo : (headerRead m cell demand).val=p.demands := by
    change (headerRead m cell (8 : Fin 34).val).val = p.demands
    rw [q.header.native (8 : Fin 34)]
    change (p.demands : Word w).val = p.demands
    exact Fin.val_cast_of_lt (by omega)
  have len : (headerRead m cell demandWords).val=2*(dims S N t l).motifs := by
    change (headerRead m cell (9 : Fin 34).val).val = _
    rw [q.header.native (9 : Fin 34)]
    change ((2*(dims S N t l).motifs : ℕ) : Word w).val = _
    exact Fin.val_cast_of_lt (by omega)
  have image : ((one (Template.input S) demand demandWords cell).execute cell pub m).2=out := by
    apply FileSpec.image
    apply PostImage.file_spec cell pub _ demand demandWords m p.demands order word endFit lo len
    intro u alt frame
    let qq:=q.demandFrame s frame
    let vs:=fun _ : Fin 1=>((p.demands+(order u).val:ℕ):Word w)
    have start : Formula.value (fun _=>cell) alt vs (Template.f demand)=(p.demands:Word w) := qq.header.field vs 8
    have bound : p.demands+(order u).val<2^w := (Nat.add_lt_add_left (order u).isLt _).trans endFit
    have off:=Template.cut_index cell alt vs p.demands (order u).val (Template.f demand) bound start rfl
    have ix := demandNumber_val S P b hc u.1 u.2
    have rowFit : 2*(num u.1).val+u.2.val<2^w :=
      ix.symm.le.trans_lt ((Nat.le_add_left (order u).val p.demands).trans_lt bound)
    rw [Template.program_value]
    apply ShrinkWidth.input_value (qq.arcs E code add sub vs) (qq.widths E code vs) hc u.1 _ u.2 bits dimensions
      (qq.header.field vs 14) rowFit _ size (sums u.1)
    exact off.trans (congrArg (fun n : ℕ => (n : Word w)) ix)
  change _ ∧ _
  rw [image]
  have f : agreesOutside p.demands (p.demands+2*(dims S N t l).motifs) out m:=fill_frame file m
  refine ⟨?_,f,q.demandFrame s f,?_⟩
  · change (headerRead m cell demand).val+(headerRead m cell demandWords).val<2^w
    rwa [lo,len]
  · intro a j
    have ix:=demandNumber_val S P b hc a j
    have top : (order (a,j)).val < 2*(dims S N t l).motifs := (order (a,j)).isLt
    have pos : p.demands+2*(num a).val+j.val=p.demands+(order (a,j)).val :=
      (Nat.add_assoc ..).trans (congrArg (p.demands + ·) ix.symm)
    rw [pos]
    simp [out,fillSegment,file,top,word]


end ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkStage.Resident

end OAI
