import OAI.ThreeFlat.Diagonal.CompressorPreFrame

namespace OAI
/-! # The first native prepass publishes all eight sliced old displacement columns -/
namespace ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkStage.Resident
open Computability.VPVNP.Compression Computability.VPVNP.BurstRAM Computability.VPVNP.BurstRAM.PrivateRAM RAM RAM.DescriptorScan RAM.PhysicalPinsExpr
open scoped Fin.NatCast
variable {B H : Type} [AddCommGroup H] {w N t l : ℕ} {S : Graph.Stage}
variable {P : PackingData B H (BitWord t) (BitWord l) S.degree S.colors}
variable {b : B ≃ Fin N} {p : Pointers} {cell : Word w} {m : Memory w}
variable {prior : Arc B H (BitWord t) (BitWord l) S.degree S.colors → ℕ}
local notation "C" => incoming S N p
local notation "x" => dims S N t l

def splitNumbers (b : B ≃ Fin N) (d : ℕ) : ((Bool × Fin 4) × (B × Fin d)) ≃ Fin (8*(N*d)) :=
  let field:=(finTwoEquiv.symm.prodCongr (Equiv.refl (Fin 4))).trans finProdFinEquiv
  (field.prodCongr (PostImage.slotNumbers b)).trans finProdFinEquiv

theorem splitNumbers_val (b : B ≃ Fin N) (d : ℕ) (rev : Bool) (j : Fin 4) (u : B × Fin d) :
    (splitNumbers b d ((rev,j),u)).val =
      (N*d)*((if rev then 4 else 0)+j.val)+SlotImage.ordinal b u := by
  change (PostImage.slotNumbers b u).val+(N*d)*(j.val+4*(finTwoEquiv.symm rev).val)=_
  rw [PostImage.slotNumbers_val]
  cases rev <;> simp [finTwoEquiv] <;> ring

def splitSpan (S : Graph.Stage) : Recipe :=
  .one (splitRow Template.o Template.ptr (.reg 0) S.colors S.degree) splitShifts splitWords

theorem fill_frame {lo size : ℕ} (f : ℕ → Word w) (m : Memory w) :
    agreesOutside lo (lo+size) (fillSegment lo size f m) m := by
  intro a outside
  have miss : ¬(lo≤a ∧ a<lo+size) := by rcases outside with l|r <;> omega
  simp [fillSegment,miss]

omit [AddCommGroup H] in
theorem Old.slice (old : Old S P b p cell prior m) (s : Fresh x p cell.val) (pub : Fin 1→Word w)
    (dim : S.degree<2^w ∧ 2^S.colors<2^w ∧ 2^t<2^w) (eight : 8<2^w) :
    let pass:=(splitSpan S).install cell
    let out:=(pass.execute cell pub m).2
    pass.fits cell pub m ∧ agreesOutside p.split (p.split+8*(C).rows) out m ∧
      Sliced S P b p cell prior out := by
  let word:=fun u : ((Bool × Fin 4) × (B × Fin S.degree))=>
    (StoredColumns.digit S.colors S.degree t u.1.2.val (m (SlotImage.cell C b u.2 u.1.1 2)).val:Word w)
  let file:=PostImage.file (splitNumbers b S.degree) word p.split
  let res:=fillSegment p.split (8*(C).rows) file m
  have lo:=s.demandEnd
  have s1:=s.splitEnd
  have s2:=s.colorEnd
  have s3:=s.offsetEnd
  have high:=s.high
  have rows : (C).rows = (x).oldEdges := rfl
  have rowCount : (C).rows = N*S.degree := rfl
  have endFits : p.split+8*(C).rows<2^w := by have :=cell.isLt;omega
  have splitStart : (headerRead m cell splitShifts).val=p.split := by
    change (headerRead m cell (16 : Fin 34).val).val = p.split
    rw [old.header.native (16:Fin 34)]
    change (p.split : Word w).val = p.split
    exact Fin.val_cast_of_lt (by omega)
  have len : (headerRead m cell splitWords).val=8*(C).rows := by
    change (headerRead m cell (17 : Fin 34).val).val = 8*(C).rows
    rw [old.header.native (17:Fin 34)]
    change ((8*(C).rows : ℕ) : Word w).val = 8*(C).rows
    exact Fin.val_cast_of_lt (by omega)
  have material : (((splitSpan S).install cell).execute cell pub m).2=res := by
    apply FileSpec.image
    apply PostImage.file_spec cell pub (splitRow Template.o Template.ptr (.reg 0) S.colors S.degree)
      splitShifts splitWords m p.split (splitNumbers b S.degree) word endFits splitStart len
    rintro ⟨⟨rev,j⟩,v⟩ alt fields
    have hold := old.frame s (smallerFrame s (by omega) (by omega) fields)
    have raw : alt (SlotImage.cell C b v rev 2)=m (SlotImage.cell C b v rev 2) := by
      apply fields _ (.inl ?_)
      exact ((SlotImage.cell_range old.stored v rev 2).2.trans_le s.oldGraph).trans_le (by omega)
    have address : p.split + (splitNumbers b S.degree ((rev,j),v)).val =
        p.split + (C).rows*((if rev then 4 else 0)+j.val) + SlotImage.ordinal b v := by
      rw [splitNumbers_val, rowCount, Nat.add_assoc]
    change (Template.emit cell (splitRow Template.o Template.ptr (.reg 0) S.colors S.degree)).eval
        pub alt (fun _ => ((p.split+(splitNumbers b S.degree ((rev,j),v)).val : ℕ) : Word w)) =
      (StoredColumns.digit S.colors S.degree t j.val (m (SlotImage.cell C b v rev 2)).val : Word w)
    rw [address, ←raw]
    exact hold.splitStep pub v rev j endFits dim eight
  change _ ∧ _
  rw [material]
  have frame : agreesOutside p.split (p.split+8*(C).rows) res m := fill_frame file m
  refine ⟨?_,frame,old.frame s (smallerFrame s (by omega) (by omega) frame),endFits.le,?_⟩
  · change (headerRead m cell splitShifts).val + (headerRead m cell splitWords).val<2^w
    rwa [splitStart,len]
  · intro u rev j
    let k:=((rev,j),u)
    have pos : (splitNumbers b S.degree k).val < 8*(C).rows := (splitNumbers b S.degree k).isLt
    have ix : p.split+(C).rows*((if rev then 4 else 0)+j.val)+SlotImage.ordinal b u =
        p.split+(splitNumbers b S.degree k).val := by rw [splitNumbers_val, rowCount, Nat.add_assoc]
    rw [ix]
    have raw:=((SlotImage.cell_range old.stored u rev 2).2.trans_le s.oldGraph).trans_le (by omega : p.demands≤p.split)
    have digit_le (v : ℕ) : StoredColumns.digit S.colors S.degree t j.val v≤v := by
      unfold StoredColumns.digit
      split_ifs
      · exact Nat.mod_le _ _
      · exact (Nat.mod_le ..).trans (Nat.div_le_self ..)
      · exact (Nat.mod_le ..).trans ((Nat.div_le_self ..).trans (Nat.div_le_self ..))
      · exact (Nat.div_le_self ..).trans ((Nat.div_le_self ..).trans (Nat.div_le_self ..))
    have digitFits:= (digit_le (m (SlotImage.cell C b u rev 2)).val).trans_lt (m _).isLt
    change (fillSegment _ _ file m _).val=_
    rw [show fillSegment p.split (8*(C).rows) file m (p.split+(splitNumbers b S.degree k).val)=word k by
      simp [file,fillSegment,pos],frame _ (.inl raw)]
    exact Fin.val_cast_of_lt digitFits


end ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkStage.Resident

end OAI
