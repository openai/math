import OAI.Hierarchy.DescentSortedRoster
import OAI.Hierarchy.DescentNativeBankLookup
import OAI.Hierarchy.ProtocolRAMGeneratedWrite

namespace OAI
/-! # Issuing the physically sorted old aperture at the new shared neighbor table -/
namespace Hierarchy.DescentSortedRoster
open DescentSIMDLookup DescentPackedColony DescentFallbackRankRAM DescentIssuedTerminalId
open ThreeFlat.RAM Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {D H w G M : ℕ}

structure Chart where
  raw : Bank
  origin : Bank
  slot : Bank

def get (C : Chart) (j : Fin D) :=
  Expr.lookup C.raw (.op .add (.lookup C.origin .row) (.lit j.val))
def code (C : Chart) (D H : ℕ) :=
  pick (fun j : Fin D=>get C j) (.lookup C.slot .row) H (List.finRange D)

variable (C : Chart) (peer : Fin H→Fin D→Option (Fin H)) (m : Memory w)

structure Raw where
  origin : ∀v : Fin H,∀j : Fin D,m (C.origin.base+(v.val*D+j.val))=((v.val*D:ℕ):Word w)
  slot : ∀v : Fin H,∀j : Fin D,m (C.slot.base+(v.val*D+j.val))=(j.val:Word w)
  rows : ∀v : Fin H,∀j : Fin D,m (C.raw.base+(v.val*D+j.val))=(target (peer v j):Word w)

structure Room (C : Chart) (D H w out : ℕ) : Prop where
  read : ∀b∈[C.raw,C.origin,C.slot], b.Fits w out ∧ H*D≤b.size
  h : H<2^w
  d : D<2^w
  endFit : out+H*D<2^w

theorem built_fits (out : ℕ) (fit : Room C D H w out) : (code C D H).Fits w out := by
  have src j : (get C (j : Fin D)).Fits w out :=
    ⟨(fit.read C.raw (by simp)).1,⟨⟨(fit.read C.origin (by simp)).1,trivial⟩,trivial⟩⟩
  have guard (j : Fin D) (e : Expr) (ef : e.Fits w out) (xs : List (Fin D)) :
      (unlessSeen (get C j) e (xs.map (get C))).Fits w out := by
    induction xs with
    | nil=>exact ef
    | cons a as ih=>exact ⟨src a,src j,trivial,ih⟩
  have rb (j i : Fin D) : (rankBit (get C) (get C j) i).Fits w out :=
    guard i (.branch .lt (get C i) (get C j) (.lit 1) (.lit 0))
      ⟨src i,src j,trivial,trivial⟩ (DescentFallbackRankRAM.prior i)
  have total (j : Fin D) (xs : List (Fin D)) :
      (foldSum (xs.map (rankBit (get C) (get C j)))).Fits w out := by
    induction xs with
    | nil=>trivial
    | cons q qs ih=>exact ⟨rb j q,ih⟩
  have ctl : (Expr.lookup C.slot .row).Fits w out:=⟨(fit.read C.slot (by simp)).1,trivial⟩
  have build (xs : List (Fin D)) :
      (pick (get C) (.lookup C.slot .row) H xs).Fits w out := by
    induction xs with
    | nil=>trivial
    | cons j js ih=>exact ⟨⟨src j,trivial,
        ⟨total j (Finset.univ : Finset (Fin D)).toList,ctl,trivial,trivial⟩,trivial⟩,trivial,src j,ih⟩
  exact build (List.finRange D)

theorem issued (out : ℕ) (fit : Room C D H w out) (mounted : Raw C peer m) :
    let dst:=image out (H*D) (code C D H) m
    (scan w out (H*D) (code C D H)).Exec m dst (4+(H*D)*(2*(code C D H).work+4)) ∧
      (∀v : Fin H,∀i : Fin D,dst (out+(v.val*D+i.val))=(target (indexed peer v i):Word w)) ∧
      ∀a<out,dst a=m a := by
  refine ⟨@scan_exec w out (H*D) (code C D H) m (built_fits C out fit) fit.endFit,?_,
    fun a ha=>ProtocolRAMGeneratedWrite.frame_image out (H*D) (code C D H) m a (.inl ha)⟩
  intro v i
  have atRow (t : Fin D) : v.val*D+t.val<H*D :=
    (Nat.add_lt_add_left t.isLt _).trans_le (by rw [←Nat.succ_mul];exact Nat.mul_le_mul_right _ v.isLt)
  let q : Fin (H*D):=⟨_,atRow i⟩
  let x : Word w:=(q.val:Word w)
  have nd (b) (member : b∈[C.raw,C.origin,C.slot]) : b.size<2^w := (fit.read b member).1.2.1
  have rowAt : (Expr.row.eval m x)=((v.val*D+i.val:ℕ):Word w):=rfl
  have orig:=(lookup_nat C.origin m x .row (v.val*D+i.val) rowAt ((atRow i).trans_le (fit.read C.origin (by simp)).2)
    (nd C.origin (by simp))).trans (mounted.origin v i)
  have sl:=(lookup_nat C.slot m x .row (v.val*D+i.val) rowAt ((atRow i).trans_le (fit.read C.slot (by simp)).2)
    (nd C.slot (by simp))).trans (mounted.slot v i)
  have src (j : Fin D) : (get C j).eval m x=(target (peer v j):Word w) := by
    have ix : (Expr.op .add (.lookup C.origin .row) (.lit j.val)).eval m x=((v.val*D+j.val:ℕ):Word w) := by
      change (Expr.lookup C.origin .row).eval m x+(j.val:Word w)=_
      rw [orig,Nat.cast_add]
    exact (lookup_nat C.raw m x _ (v.val*D+j.val) ix ((atRow j).trans_le (fit.read C.raw (by simp)).2)
      (nd C.raw (by simp))).trans (mounted.rows v j)
  apply (ProtocolRAMGeneratedWrite.read_image out (H*D) (code C D H) m q).trans
  exact pick_read peer m x (get C) v fit.h fit.d src (.lookup C.slot .row) i
    (by rw [sl,Fin.val_cast_of_lt (i.isLt.trans fit.d)])

theorem ports (P : Ports D) (out : Bank) (fit : Room C D H w out.base) (raw : Raw C peer m)
    (oldPorts : Mounted P peer m G M) (left : ∀j,(P.ids j).base+H*chunks G M≤out.base)
    (off : P.offsets.base+H≤out.base) (ch : P.chunks.base+H*chunks G M≤out.base) :
    Mounted {P with roster:=out} (indexed peer) (image out.base (H*D) (code C D H) m) G M := by
  obtain ⟨_,board,prior⟩:=issued C peer m out.base fit raw
  refine ⟨fun p j=>?_,board,fun v=>?_,fun p=>?_⟩
  · rw [prior _ ((Nat.add_lt_add_left (row H G M p).isLt _).trans_le (left j))]
    exact oldPorts.ids p j
  · rw [prior _ ((Nat.add_lt_add_left v.isLt _).trans_le off)]
    exact oldPorts.offsets v
  · rw [prior _ ((Nat.add_lt_add_left (row H G M p).isLt _).trans_le ch)]
    exact oldPorts.chunks p

end
end Hierarchy.DescentSortedRoster

end OAI
