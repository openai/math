import OAI.ThreeFlat.Diagonal.CompressorCandidateList
import OAI.ThreeFlat.Diagonal.CompressorArcBridge
import OAI.ThreeFlat.Diagonal.CompressorEdgeKey

namespace OAI
/-! # Native mixed-radix keys on normalized old motifs -/
namespace ThreeFlat.Diagonal.CompressorPacking.Native.Graph
open Computability.VPVNP.Compression Computability.VPVNP.BurstRAM Computability.VPVNP.BurstRAM.PrivateRAM Placement
open scoped Classical Fin.NatCast Fin.CommRing
variable {B H : Type*} [AddCommGroup H] {w t l : ℕ}
variable (S : Stage) (P : PackingData B H (BitWord t) (BitWord l) S.degree S.colors)
variable (E : Codec B w S.colors t l)
variable (code : B ↪ ℕ) (bound : ∀ i, S.pieces i ≤ S.pieceRadix)

def baseRole (lay rev : Bool) (i : Fin 4) : Role :=
  if rev then (supplyRoles lay i).2 else (supplyRoles lay i).1

def roleNumber : Role → Fin 3 | .a => 0 | .b => 1 | .d => 2

theorem roleIndex (lay rev : Bool) (i : Fin 4) :
    (if rev then (roles lay i).2 else (roles lay i).1) = roleNumber (baseRole lay rev i) := by
  cases lay <;> cases rev <;> fin_cases i <;> rfl

theorem roleOwner (lay : Bool) (z : Role) : ownerLayout lay (roleNumber z)=Local.roleLayout lay z := by
  cases z <;> rfl

def edgeId (e : ShrinkEdge P S.pieces) : ℕ :=
  1+edgeKey P code (tagOrdinal t).toEmbedding S.pieces S.pieceRadix bound e

def idEmbedding (fit : ∀ e, edgeId S P code bound e<2^w) : ShrinkEdge P S.pieces ↪ Word w where
  toFun e := ⟨_,fit e⟩
  inj' := by
    intro a b eq
    have h := congrArg Fin.val eq
    change 1+_ = 1+_ at h
    exact (edgeOrder P code (tagOrdinal t).toEmbedding S.pieces S.pieceRadix bound).injective
      (Nat.add_left_cancel h)

def rowRadices : Radices (Word w) := ⟨((2^t : ℕ):Word w),((2^l : ℕ):Word w),((2^S.colors : ℕ):Word w),S.degree⟩

private theorem tag_as_cast {c : ℕ} (fit : c≤w) (x : BitWord c) :
    tagWord fit x = ((tagOrdinal c x).val : Word w) :=
  Fin.ext (Nat.mod_eq_of_lt (tagWord fit x).isLt).symm

/-- Deleting the remaining lane by rooting a motif leaves precisely the
digits read by the slot-key formula. -/
theorem encode_identifier (hc : ∀ b, E.base b = (code b : Word w))
    (m : Memory w) (a : P.Motif) (k : Fin 4) (j : Fin (S.pieces k)) :
    let o := words m
    let r := rowRadices (w:=w) (t:=t) (l:=l) S
    let e := encodeEnds P E a.val
    let old := appendDigit o (encodeBase o r e.source.site) (o.lit S.degree) e.originalSlot
    let raw := appendDigit o (appendDigit o old r.colors e.source.bits) (o.lit S.degree) e.source.slot
    o.bin .add (o.lit 1) (appendDigit o (appendDigit o raw (o.lit 4) (o.lit k.val))
      (o.lit S.pieceRadix) (o.lit j.val)) =
      (edgeId S P code bound ⟨k,normalize P a,j⟩ : Word w) := by
  simp [encodeEnds,posCode,siteCode,sourcePosition,encodeBase,rowRadices,appendDigit,words,
    BinaryOp.eval,edgeId,edgeKey,rootKey,appendKey,normalize,moveMotif,moveArc,moveSlot,moveSite,
    hc,tag_as_cast,tagOrdinal,Nat.cast_add,Nat.cast_mul]
  first
  | with_unfolding_all rfl

theorem actualRole (G : ArcColumns (Word w)) (m : Memory w) (R : ArcReads P E G m)
    (lay : Bool) (a : P.Motif) (r : Role) :
    siteAt (roleSites (words m) G S.degree lay (encodeEnds P E a.val)) (roleNumber r) =
      siteCode E (siteOf P lay r a) := by
  rw [roles_code R]
  cases r <;> rfl

theorem invalid_role (G : ArcColumns (Word w)) (m : Memory w) (R : ArcReads P E G m)
    (lay : Bool) (a : Arc B H (BitWord t) (BitWord l) S.degree S.colors)
    (hs : P.thick (sourcePosition a)) (ht : P.thick (sourcePosition (P.actual a))) :
    (roleSites (words m) G S.degree lay (encodeEnds P E a)).valid = 0 := by
  have hs' := (thick_bit R.toGraphReads (sourcePosition a)).2 hs
  have ht' := (thick_bit R.toGraphReads (sourcePosition (P.actual a))).2 ht
  change (if thickBit (words m) G.toColumns (posCode P E (sourcePosition a))=1 then
    if thickBit (words m) G.toColumns (posCode P E (sourcePosition (P.actual a)))=1 then 0 else 1 else 1) = _
  simp only [hs',ht',ite_true]

theorem normalize_base (lay : Bool) (r : Role) (a : P.Motif) :
    base (siteOf P lay r (normalize P a).val) = base (siteOf P lay r a) := by
  change base (siteOf P lay r (moveMotif P _ a)) = _
  rw [moves_of_role]
  rfl


end ThreeFlat.Diagonal.CompressorPacking.Native.Graph

end OAI
