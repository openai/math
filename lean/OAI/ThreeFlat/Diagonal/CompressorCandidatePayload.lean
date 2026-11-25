import OAI.ThreeFlat.Diagonal.CompressorCandidateMatch
import OAI.ThreeFlat.Diagonal.CompressorLaneSplit

namespace OAI
/-! # The neighbor and XOR shift carried by each candidate with a nonzero key -/
namespace ThreeFlat.Diagonal.CompressorPacking.Native.Graph
open Computability.VPVNP.Compression Computability.VPVNP.BurstRAM Computability.VPVNP.BurstRAM.PrivateRAM Placement
open scoped Classical Fin.NatCast
variable {B H : Type*} [AddCommGroup H] {w t l : ℕ}
variable (S : Stage) (P : PackingData B H (BitWord t) (BitWord l) S.degree S.colors)
variable (E : Codec B w S.colors t l) (G : ArcColumns (Word w)) (m : Memory w)
variable (R : ArcReads P E G m)
variable (code : B ↪ ℕ) (bound : ∀ i, S.pieces i≤S.pieceRadix)
variable (fit : ∀ e, edgeId S P code bound e<2^w)

noncomputable def sortedKey :
    letI : LinearOrder (ShrinkEdge P S.pieces) := LinearOrder.lift' _
      (edgeOrder P code (tagOrdinal t).toEmbedding S.pieces S.pieceRadix bound).injective
    ShrinkEdge P S.pieces ↪o Word w := by
  letI : LinearOrder (ShrinkEdge P S.pieces) := LinearOrder.lift' _
    (edgeOrder P code (tagOrdinal t).toEmbedding S.pieces S.pieceRadix bound).injective
  exact { toEmbedding := idEmbedding S P code bound fit,
          map_rel_iff' := by
            intro a b
            let key := edgeKey P code (tagOrdinal t).toEmbedding S.pieces S.pieceRadix bound
            change 1 + key a ≤ 1 + key b ↔ key a ≤ key b
            omega }

def baseAddress (b : B × BitWord t) : Word w :=
  (E.base b.1)*((2^t:ℕ):Word w)+tagWord E.tags b.2

def otherSite (lay rev : Bool) (q : ShrinkEdge P S.pieces) :=
  slotSite P lay (baseRole lay (!rev)) q

def wireShift (lay : Bool) (q : ShrinkEdge P S.pieces) : BitWord l :=
  (slotSite P lay (baseRole lay true) q).2.2 - (slotSite P lay (baseRole lay false) q).2.2

private theorem other_role (lay rev : Bool) (k : Fin 4) :
    (if rev then (roles lay k).1 else (roles lay k).2) = roleNumber (baseRole lay (!rev) k) := by
  cases lay <;> cases rev <;> fin_cases k <;> rfl

private theorem root_diff (lay rev : Bool) (k : Fin 4) (z : P.Motif) (j : Fin (S.pieces k)) :
    (siteOf P lay (baseRole lay rev k) z).2.2 - (siteOf P lay (baseRole lay (!rev) k) z).2.2 =
      wireShift S P lay ⟨k,normalize P z,j⟩ := by
  unfold wireShift slotSite
  simp only [normalize,moves_of_role,moveSite,add_sub_add_right_eq_sub]
  cases rev <;> simp [sub_eq_add_neg,binary_neg,add_comm]

include R
theorem candidate_payload (lay rev thin inc : Bool)
    (v : B × BitWord t) (k : Fin 4) (j : Fin (S.pieces k)) (h : Fin S.degree)
    (u : Fin (2^S.colors)) (i : Fin S.degree)
    (e : ShrinkEdge P S.pieces)
    (hit : Local.slotCandidate P lay (baseRole lay rev) S.pieces v
      ⟨k,((thin,h,(tagOrdinal S.colors).symm u),inc,i),j⟩=some e) :
    let z := candidateWith (words m) G (rowRadices (w:=w) (t:=t) (l:=l) S) S lay rev thin inc
      (siteCode E (v.1,v.2,(0:BitWord l))) k j h u i
    z.otherBase=baseAddress S E (base (otherSite S P lay rev e)) ∧ z.shift=tagWord E.lanes (wireShift S P lay e) := by
  let f := baseRole lay rev k
  let s := (v.1,v.2,(0:BitWord l))
  let dir := Local.roleLayout lay f
  let bits := (tagOrdinal S.colors).symm u
  let a := Local.incidentArc P dir s ((thin,h,bits),inc,i)
  have low : ((words m).lit u.val)=tagWord E.colors bits := by
    apply Fin.ext
    change u.val%2^w=(tagOrdinal S.colors bits).val
    rw [Nat.mod_eq_of_lt (u.isLt.trans_le (Nat.pow_le_pow_right (by decide) E.colors)),Equiv.apply_symm_apply]
  have arc : fromChild (words m) G S.degree dir thin inc (siteCode E s)
      ((words m).lit h.val) ((words m).lit u.val) ((words m).lit i.val) = encodeEnds P E a := by
    rw [low]
    exact local_arc R dir thin inc s h i bits
  change (((if ok : ¬(P.thick (sourcePosition a) ∧ P.thick (sourcePosition (P.actual a))) then
      some (⟨a,ok⟩ : P.Motif) else none).map (normalize P)).map _) = some e at hit
  split at hit <;> rename_i ok
  · let z : P.Motif := ⟨a,ok⟩
    have eq : (⟨k,normalize P z,j⟩ : ShrinkEdge P S.pieces)=e := Option.some.inj hit
    subst e
    have atOld := actualRole S P E G m R lay z f
    have other := actualRole S P E G m R lay z (baseRole lay (!rev) k)
    have packed (x : Computability.VPVNP.Compression.Site B (BitWord t) (BitWord l)) :
        encodeBase (words m) (rowRadices (w:=w) (t:=t) (l:=l) S) (siteCode E x) =
          baseAddress S E (base x) := rfl
    simp only [candidateWith,roleIndex,other_role,roleOwner,encodeCandidate]
    rw [arc,other,atOld,packed]
    constructor
    · change baseAddress S E (base (siteOf P lay (baseRole lay (!rev) k) z)) =
        baseAddress S E (base (siteOf P lay (baseRole lay (!rev) k) (normalize P z).val))
      rw [normalize_base S P]
    · change BinaryOp.bitXor.eval (tagWord E.lanes (siteOf P lay f z).2.2)
        (tagWord E.lanes (siteOf P lay (baseRole lay (!rev) k) z).2.2) = _
      rw [←tagWord_sub,root_diff S P lay rev k z j]
  · simp at hit


end ThreeFlat.Diagonal.CompressorPacking.Native.Graph

end OAI
