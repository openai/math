import OAI.ThreeFlat.Diagonal.CompressorCandidateCode

namespace OAI
/-! # Identification of the native slot list with the local incidence enumeration -/
namespace ThreeFlat.Diagonal.CompressorPacking.Native.Graph
open Computability.VPVNP.Compression Computability.VPVNP.BurstRAM Computability.VPVNP.BurstRAM.PrivateRAM Placement
open scoped Classical Fin.NatCast
variable {B H : Type*} [AddCommGroup H] {w t l : ℕ}
variable (S : Stage) (P : PackingData B H (BitWord t) (BitWord l) S.degree S.colors)
variable (E : Codec B w S.colors t l) (G : ArcColumns (Word w)) (m : Memory w)
variable (R : ArcReads P E G m)
variable (code : B ↪ ℕ) (hc : ∀ b, E.base b = (code b : Word w))
variable (hi : Function.Injective E.base) (bound : ∀ i, S.pieces i≤S.pieceRadix)
variable (fit : ∀ e, edgeId S P code bound e<2^w)

private theorem tag_eq {a b : BitWord t} (ft : t≤w) :
    tagWord ft a=tagWord ft b ↔ a=b := by
  constructor
  · intro h
    exact (tagOrdinal t).injective (Fin.ext (congrArg (fun x : Word w => x.val) h))
  · rintro rfl
    rfl

include hi in
private theorem guarded (o : Ops (Word w)) (v : B × BitWord t)
    (a : Computability.VPVNP.Compression.Site B (BitWord t) (BitWord l)) (key : Word w)
    (h : o=words m) :
    o.choose (siteCode E a).base (siteCode E (v.1,v.2,(0 : BitWord l))).base
      (o.choose (siteCode E a).tag (siteCode E (v.1,v.2,(0 : BitWord l))).tag key 0) 0 =
      if base a=v then key else 0 := by
  subst o
  rcases a with ⟨b,z,g⟩
  rcases v with ⟨v,q⟩
  by_cases hb : b=v <;> by_cases ht : z=q <;>
    simp [base,words,siteCode,Prod.ext_iff,hi.eq_iff,tag_eq,hb,ht]

include R hi hc
theorem candidate_match (nw : (1 : Word w)≠0) (lay rev thin inc : Bool)
    (v : B × BitWord t) (k : Fin 4) (j : Fin (S.pieces k)) (h : Fin S.degree)
    (u : Fin (2^S.colors)) (i : Fin S.degree) :
    (candidateWith (words m) G (rowRadices (w:=w) (t:=t) (l:=l) S) S lay rev thin inc
      (siteCode E (v.1,v.2,(0 : BitWord l))) k j h u i).key =
    refKey P lay (baseRole lay rev) S.pieces (idEmbedding S P code bound fit) v
      ⟨k,((thin,h,(tagOrdinal S.colors).symm u),inc,i),j⟩ := by
  let q := (tagOrdinal S.colors).symm u
  let s : Computability.VPVNP.Compression.Site B (BitWord t) (BitWord l) := (v.1,v.2,0)
  let r := baseRole lay rev k
  let dir := Local.roleLayout lay r
  let a := Local.incidentArc P dir s ((thin,h,q),inc,i)
  have low : (u.val : Word w) = tagWord E.colors q := by
    apply Fin.ext
    rw [Fin.val_natCast,Nat.mod_eq_of_lt (u.isLt.trans_le (Nat.pow_le_pow_right (by decide) E.colors))]
    exact (congrArg Fin.val ((tagOrdinal S.colors).apply_symm_apply u)).symm
  unfold candidateWith
  simp only [roleIndex,roleOwner]
  have arc : fromChild (words m) G S.degree dir thin inc (siteCode E s)
      ((words m).lit h.val) ((words m).lit u.val) ((words m).lit i.val) = encodeEnds P E a := by
    rw [show (words m).lit u.val=tagWord E.colors q from low]
    exact local_arc R dir thin inc s h i q
  rw [arc]
  by_cases bad : P.thick (sourcePosition a) ∧ P.thick (sourcePosition (P.actual a))
  · have invalid := invalid_role S P E G m R lay a bad.1 bad.2
    have miss : Local.slotCandidate P lay (baseRole lay rev) S.pieces v
        ⟨k,((thin,h,q),inc,i),j⟩ = none := by
      have no : Local.lookup P dir s ((thin,h,q),inc,i)=none := by
        change (if h : ¬(P.thick (sourcePosition a) ∧ P.thick (sourcePosition (P.actual a))) then
          some (⟨a,h⟩ : P.Motif) else none) = none
        simp [bad]
      change (((Local.lookup P dir s ((thin,h,q),inc,i)).map (normalize P)).map _) = none
      rw [no]
      rfl
    rw [refKey,miss]
    change (words m).choose (roleSites (words m) G S.degree lay (encodeEnds P E a)).valid 1 _ 0 = _
    rw [invalid]
    simp [words,nw.symm]
  · let z : P.Motif := ⟨a,bad⟩
    let e : ShrinkEdge P S.pieces := ⟨k,normalize P z,j⟩
    have hit : Local.slotCandidate P lay (baseRole lay rev) S.pieces v
        ⟨k,((thin,h,q),inc,i),j⟩ = some e := by
      change (((Local.lookup P dir s ((thin,h,q),inc,i)).map (normalize P)).map _) = some e
      rw [Local.lookup_eq P dir s ((thin,h,q),inc,i) z rfl]
      rfl
    rw [refKey,hit]
    have key := encode_identifier S P E code bound hc m z k j
    dsimp only at key
    let slots := roleSites (words m) G S.degree lay (encodeEnds P E z.val)
    have valid : slots.valid = 1 := congrArg RoleSites.valid (roles_code R lay z)
    have here : siteAt slots (roleNumber r) = siteCode E (siteOf P lay r z) :=
      actualRole S P E G m R lay z r
    have one (x : Word w) : (words m).choose 1 1 x 0 = x := by simp [words]
    change (words m).choose slots.valid 1
      ((words m).choose (siteAt slots (roleNumber r)).base (siteCode E s).base
        ((words m).choose (siteAt slots (roleNumber r)).tag (siteCode E s).tag _ 0) 0) 0 = _
    rw [valid,one,here,key,guarded S E m hi (words m) v (siteOf P lay r z) _ rfl]
    have sameSite : base (slotSite P lay (baseRole lay rev) e) = base (siteOf P lay r z) :=
      normalize_base S P lay r z
    by_cases atSite : base (siteOf P lay r z) = v
    · have chosen : base (slotSite P lay (baseRole lay rev) e) = v := sameSite.trans atSite
      simp only [ite_eq_left atSite, ite_eq_left chosen]
      exact Fin.ext (Nat.mod_eq_of_lt (fit e))
    · have absent : base (slotSite P lay (baseRole lay rev) e) ≠ v := fun h => atSite (sameSite.symm.trans h)
      simp only [ite_eq_right atSite, ite_eq_right absent]

end ThreeFlat.Diagonal.CompressorPacking.Native.Graph

end OAI
