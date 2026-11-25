import OAI.ThreeFlat.Diagonal.CompressorCandidatePayload
import OAI.ThreeFlat.Diagonal.CompressorSelectedSlot

namespace OAI
/-! # Support and payload of the complete bounded shrink-candidate traversal -/
namespace ThreeFlat.Diagonal.CompressorPacking.Native.Graph
open Computability.VPVNP.Compression Computability.VPVNP.BurstRAM Computability.VPVNP.BurstRAM.PrivateRAM Placement
open scoped Classical Fin.NatCast
variable {B H : Type*} [AddCommGroup H] [Fintype B] [Fintype H] {w t l : ℕ}
variable (S : Stage) (P : PackingData B H (BitWord t) (BitWord l) S.degree S.colors)
variable (E : Codec B w S.colors t l) (G : ArcColumns (Word w)) (m : Memory w)
variable (R : ArcReads P E G m) (code : B ↪ ℕ) (hc : ∀ b, E.base b=(code b:Word w))
variable (hi : Function.Injective E.base) (bound : ∀i,S.pieces i≤S.pieceRadix)
variable (fit : ∀e,edgeId S P code bound e<2^w)

def visitWord (lay rev : Bool) (v : B × BitWord t) (q : Local.EdgeIndex S.degree S.colors S.pieces) :
    Candidate (Word w) :=
  let ix := q.2.1
  candidateWith (words m) G (rowRadices (w:=w) (t:=t) (l:=l) S) S lay rev ix.1.1 ix.2.1
    (siteCode E (v.1,v.2,(0:BitWord l))) q.1 q.2.2 ix.1.2.1 (tagOrdinal S.colors ix.1.2.2) ix.2.2

def visitWords (lay rev : Bool) (v : B × BitWord t) : List (Candidate (Word w)) :=
  (Local.visits S.degree S.colors S.pieces).map (visitWord S E G m lay rev v)

include R hc hi
omit [Fintype B] [Fintype H] in
theorem visitKey (one : (1:Word w)≠0) (lay rev : Bool) (v : B × BitWord t)
    (q : Local.EdgeIndex S.degree S.colors S.pieces) :
    (visitWord S E G m lay rev v q).key =
      refKey P lay (baseRole lay rev) S.pieces (idEmbedding S P code bound fit) v q := by
  rcases q with ⟨k,⟨⟨thin,h,u⟩,inc,i⟩,j⟩
  simpa only [visitWord,Equiv.symm_apply_apply] using
    candidate_match S P E G m R code hc hi bound fit one lay rev thin inc v k j h (tagOrdinal S.colors u) i

omit R hc hi [Fintype B] [Fintype H] in
private theorem key_ne (q : ShrinkEdge P S.pieces) : idEmbedding S P code bound fit q≠0 := by
  intro h
  have := congrArg Fin.val h
  change 1+_ = 0 at this
  omega

theorem visitSupport (one : (1:Word w)≠0) (lay rev : Bool) (v : B × BitWord t) :
    Rank.eligible ((visitWords S E G m lay rev v).map Candidate.key) =
      (CompressorRegularize.incident (fun q => base (slotSite P lay (baseRole lay rev) q)) v).map
        (idEmbedding S P code bound fit) := by
  let key := idEmbedding S P code bound fit
  have fields : Candidate.key ∘ visitWord S E G m lay rev v =
      refKey P lay (baseRole lay rev) S.pieces key v := by
    funext q
    exact visitKey S P E G m R code hc hi bound fit one lay rev v q
  rw [visitWords, List.map_map, fields]
  have support := refKey_support P lay (baseRole lay rev) S.pieces key
    (key_ne S P code bound fit) v
  ext value
  simpa only [Finset.mem_map, CompressorRegularize.incident, Finset.mem_filter,
    Finset.mem_univ, true_and] using (Finset.ext_iff.mp support value)

omit [Fintype B] [Fintype H] in
theorem visitPayload (one : (1:Word w)≠0) (lay rev : Bool) (v : B × BitWord t)
    (a : Candidate (Word w)) (ha : a∈visitWords S E G m lay rev v) (e : ShrinkEdge P S.pieces)
    (id : a.key=idEmbedding S P code bound fit e) :
    a.otherBase=baseAddress S E (base (otherSite S P lay rev e)) ∧ a.shift=tagWord E.lanes (wireShift S P lay e) := by
  obtain ⟨q,_,rfl⟩ := List.mem_map.mp ha
  rw [visitKey S P E G m R code hc hi bound fit one] at id
  let order := idEmbedding S P code bound fit
  obtain ⟨e',hit,_,same⟩ := (refKey_ne_zero P lay (baseRole lay rev) S.pieces order (key_ne S P code bound fit)
    v q (order e)).1 ⟨id,key_ne S P code bound fit e⟩
  have eq : e'=e := order.injective same
  subst e'
  rcases q with ⟨k,⟨⟨thin,h,u⟩,inc,i⟩,j⟩
  have result := candidate_payload S P E G m R lay rev thin inc v k j h (tagOrdinal S.colors u) i e
    (by simpa only [Equiv.symm_apply_apply] using hit)
  exact result


end ThreeFlat.Diagonal.CompressorPacking.Native.Graph

end OAI
