import OAI.Hierarchy.DescentResetPrivateDonors
import OAI.Hierarchy.DescentResetLocalNodes

namespace OAI
/-! # Every actual primary-reset operand slot comes from its original donor -/
set_option quotPrecheck false

namespace Hierarchy.DescentBundleHistory
open DescentKernelHistory DescentLocalPrivateNames DescentOrderedWords DescentNamedContact DescentRouterBank Computability.BorderVNP.Crossing
open scoped Classical BigOperators
noncomputable section
variable {p:ℕ} (hp:0<p)
section
variable {n d L : ℕ} {P H Q X Y : Type} [Fintype H] [Fintype Q] {bs : P→ℕ}
variable (N : Network n P bs) (home : N.Site→H) (group : Bool→N.Edge→Q)
variable (R : Network d (Bool×Q) (publicWidth group N.width)) (key : N.Edge↪Fin L)
variable (whole : ∀e,p∣N.width e) (old : SiteBits (U:=X) N) (src : ∀v,Shape p (old v)) (h : H)
local notation "M" => DescentResetTrunks.network N home group R
local notation "rr" => oldGather N home group R key old h
local notation "sh" => oldGatherShape N home group R key whole old src h
local notation "result" => (inShape N home group R key whole old src h).recipe hp
local notation "bw" => boundaryWidth (M) (.inl (false,h))
local notation "noWidth" => (Empty.elim : Empty→ℕ)
local notation "rt" => (fun (_ : Fibre home h) (b : BitRef bw)=>(Sum.inl b : BitRef bw⊕BitRef noWidth))
local notation "maps" => (fun _ : Fibre home h=>({map:=id,read:=fun _ _=>rfl} : BlockMap p bw bw id).publicOnly)


local notation "originalNode" => DescentResetLocalNodes.gathered N home group R key old h

omit [Fintype Q] in
theorem retained_argument_count (i:Fibre home h) (u:(rr i).Node) :
    (result).arity ⟨i,u⟩=((src i.val).recipe hp).arity (originalNode i u) := by
  have joined : (result).arity ⟨i,u⟩=(((sh) i).recipe hp).arity u := by
    exact (congrArg List.length (combined_keys rr noWidth rt sh (fun z => nomatch z) maps i u)).trans
      (List.length_map ..)
  apply joined.trans
  rcases i with ⟨v,rfl⟩
  exact rerouteLen hp (src v) (oldBlockMap N home group R key whole v) u

/-- Both directions enumerate exactly the real slots, with the argument number
unchanged. Zero-arity nodes have no entries on either side. -/
def retainedSlots :
    Slot result ≃ (Σi:Fibre home h,Slot ((src i.val).recipe hp)) where
  toFun s:=⟨s.1.1,originalNode s.1.1 s.1.2,Fin.cast (retained_argument_count hp N home group R key whole old src h s.1.1 s.1.2) s.2⟩
  invFun s:=by
    rcases s with ⟨⟨v,rfl⟩,u,j⟩
    let donor:Fibre home (home v):=⟨v,rfl⟩
    exact ⟨⟨donor,u⟩,Fin.cast (retained_argument_count hp N home group R key whole old src (home v) donor u).symm j⟩
  left_inv := by rintro ⟨⟨⟨v,rfl⟩,u⟩,j⟩;rfl
  right_inv := by rintro ⟨⟨v,rfl⟩,u,j⟩;rfl

omit [Fintype Q] in
/-- The exact marked argument of the transferred node is the same hidden reference
as the source. Public operands stay public throughout this reset's inherited band. -/
theorem retained_slot_private (i:Fibre home h) (u:(rr i).Node)
    (j:Fin (((src i.val).recipe hp).arity (originalNode i u))) (target:(result).UsedWord) :
    let installed:=Fin.cast (retained_argument_count hp N home group R key whole old src h i u).symm j
    (result).operand ⟨i,u⟩ installed=.inr target.val ↔
      ∃t:((src i.val).recipe hp).UsedWord,
        ((src i.val).recipe hp).operand (originalNode i u) j=.inr t.val ∧ resetDonor hp N home group R key whole old src h target=⟨i,t⟩ := by
  let gathered := rr
  let shapes := sh
  let send := rt
  let relabel := maps
  let prepared := result
  rcases i with ⟨v,rfl⟩
  let donor:Fibre home (home v):=⟨v,rfl⟩
  let f:=oldBlockMap N home group R key whole v
  let first:=Fin.cast (rerouteLen hp (src v) f u).symm j
  have firstRead:=reroute_operand hp (src v) f u j
  have secondRead:=wordTransfer_read hp gathered noWidth send shapes (fun z => nomatch z) relabel donor u first
  dsimp only at secondRead ⊢
  change ((shapes donor).recipe hp).operand u first=_ at firstRead
  rw [firstRead] at secondRead
  cases seen:((src v).recipe hp).operand u j with
  | inl ext =>
    rw [seen] at secondRead
    constructor
    · intro hit
      exact (Sum.inl_ne_inr (secondRead.symm.trans hit)).elim
    · rintro ⟨t,hit,_⟩
      exact (Sum.inl_ne_inr (seen.symm.trans hit)).elim
  | inr name =>
    rw [seen] at secondRead
    let t:((src v).recipe hp).UsedWord:=⟨name,⟨u,j,seen⟩⟩
    have actual : prepared.operand ⟨donor,u⟩
        (Fin.cast (retained_argument_count hp N home group R key whole old src (home v) donor u).symm j)=
        .inr ((resetDonor hp N home group R key whole old src (home v)).symm ⟨donor,t⟩).val := secondRead
    constructor
    · intro hit
      have same : (resetDonor hp N home group R key whole old src (home v)).symm ⟨donor,t⟩=target :=
        Subtype.ext (Sum.inr.inj (actual.symm.trans hit))
      exact ⟨t,seen,by rw [←same,Equiv.apply_symm_apply]⟩
    · rintro ⟨t',hit,registered⟩
      have same:t=t':=Subtype.ext (Sum.inr.inj (seen.symm.trans hit))
      subst t'
      have delivered:target=(resetDonor hp N home group R key whole old src (home v)).symm ⟨donor,t⟩ :=
        (Equiv.eq_symm_apply _).2 registered
      simpa only [delivered] using actual

/-- The two-key SIMD lookup uses the actual donor address and the actual earlier
rectangular first occurrence, embedded in the physical prior-name word. -/
def retainedKey {D K bits:ℕ} (donor:Fibre home h↪Fin D)
    (prior:∀i:Fibre home h,Slot ((src i.val).recipe hp)↪Fin K) (fit:K≤2^bits) :
    (result).UsedWord↪Fin D×DescentSIMDLookup.Cell bits :=
  ((donorAlias hp N home group R key whole old src h donor prior).trans finProdFinEquiv.symm.toEmbedding).trans
    {toFun:=fun x=>(x.1,x.2.castLE fit),inj':=by
      rintro ⟨i,a⟩ ⟨j,b⟩ equal
      exact Prod.ext (congrArg (fun x : Fin D × Fin (2^bits) => x.1) equal) (Fin.ext (congrArg (fun x:Fin D×Fin (2^bits)=>x.2.val) equal))}

omit [Fintype Q] in
theorem retained_key_read {D K bits:ℕ} (donor:Fibre home h↪Fin D)
    (prior:∀i:Fibre home h,Slot ((src i.val).recipe hp)↪Fin K) (fit:K≤2^bits)
    (v:(result).UsedWord) (i:Fibre home h) (u:((src i.val).recipe hp).UsedWord)
    (came:resetDonor hp N home group R key whole old src h v=⟨i,u⟩) :
    retainedKey hp N home group R key whole old src h donor prior fit v=
      (donor i,(firstAlias _ (prior i) u).castLE fit) := by
  change (fun a:Fin D×Fin K=>(a.1,a.2.castLE fit))
    (finProdFinEquiv.symm (finProdFinEquiv
      (donor (resetDonor hp N home group R key whole old src h v).1,
        firstAlias _ (prior _) (resetDonor hp N home group R key whole old src h v).2)))=_
  rw [Equiv.symm_apply_apply,came]

omit [Fintype Q] in
/-- After identifying a genuine original private use there is no free terminal
key to supply. The addresses are the measured donor and its earlier occurrence. -/
theorem retained_key_at_slot {D K bits:ℕ} (donor:Fibre home h↪Fin D)
    (prior:∀i:Fibre home h,Slot ((src i.val).recipe hp)↪Fin K) (fit:K≤2^bits)
    (i:Fibre home h) (node:(rr i).Node) (j:Fin (((src i.val).recipe hp).arity (originalNode i node)))
    (v:(result).UsedWord) (used:(result).operand ⟨i,node⟩
      (Fin.cast (retained_argument_count hp N home group R key whole old src h i node).symm j)=.inr v.val) :
    ∃u:((src i.val).recipe hp).UsedWord,
      ((src i.val).recipe hp).operand (originalNode i node) j=.inr u.val ∧
      retainedKey hp N home group R key whole old src h donor prior fit v=(donor i,(firstAlias _ (prior i) u).castLE fit) := by
  obtain ⟨u,oldRead,source⟩ := (retained_slot_private hp N home group R key whole old src h i node j v).1 used
  exact ⟨u,oldRead,retained_key_read hp N home group R key whole old src h donor prior fit v i u source⟩

end
end
end Hierarchy.DescentBundleHistory

end OAI
