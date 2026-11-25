import OAI.Hierarchy.DescentCommonHostSize

namespace OAI
/-! # Recovery of the actual site from its common host name and surviving block -/

namespace Hierarchy.DescentChosenRouter
open DescentRelativeContacts DescentCanonicalPorts DescentContacts DescentGL
open scoped Classical
noncomputable section
variable {V I H A : Type} [Fintype V] [DecidableEq V] [Fintype I] [Fintype H] [Fintype A]
    {k n : ℕ} (P : Placement V I H A k (2^n)) (m : ℕ) (code : H ↪ V×Endpoint (2^n))
variable (low : ∀v,m≤P.b v) (legal : ∀t,m≤(code t).2.1.1 ∧ (code t).2.1.1≤k ∧
    (code t).2.1.2<2^(code t).2.1.1)

omit [Fintype V] [DecidableEq V] in
theorem coarse_lt (q : V×Endpoint (2^n)) (l : m≤q.2.1.1) (id : q.2.1.2<2^q.2.1.1) :
    coarseName m q<2^m := by
  change q.2.1.2/2^(q.2.1.1-m)<2^m
  apply (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).2
  rwa [←Nat.pow_add,Nat.add_sub_of_le l]

include low legal in
theorem siteGroup_lt (w : P.Site) : P.siteGroup m code w<2^m := by
  rcases w with g|t
  · exact coarse_lt (n:=n) m (goodAddress P.b P.keys P.hub (g,⟨0,Nat.two_pow_pos _⟩)) (low _) g.val.2.isLt
  · exact coarse_lt m (code t) (legal t).1 (legal t).2.2

include legal in
omit [Fintype V] [DecidableEq V] [Fintype H] in
theorem coarse_recover {a d : H} (hi : coarseName m (code a)=coarseName m (code d))
    (lo : shortName m (code a)=shortName m (code d)) : a=d :=
  code.injective (DescentRelativeContacts.relative_injective (k:=m) (r:=0) (legal a).1 (legal d).1 hi lo)
end
end Hierarchy.DescentChosenRouter

namespace Hierarchy.DescentCommonHost
open DescentChosenRouter DescentContacts DescentCanonicalPorts DescentRelativeContacts DescentMixedRouter
open scoped Classical
noncomputable section
variable {V I H A K : Type} [Fintype V] [DecidableEq V] [Fintype I] [Fintype H] [Fintype A] [Field K]
variable {k n h C₀ bits u : ℕ} (P : Placement V I H A k (2^n)) (G : NonlinearExpanders.Graph n h)
local notation "Z" => V×Endpoint (2^n)
local notation "R" => DescentCommonPalette.rotor G
local notation "X" => Node V Z (Computability.BorderVNP.Crossing.Network.Site R)
variable (m : ℕ) (code : H ↪ V × Endpoint (2^n)) (low : ∀v,m≤P.b v) (legal : ∀t,m≤(code t).2.1.1 ∧
    (code t).2.1.1≤k ∧ (code t).2.1.2<2^(code t).2.1.1)
local notation "lab" => fun t=>shortName m (code t)
variable (hw : 0<bits) (pay : ℝ) (hardware : Hardware (K:=K) (C₀:=C₀) (u:=u) P G hw pay) (D : ℕ)
local notation "Q" => network G hw u P.contact P.input P.site P.owner P.align (selected P G hw pay hardware) D
local notation "view" => bankNode P G m code hw pay hardware D
local notation "sn" => short (m:=m) P.b

def rawName : (Bool×H)⊕(Q).Site→X := Sum.elim (fun st=>.trunk st.1 (lab st.2)) view
def rawCoordinate : (Bool×H)⊕(Q).Site→ℕ :=
  Sum.elim (fun st=>coarseName m (code st.2)) (fun v=>P.siteGroup m code v.1.2)
local notation "nm" => rawName P G m code hw pay hardware D
local notation "ix" => rawCoordinate P G m code hw pay hardware D

include low legal in
theorem raw_lt (z : (Bool×H)⊕(Q).Site) : ix z<2^m := by
  rcases z with st|v
  · exact coarse_lt m (code st.2) (legal st.2).1 (legal st.2).2.2
  · exact siteGroup_lt P m code low legal v.1.2

include legal in
theorem raw_recover {x y : (Bool×H)⊕(Q).Site} (same : ix x=ix y) (names : nm x=nm y) : x=y := by
  let kind : X → ℕ
    | .trunk .. => 0
    | .good .. => 1
    | .fall .. => 2
  have sameKind := congrArg kind names
  rcases x with ⟨s,t⟩ | ⟨⟨s,g|t⟩,a⟩ <;> rcases y with ⟨j,c⟩ | ⟨⟨j,q|c⟩,v⟩
  · obtain ⟨sj,ends⟩ := Node.trunk.inj names
    have roots := coarse_recover m code legal same ends
    exact congrArg Sum.inl (Prod.ext sj roots)
  · exact False.elim ((by decide : (0:ℕ) ≠ 1) sameKind)
  · exact False.elim ((by decide : (0:ℕ) ≠ 2) sameKind)
  · exact False.elim ((by decide : (1:ℕ) ≠ 0) sameKind)
  · obtain ⟨sj,bases,cell⟩ := Node.good.inj names
    have roots : g=q := Subtype.ext (recover (m:=m) P.b same bases)
    subst j
    subst q
    have av : a=v := (DescentCommonPalette.rotorSiteEquiv G D
      (selectedRotorLayers P G hw pay hardware s g) C₀ bits u).symm.injective cell
    subst v
    rfl
  · exact False.elim ((by decide : (1:ℕ) ≠ 2) sameKind)
  · exact False.elim ((by decide : (2:ℕ) ≠ 0) sameKind)
  · exact False.elim ((by decide : (2:ℕ) ≠ 1) sameKind)
  · obtain ⟨sj,ends,words⟩ := Node.fall.inj names
    have roots := coarse_recover m code legal same ends
    subst j;subst c
    have av : a=v := DescentCommonPalette.path_injective (t:=(P.fallbackBook s t).height) words
    subst v;rfl

theorem public_coordinate (s : Bool) (p : P.Public) : ix (.inr ((Q).attach (s,p)))=coarseName m (publicAddress P code p) := by
  rcases p with ⟨g,j⟩|t <;> rfl

theorem bank_coordinate (links : P.CommonGroups m code) (e : (Q).Edge) :
    ix (.inr ((Q).src e))=ix (.inr ((Q).dst e)) := by
  rcases e with c|⟨_,_⟩
  · exact links c
  · rfl

end
end Hierarchy.DescentCommonHost

end OAI
