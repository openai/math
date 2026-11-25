import OAI.Hierarchy.DescentResetRateNumbers
import OAI.Hierarchy.DescentReentryCommonHost
import OAI.Hierarchy.DescentResetIntervalAddress

namespace OAI
/-! # Counting exactly the common physical positions that support reentry -/

namespace Hierarchy.DescentCommonHost
open DescentContacts DescentHostDirectory DescentResetHostSize DescentRelativeContacts
open DescentColonies DescentCanonicalPorts DescentChosenRouter
open scoped Classical BigOperators
noncomputable section
variable {V : Type} [Fintype V] {n h : ℕ} (G : NonlinearExpanders.Graph n h)
local notation "Y" => (2^n : ℕ)
local notation "R" => DescentCommonPalette.rotor G
local notation "T" => DescentCommonPalette.tree
local notation "X" => Node V (V×Endpoint Y) (Computability.BorderVNP.Crossing.Network.Site R)

abbrev Pool (V : Type) (r Ht : ℕ) :=
  Bool × V × Code r × (Option (Fin Y) ⊕ ((R).Site ⊕ (Option (Fin Y) × (T Ht).Site)))

def render (r Ht : ℕ) : Pool G V r Ht→X
  | (s,v,a,.inl tag) => .trunk s (v,a.val,tag)
  | (s,v,a,.inr (.inl cell)) => .good s (v,a.val.2) cell
  | (s,v,a,.inr (.inr (tag,cell))) => .fall s (v,a.val,tag) (DescentCommonPalette.path (t:=Ht) cell)

def raiseTree {t Ht : ℕ} (cap : t≤Ht) (x : (T t).Site) : (T Ht).Site :=
  ⟨⟨x.1.val,lt_of_lt_of_le x.1.isLt (Nat.succ_le_succ cap)⟩,x.2⟩

theorem rotor_count : Fintype.card (R).Site=(2*h+4)*Y := by
  rw [DescentCommonPalette.rotor,DescentPhysicalSplit.site_count]
  have count (v) : DescentPhysicalSplit.count (DescentRotor.Physical.host G.arcs 0 0 0 0 0) v=2*h+2 := by
    refine (Fintype.card_congr (DescentRotor.Physical.rowFibre (D:=0) («R»:=0) (C:=0) (w:=0) (u:=0) G v)).trans ?_
    refine Eq.trans ?_ (DescentRotor.regular_slots G v)
    exact congrArg (@Fintype.card (DescentRotor.Slot G.arcs v)) (Subsingleton.elim _ _)
  calc
    _ = ∑ _v : Fin (2^n), ((2*h+2)+2) :=
      Finset.sum_congr rfl fun v _ => congrArg (· + 2) (count v)
    _ = _ := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul]
      ring

theorem pool_count (r Ht : ℕ) :
    Fintype.card (Pool G V r Ht)≤(2*((Y+1)+((2*h+4)*Y+(Y+1)*2^(Ht+1))))*2^(r+1)*Fintype.card V := by
  have interval : Fintype.card (Code r)≤2^(r+1) :=
    (Fintype.card_coe (codes r)).le.trans ((Nat.le_succ _).trans (codes_card r))
  have tree : Fintype.card (T Ht).Site≤2^(Ht+1) := by
    have paid : Fintype.card (T Ht).Site+1=2^(Ht+1) := DescentContactTree.Physical.sites (h:=Ht) (D:=0) (fun (_ : Unit) (_ : ℕ)=>false) (fun _=>0)
    omega
  simp only [Pool,Fintype.card_prod,Fintype.card_bool,Fintype.card_sum,Fintype.card_option,Fintype.card_fin,rotor_count]
  calc _ ≤ 2*(Fintype.card V*(2^(r+1)*(Y+1+((2*h+4)*Y+(Y+1)*2^(Ht+1))))) := by gcongr
       _ = _ := by ring

end
end Hierarchy.DescentCommonHost

namespace Hierarchy.DescentSixParty.ResetInput
open DescentCommonHost DescentChosenRouter DescentRelativeContacts DescentContacts DescentHostDirectory
open scoped Classical
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {A : MarkedWorld F d P bits}
    {price ε : ℝ} {h C Ht : ℕ} (Z : ResetInput A price ε h C Ht) (T : Terminals Z)
local notation "Y" => (2^Z.n : ℕ)
local notation "R" => Z.placement
local notation "m" => T.commonDepth

theorem placed_support {r t : ℕ} (groups : Z.k-m≤r)
    (bounds : ∀z,(T.code z).2.1.1≤Z.k) (heights : ∀s z,((R).fallbackBook s z).height≤t) :
    commonNames Z T ⊆ Finset.univ.image (render Z.graph (V:=Z.V) r t) := by
  have code (q : Z.V×Endpoint Y) (fit : q.2.1.1≤Z.k) :
      (shortName m q).2.1∈codes r :=
    mem_codes (by omega) (Nat.mod_lt _ (Nat.two_pow_pos _))
  intro x hx
  obtain ⟨v,_,rfl⟩ := Finset.mem_image.mp hx
  unfold commonName
  change Sum.elim _ _ (resetNames Z T v)∈_
  rcases resetNames Z T v with ⟨s,z⟩|⟨⟨s,g|z⟩,cell⟩
  · exact Finset.mem_image.mpr ⟨(s,(T.code z).1,⟨_,code _ (bounds z)⟩,.inl (T.code z).2.2),Finset.mem_univ _,rfl⟩
  · let p := g.val
    have ht := (R).depth p.1
    have ok : ((R).b p.1-m,p.2.val%2^((R).b p.1-m))∈codes r :=
      mem_codes (by omega) (Nat.mod_lt _ (Nat.two_pow_pos _))
    let layers := DescentChosenRouter.selectedRotorLayers Z.placement Z.graph Z.positive Z.pay Z.circuit s g
    let physical := (DescentCommonPalette.rotorSiteEquiv Z.graph d layers C Z.width Z.unit).symm cell
    exact Finset.mem_image.mpr ⟨(s,p.1,⟨_,ok⟩,.inr (.inl physical)),Finset.mem_univ _,rfl⟩
  · exact Finset.mem_image.mpr ⟨(s,(T.code z).1,⟨_,code _ (bounds z)⟩,
      .inr (.inr ((T.code z).2.2,raiseTree (heights s z) cell))),Finset.mem_univ _,rfl⟩

theorem placed_count {r t : ℕ} (groups : Z.k-m≤r)
    (bounds : ∀z,(T.code z).2.1.1≤Z.k) (heights : ∀s z,((R).fallbackBook s z).height≤t) :
    Fintype.card ↥(commonNames Z T) ≤
      (2*((Y+1)+((2*h+4)*Y+(Y+1)*2^(t+1))))*2^(r+1)*Fintype.card Z.V := by
  have all := placed_support Z T groups bounds heights
  rw [Fintype.card_coe]
  exact (Finset.card_le_card all).trans (Finset.card_image_le.trans (by
    rw [Finset.card_univ];exact pool_count (V:=Z.V) Z.graph r t))
theorem placed_growth {r : ℕ} (groups : Z.k-m≤r) :
    Fintype.card ↥(commonNames Z T) ≤
      Fintype.card Z.V*(2^(resetHostGain h Y Ht)*2^r) := by
  let a := (Y+1)+((2*h+4)*Y+(Y+1)*2^(Ht+1))
  have bound := placed_count Z T groups (fun t=>(T.codeLegal t).2.1) T.bookHeight
  have gain : 4*a≤2^(resetHostGain h Y Ht) := Nat.le_pow_clog (by decide : 1<2) _
  calc _ ≤ 2*a*2^(r+1)*Fintype.card Z.V := bound
       _ = Fintype.card Z.V*(4*a*2^r) := by rw [Nat.pow_succ];ring
       _ ≤ _ := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ gain)

end
end Hierarchy.DescentSixParty.ResetInput

end OAI
