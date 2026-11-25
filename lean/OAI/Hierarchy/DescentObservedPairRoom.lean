import OAI.Hierarchy.DescentObservedBitLoads
import OAI.Hierarchy.DescentGoodBaseRoom

namespace OAI
/-! # The capacity of each observed contact pays for its actual old physical bit slots -/

namespace Hierarchy.DescentChosenRouter.Dyadic
open DescentGL DescentColonies DescentBaseProfile DescentSixParty DescentBaseVariance DescentRouterSlots
open scoped Classical BigOperators
noncomputable section
variable {F H P V : Type} [Field F] [Fintype V] [DecidableEq V] {d k : ℕ} {bits : P→ℕ}
variable (W : MarkedWorld F d P bits) (pos : W.graph.Site→V) (ix : W.graph.Site→Block k)
variable (wire : ℕ) (D : Dyadic V (BitsOf W) k)

/-- The price of the one common directed link shared by the two observed bases. -/
def physicalCapacity (f B K : ℕ) (a : D.Pairs) :=
  let v := (D.endAt false a).val.1
  let w := (D.endAt true a).val.1
  pairCapacity k (D.b v) (D.b w) (blockMean k (fun i=>(pairLoad W pos ix wire v w i:ℝ))) ((2:ℕ)^f*B) K

variable (trace : ∀s i,D.old s i=physicalOld W pos ix s i)
variable (near : V→Finset V) (Δ f B K : ℕ) (weight : V→Block k→ℕ)
local notation "traffic" => (fun v w i => (pairLoad W pos ix wire v w i:ℝ))

include trace

omit [Field F] in
/-- All paid old bits at one real ordered contact fit the native finer-cell reservation. -/
theorem physical_amount (hB : 0<B) (reached : D.keys = resetKeys near Δ f B K weight traffic D.b D.hk D.L)
    (core : ∀ p : D.Paid,p.val.1∈W.core)
    (adj : ∀ e∈W.core,pos (W.graph.dst e)∈near (pos (W.graph.src e)))
    (same : ∀ e∈W.core,ix (W.graph.src e)=ix (W.graph.dst e)) (a : D.Pairs) :
    (contactCounts D.edge a:ℝ)*wire ≤ physicalCapacity W pos ix wire D f B K a := by
  let v := (D.endAt false a).val.1
  let w := (D.endAt true a).val.1
  let hj := max_le (D.hk v) (D.hk w)
  let cell := dyadicLayout hj D.L
  obtain ⟨root,_,hr⟩ := Finset.mem_image.mp a.property
  have re : D.edge root = a := Subtype.ext hr
  let x := ix (W.graph.src root.val.1)
  have ends (p : D.Paid) (eq : D.edge p=a) (s : Bool) :
      baseOf D.b D.hk D.L (physicalOld W pos ix s p.val) = (D.endAt s a).val := by
    rw [←trace,←eq,D.endAt_edge]; rfl
  have address (p : D.Paid) (eq : D.edge p=a) (s : Bool) :
      (physicalOld W pos ix s p.val).1=(D.endAt s a).val.1 := congrArg Sigma.fst (ends p eq s)
  have prefixKey (p : D.Paid) (eq : D.edge p=a) (s : Bool) :
      group (D.b (D.endAt s a).val.1) (rearrange D.L (physicalOld W pos ix s p.val).2) = (D.endAt s a).val.2.val := by
    have id := congrArg (fun q : BaseId D.b => q.2.val) (ends p eq s)
    change (dyadicLayout (D.hk (physicalOld W pos ix s p.val).1) D.L (physicalOld W pos ix s p.val).2).val = _ at id
    rw [layout_id, address p eq s] at id
    exact id
  have site (p : D.Paid) (eq : D.edge p=a) : pos (W.graph.src p.val.1)=v ∧ pos (W.graph.dst p.val.1)=w :=
    ⟨address p eq false,address p eq true⟩
  have prefix_cell (p : D.Paid) (eq : D.edge p=a) : cell (ix (W.graph.src p.val.1))=cell x := by
    apply Fin.ext
    simp only [cell,layout_id]
    rcases le_total (D.b v) (D.b w) with h | h
    · rw [max_eq_right h]
      have one := (prefixKey p eq true).trans (prefixKey root re true).symm
      change group (D.b w) (rearrange D.L (ix (W.graph.dst p.val.1))) =
        group (D.b w) (rearrange D.L (ix (W.graph.dst root.val.1))) at one
      rwa [←same _ (core p),←same _ (core root)] at one
    · rw [max_eq_left h]
      exact (prefixKey p eq false).trans (prefixKey root re false).symm
  have edge : w ∈ near v := by simpa only [(site root re).1,(site root re).2] using adj root.val.1 (core root)
  let c : Contacts near := ⟨v,w,edge⟩
  have good : baseOf D.b D.hk D.L (v,x) ∉validBases D.b (resetKeys near Δ f B K weight traffic D.b D.hk D.L) := by
    rw [←reached]
    have witness := ends root re false
    change baseOf D.b D.hk D.L (pos (W.graph.src root.val.1),x) = _ at witness
    rw [(site root re).1] at witness
    rw [witness]
    exact (D.endAt false a).property.1
  have room := good_pair_room near Δ f B K weight traffic D.b D.hk D.L hB c x (Or.inl good)
  let serial : {p : D.Paid // D.edge p=a} ↪ BitsOf W :=
    ⟨fun t=>t.val.val,fun _ _ h=>Subtype.ext (Subtype.ext h)⟩
  have bill := directed_bits_le W pos ix serial wire v w cell (cell x) (fun t=>
    ⟨core t.val,(site t.val t.property).1,(site t.val t.property).2,prefix_cell t.val t.property⟩)
  have count : Fintype.card {p : D.Paid // D.edge p=a}=contactCounts D.edge a := by
    rw [Fintype.card_subtype]
    apply congrArg Finset.card
    ext p
    simp
  rw [count] at bill
  exact bill.trans room

end
end Hierarchy.DescentChosenRouter.Dyadic

end OAI
