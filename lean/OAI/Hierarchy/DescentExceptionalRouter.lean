import OAI.Hierarchy.DescentRouterSlots
import OAI.Hierarchy.DescentSubstitutionDegree

namespace OAI
/-! # End-to-end exceptional routing with two physical banks of binary relay trees -/

namespace Hierarchy.DescentExceptionalRouter
open Computability.BorderVNP.Crossing DescentRouterSlots DescentNamedContact
open scoped Classical BigOperators
noncomputable section
variable {I C R W K : Type} [Fintype I] [Fintype C] [Fintype R] [Fintype W] [CommSemiring K]
variable (D : ℕ) (contact : I→C) (input : Bool→I→R) (site : Bool→R→W) (owner : Bool→C→W) (wt : I→ℕ)
variable (align : ∀s i,site s (input s i)=owner s (contact i))
variable (s : Bool) (w : W)
local notation "B" => DescentRouterBank.network D contact input site owner wt
local notation "lp" => link contact owner s w
local notation "cost" => amount contact owner wt s w
local notation "T" => DescentNamedContact.network lp cost D
local notation "slot" => DescentNetworkSubstitution.Slot B (s,w)
local notation "lens" => DescentNetworkSubstitution.slotWidth B (s,w)

def position (q : slot) : Pin (LinkId owner s w) := Sum.map (fun _=>()) id
  (names D contact input site owner wt s w q)

def words (p : Ports lens) : Ports (bits lp cost) := write lp cost
  (sourceWord D contact input site owner wt s w align p) (targetWord D contact input site owner wt s w p)

omit [Fintype R] in
/-- Each packed output reads only pins attached at the same terminal of its contact tree. -/
theorem words_local (N : Network D (Pin (LinkId owner s w)) (bits lp cost)) :
    DescentLocalAdapters.Local N (position D contact input site owner wt s w) lens
    (words D contact input site owner wt align s w) := by
  intro v x y agree p atv
  rcases p with u|c
  · cases u
    apply congrArg (fun row => (DescentContactTree.Physical.concat cost).symm row)
    funext i
    have same := agree (rootSlot D contact input site owner wt s w (root contact input site owner s w align i))
      (by simpa [position] using atv)
    simp only [sourceWord,same]
  · have fibre_ext {E J : Type} [Fintype E] [Fintype J] (label : E → J) (weight : E → ℕ)
        (j : J) (a b : DescentContactTree.Physical.Row weight)
        (h : ∀ i, label i = j → a i = b i) : (labels label weight).symm a j = (labels label weight).symm b j := by
      have rows : (fun i : Fibre label j => a i.val) = (fun i : Fibre label j => b i.val) :=
        funext fun i => h i.val i.property
      let pack := DescentContactTree.Physical.concat (fun i : Fibre label j => weight i.val)
      let encode : ((i : Fibre label j) → Fin (weight i.val) → Bool) →
          (Fin (width label weight j) → Bool) := pack.invFun
      with_unfolding_all exact congrArg encode rows
    apply fibre_ext lp cost c (targetWord D contact input site owner wt s w x)
      (targetWord D contact input site owner wt s w y)
    intro i hit
    have same := agree (linkSlot D contact input site owner wt s w (link contact owner s w i))
      (by simpa [position,hit] using atv)
    unfold targetWord
    rw [same]

def device : Network D slot lens := DescentLocalAdapters.graph T (position D contact input site owner wt s w) lens

def tables : (device D contact input site owner wt s w).Tables K :=
  DescentLocalAdapters.tables T (position D contact input site owner wt s w) lens
    (DescentNamedContact.tables (K:=K) lp cost D) (words D contact input site owner wt align s w)

omit [Fintype R] in
/-- This device actually reads its own external root and its assigned direct-link
words, with its contact order translated through the true common bundle labels. -/
theorem value (x : Bool→DescentContactTree.Physical.Row wt) (z : DescentContactTree.Physical.Row wt) :
    (device D contact input site owner wt s w).value (tables (K:=K) D contact input site owner wt align s w)
      (DescentRouterBank.feed D contact input site owner wt x z s w)=
      if ∀i,owner s (contact i)=w → x s i=z i then 1 else 0 := by
  let f := DescentRouterBank.feed D contact input site owner wt x z s w
  refine (DescentLocalAdapters.value T (position D contact input site owner wt s w) lens
    (DescentNamedContact.tables (K:=K) lp cost D) (words D contact input site owner wt align s w)
    (words_local D contact input site owner wt align s w T) f).trans
    ((value_words (K:=K) lp cost D (sourceWord D contact input site owner wt s w align f)
      (targetWord D contact input site owner wt s w f)).trans ?_)
  have indicators (P Q : Prop) (dp : Decidable P) (dq : Decidable Q) (eqv : P ↔ Q) :
      @ite K P dp 1 0 = @ite K Q dq 1 0 := by
    by_cases p : P
    · simp [p,eqv.mp p]
    · have q : ¬ Q := fun h => p (eqv.mpr h)
      simp [p,q]
  exact indicators _ _ _ _ (word_agreement D contact input site owner wt s w align x z)

theorem degree (single : Subsingleton (InputId site s w)) (v : (device D contact input site owner wt s w).Site) :
    (device D contact input site owner wt s w).bitDegree v≤3 := by
  have one : Function.Injective (fun _ : InputId site s w=>()) := fun _ _ _=>single.elim _ _
  exact (DescentLocalAdapters.degree _ _ _ ((Sum.map_injective.mpr ⟨one,Function.injective_id⟩).comp
    (names D contact input site owner wt s w).injective) v).trans (DescentNamedContact.degree lp cost D v)

omit [Fintype R] in
theorem wires : (∑e,(device D contact input site owner wt s w).width e)=
    DescentContactTree.codeHeight (LinkId owner s w)*∑i : Item contact owner s w,wt i.val :=
  DescentNamedContact.wires lp cost D

/-- In the exceptional bank a root is one old terminal, so its coarse site index
is exactly that terminal. Distinct endpoints may use unrelated contact catalogs. -/
def exceptional (D : ℕ) (contact : I→C) (ends : Bool→C→W) (wt : I→ℕ) :=
  let input := fun s i=>ends s (contact i)
  let site := fun (_ : Bool)=>id (α:=W)
  DescentNetworkSubstitution.network (DescentRouterBank.network D contact input site ends wt)
    (fun v=>device D contact input site ends wt v.1 v.2)

def exceptionalTables (D : ℕ) (contact : I→C) (ends : Bool→C→W) (wt : I→ℕ) :=
  let input := fun s i=>ends s (contact i)
  let site := fun (_ : Bool)=>id (α:=W)
  DescentNetworkSubstitution.tables (DescentRouterBank.network D contact input site ends wt)
    (fun v=>device D contact input site ends wt v.1 v.2)
    (fun v=>tables (K:=K) D contact input site ends wt (fun _ _=>rfl) v.1 v.2)

theorem exceptional_value (ends : Bool→C→W) (x y : DescentContactTree.Physical.Row wt) :
    let input := fun s i=>ends s (contact i)
    let rows := fun b : Bool=>if b then y else x
    (exceptional D contact ends wt).value (exceptionalTables (K:=K) D contact ends wt)
      (DescentRouterBank.publicWords input wt rows)=if x=y then 1 else 0 := by
  let inp (b : Bool) (i : I) := ends b (contact i)
  let st (_ : Bool) := id (α := W)
  have a (b : Bool) (i : I) : st b (inp b i) = ends b (contact i) := rfl
  let rows (b : Bool) := if b then y else x
  have eval := DescentRouterBank.substituted_value (K := K) (d := D)
    D contact inp st ends wt
    (fun v => device D contact inp st ends wt v.1 v.2)
    (fun v => tables (K := K) D contact inp st ends wt a v.1 v.2)
    (fun xs z b u => value (K := K) D contact inp st ends wt a b u xs z)
    (DescentRouterBank.publicWords inp wt rows)
  rw [DescentRouterBank.publicRows_words, DescentRouterBank.publicRows_words] at eval
  exact eval

private theorem degree_from_slot {A : Type*} {b : A → ℕ} {d : ℕ}
    (net : Network d A b) (j : net.Site) {left right : Fintype A} {n k : ℕ}
    (count : n = @Network.bitDegree d A left b net j)
    (cap : @Network.bitDegree d A right b net j ≤ k) : n ≤ k := by
  cases Subsingleton.elim left right
  exact count.le.trans cap

theorem exceptional_degree (ends : Bool→C→W) (v : (exceptional D contact ends wt).Site) :
    (exceptional D contact ends wt).bitDegree v≤3 := by
  let inp (b : Bool) (i : I) := ends b (contact i)
  let st (_ : Bool) := id (α := W)
  have single : Subsingleton (InputId st v.1.1 v.1.2) :=
    ⟨fun r t => Subtype.ext (r.property.trans t.property.symm)⟩
  have count := DescentNetworkSubstitution.degree (DescentRouterBank.network D contact inp st ends wt)
    (fun u => device D contact inp st ends wt u.1 u.2) v.1 v.2
  have cap := degree D contact inp st ends wt v.1.1 v.1.2 single v.2
  exact degree_from_slot (device D contact inp st ends wt v.1.1 v.1.2) v.2 count cap

end
end Hierarchy.DescentExceptionalRouter

end OAI
