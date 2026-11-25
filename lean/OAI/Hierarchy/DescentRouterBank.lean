import OAI.Hierarchy.DescentNamedContact
import OAI.Hierarchy.DescentNetworkSubstitution

namespace OAI
/-! # Coarse physical contacts between the two banks of actual reset routers -/

namespace Hierarchy.DescentRouterBank
open Computability.BorderVNP.Crossing DescentContactTree.Physical DescentNamedContact
open scoped BigOperators Classical
noncomputable section

variable {I C R W : Type} [Fintype I] [Fintype C] [Fintype R] [Fintype W]
variable {d : ℕ} (D : ℕ) (contact : I → C) (input : Bool → I → R)
variable (site : Bool → R → W) (owner : Bool → C → W) (wt : I → ℕ)

def publicWidth (p : Bool × R) := width (input p.1) wt p.2

abbrev network : Network D (Bool × R) (publicWidth input wt) where
  Site := Bool × W
  Edge := C
  finiteSite := inferInstance
  finiteEdge := inferInstance
  src c := (false,owner false c)
  dst c := (true,owner true c)
  width := width contact wt
  attach p := (p.1, site p.1 p.2)
  position _ := 0
  in_ball _ := by simp

local notation "N" => network D contact input site owner wt

def publicWords (x : Bool → Row wt) : Ports (publicWidth input wt) :=
  fun t => (labels (input t.1) wt).symm (x t.1) t.2

def publicRows (p : Ports (publicWidth input wt)) (s : Bool) : Row wt :=
  labels (input s) wt (fun r => p (s,r))

omit [Fintype R] in
@[simp] theorem publicRows_words (x : Bool → Row wt) (s : Bool) :
    publicRows input wt (publicWords input wt x) s = x s := by
  change (labels (input s) wt) ((labels (input s) wt).symm (x s)) = x s
  exact (labels (input s) wt).apply_symm_apply (x s)

omit [Fintype R] in
@[simp] theorem publicWords_rows (p : Ports (publicWidth input wt)) :
    publicWords input wt (publicRows input wt p) = p := by
  funext t
  rcases t with ⟨s,r⟩
  exact congrFun ((labels (input s) wt).symm_apply_apply (fun r => p (s,r))) r

/-- The actual oriented gadget slots see the same old contact word at both bank endpoints. -/
def feed (x : Bool → Row wt) (z : Row wt) (s : Bool) (w : W) :
    Ports (DescentNetworkSubstitution.slotWidth N (s,w)) :=
  DescentNetworkSubstitution.visible N ((labels contact wt).symm z) (publicWords input wt x) (s,w)

omit [Fintype R] in
@[simp] theorem feed_source (x : Bool → Row wt) (z : Row wt) (s : Bool) (w : W)
    (e : {e : (N).Edge // (N).src e = (s,w)}) :
    feed D contact input site owner wt x z s w (.inl e) = (labels contact wt).symm z e.val := rfl

omit [Fintype R] in
@[simp] theorem feed_target (x : Bool → Row wt) (z : Row wt) (s : Bool) (w : W)
    (e : {e : (N).Edge // (N).dst e = (s,w)}) :
    feed D contact input site owner wt x z s w (.inr (.inl e)) = (labels contact wt).symm z e.val := rfl

omit [Fintype R] in
@[simp] theorem feed_public (x : Bool → Row wt) (z : Row wt) (s : Bool) (w : W)
    (p : {p : Bool × R // (N).attach p = (s,w)}) :
    feed D contact input site owner wt x z s w (.inr (.inr p)) = publicWords input wt x p.val := rfl

variable {K : Type*} [CommSemiring K]
variable (align : ∀ s i, site s (input s i) = owner s (contact i))

private def check (a : (N).Assignment) (p : Ports (publicWidth input wt)) (v : (N).Site) : K :=
  if ∀ i, owner v.1 (contact i) = v.2 → publicRows input wt p v.1 i = labels contact wt a i then 1 else 0

include align in
omit [Fintype R] in
private theorem check_local : DescentLocalTables.Supported N (check (K:=K) D contact input site owner wt) := by
  rintro ⟨s,w⟩ a b x y wires pins
  unfold check
  refine if_congr ?_ rfl rfl
  apply forall_congr'
  intro i
  apply forall_congr'
  intro hi
  have hx := pins (s,input s i) (congrArg (Prod.mk s) ((align s i).trans hi))
  have hc := wires (contact i) (by
    cases s
    · exact Or.inl (congrArg (Prod.mk false) hi)
    · exact Or.inr (congrArg (Prod.mk true) hi))
  let pinWord := concat (fun t : Fibre (input s) (input s i) => wt t.val)
  let wireWord := concat (fun t : Fibre contact (contact i) => wt t.val)
  change (pinWord (x (s,input s i)) ⟨i,rfl⟩ = wireWord (a (contact i)) ⟨i,rfl⟩) ↔
    (pinWord (y (s,input s i)) ⟨i,rfl⟩ = wireWord (b (contact i)) ⟨i,rfl⟩)
  rw [hx,hc]

def tables : (N).Tables K := DescentLocalTables.tables N (check D contact input site owner wt)

include align in
omit [Fintype R] in
theorem table_read (x : Bool → Row wt) (z : Row wt) (s : Bool) (w : W) :
    (N).read (tables (K:=K) D contact input site owner wt) ((labels contact wt).symm z) (publicWords input wt x) (s,w) =
      if ∀ i, owner s (contact i) = w → x s i = z i then 1 else 0 := by
  rw [tables, DescentLocalTables.read _ _ (check_local D contact input site owner wt align)]
  simp only [check, publicRows_words, Equiv.apply_symm_apply]

omit [Fintype R] in
/-- The product at the two banks fixes one global hidden bundle tuple. -/
theorem value_from_reads (T : (N).Tables K)
    (entry : ∀ x z s w, (N).read T ((labels contact wt).symm z) (publicWords input wt x) (s,w) =
      if ∀ i, owner s (contact i) = w → x s i = z i then 1 else 0) (x : Bool → Row wt) :
    (N).value T (publicWords input wt x) = if x false = x true then 1 else 0 := by
  classical
  have term (z : Row wt) : (∏ t : Bool × W, (N).read T ((labels contact wt).symm z) (publicWords input wt x) t) =
      if x false = z ∧ x true = z then 1 else 0 := by
    calc
      _ = ∏ t : Bool × W, (if ∀ i, owner t.1 (contact i) = t.2 → x t.1 i = z i then (1:K) else 0) :=
        Finset.prod_congr rfl fun ⟨s,w⟩ _ => entry x z s w
      _ = _ := by
        rw [Fintype.prod_boole]
        refine if_congr ?_ rfl rfl
        constructor
        · intro h
          exact ⟨funext (fun i => h (false,owner false (contact i)) i rfl),
            funext (fun i => h (true,owner true (contact i)) i rfl)⟩
        · rintro ⟨l,r⟩ ⟨s,w⟩ i _
          cases s
          · exact congrFun l i
          · exact congrFun r i
  unfold Network.value
  rw [← (labels contact wt).symm.sum_comp]
  simp_rw [term]
  by_cases same : x false = x true
  · simp [same]
  · have absent (z : Row wt) : ¬ (x false = z ∧ x true = z) := fun h => same (h.1.trans h.2.symm)
    simp [absent,same]

include align in
omit [Fintype R] in
theorem value (x : Bool → Row wt) :
    (N).value (tables (K:=K) D contact input site owner wt) (publicWords input wt x) =
      if x false = x true then 1 else 0 :=
  value_from_reads D contact input site owner wt _ (table_read D contact input site owner wt align) x

omit [Fintype R] in
/-- The literal substituted rotor and tree networks realize equality at every grouped exterior pin word. -/
theorem substituted_value
    (M : (t : (N).Site) → Network d (DescentNetworkSubstitution.Slot N t) (DescentNetworkSubstitution.slotWidth N t))
    (T : (t : (N).Site) → (M t).Tables K)
    (localValue : ∀ (x : Bool → Row wt) (z : Row wt) (s : Bool) (w : W),
      (M (s,w)).value (T (s,w)) (feed D contact input site owner wt x z s w) =
      if ∀ i, owner s (contact i) = w → x s i = z i then (1 : K) else 0) (pins : Ports (publicWidth input wt)) :
    (DescentNetworkSubstitution.network N M).value (DescentNetworkSubstitution.tables (K:=K) N M T) pins =
      if publicRows input wt pins false = publicRows input wt pins true then (1 : K) else 0 := by
  rw [DescentNetworkSubstitution.value_substitute N M T pins]
  conv_lhs => rw [← publicWords_rows input wt pins]
  apply value_from_reads D contact input site owner wt
  intro x z s w
  rw [DescentNetworkSubstitution.read_coefficient]
  exact localValue x z s w

omit [Fintype R] in
theorem contact_width : (∑ c : (N).Edge, (N).width c) = ∑ i, wt i := width_sum contact wt

end
end Hierarchy.DescentRouterBank

end OAI
