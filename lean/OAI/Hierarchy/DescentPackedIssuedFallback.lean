import OAI.Hierarchy.DescentPhysicalFallbackPanel
import OAI.Hierarchy.DescentPackedFallbackTree
import OAI.Hierarchy.DescentPrivateTreeTemplate

namespace OAI
/-! # Local packed leaf counts recover the selected physical fallback graph's private widths -/

namespace Hierarchy.DescentSixParty.GroupStage
open DescentIssuedFallbackPanel DescentSharedCableNames.Stage DescentGL DescentColonies DescentChosenRouter
open DescentResetAttachments StarKeys DescentTreePrefixIntervals DescentContactTree DescentRouterSlots
open DescentPackedFallbackTree
open scoped Classical BigOperators
noncomputable section
variable {F P J V : Type} [Field F] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
    {d k i m g h C Ht : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F}
    {q ε : ℝ} (A : GroupStage W G q ε J V k) (S : DescentCompiler.AtomSchedule) (ready : A.StateBounds S i)
variable (digits : Block m≃J×Block k) (native : W.graph.Edge↪ℕ)
variable (Z : ResetInput (F:=F) (W.granular A.grainCount (A.z*G.b) (A.grainCount_fit S ready))
    (q*A.wire) ε h C Ht) (T : ResetInput.Terminals (F:=F) Z)
variable (frame : ResetInput.SourceFrame (F:=F) (V:=V) (k:=m) Z T (fun u=>(A.pos u).2)
    (StarKeys.filled W.graph A.pos A.block digits) A.hub g)
local notation "c" => T.commonDepth
local notation "R" => Z.placement
local notation "E" => Grain A


local notation "slots" => 2^(m-c)*(2*A.cap)

def arrivedLeaf (s : Bool) (t : Z.Fallback) (e : E) : Option (Fin (2^Ht)) :=
  if eqn : falls A S ready Z s t e then
    let x:=(Z.placement.fallbackBook s t).codes ⟨(R).contact e,eqn⟩
    some ⟨start Ht x,by
      have h:=T.bookHeight s t
      have le : start Ht x < stop Ht x:=Nat.mul_lt_mul_of_pos_right (Nat.lt_succ_self _) (Nat.two_pow_pos _)
      exact le.trans_le (stop_le h x)⟩
  else none

/-- A fixed local slot is gated by the measured side, owner and signed-port ticket.
The packed row contains no global edge identifier. -/
def leafPanel (s : Bool) (t : Z.Fallback) : Panel Ht slots := fun j=>
  (fallbackPanel A S ready digits native Z T frame s t (finProdFinEquiv.symm j)).bind
    (arrivedLeaf A S ready Z T s t)

private def counts (s : Bool) (t : Z.Fallback) (v : DescentPrivateTreeTemplate.Template) (e : E) : Prop :=
  ∃l,arrivedLeaf A S ready Z T s t e=some l ∧ v.lo≤l.val ∧ l.val<v.hi

private theorem count_arrivals {I X : Type} [Fintype I] {H n : ℕ}
    (order : I ≃ Fin n) (table : I → Option X) (arrive : X → Option (Fin (2^H)))
    (v : DescentPrivateTreeTemplate.Template) (test : X → Bool)
    (hit : ∀ e, test e = true ↔ ∃ x, arrive e = some x ∧ v.lo ≤ x.val ∧ x.val < v.hi) :
    DescentPackedFallbackTree.count (fun j => (table (order.symm j)).bind arrive) v =
      ∑ i, if (table i).any test then 1 else 0 := by
  unfold DescentPackedFallbackTree.count
  rw [←order.sum_comp]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Equiv.symm_apply_apply]
  cases outcome : table i <;> simp [hit]

theorem leafPanel_count (s : Bool) (t : Z.Fallback) (v : DescentPrivateTreeTemplate.Template) :
    DescentPackedFallbackTree.count (leafPanel A S ready digits native Z T frame s t) v =
      ∑e : E,if falls A S ready Z s t e ∧ counts A S ready Z T s t v e then 1 else 0 := by
  let test := fun e => decide (counts A S ready Z T s t v e)
  have census := fallbackPanel_count A S ready digits native Z T frame s t test
  simp only [Finset.card_filter] at census
  refine (count_arrivals finProdFinEquiv (fallbackPanel A S ready digits native Z T frame s t)
    (arrivedLeaf A S ready Z T s t) v test (by
      intro e
      exact ⟨fun yes => @of_decide_eq_true (counts A S ready Z T s t v e) _ yes,
        fun yes => @decide_eq_true (counts A S ready Z T s t v e) _ yes⟩)).trans ?_
  simpa only [test, decide_eq_true_eq] using census

/-- The chosen subtree actually carries this many input bundles of width unit. -/
private theorem sum_supported {X : Type} [Fintype X] (p : X → Prop) [Fintype {x // p x}]
    (f : X → ℕ) (off : ∀ x, ¬p x → f x = 0) :
    (∑ x : {x // p x}, f x.val) = ∑ x, f x := by
  classical
  let U := Finset.univ.filter p
  exact (Finset.sum_subtype (p := p) U (fun x => by simp [U]) f).symm.trans
    (Finset.sum_subset (Finset.subset_univ U) (fun x _ hx => off x (fun hp => hx (by simp [U,hp]))))

theorem private_width (s : Bool) (t : Z.Fallback) (e : Physical.Edge (Z.placement.fallbackBook s t).height)
    (site : ∀d,Physical.Site d→ℕ) :
    let N:=DescentFixedExceptionalRouter.device d (R).contact (R).input (R).site (R).owner (fun _=>Z.unit) s (.inr t) ((Z.placement.fallbackBook s t).codes)
    let typ:=DescentPrivateTreeTemplate.lookup Ht (Z.placement.fallbackBook s t).height
      (DescentResetCableSlots.tree (R) Ht T.bookHeight Z.graph s t e).val (site _)
    N.width e=Z.unit*DescentPackedFallbackTree.count (leafPanel A S ready digits native Z T frame s t) typ := by
  let typ:=DescentPrivateTreeTemplate.lookup Ht (Z.placement.fallbackBook s t).height
      (DescentResetCableSlots.tree (R) Ht T.bookHeight Z.graph s t e).val (site _)
  have live:=DescentPrivateTreeTemplate.edgeAt_slot (R) Ht T.bookHeight Z.graph s t e
  have lo : typ.lo=start Ht e.2:=by simp [typ,DescentPrivateTreeTemplate.lookup,live]
  have hi : typ.hi=stop Ht e.2:=by simp [typ,DescentPrivateTreeTemplate.lookup,live]
  refine (DescentPrivateTreeWidths.device_width d Z.placement.contact Z.placement.input
    Z.placement.site Z.placement.owner (fun _ => Z.unit) s (.inr t)
    (Z.placement.fallbackBook s t).codes (T.bookHeight s t) e).trans ?_
  change _ = Z.unit * DescentPackedFallbackTree.count (leafPanel A S ready digits native Z T frame s t) typ
  rw [leafPanel_count,Finset.mul_sum]
  let wgt (j : E):=if falls A S ready Z s t j ∧ counts A S ready Z T s t typ j then Z.unit else 0
  have expand (j : E) : Z.unit*(if falls A S ready Z s t j ∧ counts A S ready Z T s t typ j then 1 else 0)=wgt j := by
    split <;> simp_all [wgt]
  simp_rw [expand]
  have same : (∑j : Item (R).contact (R).owner s (.inr t),wgt j.val)=∑j,wgt j := by
    exact sum_supported (X := E) (fun x => (R).owner s ((R).contact x) = .inr t) wgt (by
      intro j miss
      have outside : ¬falls A S ready Z s t j := miss
      simp [wgt,outside])
  refine Eq.trans ?_ same
  refine Finset.sum_congr ?_ ?_
  · ext j
    simp only [Finset.mem_univ]
  intro j _
  have owned : falls A S ready Z s t j.val:=j.property
  let a := DescentPrivateTreeWidths.leaf (Z.placement.fallbackBook s t).codes
    (link (R).contact (R).owner s (.inr t)) Ht j
  have hcount : counts A S ready Z T s t typ j.val ↔ start Ht e.2 ≤ a ∧ a < stop Ht e.2 := by
    simp only [counts, arrivedLeaf, dite_eq_left owned, Option.some.injEq, exists_eq_left', lo, hi]; rfl
  exact if_congr (⟨fun h => ⟨owned,hcount.mpr h⟩, fun h => hcount.mp h.2⟩ :
    (start Ht e.2 ≤ a ∧ a < stop Ht e.2) ↔
      (falls A S ready Z s t j.val ∧ counts A S ready Z T s t typ j.val)) rfl rfl

end
end Hierarchy.DescentSixParty.GroupStage

end OAI
