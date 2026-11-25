import OAI.Hierarchy.GridOrderedDataRAM
import OAI.Hierarchy.GridThroughOrdered
import OAI.Hierarchy.GridThroughScheduled
import OAI.Hierarchy.GridThroughIdle
import OAI.Hierarchy.GridWiringNetwork

namespace OAI
/-! # Native scatter addresses of a tick assignment -/

namespace Hierarchy.GridOrderedPinOrigins
open GridThrough GridThrough.Ordered GridOrderedDataRAM
open ThreeFlat.RAM Computability.VPVNP.BurstRAM
open scoped Fin.CommRing

variable {r k n q d w : ℕ} (A : PinAssignment (Fin r) k n q d)

def endpoint (i : Fin (r*2)) : Touch A.touch × Bool :=
  let u := sides.symm i
  (⟨(u.1,A.row u.1 (A.direction u.1)),rfl⟩,u.2)

def address (i : Fin (r*2)) : Fin ((n+1)^k*(q*d)) := dataCode (A.dest (endpoint A i))

theorem address_val (e : Fin r) (b : Bool) :
    (address A (sides (e,b))).val =
      (finFunctionFinEquiv (A.row e)).val*(q*d)+(A.tick e).2.val*d+(A.slot (e,b)).val := by
  simp only [address,endpoint,Equiv.symm_apply_apply]
  change (finProdFinEquiv (finFunctionFinEquiv (A.row e),
    finProdFinEquiv ((A.tick e).2,A.slot (e,b)))).val = _
  simp only [finProdFinEquiv_apply_val]
  ring

theorem address_injective : Function.Injective (address A) := by
  intro i j same
  have eq := A.dest.injective (dataCode.injective same)
  have ij : sides.symm i = sides.symm j := congrArg (fun z : Touch A.touch × Bool => (z.1.val.1,z.2)) eq
  exact sides.symm.injective ij

def slot (i : ℕ) : ℕ :=
  if h : i < r*2 then (address A ⟨i,h⟩).val else 0

def centerBase (r n : ℕ) := 2+r*2+r*((n+1)*2)

noncomputable def value (c : Cell k n) (i : Fin (q*d)) : ℕ :=
  (A.data c i).elim (fun z => centerBase r n+(sides (z.1.val.1,z.2)).val) Bool.toNat

/-- Every data-bank read after the actual RAM loop equals the intended
center source or literal. Distinct endpoint destinations come from fresh
slots in the actual receiving tick. -/
theorem prepared_at (S : GridOrderedDataRAM.Banks) (m : Memory w) (c : Cell k n) (i : Fin (q*d))
    (base : S.center=centerBase r n)
    (literal : ∀ a : Cell k n × Fin (q*d), m (S.literal+(dataCode a).val) =
      ((A.literal a).toNat:Word w)) :
    prepared S ((n+1)^k*(q*d)) (r*2) (slot A) m (S.data+(dataCode (c,i)).val) =
      (value A c i:Word w) := by
  classical
  let init := PhysicalInputCopy.copied S.literal ((n+1)^k*(q*d)) S.data m
  change image S (slot A) init (r*2) _ = _
  cases h : A.data c i with
  | inl z =>
    let j : Fin (r*2) := sides (z.1.val.1,z.2)
    have id : endpoint A j=z := by
      simp only [endpoint,j,Equiv.symm_apply_apply]
      exact Prod.ext (Subtype.ext (Prod.ext rfl (Option.some.inj z.1.property))) rfl
    have assigned : A.dest z=(c,i) := (pinSource_inl ..).mp h
    have addr : slot A j.val=(dataCode (c,i)).val := by
      simp [slot,j.isLt,address,id,assigned]
    rw [← addr,image_hit S (slot A) init (r*2) j.val j.isLt (by
      intro t ht same
      have equal : address A ⟨t,ht⟩=address A j := Fin.ext (by simpa [slot,ht,j.isLt] using same)
      exact congrArg Fin.val (address_injective A equal))]
    simp [value,h,base,j]
  | inr b =>
    have absent : ∀ u, A.dest u≠(c,i) := by
      intro z same
      have on : A.data c i=.inl z := (pinSource_inl ..).mpr same
      rw [h] at on
      cases on
    have bh : b=A.literal (c,i) := Sum.inr.inj (h.symm.trans (pinSource_unused _ _ _ absent))
    rw [image_unchanged S (slot A) init (r*2) _ (by
      intro t ht eq
      have hit : dataCode (c,i)=address A ⟨t,ht⟩ :=
        Fin.ext (by simpa [slot,ht] using Nat.add_left_cancel eq)
      exact absent _ (dataCode.injective hit).symm)]
    dsimp only [init]
    rw [PhysicalInputCopy.copied_at _ _ _ _ _ (dataCode (c,i)).isLt,literal]
    simp [value,h,bh]

/-- The origin computed by the scatter is precisely the source pointer of a
copy of the controller built from this schedule. -/
theorem scheduled_value (width : Fin k → ℕ)
    (count : Fin k → GridTicks.Tick k (n+1) q → ℕ)
    (conservation : ∀ j t, (GridTicks.pairFiber A.direction (fun e => GridTicks.index (A.tick e)) j t).card=count j t)
    (enough : ∀ x j, width j ≤ ((GridTicks.pairsOn (count j) (GridTicks.lineTicks j x)) \
      (GridTicks.pairsOn (count j) (GridTicks.cellTicks x))).card)
    (c : Cell k n) (i : Fin (q*d)) :
    let P := GridThrough.Program.ofScheduled A width count conservation enough
    value A c i=BitLayout.sourceAddress (UniversalGrid.Wiring.source (sourcePin P P.data c (.inl i))) := by
  dsimp only
  change value A c i = BitLayout.sourceAddress (UniversalGrid.Wiring.source
    ((A.data c i).elim (fun z => center (n:=n) z.1.val.1 z.2) (fun b => Sum.inr (Sum.inr b))))
  cases h : A.data c i with
  | inr b => simp [value,h,UniversalGrid.Wiring.source,BitLayout.sourceAddress]
  | inl u =>
    simp [value,h,centerBase,exterior_number,UniversalGrid.Wiring.source,BitLayout.sourceAddress,
      center,center_number,BitLayout.hiddenBase]
    omega

/-- With no touched endpoints, the native copy leaves all data pins at their
literal values, including an idle controller's pins. -/
theorem idle_value {p : ℕ} {width : Fin k → ℕ}
    (P : GridThrough.Program (Fin r) n p width) (literal : Cell k n → Fin p → Bool)
    (S : GridOrderedDataRAM.Banks) (m : Memory w) (c : Cell k n) (i : Fin p)
    (bits : ∀ v : Cell k n × Fin p, m (S.literal+(dataCode v).val)=((literal v.1 v.2).toNat:Word w)) :
    let idle := P.idle literal
    prepared S ((n+1)^k*p) 0 (fun _ => 0) m (S.data+(dataCode (c,i)).val) =
      (BitLayout.sourceAddress (UniversalGrid.Wiring.source (sourcePin idle idle.data c (.inl i))):Word w) := by
  dsimp only [prepared,image]
  rw [PhysicalInputCopy.copied_at _ _ _ _ _ (dataCode (c,i)).isLt,bits]
  rfl

theorem scatter_cost (S : GridOrderedDataRAM.Banks)
    (nf : r*2 < 2^w) (dstFit : S.dest+r*2 ≤ 2^w) (dataFit : S.data+(n+1)^k*(q*d) < 2^w)
    (litFit : S.literal+(n+1)^k*(q*d) < 2^w)
    (away : S.data+(n+1)^k*(q*d) ≤ S.dest ∨ S.dest+r*2 ≤ S.data)
    (input : S.data ≤ S.literal ∨ S.literal+(n+1)^k*(q*d) ≤ S.data) :
    (prepare w S ((n+1)^k*(q*d)) (r*2)).Spec
      (fun m => ∀ i < r*2,m (S.dest+i)=(slot A i:Word w))
      (fun m o => o=prepared S ((n+1)^k*(q*d)) (r*2) (slot A) m)
      (9+5*((n+1)^k*(q*d))+11*(r*2)) :=
  prepare_spec S _ _ _ nf dstFit dataFit litFit (fun i hi => by simp [slot,hi]) away input

end Hierarchy.GridOrderedPinOrigins

end OAI
