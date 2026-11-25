import OAI.Hierarchy.DescentResetRetainedDecoder
import OAI.Hierarchy.DescentRetainedPrimitiveMover

namespace OAI
/-! # An authentic per-terminal mask and ordered donor packet for a reset -/
namespace Hierarchy.DescentResetRetainedSetup.Layout
open DescentSIMDLookup DescentOrdinaryAtomFieldRAM
open scoped Classical BigOperators Fin.CommRing
noncomputable section
variable (v : Layout)

/-- Each prior GL output names an old donor. Its rank is measured by the
original comparator on pairs of low coordinates from the selected window. -/
def donorRank (prior : Fin v.donors→Fin v.donors→Bool) (d : Fin v.donors) :=
  (Finset.univ.filter fun x=>prior x d).card

def routedDigit (accept : Fin v.donors→Bool) (prior : Fin v.donors→Fin v.donors→Bool)
    (word : Cell v.siteWord) (slot : Fin v.donors) (n : Fin v.previousNodes) (f : Fin v.fields) : Cell v.bits :=
  ∑d : Fin v.donors,if accept d=true ∧ v.donorRank prior d=slot.val then v.entry word d n f else 0

def routedWord (accept : Fin v.donors→Bool) (prior : Fin v.donors→Fin v.donors→Bool) (word : Cell v.siteWord) : Cell v.siteWord :=
  encode v.stripWord v.channels fun c=>encode v.bits v.donors fun slot=>
    let p : Fin v.fields×Fin v.previousNodes:=finProdFinEquiv.symm c
    v.routedDigit accept prior word slot p.2 p.1

def homeWord (which : ℕ) (stencil : Fin v.donors→ℕ) (prior : Fin v.donors→Fin v.donors→Bool) (word : Cell v.siteWord) :=
  v.routedWord (fun d=>decide (stencil d/2=which)) prior word

variable (accept : Fin v.donors→Bool) (prior : Fin v.donors→Fin v.donors→Bool)
    (order : Fin v.donors≃Fin v.donors) (rank : ∀d,v.donorRank prior d=(order d).val) (word : Cell v.siteWord)
local notation "out" => v.routedWord accept prior word

private theorem entry_encoded (row : Fin v.channels → Fin v.donors → Cell v.bits)
    (d : Fin v.donors) (n : Fin v.previousNodes) (f : Fin v.fields) :
    v.entry (encode v.stripWord v.channels (fun j => encode v.bits v.donors (row j))) d n f =
      row (finProdFinEquiv (f,n)) d := by
  let j : Fin v.channels := finProdFinEquiv (f,n)
  have outer := congrFun ((encode v.stripWord v.channels).symm_apply_apply
    (fun i => encode v.bits v.donors (row i))) j
  exact (congrArg (fun w => (encode v.bits v.donors).symm w d) outer).trans
    (congrFun ((encode v.bits v.donors).symm_apply_apply (row j)) d)

include rank
theorem routed_digit (d : Fin v.donors) (n : Fin v.previousNodes) (f : Fin v.fields) :
    v.routedDigit accept prior word (order d) n f=if accept d then v.entry word d n f else 0:=by
  unfold routedDigit
  rw [Finset.sum_eq_single d]
  · simp [rank]
  · intro j _ different
    have no:(order j).val≠(order d).val:=fun eqn=>different (order.injective (Fin.ext eqn))
    simp [rank,no]
  · simp

theorem routed_entry (d : Fin v.donors) (n : Fin v.previousNodes) (f : Fin v.fields) :
    v.entry out (order d) n f=if accept d then v.entry word d n f else 0:=by
  unfold routedWord
  rw [v.entry_encoded]
  simp only [Equiv.symm_apply_apply]
  exact v.routed_digit accept prior order rank word d n f

theorem routed_count (d : Fin v.donors) :
    v.originalCount out (order d)=if accept d then v.originalCount word d else 0:=by
  cases ok:accept d <;> simp only [originalCount,v.routed_entry accept prior order rank word,ok,Bool.false_eq_true,ite_false,ite_true]
  all_goals simp

theorem routed_offset (d : Fin v.donors) :
    v.offset out (order d)=∑j : Fin v.donors,
      if (order j).val<(order d).val ∧ accept j=true then v.originalCount word j else 0:=by
  unfold offset ProtocolRAMPortRanks.«prefix»
  rw [Finset.sum_filter,←order.sum_comp]
  apply Finset.sum_congr rfl
  intro j _
  rw [v.routed_count accept prior order rank word]
  by_cases small : (order j).val<(order d).val <;>cases eqn:accept j <;>simp [small]

theorem routed_old_field (d : Fin v.donors) (n : Fin v.previousNodes) (j : Fin v.previousArgs) (f : Fin 7)
    (active : accept d=true) (live : n.val<v.originalCount word d) (present : j.val<(v.entry word d n v.arityField).val) :
    v.rawField out (v.offset out (order d)+n.val) j.val f=v.entry word d n (v.operandField f j):=by
  have ln:n.val<v.originalCount out (order d):=by simpa only [v.routed_count accept prior order rank word,active,ite_true] using live
  have ar:j.val<(v.entry out (order d) n v.arityField).val:=by simpa only [v.routed_entry accept prior order rank word,active,ite_true] using present
  rw [v.cell_read out (order d) n j f ln ar,v.routed_entry accept prior order rank word,ite_eq_left active]

omit rank in
theorem original_rank (order : Fin v.donors≃Fin v.donors)
    (correct : ∀i j,prior i j=decide ((order i).val<(order j).val)) (d : Fin v.donors) :
    v.donorRank prior d=(order d).val:=by
  classical
  have eqn : (Finset.univ.filter (fun j=>prior j d)).map order.toEmbedding=Finset.Iio (order d):=by
    ext y
    constructor
    · intro hy
      obtain ⟨x,hx,rfl⟩:=Finset.mem_map.mp hy
      simpa [correct] using (Finset.mem_filter.mp hx).2
    · intro hy
      apply Finset.mem_map.mpr
      exact ⟨order.symm y,Finset.mem_filter.mpr ⟨Finset.mem_univ _,by simpa [correct] using hy⟩,order.apply_symm_apply _⟩
  simpa [donorRank] using congrArg Finset.card eqn

end
end Hierarchy.DescentResetRetainedSetup.Layout

end OAI
