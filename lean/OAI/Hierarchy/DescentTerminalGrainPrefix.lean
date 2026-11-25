import OAI.Hierarchy.DescentTerminalPointerDigits
import OAI.Hierarchy.DescentTerminalPortChart
import OAI.Hierarchy.DescentSharedCableSiblings
import OAI.Hierarchy.DescentTerminalGraphPurchase

namespace OAI
/-! # Counting the true p-word starts in the final signed cable shelf -/
namespace Hierarchy.DescentTerminalPointerDigits
open DescentSixParty DescentSharedCableNames DescentKernelHistory DescentTerminalPortChart
open DescentCompiler DescentColonies
open scoped Classical BigOperators
noncomputable section
variable {F P J V : Type} [Field F] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
    {d k i : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F} {q ε : ℝ}
    (A : GroupStage W G q ε J V k) (native : W.graph.Edge↪ℕ) (S : AtomSchedule) (ready : A.StateBounds S i)
    (names : Stage.Host J V k↪ℕ) (v : W.graph.Site)
local notation "h" => Stage.home A v
local notation "B" => Stage.source A native
local notation "live" => Stage.live A native S ready names h
local notation "signed" => Stage.signedPanel A native S ready names h
local notation "key" => label A native S ready names v
local notation "count" => A.grainCount

abbrev SiteGrains := Σe : Incident W.graph v,Fin (count e.val)
def token : SiteGrains A v↪ℕ×ℕ where
  toFun u:=(key u.1 (Nat.zero_lt_of_lt u.2.isLt),u.2.val)
  inj' := by
    rintro ⟨e,j⟩ ⟨f,l⟩ eqn
    have edge:=label_injective A native S ready names v e f (Nat.zero_lt_of_lt j.isLt) (Nat.zero_lt_of_lt l.isLt)
      (Fin.ext (congrArg Prod.fst eqn))
    subst f
    exact congrArg (Sigma.mk e) (Fin.ext (congrArg Prod.snd eqn))

private theorem recovered (u : A.CellPorts h.1.1 h.1.2 h.2) :
    (Stage.ofPort A native h u).val=Stage.stream A native (Stage.recover A h u) := by cases u <;> rfl

private theorem serial_at_end {T : Type} [DecidableEq T] {n : ℕ} (ends : Ends T n)
    (row : Fin n) (point : T) (hit : ends.src row=point ∨ ends.dst row=point) :
    ends.serial point (ends.peer point row) row=ends.serial (ends.src row) (ends.dst row) row := by
  rcases hit with rfl|rfl
  · simp [Ends.peer]
  · by_cases loop : ends.src row=ends.dst row
    · simp [Ends.peer,loop]
    · simpa only [Ends.peer,ite_eq_right loop] using (ends.both_ends row).symm

private theorem serial (u : A.CellPorts h.1.1 h.1.2 h.2) (e : Incident W.graph v) (j : Fin (count e.val))
    (same : Stage.recover A h u=⟨e.val,j⟩) :
    (live u).wire.val=Siblings.shared A native ⟨e.val,j⟩ := by
  change (B).serial h ((B).peer h (Stage.ofPort A native h u).val) (Stage.ofPort A native h u).val=_
  rw [recovered A native v u,same]
  let row:=Stage.stream A native (⟨e.val,j⟩ : Stage.Grain A)
  have src : (B).src row=Stage.home A (W.graph.src e.val) := by
    simp only [row,Stage.source,Equiv.symm_apply_apply]
  have dst : (B).dst row=Stage.home A (W.graph.dst e.val) := by
    simp only [row,Stage.source,Equiv.symm_apply_apply]
  have hit : (B).src row=h ∨ (B).dst row=h := e.property.imp
    (fun eqn=>src.trans (congrArg (Stage.home A) eqn))
    (fun eqn=>dst.trans (congrArg (Stage.home A) eqn))
  change (B).serial h ((B).peer h row) row =
    (B).serial (Stage.home A (W.graph.src e.val)) (Stage.home A (W.graph.dst e.val)) row
  rw [←src,←dst]
  exact serial_at_end B row h hit

theorem grain_read (u : A.CellPorts h.1.1 h.1.2 h.2) (e : Incident W.graph v) (j : Fin (count e.val))
    (same : Stage.recover A h u=⟨e.val,j⟩) :
    grain (live u)=token A native S ready names v ⟨e,j⟩ := by
  let pos:=Nat.zero_lt_of_lt j.isLt
  let head:=first A v e pos
  have base : Stage.recover A h head=⟨e.val,⟨0,pos⟩⟩ := by unfold head first;split <;> rfl
  have step: (live u).wire.val=(live head).wire.val+j.val := by
    rw [serial A native S ready names v u e j same,serial A native S ready names v head e ⟨0,pos⟩ base,Siblings.within]
  have piece : (live u).within.val=j.val := congrArg (fun z : Stage.Grain A=>z.2.val) same
  have peer : (live u).neighbor=(live head).neighbor := by
    apply ((Stage.neighbors A native names).same h _ _).2
    rw [recovered A native v u,recovered A native v head,same,base]
    simp [Ends.peer,Stage.source]
  apply Prod.ext
  · change (live u).neighbor.val*A.cap+((live u).wire.val-(live u).within.val)=(finProdFinEquiv ((live head).neighbor,(live head).wire)).val
    rw [piece,peer,step,finProdFinEquiv_apply_val]
    simp [Nat.add_comm,Nat.mul_comm]
  · exact piece

variable (coords : Function.Injective (fun s=>(A.pos s,A.block s)))
include coords

theorem grains_exact : grains signed=Finset.univ.map (token A native S ready names v) := by
  ext t
  rw [grains,on_panel,Finset.mem_map]
  constructor
  · rintro ⟨j,output⟩
    by_cases hit : ∃u,Stage.signed A native S ready h.1 h.2 u=j
    · obtain ⟨u,rfl⟩:=hit
      rw [Stage.signed_read,Option.map_some,Option.some.injEq] at output
      rcases u with ⟨⟨e,ep,eb⟩,l⟩|⟨⟨e,ep,eb⟩,l⟩
      · let edge : Incident W.graph v:=⟨e,Or.inl (coords (Prod.ext ep eb))⟩
        exact ⟨⟨edge,l⟩,Finset.mem_univ _,(grain_read A native S ready names v _ edge l rfl).symm.trans output⟩
      · let edge : Incident W.graph v:=⟨e,Or.inr (coords (Prod.ext ep eb))⟩
        exact ⟨⟨edge,l⟩,Finset.mem_univ _,(grain_read A native S ready names v _ edge l rfl).symm.trans output⟩
    · rw [Stage.signed_empty _ _ _ _ _ _ _ (not_exists.mp hit)] at output
      contradiction
  · rintro ⟨⟨e,j⟩,_,rfl⟩
    rcases e.property with atSrc|atDst
    · let u : A.CellPorts h.1.1 h.1.2 h.2:=.inl ⟨⟨e.val,congrArg A.pos atSrc,congrArg A.block atSrc⟩,j⟩
      exact ⟨Stage.signed A native S ready h.1 h.2 u,by rw [Stage.signed_read,Option.map_some,grain_read A native S ready names v u e j rfl]⟩
    · let u : A.CellPorts h.1.1 h.1.2 h.2:=.inr ⟨⟨e.val,congrArg A.pos atDst,congrArg A.block atDst⟩,j⟩
      exact ⟨Stage.signed A native S ready h.1 h.2 u,by rw [Stage.signed_read,Option.map_some,grain_read A native S ready names v u e j rfl]⟩

theorem lower_grains (stop : ℕ) (pin : Attached W.graph v↪ℕ) :
    lower (grains signed) stop=∑e : Incident W.graph v,
      if rank A native S ready names v pin (.inl e) < stop then count e.val else 0 := by
  unfold lower
  rw [grains_exact A native S ready names v coords,Finset.filter_map,Finset.card_map,
    Finset.card_eq_sum_ones]
  classical
  simp only [Finset.sum_filter,Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro e _
  by_cases pos : 0 < count e.val
  · rw [positive_rank _ _ _ _ _ _ pin e pos]
    change (∑ _ : Fin (count e.val), if (key e pos).val < stop then (1 : ℕ) else 0) =
      if (key e pos).val < stop then count e.val else 0
    by_cases small : (key e pos).val < stop <;> simp [small]
  · have zero : count e.val=0:=by omega
    have : IsEmpty (Fin (count e.val)) := ⟨fun j=>by have := j.isLt;omega⟩
    rw [Finset.sum_of_isEmpty]
    simp [zero]

theorem all_grains : (grains signed).card=∑e : Incident W.graph v,count e.val := by
  rw [grains_exact A native S ready names v coords,Finset.card_map,Finset.card_univ]
  simp [SiteGrains,Fintype.card_sigma]

end
end Hierarchy.DescentTerminalPointerDigits

end OAI
