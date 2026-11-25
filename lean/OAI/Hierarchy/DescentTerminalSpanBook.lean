import OAI.Hierarchy.DescentTerminalSpanCounts
import OAI.Hierarchy.DescentTerminalBookedGates

namespace OAI
/-! # One marker per charged site identifies both occupied and unused rows -/
namespace Hierarchy.DescentTerminalSpanBook
open DescentTerminalBinPack DescentTerminalRecipeRows DescentTerminalLocalPortBook
open scoped BigOperators Classical
noncomputable section
variable {S W q cap : ℕ} (sites : Fin S→Site) (fit : ∀i,(sites i).rows q≤W)
local notation "C" => counts (q:=q) sites
local notation "K" => Bins (W:=W) (q:=q) sites
local notation "start" => first W C
theorem «matches» (pos : 0<W) (p : Fin (cap*W)) :
    resolve (q:=q) sites fit p.val = fixedSpan (q:=q) (K₀:=cap) sites pos fit p := by
  apply Option.ext
  rintro ⟨v,u⟩
  rw [resolve_iff]
  obtain ⟨⟨b,r⟩,rfl⟩:=finProdFinEquiv.surjective p
  simp only [fixedSpan,Equiv.symm_apply_apply]
  by_cases h:b.val<K
  · simp only [dite_eq_left h,Option.map_eq_some_iff]
    let bin : Fin K := ⟨b.val,h⟩
    have flatten (j : Fin (C v)) : finProdFinEquiv (physical (q:=q) sites pos ⟨v,j⟩) =
        rowIndex pos C ⟨v,j⟩ :=
      (finProdFinEquiv (m:=K) (n:=W)).apply_symm_apply (rowIndex pos C ⟨v,j⟩)
    have flat (j : Fin (C v)) : physical (q:=q) sites pos ⟨v,j⟩ = (bin,r) ↔
        (finProdFinEquiv (b,r)).val = start v + j.val := by
      constructor
      · intro loc
        have index := (flatten j).symm.trans (congrArg finProdFinEquiv loc)
        have ordinal := congrArg Fin.val index
        exact ordinal.symm
      · intro value
        apply finProdFinEquiv.injective
        exact (flatten j).trans (Fin.ext value.symm)
    constructor
    · rintro ⟨j,hp,hu⟩
      exact ⟨⟨v,j⟩,(home_iff (q:=q) sites pos bin r ⟨v,j⟩).2 ((flat j).2 hp),
        Prod.ext rfl (Fin.ext hu.symm)⟩
    · rintro ⟨⟨i,j⟩,hh,same⟩
      obtain ⟨rfl,hs⟩:=Prod.mk.inj same
      have loc := (home_iff (q:=q) sites pos bin r ⟨_,j⟩).1 hh
      have slot : (j.castLE (fit _)).val = u.val := congrArg Fin.val hs
      exact ⟨j,(flat j).1 loc,slot.symm⟩
  · rw [dite_eq_right h]
    constructor
    · rintro ⟨j,hp,_⟩
      have bound := (rowIndex pos C ⟨v,j⟩).isLt
      change start v + j.val < K * W at bound
      have far := Nat.mul_le_mul_right W (Nat.le_of_not_gt h)
      change r.val + W * b.val = start v + j.val at hp
      rw [Nat.mul_comm W b.val] at hp
      exact False.elim (by omega)
    · intro missing
      cases missing

end
end Hierarchy.DescentTerminalSpanBook

end OAI
