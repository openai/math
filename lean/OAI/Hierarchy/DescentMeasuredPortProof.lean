import OAI.Hierarchy.DescentMeasuredPortTapes

namespace OAI
/-! # Native reset depths, gains and loads on every row of the physical rectangle -/

namespace Hierarchy.DescentMeasuredWeights
open DescentColonies DescentPackedExchange DescentGL
open scoped Classical BigOperators
noncomputable section
variable {V : Type} [Fintype V] [DecidableEq V] {H Δ k : ℕ}
variable (idx : V≃Fin H) (near : V→Finset V) (cap : ∀v,(near v).card≤Δ)
    (b : V→ℕ)
local notation "item" => Item (inputLevels (k:=k) b) (Contacts near)
local notation "row" => portRow (k:=k) idx near cap b
local notation "port" => atPort idx near cap
local notation "next" => neighborSlot (degree:=Δ) idx near

private def rowLevel (v : V) (s : Fin (inputLevels (k:=k) b v)) : Fin (k+1) :=
  ⟨s.val,by have h:=s.isLt;dsimp [inputLevels] at h;omega⟩

omit [DecidableEq V] in
private theorem agree {α : Type} (blank : α) (physical : Rows H k Δ→α) (value : item→α)
    (site : ∀v (s : Fin (inputLevels (k:=k) b v)),
      physical (.inl (idx v,rowLevel b v s))=value (.inl ⟨v,s⟩))
    (contact : ∀c : Contacts near,physical (.inr (port c))=value (.inr c))
    (idleLevel : ∀v (s : Fin (k+1)),¬b (idx.symm v)+s.val≤k → physical (.inl (v,s))=blank)
    (idlePort : ∀p, (¬∃c,port c=p) → physical (.inr p)=blank)
    (t : Rows H k Δ) : physical t=padded row value blank (rowOrd H k Δ t) := by
  by_cases live : ∃a : item,row a=rowOrd H k Δ t
  · obtain ⟨a,matchRow⟩:=live
    rw [←matchRow,padded_at]
    rcases a with ⟨v,s⟩|c
    · have found : Sum.inl (idx v,rowLevel b v s)=t :=
        (rowOrd H k Δ).injective ((site_row idx near cap b v s).symm.trans matchRow)
      rw [←found]
      exact site v s
    · have found : Sum.inr (port c)=t :=
        (rowOrd H k Δ).injective ((port_row idx near cap b c).symm.trans matchRow)
      rw [←found]
      exact contact c
  · rw [padded_else row value blank _ live]
    rcases t with ⟨v,s⟩|p
    · apply idleLevel
      intro enabled
      let src:=idx.symm v
      let d : Fin (inputLevels (k:=k) b src):=⟨s.val,by dsimp [inputLevels,src];omega⟩
      have found : ((idx src,rowLevel b src d):Fin H×Fin (k+1))=(v,s) :=
        Prod.ext (idx.apply_symm_apply _) (Fin.ext rfl)
      exact live ⟨.inl ⟨src,d⟩,(site_row idx near cap b src d).trans
        (congrArg (fun a=>rowOrd H k Δ (Sum.inl a)) found)⟩
    · apply idlePort
      rintro ⟨c,rfl⟩
      exact live ⟨.inr c,port_row idx near cap b c⟩

variable (hk : ∀v,b v≤k)
include hk

omit [DecidableEq V] in
theorem depth_padded (t : Rows H k Δ) :
    realDepth (b ∘idx.symm) next t =
      padded row (level (inputLevels b) (inputDepth b) (pairDepth near b)) 0 (rowOrd H k Δ t) := by
  apply agree idx near cap b
  · intro v s
    have hi : b v+s.val≤k:=inputFits b hk v s
    simp [realDepth,rowLevel,level,inputDepth,hi]
  · intro c
    rw [realDepth,atPort_read]
    change max (b (idx.symm (idx c.1))) (b (idx.symm (idx c.2.val))) =
      max (b c.1) (b c.2.val)
    rw [idx.symm_apply_apply,idx.symm_apply_apply]
  · intro v s idle
    simp [realDepth,idle]
  · intro p idle
    rw [realDepth,unlisted idx near cap p idle]; rfl

omit [DecidableEq V] in
theorem gain_padded (f B K : ℕ) (t : Rows H k Δ) :
    realGain (b ∘idx.symm) next f B K t =
      padded row (gain (inputLevels b) f B K) 0 (rowOrd H k Δ t) := by
  apply agree idx near cap b
  · intro v s
    have hi : b v+s.val≤k:=inputFits b hk v s
    simp [realGain,rowLevel,gain,hi]
  · intro c
    rw [realGain,atPort_read]; rfl
  · intro v s idle
    simp [realGain,idle]
  · intro p idle
    rw [realGain,unlisted idx near cap p idle]; rfl

omit [DecidableEq V] in
theorem load_padded (sites : Fin H→Bits k→ℕ) (flow : Port H Δ→Bits k→ℕ)
    (x : V→Bits k→ℕ) (y : Contacts near→Bits k→ℕ) (siteRead : ∀v,sites (idx v)=x v)
    (trafficRead : ∀c,flow (port c)=y c) (t : Rows H k Δ) :
    realLoad (b ∘idx.symm) next sites flow t =
      padded row (load (inputLevels b) x y) (fun _=>0) (rowOrd H k Δ t) := by
  apply agree idx near cap b
  · intro v s
    have hi : b v+s.val≤k:=inputFits b hk v s
    simpa [realLoad,rowLevel,load,Function.comp_def,hi] using siteRead v
  · intro c
    rw [realLoad,atPort_read]
    exact trafficRead c
  · intro v s idle
    simp [realLoad,idle]
  · intro p idle
    rw [realLoad,unlisted idx near cap p idle]; rfl

end
end Hierarchy.DescentMeasuredWeights

end OAI
