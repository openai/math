import OAI.Hierarchy.TaggedWidePadding
import OAI.Hierarchy.TaggedShorterSlotWidth
import OAI.ThreeFlat.Diagonal.TraceBanks

namespace OAI
/-! # Direct zero suffix tests from the native stored slot widths -/

noncomputable section
namespace Hierarchy.Tagged.WidePadding
open ThreeFlat Routing Diagonal TraceWords TraceBanks
open Computability.VPVNP.BurstRAM TaggedShorterSlotWidth
open scoped Classical BigOperators
variable {F V : Type*} [Fintype V] {b W n groups D : ℕ} {c : Fin groups→ℕ}

/-- The native publisher's zero default also rules out every unused data
pin. Only a constant true wire is needed for the padding circuit's flag. -/
theorem stored_live (pl : ∀g,Bool→Fin (c g) ↪ Fin D) (width : Transport c→ℕ)
    (s : Slot groups D) (col : ℕ) :
    col<value pl width s ↔ ∃u : Fin (c s.1),pl s.1 s.2.1 u=s.2.2 ∧ col<width ⟨s.1,u⟩ := by
  rcases s with ⟨g,side,i⟩
  constructor
  · intro above
    by_cases used : i∈Set.range (pl g side)
    · obtain ⟨u,rfl⟩ := used
      exact ⟨u,rfl,by simpa only [value_live pl width (⟨g,u⟩ : Transport c) side] using above⟩
    · rw [value_blank pl width (g,side,i) used] at above
      omega
  · rintro ⟨u,hit,short⟩
    change pl g side u=i at hit
    change col<width ⟨g,u⟩ at short
    rw [←hit,value_live pl width (⟨g,u⟩ : Transport c) side]
    exact short

/-- The genuine CPU observer exposes machine width plus one bits; the
suffix checker reads only the indicated low local-width bits. -/
theorem low_width (a : Word W) (v : ℕ) (echoed : a.val=v) (fits : v<2^b) (narrow : b≤W+1) (j : Fin b) :
    bits (wide a) (j.castLE narrow) = bits (⟨v,fits⟩ : Word b) j := by
  change (wide a).val.testBit j.val=v.testBit j.val
  change a.val.testBit j.val=v.testBit j.val
  rw [echoed]

/-- Activation of a true absolute physical payload column. Its static
subslot ordinal is obtained via remainder by the public lane count. -/
theorem stored_eval [CommRing F] (ports : Ports V n b) (x : V→Bool)
    (pl : ∀g,Bool→Fin (c g) ↪ Fin D) (width : Transport c→ℕ)
    (slot : Fin n→Slot groups D) (lanes field : ℕ) (sub : Fin n→Fin field)
    (col : ∀i,(ports.col i).val=(slot i).2.2.val%lanes*field+(sub i).val)
    (used : ∀i,x (ports.live i)=true)
    (out : Fin n→Word W) (reported : ∀i,(out i).val=value pl width (slot i))
    (fits : ∀i,value pl width (slot i)<2^b) (narrow : b≤W+1)
    (read : ∀i j,x (ports.width i j)=bits (wide (out i)) (j.castLE narrow)) :
    TypedWiring.value (ports.network (F:=F)) x =
      if ∀i,x (ports.payload i)=true →
        ∃u : Fin (c (slot i).1),pl (slot i).1 (slot i).2.1 u=(slot i).2.2 ∧
          (slot i).2.2.val%lanes*field+(sub i).val<width ⟨(slot i).1,u⟩ then 1 else 0 := by
  let small := fun i=>(⟨value pl width (slot i),fits i⟩ : Word b)
  rw [ports.eval x small (fun i j=>(read i j).trans (low_width (out i) _ (reported i) (fits i) narrow j))]
  have each (i : Fin n) : x (ports.live i)=true ∧ ports.col i<small i ↔
      ∃u : Fin (c (slot i).1),pl (slot i).1 (slot i).2.1 u=(slot i).2.2 ∧
        (slot i).2.2.val%lanes*field+(sub i).val<width ⟨(slot i).1,u⟩ := by
    simpa only [used i,true_and,Fin.lt_def,small,col i] using
      stored_live pl width (slot i) ((slot i).2.2.val%lanes*field+(sub i).val)
  simp only [each]

end Hierarchy.Tagged.WidePadding

end
end OAI
