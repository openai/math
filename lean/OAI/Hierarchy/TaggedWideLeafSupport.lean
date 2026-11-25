import OAI.Hierarchy.ProtocolStackContraction
import OAI.Hierarchy.TaggedWideReportGrouping

namespace OAI
/-! # Which physical positive-bank pins may carry a true payload bit -/

noncomputable section
namespace Hierarchy.Tagged.WideStack.Leaf
open ProtocolStackContraction
open scoped Classical BigOperators
variable {G : Type} [Fintype G] {D w : ℕ} {c : G→ℕ}
    (place : ∀g,Bool→Fin (c g) ↪ Fin D) (live : Edge c→Fin w→Prop)

def Supported (x : Slot G D → Fin w → Bool) : Prop :=
  (∀b i j,x (none,b,i) j=false) ∧
    ∀g b i j,x (some g,b,i) j=true → ∃u,place g b u=i ∧ live ⟨g,u⟩ j

omit [Fintype G] in
theorem padding_of_supported {x : Slot G D → Fin w → Bool} (ok : Supported place live x) :
    Padding place (fun _=>false) x := by
  refine ⟨fun b i=>funext (ok.1 b i),?_⟩
  intro g b i outside
  funext j
  cases bit : x (some g,b,i) j with
  | false => rfl
  | true =>
    obtain ⟨u,atPin,_⟩ := ok.2 g b i j bit
    exact (outside ⟨u,atPin⟩).elim

omit [Fintype G] in
theorem supported_encode (a : Edge c → Fin w → Bool) :
    Supported place live (encode place (fun _=>false) a) ↔ ∀e j,a e j=true → live e j := by
  constructor
  · intro ok e j bit
    obtain ⟨g,u⟩ := e
    have pin := encode_active place (fun _ : Fin w=>false) a g false u
    obtain ⟨v,hv,below⟩ := ok.2 g false _ j ((congrFun pin j).trans bit)
    obtain rfl := (place g false).injective hv
    exact below
  · intro ok
    refine ⟨fun _ _ _=>rfl,?_⟩
    intro g b i j bit
    by_cases used : i∈Set.range (place g b)
    · obtain ⟨u,rfl⟩ := used
      refine ⟨u,rfl,ok _ j ?_⟩
      simpa only [encode_active] using bit
    · have blank := (encoded_valid place (fun _ : Fin w=>false) a).1.2 g b i used
      have bad := (congrFun blank j).symm.trans bit
      contradiction

theorem fixedSlot_mod {ports lanes D : ℕ} (fit : ports*lanes≤D) (p : Fin ports) (u : Fin lanes) :
    (fixedSlot fit (p,u)).val%lanes=u.val := by
  change (u.val+lanes*p.val)%lanes=u.val
  rw [Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt u.isLt]

omit [Fintype G] in
/-- The support relation measured by the hardware uses only the absolute
location modulo the reserved lane count. At an occupied common ID this is
the actual subslot ordinal. -/
theorem stored_supported (lanes : ℕ) (length : Edge c→ℕ)
    (digit : Edge c→ℕ) (offset : ∀g b u,(place g b u).val%lanes=digit ⟨g,u⟩)
    (x : Slot G D → Fin w → Bool) :
    ((∀b i j,x (none,b,i) j=false) ∧
      ∀g b i j,x (some g,b,i) j=true → ∃u,place g b u=i ∧ i.val%lanes*w+j.val<length ⟨g,u⟩) ↔
      Supported place (fun e j=>digit e*w+j.val<length e) x := by
  constructor <;> rintro ⟨idle,active⟩ <;> refine ⟨idle,?_⟩ <;> intro g b i j bit
  · obtain ⟨u,rfl,h⟩ := active g b i j bit
    exact ⟨u,rfl,by simpa only [offset] using h⟩
  · obtain ⟨u,rfl,h⟩ := active g b i j bit
    exact ⟨u,rfl,by simpa only [offset] using h⟩

end Hierarchy.Tagged.WideStack.Leaf

end
end OAI
