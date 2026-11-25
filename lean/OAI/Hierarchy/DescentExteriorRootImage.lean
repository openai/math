import OAI.Hierarchy.DescentExteriorVoteImage
import OAI.Hierarchy.DescentExteriorInitialWires

namespace OAI
/-! # One original input for the packed seed, chronological profiles, public exterior and both proposals -/
namespace Hierarchy.DescentExteriorShelf.Root
open DescentExterior DescentGL Computability.VPVNP.BurstRAM Computability.VPVNP.RAMMemory ThreeFlat.Diagonal
open scoped Classical
noncomputable section
variable {A : Type} {w e j r t : ℕ}
set_option quotPrecheck false
local notation "H" => span j r t e
local notation "Hidden_" => Hidden e j r t
local notation "Public_" => Public e j r t

abbrev Pin (A : Type) (e j r t : ℕ) := Public e j r t ⊕ (A⊕Hidden e j r t)

def assign (x : Fin e→ Plane j r→ Fin t→ Bool) (z : A⊕Hidden_→ Bool) : Pin A e j r t→ Bool :=
  Sum.elim (fun i=>x i.1.1 i.1.2 i.2) z

def pin (endLow origin : ℕ) (old : Fin endLow×Fin (w+1)→ A⊕Bool)
    (ij : Fin (origin+17*H)×Fin (w+1)) : Pin A e j r t⊕Bool :=
  if below : ij.1.val < origin then
    if used : ij.1.val < endLow then (old (⟨ij.1.val,used⟩,ij.2)).map (Sum.inr ∘ Sum.inl) id
    else .inr false
  else
    let i : Fin (17*H):=⟨ij.1.val-origin,by have :=ij.1.isLt;omega⟩
    (initialPin i ij.2).map (Sum.elim Sum.inl (Sum.inr ∘ Sum.inr)) id

theorem pin_read (endLow origin : ℕ) (wire : Fin endLow×Fin (w+1)→ A⊕Bool) (old : Memory w)
    (x : Fin e→ Plane j r→ Fin t→ Bool) (z : A⊕Hidden_→ Bool) (sep : endLow ≤ origin)
    (room : 2^j*t ≤ w)
    (bits : ∀i,Sum.elim (z∘Sum.inl) id (wire i)=TraceWords.bits (TraceBanks.wide (old i.1.val)) i.2)
    (ij : Fin (origin+17*H)×Fin (w+1)) :
    Sum.elim (assign x z) id (pin endLow origin wire ij)=TraceWords.bits
      (TraceBanks.wide (image endLow origin old x (z∘Sum.inr) ij.1.val)) ij.2 := by
  by_cases below : ij.1.val < origin
  · by_cases mem : ij.1.val < endLow
    · let loc : Fin endLow×Fin (w+1):=(⟨ij.1.val,mem⟩,ij.2)
      rw [pin,dite_eq_left below,dite_eq_left mem,low _ _ _ _ _ sep mem]
      have h:=bits loc
      change Sum.elim _ _ ((wire loc).map _ _)=_
      cases v : wire loc <;> simpa [v,assign,loc] using h
    · simp [pin,below,mem,image,staged,store,Nat.not_le_of_gt below,initialMemory,TraceWords.bits,TraceBanks.wide]
  · let v : Fin (17*H):=⟨ij.1.val-origin,by have :=ij.1.isLt;omega⟩
    have addr : origin+v.val=ij.1.val:=by dsimp [v];omega
    have h:=initial_read room origin (initialMemory endLow old) x (z∘Sum.inr) v ij.2
    rw [addr] at h
    rw [pin,dite_eq_right below]
    change Sum.elim _ _ ((initialPin v ij.2).map _ _)=_
    cases choice : initialPin v ij.2 with
    | inr b=>simpa [choice,image] using h
    | inl p=>cases p <;> simpa [choice,assign,readBit,image] using h

end
end Hierarchy.DescentExteriorShelf.Root

end OAI
