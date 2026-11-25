import OAI.Hierarchy.DescentMixedRouter

namespace OAI
/-! # The shared physical quantum divides every concrete installed cable -/

namespace Hierarchy.DescentMixedRouter
open Computability.BorderVNP.Crossing DescentRouterSlots DescentRotor DescentBaseProfile
open LinearAlgebra.SpectralBooks ThreeFlat
open scoped BigOperators Classical
noncomputable section

private theorem split_width {d : ℕ} {P : Type} [Fintype P] {lens : P→ℕ} (N : Network d P lens)
    (u : ℕ) (edges : ∀e,u∣N.width e) (pins : ∀p,u∣lens p) (e : (DescentPhysicalSplit.graph N).Edge) :
    u∣(DescentPhysicalSplit.graph N).width e := by
  rcases e with e|⟨v,k⟩
  · exact edges e
  · change u ∣ ∑ i : Fin (DescentPhysicalSplit.count N v), DescentPhysicalSplit.localWidth N v i
    apply Finset.dvd_sum
    intro i _
    change u∣DescentPhysicalSplit.width N (DescentPhysicalSplit.name N v i)
    cases DescentPhysicalSplit.name N v i with
    | inl p => exact pins p
    | inr p => exact edges p.1

private theorem tree_width {A : Type} [Fintype A] (dest : A→ℕ→Bool) (weight : A→ℕ)
    (u d depth : ℕ) (divides : ∀a,u∣weight a) (e : (DescentContactTree.Physical.graph dest weight d depth).Edge) :
    u∣(DescentContactTree.Physical.graph dest weight d depth).width e := by
  apply Finset.dvd_sum
  intro i _
  exact divides i.val

variable {I C R W K : Type} [Fintype I] [Fintype C] [Fintype R] [Fintype W] [Field K]
variable {n h C₀ bits d : ℕ} (G : NonlinearExpanders.Graph n h) (hw : 0<bits)
variable (u : ℕ) (contact : I→C) (input : Bool→I→R) (site : Bool→R→W) (owner : Bool→C→W)
variable (align : ∀s i,site s (input s i)=owner s (contact i))
local notation "Ch" => Choice (K:=K) (C₀:=C₀) G hw u contact input site owner align
local notation "Device" => device (K:=K) (C₀:=C₀) G hw u contact input site owner align (D:=d)
local notation "weight" => fun _ : I=>u

omit [Fintype R] in
theorem device_quantum {s : Bool} {w : W} (c : Ch s w) (e : (Device c).Edge) : u∣(Device c).width e := by
  cases c with
  | exceptional data =>
    exact tree_width (DescentFixedNamedContact.code data.book.codes (link contact owner s w)) (amount contact owner weight s w)
      u d data.book.height (fun _=>dvd_refl _) e
  | good first last p circuit =>
    exact split_width (Physical.host G.arcs d circuit.layers C₀ bits u) u
      (fun _=>⟨circuit.layers*(C₀*bits),by change circuit.layers*(u*(C₀*bits))=u*_;ring⟩)
      (fun _=>⟨circuit.layers*bits,by ring⟩) e

omit [Fintype R] in
theorem quantum (chosen : ∀ s w, Ch s w)
    (e : (network (K:=K) (C₀:=C₀) G hw u contact input site owner align chosen d).Edge) :
    u ∣ (network (K:=K) (C₀:=C₀) G hw u contact input site owner align chosen d).width e := by
  rcases e with link|⟨⟨s,w⟩,e⟩
  · change u ∣ ∑ _i : DescentNamedContact.Fibre contact link, u
    apply Finset.dvd_sum
    exact fun _ _=>dvd_refl _
  · exact device_quantum G hw u contact input site owner align (chosen s w) e

omit [Fintype R] in
theorem public_quantum (p : Bool×R) : u∣DescentRouterBank.publicWidth input weight p := by
  apply Finset.dvd_sum
  exact fun _ _=>dvd_refl _

end
end Hierarchy.DescentMixedRouter

end OAI
