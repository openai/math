import OAI.ThreeFlat.Diagonal.RefreshKernel
import OAI.ThreeFlat.Diagonal.HistoryContraction

namespace OAI
/-! # Local half-wire coordinates of the refresh history step -/

namespace ThreeFlat.Diagonal.RefreshTies

open LinearAlgebra.SpectralBooks HistoryContraction
open scoped Classical BigOperators
noncomputable section

variable {m : ℕ} {U : Type} [Fintype U]

def oldPortGraph (π : Equiv.Perm (Address U m)) : PortGraph (U × Fin m) (Address U m) :=
  ⟨fun e => (e.1,e.2.1), fun e => ((π e).1,(π e).2.1)⟩

def oldShape (π : Equiv.Perm (Address U m)) (A : Address U m → Type) [∀ e, Fintype (A e)] : Shape where
  Site := U × Fin m
  Edge := Address U m
  graph := oldPortGraph π
  Label := A

/-- The old site's directed half-words, with incoming field types transported
through the actual incoming slot address. -/
def oldAt {A : Address U m → Type} (π : Equiv.Perm (Address U m)) (u : U) (v : Fin m)
    (a : (oldPortGraph π).State A (u,v)) : OldPort A π u v :=
  (fun s => a ⟨((u,v,s),false),rfl⟩, fun s => a ⟨(π.symm (u,v,s),true),by
    change ((π (π.symm _)).1,(π (π.symm _)).2.1) = _
    rw [Equiv.apply_symm_apply]⟩)

def ends {A : Address U m → Type} (π : Equiv.Perm (Address U m)) (a : ∀ j, (oldPortGraph π).State A j)
    (side : Bool) : ∀ e, A e := fun e => a ((oldPortGraph π).vertex e side) ⟨(e,side),rfl⟩

omit [Fintype U] in
theorem oldAt_eq {A : Address U m → Type} (π : Equiv.Perm (Address U m)) (a : ∀ j, (oldPortGraph π).State A j)
    (u : U) (v : Fin m) :
    oldAt π u v (a (u,v)) = readOld π (ends π a false) (ends π a true) u v := by
  apply Prod.ext
  · rfl
  · funext s
    have aux (e q : Address U m) (h : π e = q) :
        a (q.1,q.2.1) ⟨(e,true),congrArg (fun k : Address U m => (k.1,k.2.1)) h⟩ =
          ends π a true e := by subst q; rfl
    exact aux (π.symm (u,v,s)) (u,v,s) (π.apply_symm_apply _)

/-- Edge sum for new shared bundles and sparse internal arcs. -/
abbrev RawEdge (S : U → Type) (m : ℕ) := (U × Fin m) ⊕ (Σ u, S u)

def rawGraph {S : U → Type} (δ : U × Fin m → U × Fin m) (P : ∀ u, PortGraph (Fin m) (S u)) :
    PortGraph (U × Fin m) (RawEdge S m) :=
  ⟨Sum.elim id (fun e => (e.1,(P e.1).tail e.2)), Sum.elim δ (fun e => (e.1,(P e.1).head e.2))⟩

def rawLabel {S : U → Type} (A : Address U m → Type) (B : ∀ u, S u → Type) : RawEdge S m → Type :=
  Sum.elim (fun x => Bundle A x.1 x.2) (fun e => B e.1 e.2)

instance {S : U → Type} {A : Address U m → Type} {B : ∀ u, S u → Type}
    [∀ e, Fintype (A e)] [∀ u e, Fintype (B u e)] (x : RawEdge S m) : Fintype (rawLabel A B x) := by
  cases x with
  | inl x => exact inferInstanceAs (Fintype (Bundle A x.1 x.2))
  | inr e => exact inferInstanceAs (Fintype (B e.1 e.2))

def rawShape {S : U → Type} [∀ u, Fintype (S u)] (δ : U × Fin m → U × Fin m) (P : ∀ u, PortGraph (Fin m) (S u))
    (A : Address U m → Type) (B : ∀ u, S u → Type) [∀ e, Fintype (A e)] [∀ u e, Fintype (B u e)] : Shape where
  Site := U × Fin m
  Edge := RawEdge S m
  graph := rawGraph δ P
  Label := rawLabel A B

/-- Bundle field access at either physical end uses the one external wire
assigned to that bundle. The target equation accounts for its port permutation. -/
def bundleAt {S : U → Type} (π : Equiv.Perm (Address U m)) (δ : U × Fin m → U × Fin m)
    (dest : ∀ e : Address U m, δ (e.1,e.2.2) = ((π e).1,(π e).2.2))
    (P : ∀ u, PortGraph (Fin m) (S u)) (A : Address U m → Type) (B : ∀ u, S u → Type)
    (u : U) (v : Fin m) (b : (rawGraph δ P).State (rawLabel A B) (u,v)) : BundlePort A π u v :=
  (fun i => b ⟨(.inl (u,v),false),rfl⟩ i, fun i =>
    let e := π.symm (u,i,v)
    b ⟨(.inl (e.1,e.2.2),true), by
      change δ (e.1,e.2.2)=(u,v)
      simpa only [e,Equiv.apply_symm_apply] using dest e⟩ e.2.1)

def sparseAt {S : U → Type} (δ : U × Fin m → U × Fin m) (P : ∀ u, PortGraph (Fin m) (S u))
    (A : Address U m → Type) (B : ∀ u, S u → Type) (u : U) (v : Fin m)
    (b : (rawGraph δ P).State (rawLabel A B) (u,v)) : (P u).State (B u) v := fun p =>
  b ⟨(.inr ⟨u,p.1.1⟩,p.1.2), by
    rcases p with ⟨⟨e,side⟩,hs⟩
    cases side <;> exact congrArg (Prod.mk u) hs⟩

def rawAssignment {S : U → Type} (A : Address U m → Type) (B : ∀ u, S u → Type) :
    (External A × (∀ u e, B u e)) ≃ (∀ x, rawLabel A B x) where
  toFun z := Sum.rec (fun x => z.1 x.1 x.2) (fun e => z.2 e.1 e.2)
  invFun a := (fun u v => a (.inl (u,v)), fun u e => a (.inr ⟨u,e⟩))
  left_inv _ := rfl
  right_inv a := by funext x; cases x <;> rfl

end
end ThreeFlat.Diagonal.RefreshTies

end OAI
