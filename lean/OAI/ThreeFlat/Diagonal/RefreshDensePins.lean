import OAI.ThreeFlat.Diagonal.RefreshWordSource

namespace OAI
/-! # Concrete pointers for every demand and supply field at a refresh port -/

namespace ThreeFlat.Diagonal.RefreshTies

open Computability.VPVNP.Compression LinearAlgebra.SpectralBooks HistoryContraction Expander MotifBinaryPacking
open scoped Classical BigOperators
noncomputable section

variable {U : Type} [Fintype U] {m p : ℕ} (π : Equiv.Perm (Address U m)) (δ : U×Fin m → U×Fin m)
    (dest : ∀ e : Address U m, δ (e.1,e.2.2) = ((π e).1,(π e).2.2))
    {S : U → Type} [∀ u,Fintype (S u)] (P : ∀ u, PortGraph (Fin m) (S u))
    (w : Address U m → ℕ) (s : ∀ u, S u → ℕ) (u : U) (v : Fin m)

abbrev rawWidth : RawEdge S m → ℕ := Sum.elim (fun j => ∑ i, w (j.1,i,j.2)) (fun e => s e.1 e.2)

def rawPointer (src : (q : (rawGraph δ P).Port (u,v)) → Fin (rawWidth w s q.1.1) → Fin p) :
    (rawGraph δ P).State (rawLabel (fun e => Fin (w e) → Fin p) (fun t e => Fin (s t e) → Fin p)) (u,v) := by
  rintro ⟨⟨(j|e),side⟩,eq⟩
  · exact fun i t => src ⟨(.inl j,side),eq⟩ (finSigmaFinEquiv (n:=fun i => w (j.1,i,j.2)) ⟨i,t⟩)
  · exact src ⟨(.inr e,side),eq⟩

variable (old : (q : (oldPortGraph π).Port (u,v)) → Fin (w q.1.1) → Fin p)
    (src : (q : (rawGraph δ P).Port (u,v)) → Fin (rawWidth w s q.1.1) → Fin p)

def demandPin (a : (RefreshMotif.denseGraph m).Port v) : Fin (w (addr π u a.1.1)) → Fin p :=
  portFields π u v (oldAt π u v old) (bundleAt π δ dest P _ _ u v (rawPointer δ P w s u v src)) a

def sparsePin (a : (P u).Port v) : Fin (s u a.1.1) → Fin p :=
  sparseAt δ P _ _ u v (rawPointer δ P w s u v src) a

variable {B : ∀ u, S u → Type} (pack : ∀ u a, B u a ≃ Fin (2^s u a))

def packRaw : ∀ e, rawLabel (fun a => Fin (2^w a)) B e ≃ Fin (2^rawWidth w s e)
  | .inl a => bundleWord (fun i => w (a.1,i,a.2))
  | .inr a => pack a.1 a.2

variable (pin : Fin p → Bool) (a : (oldPortGraph π).State (fun e => Fin (2^w e)) (u,v))
    (y : (rawGraph δ P).State (rawLabel (fun e => Fin (2^w e)) B) (u,v))
    (oldRead : ∀ q t, pin (old q t) = (a q).val.testBit t.val)
    (read : ∀ q t, pin (src q t) = (packRaw w s pack q.1.1 (y q)).val.testBit t.val)

include oldRead read in
omit [Fintype U] [(u : U) → Fintype (S u)] in
theorem demandPin_read (q : (RefreshMotif.denseGraph m).Port v) (t : Fin (w (addr π u q.1.1))) :
    pin (demandPin π δ dest P w s u v old src q t) = (portFields π u v (oldAt π u v a)
      (bundleAt π δ dest P _ _ u v y) q).val.testBit t.val := by
  obtain ⟨⟨⟨dir,i,j⟩,side⟩,edge⟩ := q
  cases side with
  | false =>
    change i=v at edge
    subst v
    cases dir <;> exact oldRead _ _
  | true =>
    change j=v at edge
    subst v
    have bundle (z : U × Fin m) (side : Bool)
        (h : (rawGraph δ P).vertex (.inl z) side = (u,j)) (k : Fin m) (b : Fin (w (z.1,k,z.2))) :
        pin (src ⟨(.inl z,side),h⟩ (finSigmaFinEquiv (n := fun a => w (z.1,a,z.2)) ⟨k,b⟩)) =
          ((y ⟨(.inl z,side),h⟩ k).val.testBit b.val) :=
      (read ⟨(.inl z,side),h⟩ (finSigmaFinEquiv (n := fun a => w (z.1,a,z.2)) ⟨k,b⟩)).trans
        (bundleWord_bit (fun a => w (z.1,a,z.2)) (y ⟨(.inl z,side),h⟩) k b)
    cases dir with
    | false => exact bundle (u,j) false rfl i t
    | true =>
      let e := π.symm (u,i,j)
      have atDest : δ (e.1,e.2.2) = (u,j) :=
        (dest e).trans (congrArg (fun a : Address U m => (a.1,a.2.2)) (π.apply_symm_apply (u,i,j)))
      exact bundle (e.1,e.2.2) true atDest e.2.1 t

include read in
omit [Fintype U] [(u : U) → Fintype (S u)] in
theorem sparsePin_read (q : (P u).Port v) (t : Fin (s u q.1.1)) :
    pin (sparsePin δ P w s u v src q t) = (pack u q.1.1 (sparseAt δ P _ _ u v y q)).val.testBit t.val := by
  obtain ⟨⟨e,side⟩,edge⟩ := q
  cases side <;> exact read _ _

end
end ThreeFlat.Diagonal.RefreshTies

end OAI
