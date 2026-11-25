import OAI.LinearAlgebra.MatrixExponent.Spectral.Wire

/-! # Local table expansions of simultaneous wire demands -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Spectral
open Classical

/-- Each demand leg has a named bit. A summand may introduce independent
supply bits. Each local table reads only the incident bits. -/
def Packet (K : Type) [Field K] {S E I : Type} {J : I → Type}
    [Fintype S] [Fintype E] [Fintype I] [∀ i, Fintype (J i)]
    (D : E → S × S) (W : (i : I) → J i → S × S) : Prop :=
  ∃ f : (i : I) → S → (E → Bool) → (E → Bool) → (J i → Bool) → K,
    (∀ i v x y u x' y' u',
      (∀ e, (D e).1 = v → x e = x' e) →
      (∀ e, (D e).2 = v → y e = y' e) →
      (∀ e, (W i e).1 = v ∨ (W i e).2 = v → u e = u' e) →
      f i v x y u = f i v x' y' u') ∧
    ∀ x y, (if x = y then (1 : K) else 0) = ∑ i, ∑ u, ∏ v, f i v x y u

end OAI.LinearAlgebra.MatrixExponent.Spectral
end

/-!
# Keeping the local factors of a wire identity

An existence proof can be used to choose a single basic gadget.
Composing gadgets needs the actual factors, since the label of a
derived table can only depend on its own local history.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Spectral.Packet
open Classical

variable {S E I : Type} {J : I → Type} [Fintype S] [Fintype E] [Fintype I] [∀ i, Fintype (J i)]

structure Rule (K : Type) [Field K] (D : E → S × S) (W : (i : I) → J i → S × S) where
  entry : (i : I) → S → (E → Bool) → (E → Bool) → (J i → Bool) → K
  local' : ∀ i v x y u x' y' u',
    (∀ e, (D e).1 = v → x e = x' e) →
    (∀ e, (D e).2 = v → y e = y' e) →
    (∀ e, (W i e).1 = v ∨ (W i e).2 = v → u e = u' e) →
    entry i v x y u = entry i v x' y' u'
  eval : ∀ x y, (if x = y then (1 : K) else 0) = ∑ i, ∑ u, ∏ v, entry i v x y u

variable {K : Type} [Field K] {D : E → S × S} {W : (i : I) → J i → S × S}

def rule (p : Packet K D W) : Rule K D W := ⟨p.choose, p.choose_spec.1, p.choose_spec.2⟩

theorem Rule.packet (p : Rule K D W) : Packet K D W := ⟨p.entry, p.local', p.eval⟩

/-- Change endpoint notation without transporting the factor array. -/
def Rule.congr {W' : (i : I) → J i → S × S} {D' : E → S × S}
    (p : Rule K D W) (hd : D = D') (hw : W = W') : Rule K D' W' :=
  ⟨p.entry, by rw [← hd, ← hw]; exact p.local', p.eval⟩

end OAI.LinearAlgebra.MatrixExponent.Spectral.Packet
end
