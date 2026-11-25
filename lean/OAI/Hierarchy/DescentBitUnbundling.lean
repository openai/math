import OAI.Hierarchy.DescentLocalBitHistory

namespace OAI
/-! # Exact bit readdressing when marked physical cables split into grain-sized cables -/

namespace Hierarchy.DescentKernelHistory
open Computability.BorderVNP.Crossing DescentCableUnbundling
open scoped Classical BigOperators
noncomputable section
variable {F U P : Type} [Field F] {D : ℕ} {w : P→ℕ} (N : Network D P w)
variable (core : Finset N.Edge) (m : N.Edge→ℕ) (q : ℕ) (fit : ∀e∈core,N.width e=m e*q)
local notation "Q" => network N core m q

def pieceBit (v : N.Site) : BitRef (boundaryWidth N v)→BitRef (boundaryWidth (Q) v)
  | ⟨.inr p,j⟩=>⟨.inr p,j⟩
  | ⟨.inl e,j⟩=>
    if keep : e.val∈core then
      let p := finProdFinEquiv.symm (Fin.cast (fit e.val keep) j)
      ⟨.inl ⟨.inr ⟨⟨e.val,keep⟩,p.1⟩,e.property⟩,p.2⟩
    else ⟨.inl ⟨.inl ⟨e.val,keep⟩,e.property⟩,j⟩

def unbundleBits (r : SiteBits (U:=U) N) : SiteBits (U:=U) (Q) :=
  fun v=>(r v).reroute (pieceBit N core m q fit v)

theorem unbundle_reads (s : U→List (List Bool)→F) (r : SiteBits (U:=U) N) (T : N.Tables F)
    (valid : ReadsBits N s r T) :
    ReadsBits (Q) s (unbundleBits N core m q fit r) (tables N core m q fit T) := by
  apply (reads_iff_local ..).mpr
  intro v read pins
  rw [unbundleBits,BitRecipe.reroute_eval]
  unfold tables
  rw [←(reads_iff_local N s r T).mp valid v]
  apply congrArg ((r v).value s)
  funext z
  rcases z with ⟨e|p,j⟩
  · by_cases h : e.val∈core <;> simp [pieceBit,h,localBit,splitWord,Function.comp_def]; rfl
  · rfl

theorem unbundle_atom_bits (r : SiteBits (U:=U) N) (v : N.Site) (i : (r v).Node) :
    (unbundleBits N core m q fit r v).nodeBits i=(r v).nodeBits i := rfl


end
end Hierarchy.DescentKernelHistory

end OAI
