import OAI.Hierarchy.TaggedWireChordRouter

namespace OAI
/-! # The mixed-radix bit decoding depends only on paid chord endpoints -/
noncomputable section
namespace Hierarchy.WireTelescope
open LinearAlgebra.SpectralBooks SiteTensor ChordGraph
open AdaptiveProbe Computability.VPVNP.RAMSerialization
open scoped Classical BigOperators

/-- Aggregate widths, literal graph of the paid bits, and the actual local
decoder, with both of the latter's dependent types recorded. -/
abbrev BitRows (S n : ℕ) (bits : Fin n→ℕ) :=
  (w : Widths S) × (g : PortGraph (Fin S) (Bundle bits)) × ((s:Fin S)→State w s→BitState g s)

namespace BitRows
variable {S n : ℕ}

def data (ends : Fin n→Chord S) (bits : Fin n→ℕ) : BitRows S n bits :=
  ⟨installedWidths ends bits,bitGraph (rowGraph ends) bits,fun _=>rowBits ends bits⟩

private def liveGraph {bits : Fin n→ℕ} (ends : Bundle bits→Chord S) :
    PortGraph (Fin S) (Bundle bits) :=
  ⟨fun b=>(ends b).1.1,fun b=>(ends b).1.2⟩

private def liveSourcePort {bits : Fin n→ℕ} (ends : Bundle bits→Chord S) {s : Fin S}
    (p : (liveGraph ends).Port s) : (portGraph S).Port s :=
  ⟨(ends p.1.1,p.1.2),by rcases p with ⟨⟨b,side⟩,atSite⟩; cases side <;> exact atSite⟩

/-- The real decoder factors through its ordered vector of radix coefficients
and the chord of each live bit. Dormant row endpoints appear in neither input. -/
private def decoded (bits : Fin n→ℕ) (blocks : Fin n→Widths S) (ends : Bundle bits→Chord S)
    (sizes : ∀b:Bundle bits,2^((blocks b.1) (ends b))=2^(bits b.1)) : BitRows S n bits :=
  ⟨∑i,blocks i,liveGraph ends,fun _ x p=>
    let b:=p.1.1
    let port:=liveSourcePort ends p
    let word:=finCongr (sizes b) ((blockWireIndex blocks (ends b)) (x port) b.1)
    wordBits (bits b.1) word b.2⟩

private theorem decoded_congr (bits : Fin n→ℕ) {a b : Fin n→Widths S} {left right : Bundle bits→Chord S}
    (blocks : a=b) (ends : left=right)
    (sizesLeft : ∀p:Bundle bits,2^((a p.1) (left p))=2^(bits p.1))
    (sizesRight : ∀p:Bundle bits,2^((b p.1) (right p))=2^(bits p.1)) :
    decoded bits a left sizesLeft=decoded bits b right sizesRight := by
  cases blocks
  cases ends
  rfl

/-- Moving any collection of zero-width endpoints preserves the native
aggregate widths and graph and the complete source/target transported decoder. -/
theorem data_congr (ends other : Fin n→Chord S) (bits : Fin n→ℕ)
    (active : ∀i,0<bits i→ends i=other i) : data ends bits=data other bits := by
  have blocks : (fun i=>bits i • unitChord (ends i))=(fun i=>bits i • unitChord (other i)) := by
    funext i
    by_cases paid : 0<bits i
    · rw [active i paid]
    · simp [Nat.eq_zero_of_not_pos paid]
  have live : (fun b:Bundle bits=>ends b.1)=(fun b:Bundle bits=>other b.1) := by
    funext b
    exact active b.1 (Nat.zero_lt_of_lt b.2.isLt)
  exact decoded_congr bits blocks live (fun b=>blockSize ends bits b.1) (fun b=>blockSize other bits b.1)

end BitRows

theorem rowBits_supported {S n : ℕ} (ends other : Fin n→Chord S) (bits : Fin n→ℕ)
    (active : ∀i,0<bits i→ends i=other i) : BitRows.data ends bits=BitRows.data other bits :=
  BitRows.data_congr ends other bits active

end Hierarchy.WireTelescope
end

end OAI
