import OAI.Hierarchy.DescentExteriorPackedRoot

namespace OAI
/-! # The combined input before any native instruction uses the original copied catalyst ports -/
namespace Hierarchy.DescentExteriorShelf.Root
open DescentInitialHost DescentSeedRoot DescentTerminalEpochChart DescentPackedEpochShelves DescentPackedProfileInstall
open DescentExterior DescentGL Computability.VPVNP.BurstRAM Computability.BorderVNP.Crossing
open ThreeFlat Routing Diagonal Catalyst CatalystSubstitution CorrectionBatch
open scoped Classical
noncomputable section
variable {F A B : Type} [Field F] {cp data j r t : ℕ}

def hostPin (X : Catalyst.Approximation F cp data) (R s w : ℕ)
    (seed : DescentSeedRoot.Select X R s → A) (lo C grain : ℕ)
    (ss : List (DescentTerminalEpochChart.Source A))
    (bind : A ⊕ Hidden (ExteriorCount X) j r t → B) (origin : ℕ)
    (i : Fin (origin+17*DescentExteriorShelf.span j r t (ExteriorCount X))×Fin (w+1)) :
    ((Catalyst.Port (2^(j+(j+r))*t*data) (CorrectionFrame.copiesWidth (2^(j+(j+r))*t) X.width))⊕B)⊕Bool :=
  (@pin A w (ExteriorCount X) j r t
      (DescentPackedProfileInstall.end_ (lo + DescentPackedEpochShelves.extent grain ss) C grain)
      origin (@packedPin F A _ cp data X R s w seed lo C grain ss) i).map
    (Sum.map (fun (p : Public (ExteriorCount X) j r t) =>
      @DescentExterior.publicPin F cp data X j r t p.1.1 p.1.2 p.2) bind) id

theorem hostPin_read (X : Catalyst.Approximation F cp data) (R s w : ℕ)
    (seed : DescentSeedRoot.Select X R s → A) (lo C grain : ℕ)
    (ss : List (DescentTerminalEpochChart.Source A))
    (bind : A ⊕ Hidden (ExteriorCount X) j r t → B) (origin : ℕ)
    (x : (Catalyst.Port (2^(j+(j+r))*t*data) (CorrectionFrame.copiesWidth (2^(j+(j+r))*t) X.width))→Bool) (z : B→Bool)
    (split : (DescentPackedProfileInstall.end_ (lo + DescentPackedEpochShelves.extent grain ss) C grain) ≤ origin)
    (space : 2^j*t ≤ w) (pos : 0 < grain)
    (room : ∀u∈ss,DescentTerminalEpochBits.width u.C*grain ≤ w)
    (i : Fin (origin+17*DescentExteriorShelf.span j r t (ExteriorCount X))×Fin (w+1)) :
    (hostPin (j:=j) (r:=r) (t:=t) X R s w seed lo C grain ss bind origin i).elim (Sum.elim x z) id =
      TraceWords.bits (TraceBanks.wide (@packedImage F A _ cp data (ExteriorCount X) j r t X R s w seed lo C grain ss origin
      (@DescentExterior.publicRows F cp data X j r t x) (z∘bind) i.1.val)) i.2 := by
  have h := @packed_read F A _ cp data (ExteriorCount X) j r t X R s w seed lo C grain ss origin
    (@DescentExterior.publicRows F cp data X j r t x) (z∘bind)
    split space pos room i
  refine Eq.trans ?_ h
  unfold hostPin
  cases @pin A w (ExteriorCount X) j r t
      (DescentPackedProfileInstall.end_ (lo + DescentPackedEpochShelves.extent grain ss) C grain)
      origin (@packedPin F A _ cp data X R s w seed lo C grain ss) i with
  | inr bit => rfl
  | inl p => cases p <;> rfl


end
end Hierarchy.DescentExteriorShelf.Root

end OAI
