import OAI.LinearAlgebra.SpectralBooks.PortGraph.RootedMapRelabel

/-! # Recognizing a numbered rooted map from local names

The vertex type checks the root mark and the number of incident ports. A wire
checks that its named endpoints and both port numbers describe a target wire.
These tests recover the unique rooted map isomorphism, including at loops.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

noncomputable section
namespace GridPin

open PortGraph
variable {V E W D : Type*} [Fintype V] [Fintype E] [DecidableEq V]
  [Fintype W] [Fintype D] [DecidableEq W]
  {M : RootedMap V E} {H : RootedMap W D}

private theorem portNumber_at (M : RootedMap V E) (v : V) (p : M.graph.Port v) :
    M.portNumber p.val.1 p.val.2 = (M.num v p).val := by
  rcases p with ⟨⟨e,b⟩,rfl⟩
  rfl

/-- Maps of vertex and edge names that match the local checks give a covering. -/
def coveringOfLocal (f : V → W) (g : E → D)
    (typeAt : ∀ v, M.typeAt v = H.typeAt (f v))
    (inc : ∀ e b, f (M.graph.vertex e b) = H.graph.vertex (g e) b)
    (num : ∀ e b, M.portNumber e b = H.portNumber (g e) b) :
    Covering M.graph H.graph where
  vertexName := f
  edgeName := g
  incidence := inc
  lift d b v hv := by
    let L (p : M.graph.Port v) : H.graph.Port (f v) :=
      ⟨(g p.val.1,p.val.2), (inc _ _).symm.trans (congrArg f p.property)⟩
    have hL (p : M.graph.Port v) : (M.num v p).val = (H.num (f v) (L p)).val :=
      (portNumber_at M v p).symm.trans ((num _ _).trans (portNumber_at H _ (L p)))
    have inj : Function.Injective L := fun p q h =>
      (M.num v).injective (Fin.ext ((hL p).trans ((congrArg (fun z => (H.num _ z).val) h).trans (hL q).symm)))
    have card : Fintype.card (M.graph.Port v) = Fintype.card (H.graph.Port (f v)) :=
      congrArg (fun θ : MapType => θ.degree.val) (typeAt v)
    have surj := ((Fintype.bijective_iff_injective_and_card L).mpr ⟨inj,card⟩).surjective
    obtain ⟨p,hp⟩ := surj ⟨(d,b),hv.symm⟩
    have hb : p.val.2 = b := congrArg (fun z : H.graph.Port (f v) => z.val.2) hp
    have he : g p.val.1 = d := congrArg (fun z : H.graph.Port (f v) => z.val.1) hp
    subst b
    refine ⟨p.val.1, ⟨p.property, he⟩, ?_⟩
    rintro e ⟨hv',he'⟩
    let q : M.graph.Port v := ⟨(e,p.val.2),hv'⟩
    have hq : L q = L p := Subtype.ext (Prod.ext (he'.trans he.symm) rfl)
    exact congrArg (fun z : M.graph.Port v => z.val.1) (inj hq)

/-- A successful local naming gives a map isomorphism with the given names. -/
def isoOfLocal (f : V → W) (g : E → D)
    (types : ∀ v, M.typeAt v = H.typeAt (f v))
    (inc : ∀ e b, f (M.graph.vertex e b) = H.graph.vertex (g e) b)
    (num : ∀ e b, M.portNumber e b = H.portNumber (g e) b) :
    M.Iso H := by
  let C := coveringOfLocal f g types inc num
  have root (v : V) : v = M.root ↔ f v = H.root := by
    have h := congrArg MapType.root (types v)
    simpa [RootedMap.typeAt] using h
  exact RootedMap.Iso.ofCovering C ((root _).mp rfl)
    ⟨M.root,(root _).mp rfl,fun v hv => (root v).mpr hv⟩ num

end GridPin

end

end SpectralBooks
end LinearAlgebra
end OAI
