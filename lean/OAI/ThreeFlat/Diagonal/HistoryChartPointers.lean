import OAI.ThreeFlat.Diagonal.HistoryAssemblyRelabel
import OAI.ThreeFlat.Diagonal.HistoryWordLayout

namespace OAI
/-! # Source bit locations across successive slot charts -/

namespace ThreeFlat.Diagonal.HistoryRelabel

open HistoryContraction
open scoped BigOperators Classical
noncomputable section

variable {F : Type} [CommSemiring F] {Pins : Type*} {X Y : Shape} (I : Iso X Y)
    (A : PortLayout X Pins) (B : PortLayout Y Pins)
    (width : ∀ e, A.width e = B.width (I.edge e))

/-- The old port ordinal, old bit within that port, and new port ordinal are
sufficient to translate a half-wire pointer. The bounded port width-prefixes
are the only source-dependent data. -/
def halfPointer (u : X.Site) (j : Fin (A.halfBits u)) : Fin (B.halfBits (I.site u)) :=
  let q : (o : Fin (A.count u)) × Fin (A.lengths u o) := finSigmaFinEquiv.symm j
  let a := A.port u q.1
  B.portBit (I.site u) (I.port u a) (Fin.cast (width a.1.1) q.2)

private theorem origAt (u : X.Site) (o : Fin (A.count u)) (j : Fin (A.lengths u o)) (b : X.Half u) :
    A.encode u b (finSigmaFinEquiv ⟨o,j⟩) = A.binary (A.port u o).1.1 (b (A.port u o)) j := by
  let readBit (p : (i : Fin (A.count u)) × Fin (A.lengths u i)) :=
    A.binary (A.port u p.1).1.1 (b (A.port u p.1)) p.2
  exact congrArg readBit (finSigmaFinEquiv.symm_apply_apply ⟨o,j⟩)

private theorem halfAt (u : X.Site) (b : Y.Half (I.site u)) (a : X.graph.Port u) :
    I.half u b a = (I.label a.1.1).symm (b (I.port u a)) := by
  rfl

variable (bits : ∀ e (z : Y.Label (I.edge e)) (j : Fin (A.width e)),
  B.binary (I.edge e) z (Fin.cast (width e) j) = A.binary e ((I.label e).symm z) j)

include bits in
theorem halfPointer_read (u : X.Site) (b : X.Half u) (j : Fin (A.halfBits u)) :
    B.encode (I.site u) ((I.half u).symm b) (halfPointer I A B width u j) = A.encode u b j := by
  obtain ⟨b,rfl⟩ := (I.half u).surjective b
  obtain ⟨⟨o,j⟩,rfl⟩ := finSigmaFinEquiv.surjective j
  simp only [halfPointer,Equiv.symm_apply_apply,B.portBit_read,origAt,halfAt]
  let readBit (p : (i : Fin (A.count u)) × Fin (A.lengths u i)) :=
    let a := A.port u p.1
    B.binary (I.edge a.val.1) (b (I.port u a)) (Fin.cast (width a.val.1) p.2)
  exact (congrArg readBit (finSigmaFinEquiv.symm_apply_apply ⟨o,j⟩)).trans
    (bits (A.port u o).val.1 (b (I.port u (A.port u o))) j)

/-- External pins and half-wire pointers can use different chart orders. -/
def pointer (ex : ∀ u, Fin (A.ext u) → Fin (B.ext (I.site u))) (u : X.Site) :
    Fin (A.form.width u) → Fin ((I.form B.form).width u) :=
  Fin.append (fun j => (ex u j).castAdd (B.halfBits (I.site u)))
    (fun j => Fin.natAdd (B.ext (I.site u)) (halfPointer I A B width u j))

include bits in
theorem pointer_read (ex : ∀ u, Fin (A.ext u) → Fin (B.ext (I.site u)))
    (ok : ∀ u pin j, B.pin (I.site u) pin (ex u j) = A.pin u pin j)
    (u : X.Site) (pin : Pins) (b : X.Half u) (j : Fin (A.form.width u)) :
    (I.form B.form).read u pin b (pointer I A B width ex u j) = A.form.read u pin b j := by
  refine Fin.addCases (fun x => ?_) (fun x => ?_) j
  · simpa [pointer,Iso.form,PortLayout.form] using ok u pin x
  · simpa [pointer,Iso.form,PortLayout.form] using halfPointer_read I A B width bits u b x

/-- Reuse the original physical forest as the children of a recharted stage.
This changes a child pointer inside its existing row-copy command. -/
def chartStage {R : Rewrite Y F} {t : Fin R.count} {W : Form (R.target t) Pins}
    (L : Stage R t B.form W) (ex : ∀ u, Fin (A.ext u) → Fin (B.ext (I.site u)))
    (ok : ∀ u pin j, B.pin (I.site u) pin (ex u j) = A.pin u pin j) :
    Stage (I.rewrite R) t A.form W :=
  let C := I.stage L
  { count := C.count, child := C.child, hidden := C.hidden, decode := C.decode,
    rootWidth := C.rootWidth, root := C.root, rootWire := C.rootWire,
    childWire := fun v j a => C.childWire v j (pointer I A B width ex (C.child v j).val a),
    root_eq := C.root_eq,
    read_eq := fun v j g pin b a => (C.read_eq v j g pin b _).trans
      (pointer_read I A B width bits ex ok _ _ _ a) }

private theorem castBinary {a b : ℕ} (h : a=b) (x : Fin (2^a)) (y : Fin (2^b)) (hy : y.val=x.val) (j : Fin a) :
    (MotifBinaryPacking.word b).symm y (Fin.cast h j) = (MotifBinaryPacking.word a).symm x j := by
  subst b
  have same : y=x := Fin.ext hy
  subst y
  rfl

/-- The physical chart isomorphisms have `finCongr` edge maps, hence their
word-label condition is just preservation of the integer stored on an edge. -/
theorem wordBits {V E U D P : Type} [Fintype V] [Fintype E] [Fintype U] [Fintype D]
    {G : LinearAlgebra.SpectralBooks.PortGraph V E} {H : LinearAlgebra.SpectralBooks.PortGraph U D} {a : E → ℕ} {b : D → ℕ}
    (I : Iso (WordLayout.shape G a) (WordLayout.shape H b))
    (A : WordLayout G a P) (B : WordLayout H b P)
    (width : ∀ e, a e = b (I.edge e)) (labels : ∀ e z, (I.label e z).val=z.val)
    (e : E) (z : Fin (2^b (I.edge e))) (j : Fin (a e)) :
    B.ports.binary (I.edge e) z (Fin.cast (width e) j) = A.ports.binary e ((I.label e).symm z) j := by
  apply castBinary
  exact (congrArg Fin.val ((I.label e).apply_symm_apply z)).symm.trans
    (labels e ((I.label e).symm z))

end
end ThreeFlat.Diagonal.HistoryRelabel

end OAI
