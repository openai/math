import OAI.Computability.VPVNP.SlotDemandKernel
import OAI.Computability.VPVNP.SlotIdentifierOrder
import Mathlib.Data.Finset.Sort

/-!
# Lane-independent combinatorial orders of the packed wires

For each base arc and source tag, order the old thick wires and the assigned
motifs at source-site lane zero. The order at every other lane is the transport
of that order. Thus the combinatorial identifiers used for Appendix E's scans
agree under translations even when the actual field widths vary by lane.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace Compression

variable {V Tag L : Type*} {d : ℕ} [AddCommGroup L]

private abbrev Port (V Tag L : Type*) (d : ℕ) := Site V Tag L × Fin d

/-- Preserve the bundle's base arc and tag while translating its remaining lane. -/
def translateBundle (b : Site V Tag L × Fin d) (g : L) : Site V Tag L × Fin d :=
  (translateSite b.1 g,b.2)

private def zeroBundle (b : Port V Tag L d) : Port V Tag L d := ((b.1.1,b.1.2.1,0),b.2)

private structure BundleAction (A : Type*) (port : A → Port V Tag L d) where
  move : A → L → A
  zero : ∀ a, move a 0 = a
  add : ∀ a g h, move (move a g) h = move a (g + h)
  port_move : ∀ a g, port (move a g) = translateBundle (port a) g

namespace BundleAction

variable {A : Type*} {port : A → Port V Tag L d} (S : BundleAction A port)

private def zeroFiber (b : Port V Tag L d) :
    {a : A // port a = b} ≃ {a : A // port a = zeroBundle b} where
  toFun a := ⟨S.move a.1 (-b.1.2.2), by rw [S.port_move,a.2]; simp [translateBundle,translateSite,
    zeroBundle]⟩
  invFun a := ⟨S.move a.1 b.1.2.2, by rw [S.port_move,a.2]; simp [translateBundle,translateSite,
    zeroBundle]⟩
  left_inv a := Subtype.ext (by simp [S.add,S.zero])
  right_inv a := Subtype.ext (by simp [S.add,S.zero])

private def numbering {n : ℕ} (initial : ∀ b, {a : A // port a = b} ≃ Fin n) (b : Port V Tag L d) :
    {a : A // port a = b} ≃ Fin n :=
  (S.zeroFiber b).trans (initial (zeroBundle b))

private theorem numbering_move {n : ℕ} (initial : ∀ b, {a : A // port a = b} ≃ Fin n)
    (b : Port V Tag L d) (a : {a : A // port a = b}) (g : L) :
    S.numbering initial (translateBundle b g) ⟨S.move a.1 g, (S.port_move a.1 g).trans
      (congrArg (fun v ↦ translateBundle v g) a.2)⟩ = S.numbering initial b a := by
  apply congrArg (initial (zeroBundle b))
  apply Subtype.ext
  change S.move (S.move a.1 g) (-(b.1.2.2 + g)) = S.move a.1 (-b.1.2.2)
  simp [S.add]

end BundleAction

namespace PackingData

variable {V H Tag L : Type} {d c : ℕ} [AddCommGroup H] [AddCommGroup Tag] [AddCommGroup L]
variable (P : PackingData V H Tag L d c)

private def motifBundleAction : BundleAction P.Motif P.bundle where
  move := P.translateMotif
  zero := P.translateMotif_zero
  add := P.translateMotif_add
  port_move := P.bundle_translate

/-- The old thick–thick wires also form complete translation orbits. -/
def translateThickWire (a : P.ThickWire) (g : L) : P.ThickWire :=
  ⟨translateArc a.1 g, by simpa only [actual_translate,sourcePosition_translate,thick_translate]
    using a.2⟩

private def thickBundleAction : BundleAction P.ThickWire (fun a ↦ a.1.1) where
  move := P.translateThickWire
  zero a := Subtype.ext (translateArc_zero a.1)
  add a g h := Subtype.ext (translateArc_add a.1 g h)
  port_move _ _ := rfl

/-- Transport the chosen order of CD demands at lane zero to every bundle. -/
def laneBundleNumbering (initial : P.BundleNumbering) : P.BundleNumbering :=
  P.motifBundleAction.numbering initial

/-- Transport the common endpoint order of the old thick wires from lane zero. -/
def laneThickNumbering (initial : P.ThickNumbering) : P.ThickNumbering :=
  P.thickBundleAction.numbering initial

/-- The translated motif occupies the same piece number in the translated bundle. -/
theorem laneBundleNumbering_translate (initial : P.BundleNumbering) (b : Site V Tag L × Fin d)
    (m : P.MotifFiber b) (g : L) :
    P.laneBundleNumbering initial (translateBundle b g)
      ⟨P.translateMotif m.1 g, by rw [P.bundle_translate, m.2]; rfl⟩ =
      P.laneBundleNumbering initial b m :=
  P.motifBundleAction.numbering_move initial b m g

/-- Each original wire keeps its rank in the translated concatenation order. -/
theorem laneThickNumbering_translate (initial : P.ThickNumbering) (b : Site V Tag L × Fin d)
    (a : P.ThickFiber b) (g : L) :
    P.laneThickNumbering initial (translateBundle b g)
      ⟨P.translateThickWire a.1 g, congrArg (fun v ↦ translateBundle v g) a.2⟩ =
      P.laneThickNumbering initial b a :=
  P.thickBundleAction.numbering_move initial b a g

/-- At fixed source site and arc, the old thick wire is specified by its
color word and slot-coordinate label. -/
def thickFiberIndex (b : Site V Tag L × Fin d) (x : P.ThickFiber b) : Fin (2 ^ c * d) :=
  finProdFinEquiv (bitWordFinEquiv c x.1.1.2.1, P.slotLabel x.1.1.2.2)

theorem thickFiberIndex_injective (b : Site V Tag L × Fin d) :
    Function.Injective (P.thickFiberIndex b) := by
  intro x y h
  have he := finProdFinEquiv.injective h
  exact Subtype.ext (Subtype.ext (Prod.ext (x.2.trans y.2.symm)
    (Prod.ext ((bitWordFinEquiv c).injective (congrArg Prod.fst he))
      (P.slotLabel.injective (congrArg Prod.snd he)))))

/-- The relative motif key distinguishes every old CD wire in a fixed bundle.
The role-A lane recovers the missing absolute coordinate from that bundle. -/
theorem motifFiberIndex_injective {N J : ℕ} (vertices : V ≃ Fin N) (tags : Tag ≃ Fin J)
    (b : Site V Tag L × Fin d) :
    Function.Injective (fun x : P.MotifFiber b ↦
      P.baseMotifIndex vertices tags (P.baseMotif x.1)) := by
  intro x y h
  apply Subtype.ext
  apply (P.roleLaneEquiv P.roleA P.roleA_translate).injective
  exact Prod.ext (P.baseMotifIndex_injective vertices tags h)
    (congrArg (fun t : Site V Tag L × Fin d ↦ t.1.2.2) (x.2.trans y.2.symm))

private def keyNumbering {A : Type*} [Fintype A] {n q : ℕ} (key : A → Fin n)
    (hinj : Function.Injective key) (hcard : Fintype.card A = q) : A ≃ Fin q :=
  letI := LinearOrder.lift' key hinj
  (Fintype.orderIsoFinOfCardEq A hcard).symm.toEquiv

variable [Fintype V] [Fintype H] [Fintype Tag] [Fintype L]
variable [DecidableEq V] [DecidableEq Tag] [DecidableEq L]

/-- Order the CD demands of each bundle by their relative integer keys. The
order at an arbitrary lane is the transport of the same lane-zero list. -/
def sortedBundleNumbering {N J : ℕ} (vertices : V ≃ Fin N) (tags : Tag ≃ Fin J)
    (hc : 2 ≤ c) : P.BundleNumbering :=
  P.laneBundleNumbering fun b ↦ keyNumbering
    (fun x : P.MotifFiber b ↦ P.baseMotifIndex vertices tags (P.baseMotif x.1))
    (P.motifFiberIndex_injective vertices tags b) (P.card_motifs_bundle hc b)

/-- Use the same integer-sorted list of old wires at both bundle ends and in
every translated lane. -/
def sortedThickNumbering (hc : 2 ≤ c) : P.ThickNumbering :=
  P.laneThickNumbering fun b ↦ keyNumbering (P.thickFiberIndex b)
    (P.thickFiberIndex_injective b) (P.card_thick_fiber hc b)

end PackingData

end Compression

end VPVNP
end Computability
end OAI
