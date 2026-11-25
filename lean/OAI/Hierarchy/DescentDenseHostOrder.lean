import OAI.Hierarchy.DescentResetEdgeTape
import OAI.Hierarchy.DescentCommonHostSize
import OAI.Hierarchy.DescentRosterOrder

namespace OAI
/-! # Stable dense host IDs after a real reset

The former host is one field. The remaining fields describe a fixed common
shape and admit a shared roster for all former hosts. The complete ordinal
is bounded by the product of the old host and one local roster.
-/

namespace Hierarchy.DescentDenseHostOrder
open DescentCommonHost DescentResetWireTags DescentChosenRouter DescentContacts
open scoped Classical BigOperators
noncomputable section
variable {V : Type} {n h : ℕ} (G : NonlinearExpanders.Graph n h)
local notation "R" => DescentCommonPalette.rotor G
local notation "Y" => (2^n : ℕ)
local notation "NodeAt" => fun V=>Node V (V×Endpoint Y) (Computability.BorderVNP.Crossing.Network.Site R)

def position : NodeAt V→V
  | .trunk _ z=>z.1
  | .good _ z _=>z.1
  | .fall _ z _=>z.1

def shape : NodeAt V→NodeAt Unit
  | .trunk s z=>.trunk s ((),z.2)
  | .good s z cell=>.good s ((),z.2) cell
  | .fall s z path=>.fall s ((),z.2) path

def recover (v : V) : NodeAt Unit→NodeAt V
  | .trunk s z=>.trunk s (v,z.2)
  | .good s z cell=>.good s (v,z.2) cell
  | .fall s z path=>.fall s (v,z.2) path

@[simp] theorem recover_shape (z : NodeAt V) : recover G (position G z) (shape G z)=z := by
  cases z <;> rfl

def roster (r height : ℕ) := Finset.univ.image (render G (V:=Unit) r height)

theorem shape_mem {r height : ℕ} (q : Pool G V r height) :
    shape G (render G r height q) ∈ roster G r height := by
  rcases q with ⟨s,v,a,w⟩
  refine Finset.mem_image.mpr ⟨(s,(),a,w),Finset.mem_univ _,?_⟩
  rcases w with tag|cell|⟨tag,cell⟩ <;> rfl

/-- This roster depends on the fixed rotor, interval range and fallback
depth. Its structural comparisons contain no recursively supplied host ID. -/
def localRank (r height : ℕ) : ↥(roster G r height)↪Fin ((roster G r height).card) :=
  (DescentRosterOrder.compact ((Function.Embedding.subtype _).trans
    (hostTag (⟨fun _ : Unit=>0,fun _ _ _=>Subsingleton.elim _ _⟩) G))).trans
      (finCongr (Fintype.card_coe _)).toEmbedding

theorem roster_bound (r t : ℕ) :
    (roster G r t).card≤(2*((Y+1)+((2*h+4)*Y+(Y+1)*2^(t+1))))*2^(r+1) :=
  Finset.card_image_le.trans (by
    rw [Finset.card_univ]
    simpa only [Fintype.card_unit,Nat.mul_one] using pool_count (V:=Unit) G r t)

end
end Hierarchy.DescentDenseHostOrder

namespace Hierarchy.DescentSixParty.ResetInput
open DescentDenseHostOrder DescentCommonHost
open scoped Classical BigOperators
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {A : MarkedWorld F d P bits}
    {price ε : ℝ} {h C Ht : ℕ} (Z : ResetInput A price ε h C Ht) (T : Terminals Z)
local notation "r" => (Z.k-T.commonDepth)
local notation "pool" => DescentDenseHostOrder.roster Z.graph r Ht

def localShape (x : ↥(commonNames Z T)) : ↥pool := by
  refine ⟨shape Z.graph x.val,?_⟩
  have supp:=placed_support Z T (le_refl r) (fun t=>(T.codeLegal t).2.1) T.bookHeight x.property
  obtain ⟨q,_,same⟩:=Finset.mem_image.mp supp
  exact same ▸ shape_mem Z.graph q

/-- The physical host and common shape use two bounded fields. The first
field is the dense host ID from the preceding epoch. -/
def hostFields {H : ℕ} (vertex : Z.V↪Fin H) : ↥(commonNames Z T)↪Fin H × Fin (pool).card where
  toFun x := (vertex (position Z.graph x.val),localRank Z.graph r Ht (localShape Z T x))
  inj' := by
    intro x y eqn
    have pos:=vertex.injective (congrArg Prod.fst eqn)
    have localEq:=(localRank Z.graph r Ht).injective (congrArg Prod.snd eqn)
    have sh:=congrArg Subtype.val localEq
    change shape Z.graph x.val=shape Z.graph y.val at sh
    apply Subtype.ext
    simpa only [recover_shape] using congrArg₂ (recover Z.graph) pos sh

def rawHostRank {H : ℕ} (vertex : Z.V↪Fin H) : ↥(commonNames Z T)↪Fin (H*(pool).card) :=
  (hostFields Z T vertex).trans finProdFinEquiv.toEmbedding

theorem rawHostRank_read {H : ℕ} (vertex : Z.V↪Fin H) (x : ↥(commonNames Z T)) :
    (rawHostRank Z T vertex x).val=(hostFields Z T vertex x).2.val+(pool).card*(hostFields Z T vertex x).1.val := rfl

def denseHostRank {H : ℕ} (vertex : Z.V↪Fin H) :
    ↥(commonNames Z T)↪Fin (Fintype.card ↥(commonNames Z T)) :=
  DescentRosterOrder.compact ((rawHostRank Z T vertex).trans ⟨Fin.val,Fin.val_injective⟩)

theorem denseHostRank_read {H : ℕ} (vertex : Z.V↪Fin H) (x : ↥(commonNames Z T)) :
    (denseHostRank Z T vertex x).val=
      (Finset.univ.filter fun y=>rawHostRank Z T vertex y<rawHostRank Z T vertex x).card :=
  DescentRosterOrder.compact_read _ x

theorem rank_space (H : ℕ) :
    H*(pool).card≤H*((2*((2^Z.n+1)+((2*h+4)*2^Z.n+(2^Z.n+1)*2^(Ht+1))))*2^(r+1)) :=
  Nat.mul_le_mul_left _ (roster_bound Z.graph r Ht)

end
end Hierarchy.DescentSixParty.ResetInput

end OAI
