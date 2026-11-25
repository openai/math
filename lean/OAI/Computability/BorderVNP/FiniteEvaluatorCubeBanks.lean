import OAI.Computability.BorderVNP.FiniteDiagonalCubeRawGrid
import OAI.Computability.BorderVNP.CubeTeamPrivateKeysPath
import OAI.Computability.BorderVNP.CubeScatterPaddingBanksFold
import OAI.Computability.BorderVNP.DiagonalTallyPacketEvidence

/-! # Routed finite-field paths in the native packet banks

A chronological team tape, a common strict-row word, and an owned table
lookup all use the same distributed assignment. The selector and incident
wires of the lookup are read from the path reconstructed by the finite-field
diagonal bijection. A single vertex is indexed by its packet and cube corner.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FiniteDiagonal.FieldRawLayout

open Crossing BorderVNP.Cube BorderVNP.Cube.Physical BorderVNP.Cube.Scatter BorderVNP.Cube.Tally Padding.Banks
open RoutingISA VPVNP.BurstRAM VPVNP.MotifBase DiagonalTallyPacketEmit
open scoped Classical

variable {D R w : ℕ} {P : Type} [Fintype P] {bits : P → ℕ} {N : Network D P bits}
variable {F : Type*} [Field F] {T : N.Tables F} {L : FieldPacketPlan N F} {S : FieldSiteDirectory N T}
variable (V : FieldRawLayout L S) (R : ℕ) (raw : V.Raw R)

local notation "Packets" => Packet L.dimension L.alphabet L.blocks
local notation "axis" => chosen L.bitWidth L.supply (Sigma.fst (Prod.fst raw))
local notation "path" => Prod.snd (V.read R raw)

/-- The true physical scatter data obtained by reading the routed raw choices. -/
noncomputable def bankData (packetBase singleBase : ℕ) :
    Padding.Banks.Data L.dimension L.alphabet L.blocks L.bitWidth L.copies L.alternatives L.supply :=
  Assignment.bankData raw.1.2 packetBase singleBase

/-- The table lookup for this actual packet and cube corner, using the very
selector, antipodal end words and edge words in the reconstructed field path. -/
noncomputable def visit (packetBase : ℕ) (p : Packets) (v : Vertex (L.dimension+1)) :
    Visit L.dimension L.bitWidth L.copies L.alternatives L.supply :=
  ⟨OwnedVertex.bankAt packetBase (bankWidth L.dimension L.bitWidth L.copies L.alternatives L.supply) p,
    path.2.2.2.1 p,v,path.2.2.1 p,path.2.2.2.2 p⟩

/-- Redistributing the reconstructed physical path returns exactly the original
selector tuple and all of its routed bits, including the co-located rows. -/
theorem read_routed :
    ((Assignment.adaptivePathEquiv N L.cell L.dimension L.alphabet L.blocks L.bitWidth
      L.copies L.alternatives L.supply (V.owners R)) path).2 = raw.1 := by
  let E := Assignment.adaptivePathEquiv N L.cell L.dimension L.alphabet L.blocks L.bitWidth
    L.copies L.alternatives L.supply (V.owners R)
  change (E (E.symm (_,raw.1))).2=raw.1
  rw [E.apply_symm_apply]

/-- Actual singleton contents are the independently assigned singleton lanes in the
same reconstructed path used for the inherited cell and packet weights. -/
theorem bank_single (packetBase singleBase : ℕ) (z : SingleSlot L.dimension L.alphabet L.blocks (L.copies*L.bitWidth)) :
    (V.bankData R raw packetBase singleBase).value z.1.val z.2 = path.2.1 z :=
  SingleRowData.extendSlots_apply (fun q => Assignment.lookup raw.1.2 (.inl q)) z

/-- A successful native scatter of this vertex is the physical bank read by
the exact diagonal table visit, at all locally attached ends and incident edges. -/
theorem visit_bank (packetBase singleBase : ℕ) (m : Memory w) (p : Packets) (v : Vertex (L.dimension+1)) :
    (V.bankData R raw packetBase singleBase).Holds m (.vertex p v) ↔
    let z := V.visit R raw packetBase p v
    VertexAt m z.base z.selector z.vertex z.ends z.supply := Iff.rfl

/-- The finite-field lookup at this physical address returns the actual factor
of the selected packet network at the indexed corner. -/
theorem visit_value (packetBase : ℕ) (p : Packets) (v : Vertex (L.dimension+1)) :
    L.table p ((V.visit R raw packetBase p v).entry D) =
      (packetNetwork D L.bitWidth L.supply (path.2.2.2.1 p)).read (packetTables (L.table p) D (path.2.2.2.1 p))
        (path.2.2.2.2 p) (path.2.2.1 p) v := rfl

/-- Exact assignment of each returned vertex word to the symbol's greedy owner. -/
theorem visit_of_owned (packetBase singleBase : ℕ) (m : Memory w) (team : Fin (R+1))
    (views : ∀ x, V.owners R raw.1.1 (x.row axis).1=team → (V.bankData R raw packetBase singleBase).Holds m x)
    (p : Packets) (v : Vertex (L.dimension+1)) (owned : V.owners R raw.1.1 (vertexLabel p v axis)=team) :
    let z := V.visit R raw packetBase p v
    VertexAt m z.base z.selector z.vertex z.ends z.supply :=
  (V.visit_bank R raw packetBase singleBase m p v).mp (views (.vertex p v) ((View.vertex_row_owner axis p v).symm ▸ owned))

/-- The actual native selector-dependent shared and private words of the entire
field path agree with encoding its original routed choices. -/
theorem read_tapes :
    ((pathWordsEquiv N L.cell L.dimension L.alphabet L.blocks L.bitWidth L.copies L.alternatives L.supply (V.owners R)) path).2 =
      ⟨raw.1.1,nativeWordsEquiv L.bitWidth L.supply raw.1.1 axis (V.owners R raw.1.1) raw.1.2⟩ := by
  let enc := Equiv.sigmaCongrRight (fun u => nativeWordsEquiv L.bitWidth L.supply u
    (chosen L.bitWidth L.supply u) (V.owners R u))
  exact congrArg enc (V.read_routed R raw)

/-- The word on each shared row contains its selected crossing wires once. -/
theorem shared_tape (pair : Symbols L.alphabet) :
    (((nativeWordsEquiv L.bitWidth L.supply raw.1.1 axis (V.owners R raw.1.1)) raw.1.2).1 pair).val =
      commonCrossings L.bitWidth axis pair raw.1.1 path.2.2.2.2 path.2.1 :=
  nativeWordsEquiv_shared raw.1.2 pair

/-- The actual native dispatcher consumes the chronological team word supplied by
the same shared/private equivalence, even if both sides are on this team. -/
theorem team_tape (team : Fin (R+1)) (l : TeamRowPrepare.Layout) (dim : l.d=L.alphabet)
    (id : l.teamID=team.val) (packetBase singleBase : ℕ) :
    (((nativeWordsEquiv L.bitWidth L.supply raw.1.1 axis (V.owners R raw.1.1)) raw.1.2).2 team).val =
      TeamRows.choices l (TeamRows.wordOwner (Fin.val ∘ V.owners R raw.1.1))
        ((V.bankData R raw packetBase singleBase).privateTapeAt l) :=
  nativeWordsEquiv_teamRows ⟨Fin.val,Fin.val_injective⟩ raw.1.2 team l dim id packetBase singleBase

end FiniteDiagonal.FieldRawLayout

end BorderVNP
end Computability
end OAI
