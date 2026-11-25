import OAI.Hierarchy.DescentActorDestination
import OAI.Hierarchy.DescentChronologicalFee
import OAI.Hierarchy.DescentPrivateOwnerRows

namespace OAI
/-! # Exact same-owner charge on the physical rows of an issued ordinary stage -/

namespace Hierarchy.DescentStageEdgeReceipt
open Computability.BorderVNP.Crossing DescentSixParty DescentKernelHistory DescentHostDirectory DescentNetworkPartition
open DescentHistoryOrder GadgetNetwork DescentPacking DescentSixParty.StarKeys
open scoped Classical BigOperators
noncomputable section
set_option quotPrecheck false
variable {F P H : Type} [Field F] [Fintype H] [DecidableEq H] {d : ℕ} {bits : P→ℕ}
variable {W : MarkedWorld F d P bits} {G : PoweredGadget F} {u ε : ℝ}
variable (he : 0≤ε) (T : StageInput W G u ε) (c : (T.result he).Choice)
local notation "r" => BitDescription.scannedRows he T
local notation "sw" => branchWidth G (fun _ : (r).pairs=>T.z) ((r).profile c)
/-- The reported owner travels through the chosen motif, hub reclaim, and every finally
installed site permutation before the native directory encodes it. -/
def rawOwner {A : MarkedWorld F d P bits} (n : Normalize A) (input : A=scanWorld he T c)
    (id : n.result.graph.Site↪ℕ) : (rawGraph he T c).Site→ℕ := id ∘ n.destination ∘ rawInput he T c input

/-- The raw row number is the actual sparse-tape ordinal. Every existing edge uses
its old row, and every paired motif occupies its own ten consecutive appended rows. -/
def rawOrdinal (old : W.graph.Edge↪Fin (Fintype.card W.graph.Edge)) (pair : ScanNumbers he T) :
    (rawGraph he T c).Edge≃Fin (Fintype.card W.graph.Edge+10*Fintype.card (r).pairs) := by
  let number (e : (rawGraph he T c).Edge) : Fin (Fintype.card W.graph.Edge+10*Fintype.card (r).pairs) :=
    ⟨MarkedWorld.edgeNumber W (dense old) pair e,MarkedWorld.edgeNumber_room W (dense old) pair e⟩
  refine Equiv.ofBijective number ((Fintype.bijective_iff_injective_and_card _).2 ⟨?_,?_⟩)
  · intro a b h
    exact MarkedWorld.edgeNumber_inj W (dense old) pair (congrArg Fin.val h)
  · change Fintype.card (W.graph.Edge ⊕ (((r).pairs×Fin 2)⊕((r).pairs×Fin 8)))=_
    simp only [Fintype.card_sum,Fintype.card_prod,Fintype.card_fin]
    omega

@[simp] theorem rawOrdinal_val (old : W.graph.Edge↪Fin (Fintype.card W.graph.Edge)) (pair : ScanNumbers he T)
    (e : (rawGraph he T c).Edge) :
    (rawOrdinal he T c old pair e).val=MarkedWorld.edgeNumber W (dense old) pair e := rfl

variable {he T c} {old : W.graph.Edge↪Fin (Fintype.card W.graph.Edge)} {root : H↪ℕ}
variable {A : MarkedWorld F d P bits} {n : Normalize A} {t : Tape n.result.graph.Edge} {pair : ScanNumbers he T}

theorem IssuedRows.owner_test (issued : IssuedRows he T c old root A n t pair) (input : A=scanWorld he T c)
    (id : n.result.graph.Site↪ℕ) :
    let raw:=rawGraph he T c
    let code:=rawOwner he T c n input id
    (∑e:raw.Edge,if code (raw.src e)=code (raw.dst e) then raw.width e else 0)=scanFee he T c+mergeFee n := by
  dsimp only
  simp only [rawOwner,Function.comp_apply,Function.Embedding.apply_eq_iff_eq]
  clear id
  induction issued with
  | stage col same hub k g q legal source oldCut used cut=>
    let key:=nativeKey W.graph W.core (scanHomeAt he T) (scanColorAt he T) T.cap col same (bestLayout sw)
    let loc : (rawGraph he T c).Site → (scanWorld he T c).graph.Site :=
      newSite W.graph (r).pick (bestLayout sw) (r).pack
    let after:=MarkedWorld.address (scanWorld he T c) key hub k g
    let pos:=fun _ : (scanWorld he T c).graph.Site=>(0:EuclideanSpace ℝ (Fin d))
    let physical:=rawGraph he T c
    change _ = absorbed physical loc + (absorbed (scanWorld he T c).graph after + 0)
    calc
      _ = absorbed physical (after ∘ loc) := by
        rw [absorbed_eq_test]
        apply Finset.sum_congr rfl
        intro e _
        by_cases h : after (loc (physical.src e)) = after (loc (physical.dst e))
        · exact (ite_eq_left h).trans (ite_eq_left h).symm
        · exact (ite_eq_right h).trans (ite_eq_right h).symm
      _ = absorbed physical loc + absorbed (quotient physical loc pos (fun _ => by simp [pos])) after :=
        (absorbed_comp physical loc after pos (fun _ => by simp [pos])).symm
      _ = _ := by
        rw [Nat.add_zero]
        rfl
  | named n t issued site ih=>
    simp only [Normalize.destination_appendNames,mergeFee_appendNames]
    exact ih input

/-- A dense enumeration of old, arm and supply rows yields the identical integer
when its three physical columns read the actual owner, owner and width. -/
theorem IssuedRows.published_charge (issued : IssuedRows he T c old root A n t pair) (input : A=scanWorld he T c)
    (id : n.result.graph.Site↪ℕ) {size : ℕ} (addr : (rawGraph he T c).Edge≃Fin size)
    (src dst width : Fin size→ℕ)
    (src_read : ∀e,src (addr e)=rawOwner he T c n input id ((rawGraph he T c).src e))
    (dst_read : ∀e,dst (addr e)=rawOwner he T c n input id ((rawGraph he T c).dst e))
    (width_read : ∀e,width (addr e)=(rawGraph he T c).width e) :
    (∑i,if src i=dst i then width i else 0)=scanFee he T c+mergeFee n := by
  rw [←addr.sum_comp (fun i=>if src i=dst i then width i else 0)]
  simp only [src_read,dst_read,width_read]
  exact issued.owner_test input id

end
end Hierarchy.DescentStageEdgeReceipt

namespace Hierarchy.DescentSixParty.Chronology
open DescentStageEdgeReceipt DescentKernelHistory DescentPacking
open scoped Classical BigOperators
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F}
variable {S : DescentCompiler.AtomSchedule} {q u ε : ℝ} {k i z D w hist z' D' : ℕ}
variable {a : Reached W G q ε S k i z D w hist} {he : 0≤ε} {T : StageInput W G u ε}
variable {c : (T.result he).Choice} {n : Normalize ((T.result he).state c)}
variable {b : Reached n.result G q ε S k (i+1) z' D' w hist}
local notation "raw" => rawGraph he T c
local notation "input" => (BitDescription.scannedRows he T).state c

/-- The conditional sum of authentic numerical source, destination and width words
is precisely the private archive increment at this issued ordinary transition. -/
theorem OrdinaryLink.published_fee (ticket : OrdinaryLink a he T c n b) {size : ℕ}
    (addr : (raw).Edge≃Fin size) (src dst width : Fin size→ℕ)
    (src_read : ∀e,src (addr e)=rawOwner he T c n input (originalId _) ((raw).src e))
    (dst_read : ∀e,dst (addr e)=rawOwner he T c n input (originalId _) ((raw).dst e))
    (width_read : ∀e,width (addr e)=(raw).width e) :
    (∑i,if src i=dst i then width i else 0)=ordinaryFee ticket :=
  ticket.issued.published_charge input (originalId _) addr src dst width src_read dst_read width_read

/-- Compare word addresses in the real tape order chosen by the issued stage. -/
theorem OrdinaryLink.raw_row_fee (ticket : OrdinaryLink a he T c n b)
    (src dst width : ℕ→ℕ)
    (src_read : ∀e,src (MarkedWorld.edgeNumber W (dense a.order) ticket.pair e)=
      rawOwner he T c n input (originalId _) ((raw).src e))
    (dst_read : ∀e,dst (MarkedWorld.edgeNumber W (dense a.order) ticket.pair e)=
      rawOwner he T c n input (originalId _) ((raw).dst e))
    (width_read : ∀e,width (MarkedWorld.edgeNumber W (dense a.order) ticket.pair e)=(raw).width e) :
    (∑i : Fin (Fintype.card W.graph.Edge+10*Fintype.card (BitDescription.scannedRows he T).pairs),
      if src i.val=dst i.val then width i.val else 0)=ordinaryFee ticket :=
  ticket.published_fee (rawOrdinal he T c a.order ticket.pair) (fun i=> src i.val) (fun i=>dst i.val)
    (fun i=>width i.val) src_read dst_read width_read

end
end Hierarchy.DescentSixParty.Chronology

end OAI
