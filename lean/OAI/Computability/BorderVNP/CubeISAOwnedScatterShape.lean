import OAI.Computability.BorderVNP.CubeISAOwnedVertexCallback
import OAI.Computability.BorderVNP.CubeScatterPacket
import OAI.Computability.BorderVNP.RoutingISATableEvents

/-! # Reading the selected cube packet and its owner before scattering -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Scatter

open RoutingISA RoutingISA.OwnedVertex Physical Physical.VertexIndex
open VPVNP.BurstRAM VPVNP.MotifBase DiagonalResidueRAM Tally

/-- Install the grouping symbol, its coordinate and the half-cube dimension. -/
def loadOwner : Code := .block [.copy 39 3, .copy 40 4, .copy 48 5]

/-- Decode the copied selector and compute the axis and owner keys of the body dispatcher. -/
def decodeOwner : Code := .seq OwnedVertex.selectorShape
  (.seq SelectorRead.reader (.seq loadOwner OwnedVertex.prepareShape))

/-- Cost of reading the selector and preparing the two group keys. -/
def decodeOwnerCost (n width : ℕ) : ℕ :=
  2 + (SelectorRead.init.slots + width * (SelectorRead.step.slots + 1) + 1 + (requireLt 43 42).slots) +
  3 + (shapeSetup.slots + n * (shapeBody.slots + 1) + 1)

/-- Entry words retained by the enclosing owned-row traversal. -/
structure OwnerInput {w n d blocks K h : ℕ} (p : Packet n d blocks) (i : Fin (n+1))
    (high : Bool) (r : Bank w) : Prop where
  /-- Upper endpoint symbol of this strict pair. -/
  upper : readings r 15 = (p.1.1 i).val.2.val
  /-- Orientation of this packet. -/
  orientation : readings r 25 = p.1.2.toNat
  /-- Grouping symbol of the local team. -/
  group : readings r 3 = (groupSymbol p i high).val
  /-- Grouping coordinate. -/
  axis : readings r 4 = i.val
  /-- Number of coordinates other than the grouping coordinate. -/
  dim : readings r 5 = n
  /-- Width in bits of the common selector. -/
  bits : readings r 8 = selectorWidth n K h
  /-- Number of valid common selectors. -/
  count : readings r 9 = Fintype.card (Selector n K h)

/-- The registers written by the key-decoding prefix. -/
def decodeScratch : List Reg := [39,40,41,42,43,44,45,46,48,50,51,52,53,54]

variable {w n d blocks K h : ℕ} {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8}

/-- The selector reader and the owner calculation run without altering memory or input cursors.
The three keys are the exact ordinal, coordinate place, and local ownership bit. -/
theorem decodeOwner_run (p : Packet n d blocks) (i : Fin (n+1)) (high : Bool)
    (u : Selector n K h) (r : Bank w) (m : Memory w) (base : ℕ)
    (entry : OwnerInput (K := K) (h := h) p i high r) (addr : readings r 24 = base)
    (stored : SelectorRead.Stored (readings m) base u)
    (fit : max (Fintype.card (Selector n K h)) (2^(n+1)) < 2^w)
    (room : base + selectorWidth n K h ≤ 2^w) :
    ∃ t es, Runs pub mac decodeOwner r m es t m ∧ TraceOK es [] es.length ∧
      traceCost es ≤ decodeOwnerCost n (selectorWidth n K h) ∧
      t 43 = word w (selectorOrder n K h u).val ∧ t 44 = word w (2^i.val) ∧
      t 45 = wordBit w (ownerBit i p.1.2 high) ∧
      ∀ j : Reg, j ∉ decodeScratch → t j = r j := by
  have cube : 2^(n+1) < 2^w := (le_max_right ..).trans_lt fit
  have two : 2 < 2^w := (Nat.pow_le_pow_right (by decide : 1 ≤ 2) (by omega : 1 ≤ n+1)).trans_lt cube
  have half : 2^n < 2^w := (Nat.pow_le_pow_right (by decide) (Nat.le_succ n)).trans_lt cube
  let first := effect false r m OwnedVertex.selectorShape
  have start := effect_runs pub mac false r m OwnedVertex.selectorShape (by decide)
  have hbase : readings first.bank 24 = base := addr
  have hwidth : readings first.bank 41 = selectorWidth n K h := entry.bits
  have hcount : readings first.bank 42 = Fintype.card (Selector n K h) := entry.count
  obtain ⟨es,a,ma,read,costRead,mem,rank,_⟩ := SelectorRead.physical_run
    (pub := pub) (mac := mac) first.bank m base u stored hbase hwidth hcount two room
  have eqMem : ma = m := funext fun j => Fin.ext (congrFun mem j)
  subst ma
  have firstKeep (j : Reg) (hj : j.val < 39) : a j = r j := by
    have k : ∀ j : Reg, j.val < 39 → SelectorRead.reader.keeps j = true ∧
        OwnedVertex.selectorShape.keeps j = true := by decide
    exact (read.keepsReg (k j hj).1).trans (start.keepsReg (k j hj).2)
  let move := effect false a m loadOwner
  have setup := effect_runs pub mac false a m loadOwner (by decide)
  have mu : readings move.bank 15 = (p.1.1 i).val.2.val :=
    (congrArg Fin.val (firstKeep 15 (by decide))).trans entry.upper
  have mo : readings move.bank 25 = p.1.2.toNat :=
    (congrArg Fin.val (firstKeep 25 (by decide))).trans entry.orientation
  have mg : readings move.bank 39 = (groupSymbol p i high).val :=
    (congrArg Fin.val (firstKeep 3 (by decide))).trans entry.group
  have mc : readings move.bank 40 = i.val :=
    (congrArg Fin.val (firstKeep 4 (by decide))).trans entry.axis
  have md : readings move.bank 48 = n :=
    (congrArg Fin.val (firstKeep 5 (by decide))).trans entry.dim
  obtain ⟨fs,t,mt,shape,costShape,place,side,_,mem',_,_⟩ :=
    OwnedVertex.prepareShape_run pub mac p i high move.bank m mu mo mg mc md half two
  have eqMem' : mt = m := funext fun j => Fin.ext (congrFun mem' j)
  subst mt
  let tr := first.trace ++ (es ++ (move.trace ++ fs))
  have run : Runs pub mac decodeOwner r m tr t m := start.seq (read.seq (setup.seq shape))
  have all := run.unsigned_events (by decide)
  have fitWord {v : Word w} {k : ℕ} (eqn : v.val = k) : v = word w k :=
    Fin.ext (eqn.trans (word_val w k (eqn ▸ v.isLt)).symm)
  have rank' : (t 43).val = (selectorOrder n K h u).val :=
    (congrArg Fin.val ((shape.keepsReg (k := 43) (by decide)).trans
      (setup.keepsReg (k := 43) (by decide)))).trans rank
  refine ⟨t,tr,run,⟨rfl,List.flatMap_eq_nil_iff.mpr (fun e he => (all e he).1),fun e he => (all e he).2⟩,
    ?_,fitWord rank',fitWord place,fitWord side,?_⟩
  · have hc₁ : traceCost first.trace = 2 := rfl
    have hc₂ : traceCost move.trace = 3 := rfl
    simp only [tr,traceCost,VPVNP.RAMBuckets.cost_append] at *
    unfold decodeOwnerCost
    omega
  · intro j hj
    exact run.keepsReg ((by decide : ∀ j : Reg, j ∉ decodeScratch → decodeOwner.keeps j = true) j hj)

end Cube.Scatter

end BorderVNP
end Computability
end OAI
