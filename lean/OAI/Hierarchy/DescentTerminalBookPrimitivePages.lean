import OAI.Hierarchy.DescentTerminalBookMeasured
import OAI.Hierarchy.DescentTerminalPrimitivePublicPair

namespace OAI
/-! # Connecting the original scalar and actor frames to the six geometry printers -/
namespace Hierarchy.DescentTerminalLocalPortBook.Rasters
open DescentSixParty DescentCompiler DescentSharedCableNames DescentColonies DescentChosenRouter DescentPacking
open DescentStageEdgeReceipt DescentPacking.PackedMatch.Local.Stage DescentTerminalSignedGrainWord
open DescentTerminalGraphRows DescentSortedRoster ProtocolRAM DescentSIMDLookup Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.Routing
open Computability.BorderVNP.Crossing
open scoped Classical BigOperators Fin.CommRing
noncomputable section

variable {F P V:Type} [Field F] [Fintype P] [Fintype V] [DecidableEq V] {groups d k i H p bw argc w:ℕ}
    {bits:P→ℕ} {W:MarkedWorld F d P bits} {G:PoweredGadget F} {price ε:ℝ}
    (A:GroupStage W G price ε (Fin groups) V k) (hosts:V↪Fin H) (S:AtomSchedule) (ready:A.StateBounds S i)
    (native:W.graph.Edge↪Fin (Fintype.card W.graph.Edge)) (raw:Fin H→Fin A.degree→Option (Fin H))
    (rack:Rasters A.degree (2^k) A.cap) (m:Memory w)
local notation "ord" => native.trans Fin.valEmbedding
local notation "roster" => indexed raw
local notation "atH" => fun v:W.graph.Site=>hosts (Prod.snd (A.pos v))
local notation "signed" => Prepare.signed A ord S ready (Function.Embedding.refl (Fin groups)) hosts


open DescentTerminalVertexFields DescentTerminalPointerIssue DescentTerminalSiteShelves
variable {q tags hid N M:ℕ}
local notation "arBits" => Nat.clog 2 (q+1)
local notation "shelf" => MaskAllocation.shelf (q:=q) (t:=tags) (H:=hid) (N:=N) (A:=M) (p:=p) (groups:=groups)
  rack.geometry 0
local notation "meas" h => measured (q:=q) (t:=tags) (H:=hid) (N:=N) (A:=M) (w:=p) (groups:=groups) shelf m h

/-- The f0 hypothesis is the original primitive scalar receipt (.ports).
The other data are the attained actor mask, the two signed wings and the
bounded earlier common-host roster. -/
theorem from_pages (near:∀v,present raw (hosts v)=(A.near v).map hosts)
    (peers:∀h j z,roster h j=some z→ rack.roster.read m ((h.val*A.degree+j.val:ℕ):Word w)=(z.val:Word w))
    (word:2<2^w) (tiny:2<2^bw) (homes:H≤2^w)
    (maskCap:∀b,H≤(rack.geometry.occupied b).size) (portCap:∀b,H≤(rack.geometry.primitive b 0).size)
    (actors:∀h:Fin H,∀b:Block k,m ((rack.geometry.occupied b).base+h.val)=
      ((encode 1 groups (fun g=>(if ∃v:W.graph.Site,atH v=h ∧ (A.pos v).1=g ∧ A.block v=b then 1 else 0):Fin groups→Cell 1)).val:Word w))
    (scalar:∀v:W.graph.Site,venueField (cellAt (meas (atH v)) (finProdFinEquiv ((A.pos v).1,A.block v))) publicArity=
      DescentTerminalGraphRows.arity W.graph p v)
    (shelfBits:groups≤bw) (bitsRoom:bw≤w) (argBits:arBits*groups≤bw)
    (wingWide:DescentSignedCableCodec.width A.degree A.cap*groups≤bw)
    (pitch:ℕ) (covered:groups≤pitch) (wide:DescentSignedCableCodec.width A.degree A.cap*pitch≤w)
    (wings:∀b t,DescentPackedColony.Reads (rack.wing b t) (fun h g=>DescentSignedCableCodec.encode (signed b t h g)) pitch m)
    (wingCap:∀b t,H≤(rack.wing b t).size) :
    Inputs (p:=p) (bw:=bw) (argc:=arBits) A hosts S ready native raw rack m := by
  refine ⟨near,peers,word,tiny,homes,shelfBits,argBits,?_,?_,⟨pitch,covered,wide,wings⟩,wingWide,wingCap⟩
  · intro g h b
    let mask:Fin groups→Cell 1:=fun j=>if ∃v:W.graph.Site,atH v=h ∧ (A.pos v).1=j ∧ A.block v=b then 1 else 0
    have len:(encode 1 groups mask).val<2^w:=(encode 1 groups mask).isLt.trans_le
      (Nat.pow_le_pow_right (by decide) (by simpa using shelfBits.trans bitsRoom))
    change digit 1 g.val ((rack.geometry.occupied b).read m (h.val:Word w)).val=_
    rw [Bank.read,Fin.val_cast_of_lt (h.isLt.trans_le homes),Nat.mod_eq_of_lt (h.isLt.trans_le (maskCap b)),actors]
    change digit 1 g.val (((encode 1 groups mask).val:Word w)).val=_
    rw [Fin.val_cast_of_lt len,digit_encode]
    unfold mask;split <;> rfl
  · intro v
    let h:=atH v
    let block:=A.block v
    have read:=public_field (q:=q) (hid:=hid) (tags:=tags) (N:=N) (M:=M) (p:=p) shelf m block
      (rack.geometry.primitive block 0).base (by simp only [MaskAllocation.shelf,MaskAllocation.Channels.primitive_at])
      (by simpa only [MaskAllocation.shelf,MaskAllocation.Channels.primitive_at] using portCap block) homes h (A.pos v).1
    have port:=scalar v
    rw [read] at port
    change digit arBits (A.pos v).1.val ((rack.geometry.primitive block 0).read m (h.val:Word w)).val=_
    rw [Bank.read,Fin.val_cast_of_lt (h.isLt.trans_le homes),Nat.mod_eq_of_lt (h.isLt.trans_le (portCap block))]
    exact port

end
end Hierarchy.DescentTerminalLocalPortBook.Rasters

end OAI
