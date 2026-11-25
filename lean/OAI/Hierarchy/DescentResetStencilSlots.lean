import OAI.Hierarchy.DescentResetStencilReaders
import OAI.Hierarchy.DescentResetStencilGather
import OAI.Hierarchy.DescentResetMeasuredFields

namespace OAI
/-! # Decoding every terminal stencil slot from the physical primitive banks -/
namespace Hierarchy.DescentPlainTerminal.Suffix.Stencil
open DescentGL DescentColonies DescentPackedColony DescentSIMDLookup DescentPackedZip DescentIssuedFallbackPanel
open DescentPacking.PackedMatch.Local
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open scoped BigOperators Classical Fin.CommRing
noncomputable section
variable {H m c q n b M w : ℕ}
local notation "r" => m-c

/-- Only host parameters are scalar. The data, split decisions and coordinate
planes each arrive as words packed over all high groups sharing a host. -/
structure Inputs (m c q : ℕ) where
  header : Fin 3→Expr
  portHeader : Fin q→Fin 2→Expr
  weights : Expr
  flows : Fin q→Expr
  splits : Expr
  planes : Fin m→Expr
  broadcastBank : Bank
  mask : Bank
  amount : Block (m-c)→Bank
  vote : Fin (m-c)→Block (m-c)→Bank
  planeTables : Fin m→Tables
  compare : Block (m-c)→Block (m-c)→Bank

def Inputs.field (P : Inputs m c q) : Slot r q→Expr
  | .inl j=>Readers.broadcast P.broadcastBank P.mask (P.header j)
  | .inr (.inl (.inl x))=>PackedOrder.projected (P.amount x) P.weights
  | .inr (.inl (.inr (z,x)))=>PackedOrder.projected (P.vote z x) P.splits
  | .inr (.inr (.inl (i,x)))=>PackedOrder.projected (P.compare i x) (Gather.assembly P.planeTables P.planes)
  | .inr (.inr (.inr (j,.inl s)))=>Readers.broadcast P.broadcastBank P.mask (P.portHeader j s)
  | .inr (.inr (.inr (j,.inr x)))=>PackedOrder.projected (P.amount x) (P.flows j)

def physical (small : c≤ m) (basis : DescentGL.Layout m)
    (head : Fin H→Fin 3→Cell n) (port : Fin H→Fin q→Fin 2→Cell n)
    (weight : Fin H→Block c→Block r→ℕ) (flow : Fin q→Fin H→Block c→Block r→ℕ)
    (rows : Block c→Scan.Buffer (Fin H) r) (v : Fin H) (hi : Block c) : panel r q n
  | .inl s=>head v s
  | .inr (.inl (.inl x))=>(weight v hi x:Cell n)
  | .inr (.inl (.inr (z,x)))=>((Scan.lookup (rows hi) z.val v x).toNat:Cell n)
  | .inr (.inr (.inl (i,x)))=>if (rearrange basis).symm (join small hi i)<(rearrange basis).symm (join small hi x)
    then 1 else 0
  | .inr (.inr (.inr (j,.inl s)))=>port v j s
  | .inr (.inr (.inr (j,.inr x)))=>(flow j v hi x:Cell n)

structure ReadersROM (P : Inputs m c q) (n b M H w out : ℕ) (mem : Memory w) : Prop where
  repeatFit : P.broadcastBank.Fits w out
  maskFit : P.mask.Fits w out
  repeatWidth : P.broadcastBank.bits=n
  rowCount : H*chunks (2^c) M≤P.mask.size
  word : n*M≤w
  broadcast : Readers.BroadcastROM P.broadcastBank P.mask H (2^c) M n mem
  amounts (x : Block r) : (P.amount x).Fits w out ∧ (P.amount x).bits=(b*2^r)*M ∧
    ∀z:Cell ((b*2^r)*M),mem ((P.amount x).base+z.val)=((DescentSIMDLookup.table (Readers.amount (n:=n) (b:=b) x) z).val:Word w)
  votes (d : Fin r) (x : Block r) : (P.vote d x).Fits w out ∧ (P.vote d x).bits=(1+r*2^r)*M ∧
    ∀z:Cell ((1+r*2^r)*M),mem ((P.vote d x).base+z.val)=((DescentSIMDLookup.table (Readers.vote (n:=n) d x) z).val:Word w)
  gather : Gather.Bounds (w:=w) (d:=2^r) (M:=M) P.planeTables P.planes out
  planeRoms (d : Fin m) : Static (P.planeTables d) (Gather.setField (d:=2^r) d) M mem
  comparisons (i x : Block r) : (P.compare i x).Fits w out ∧ (P.compare i x).bits=PackedOrder.bits r m*M ∧
    ∀z : Cell (PackedOrder.bits r m*M),mem ((P.compare i x).base+z.val)=
      ((DescentSIMDLookup.table (M:=M) (PackedOrder.cmp (n:=n) (m:=m) i x) z).val:Word w)

theorem source_slots (small : c≤ m) (basis : DescentGL.Layout m) (P : Inputs m c q)
    (head : Fin H→Fin 3→Cell n) (port : Fin H→Fin q→Fin 2→Cell n)
    (weight : Fin H→Block c→Block r→ℕ) (flow : Fin q→Fin H→Block c→Block r→ℕ)
    (rows : Block c→Scan.Buffer (Fin H) r) (out : ℕ) (mem : Memory w)
    (rom : ReadersROM P n b M H w out mem)
    (headWords : ∀j (p : Row H (2^c) M),(P.header j).eval mem ((DescentSIMDLookup.row H (2^c) M p).val:Word w)=(head p.1 j).val)
    (portWords : ∀j s (p : Row H (2^c) M),(P.portHeader j s).eval mem ((DescentSIMDLookup.row H (2^c) M p).val:Word w)=(port p.1 j s).val)
    (smallWeight : ∀v hi x,weight v hi x<2^b) (smallFlow : ∀j v hi x,flow j v hi x<2^b)
    (weights : Source P.weights (fun v hi=>DescentPackedColony.counts b (weight v hi)) M mem)
    (flows : ∀j,Source (P.flows j) (fun v hi=>DescentPackedColony.counts b (flow j v hi)) M mem)
    (splitWords : Source P.splits (fun v hi=>cache (rows hi) v) M mem)
    (planes : ∀d,Source (P.planes d) (fun (_ : Fin H) hi=>PackedOrder.panel small basis hi d) M mem) :
    ∀j,Source (P.field j) (fun v hi=>physical small basis head port weight flow rows v hi j) M mem := by
  have broadcast (s : Expr) (x : Fin H→Cell n) (atRow : ∀p : Row H (2^c) M,
      s.eval mem ((DescentSIMDLookup.row H (2^c) M p).val:Word w)=(x p.1).val) :=
    Readers.broadcast_source P.broadcastBank P.mask s x mem out rom.repeatFit rom.maskFit rom.repeatWidth
      rom.rowCount rom.word rom.broadcast atRow
  have amount (x : Block r) (src : Expr) (v : Fin H→Block c→Block r→ℕ) (lt : ∀h i j,v h i j<2^b)
      (source : Source src (fun h i=>DescentPackedColony.counts b (v h i)) M mem) :=
    Readers.amount_source x (P.amount x) src out mem v lt (rom.amounts x).1 (rom.amounts x).2.1
      (rom.amounts x).2.2 source
  intro j
  rcases j with s|((x|⟨d,x⟩)|(⟨i,x⟩|⟨j,z⟩))
  · exact broadcast _ _ (headWords s)
  · exact amount x P.weights weight smallWeight weights
  · exact Readers.vote_source d x (P.vote d x) P.splits out mem rows (rom.votes d x).1
      (rom.votes d x).2.1 (rom.votes d x).2.2 splitWords
  · exact PackedOrder.order_field small basis P.planeTables P.planes i x out (P.compare i x) mem rom.gather
      rom.planeRoms planes (rom.comparisons i x).1 (rom.comparisons i x).2.1 (rom.comparisons i x).2.2
  · cases z with
    | inl s=>exact broadcast _ _ (portWords j s)
    | inr x=>exact amount x (P.flows j) (flow j) (smallFlow j) (flows j)

end
end Hierarchy.DescentPlainTerminal.Suffix.Stencil

end OAI
