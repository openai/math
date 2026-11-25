import OAI.Hierarchy.DescentTerminalPointerArity
import OAI.Hierarchy.DescentTerminalPointerPair
import OAI.Hierarchy.DescentTerminalPointerFromPages

namespace OAI
/-! # Both true public and operand-reference fields in one attained terminal memory -/
namespace Hierarchy.DescentTerminalPointerIssue
open Computability.BorderVNP.Crossing DescentSixParty DescentSharedCableNames DescentKernelHistory DescentTerminalPortChart
open DescentBundleHistory DescentTerminalBoundaryBasis DescentCompiler DescentColonies DescentLocalPrivateNames
open DescentOperandStateBanks DescentTerminalPointerDigits DescentTerminalChronologicalBooks
open ThreeFlat.Routing DescentTerminalVertexFields
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM DescentSIMDLookup
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical BigOperators Fin.CommRing
noncomputable section
set_option quotPrecheck false


section PublicField
variable {q hid tags N M p groups blocks shops wb : ℕ}
local notation "reader" => measured (q:=q) (t:=tags) (H:=hid) (N:=N) (A:=M) (w:=p) (groups:=groups)
local notation "bits₀" => Nat.clog 2 (q+1)
/-- Only the low group digit of the real scalar row is read for the public arity. -/
theorem public_field (machine : MaskedShelf blocks) (m : Memory wb) (b : Fin blocks) (start : ℕ)
    (atBase : (machine.channel (finProdFinEquiv (b,(0:Fin 8).succ))).base=start)
    (keep : shops≤(machine.channel (finProdFinEquiv (b,(0:Fin 8).succ))).size) (hostFits : shops≤2^wb)
    (h : Fin shops) (g : Fin groups) :
    venueField (cellAt (reader machine m h) (finProdFinEquiv (g,b))) publicArity=
      digit bits₀ g.val (m (start+h.val)).val := by
  rw [venue_digit]
  change digit bits₀ 0 ((cellAt (reader machine m h) (finProdFinEquiv (g,b))) 0).val=_
  rw [cell_digit, measured_channel]
  change digit bits₀ 0 (digit (1*bits₀) g.val
    (((machine.channel (finProdFinEquiv (b,(0:Fin 8).succ))).read m (h.val:Computability.VPVNP.BurstRAM.Word wb)).val%2^(1*bits₀*groups)))=_
  rw [Nat.one_mul,digit_clip,Bank.read,Fin.val_cast_of_lt (h.isLt.trans_le hostFits),
    Nat.mod_eq_of_lt (h.isLt.trans_le keep),atBase]
  have bound:=DescentTerminalSignedGrainWord.digit_bound bits₀ g.val (m (start+h.val)).val
  simp only [digit,Nat.zero_add,Nat.mul_one,Nat.mul_zero,pow_zero,Nat.div_one]
  exact Nat.mod_eq_of_lt bound
end PublicField

section Reached
variable {F P J V Tag : Type} [Field F] [Fintype P] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
    {d k i p q N M K tags : ℕ} {bits:P→ℕ} {W:MarkedWorld F d P bits} {G:PoweredGadget F} {price ε:ℝ}
    (A:GroupStage W G price ε J V k) (native:W.graph.Edge↪ℕ) (S:AtomSchedule) (ready:A.StateBounds S i)
    (names:Stage.Host J V k↪ℕ) (v:W.graph.Site) (coords:Function.Injective (fun s=>(A.pos s,A.block s)))
    (port:Attached W.graph v↪ℕ) (hp:0<p) (scale psize:ℕ) (whole:A.z*G.b=scale*p)
    (common:∀z:Attached W.graph v,poolBatchCount (bits z.val) p=psize)
    (r:Recipe Tag (BlockRef p (boundaryWidth W.graph v))) (code:Tag→ Fin tags)
    (birth:r.Node↪ℕ) (nodes:Fintype.card r.Node≤N) (arity:∀u,r.arity u≤M) (aliases:Slot r↪Fin K)
    (t:CellInputs A.degree A.cap N M)
local notation "rk" => rank A native S ready names v port
local notation "loc" => slot r birth nodes arity
local notation "chart" => (firstAlias r aliases).trans Fin.valEmbedding
local notation "G'" => W.graph
local notation "sparse" => Origin G' v r birth nodes arity aliases rk port t
local notation "sig" => Stage.signedPanel A native S ready names (Stage.home A v)



variable {hid groups blocks shops wb d0:ℕ} (config:Widths) (index:ℕ→ℕ→ℕ→ℕ) (frozenBits : ℕ)
    (pages:Gather.Pages blocks A.cap M) (before:Memory wb) (origin:ℕ) (machine:MaskedShelf blocks)
local notation "L" => columns A.cap N M
local notation "H" => blocks*shops
local notation "sz" => Nat.clog 2 (q+hid+1)
local notation "sz₀" => Nat.clog 2 (q+1)
local notation "f7" => output A.cap N M A.degree groups d0 sz q scale psize config index
local notation "f0" => publicCell (cap:=A.cap) (N:=N) (A:=M) (d:=d0) A.degree q scale psize frozenBits groups config
local notation "ps" => Gather.dropOff origin blocks shops L pages.address
local notation "B" => Gather.banks («L»:=L) origin H
local notation "base" => Gather.rom origin L H
local notation "shelf" => DescentTerminalPointerFrame.size L d0
local notation "a0" => base+shelf
local notation "base7" => a0+H
local notation "a7" => base7+shelf
local notation "warm" => ProtocolRAM.result ps before
local notation "mid" => DescentTerminalPointerFrame.result base B H f0 warm
local notation "done" => DescentTerminalPointerFrame.result base7 B H f7 mid
local notation "p0" => DescentTerminalPointerFrame.program wb base B H f0
local notation "p7" => DescentTerminalPointerFrame.program wb base7 B H f7
local notation "work" => ((4+10*shelf)+(4+H*(16+26*L)))
local notation "meas" => measured (q:=q) (t:=tags) («H»:=hid) (N:=N) (A:=M) (w:=p) (groups:=groups)
variable (b:Fin blocks) (h:Fin shops) (g:Fin groups)
local notation "cell" => pages.source (N:=N) (d:=d0) before b h
local notation "exposed" => DescentTerminalGraphRows.arity G' p v
include coords whole common in
theorem primitive_pair
    (legal:∀j x,(pages.address (N:=N) j x).Fits origin shops wb) (off:2^d0<2^wb)
    (space:a7+H<2^wb) (fits₀:sz₀*groups≤wb) (fits₇:sz*(N*M)*groups≤wb)
    (pbase:(machine.channel (finProdFinEquiv (b,(0:Fin 8).succ))).base=a0+b.val*shops)
    (abase:(machine.channel (finProdFinEquiv (b,(7:Fin 8).succ))).base=a7+b.val*shops)
    (pkeep:shops≤(machine.channel (finProdFinEquiv (b,(0:Fin 8).succ))).size)
    (akeep:shops≤(machine.channel (finProdFinEquiv (b,(7:Fin 8).succ))).size)
    (publicRoom:exposed≤q) (privateRoom:Fintype.card r.UsedWord≤hid) (read:SourceRead config cell g.val t)
    (prior:Origin G' v r birth nodes arity aliases rk port (reindexed t (index (cell mcol).val (cell fcol).val)))
    (ports:DescentTerminalFrozenRoster.length frozenBits (cell fcol).val=Fintype.card (Attached G' v)) (chips:t.chips=sig) :
    (((ProtocolRAM.program wb ps).seq p0).seq p7).Exec before done ((ProtocolRAM.clock ps+work)+work) ∧
    CheapCode (((ProtocolRAM.program wb ps).seq p0).seq p7) ∧
    venueField (cellAt (meas machine done h) (finProdFinEquiv (g,b))) publicArity=exposed ∧
    (∀u (j:Fin (r.arity u)),venueField (cellAt (meas machine done h) (finProdFinEquiv (g,b)))
      (nodeArg (row r birth nodes u) (j.castLE (arity u)))=
        (((numbered G' hp v rk r.restricted code).operand u j).elim (fun a=>a.val+1) (fun a=>q+(ordinal chart a).val+1))) ∧
    (∀a,a<origin ∨ a7+H≤a→done a=before a) ∧ ProtocolRAM.clock ps≤4+(L*blocks)*(4+shops*18) := by
  have hold:=Gather.Pages.pair pages before origin shops f0 f7 legal off space
  have hosts:shops≤H:=by simpa using Nat.mul_le_mul_right shops (Nat.succ_le_of_lt (Nat.zero_lt_of_lt b.isLt))
  have hostWord:shops≤2^wb:=by omega
  have slab (base₀ : ℕ) : base₀+b.val*shops+h.val=base₀+(finProdFinEquiv (b,h)).val:=by
    rw [finProdFinEquiv_apply_val];ring
  refine ⟨hold.1,hold.2.1,?_,?_,hold.2.2.2.1,hold.2.2.2.2⟩
  · rw [public_field machine done b _ pbase pkeep hostWord,slab,(hold.2.2.1 b h).1,
      Fin.val_cast_of_lt ((f0 cell).isLt.trans_le (Nat.pow_le_pow_right (by decide) fits₀))]
    have live : (decode A.degree config (fun _ _ j=>j) cell g.val).chips=sig:=(funext read.chips).trans chips
    have total:=boundary_count A native S ready names v coords hp scale psize whole common
    have small:exposed<2^sz₀:=(Nat.lt_succ_of_le publicRoom).trans_le (Nat.le_pow_clog (by decide) _)
    simp only [publicCell,digit_encode,live,ports,total,Fin.val_cast_of_lt small]
  · intro u j
    rw [family_digit machine done _ b abase akeep hostWord,slab,(hold.2.2.1 b h).2,
      Fin.val_cast_of_lt ((f7 cell).isLt.trans_le (Nat.pow_le_pow_right (by decide) fits₇))]
    have actual:=reached_argument (q:=q) A native S ready names v coords port hp scale psize whole common r code birth nodes arity
      aliases t config cell g.val index read prior chips u j
    have small:=reference_fits (q:=q) («H»:=hid) A native S ready names v port hp r code aliases publicRoom privateRoom u j
    change digit sz (loc ⟨u,j⟩).val (digit (sz*(N*M)) g.val (f7 cell).val)=_
    simp only [output,digit_encode,actual,Fin.val_cast_of_lt small]
    rfl

end Reached
end
end Hierarchy.DescentTerminalPointerIssue

end OAI
