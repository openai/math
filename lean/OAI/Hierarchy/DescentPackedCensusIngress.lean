import OAI.Hierarchy.DescentPackedSignedCensusRAM
import OAI.Hierarchy.DescentPackedHubBroadcast
import OAI.Hierarchy.DescentPackedMatchChooserInput

namespace OAI
/-! # From the old graph words to the census of the ordinary chooser -/
namespace Hierarchy.DescentPacking.PackedMatch.Local.Stage.Census
open DescentSixParty DescentSIMDLookup DescentPackedColony DescentPackedZip ProtocolRAM
open ThreeFlat.RAM PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section

def beginSum (origin H G M : ℕ) := origin+H*chunks G M+2^(Broadcast.widthBits H G M)

variable {F P J V : Type} [Field F] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
  {d k age G H M w : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {gadget : PoweredGadget F} {price ε : ℝ}
variable (A : GroupStage W gadget price ε J V k) (native : W.graph.Edge↪ℕ) (S : DescentCompiler.AtomSchedule)
  (ready : A.StateBounds S age) (groups : J≃Fin G) (hosts : V↪Fin H)
  (b origin out u : ℕ) (hubBank : Bank) (atom : Fin (2^k)→Expr) (wires : Fin (2^k)→Fin (2*A.cap)→Bank)
local notation "n" => H*chunks G M
local notation "radix" => 2^k
local notation "col" => order radix A.cap
local notation "start" => beginSum origin H G M
local notation "oldBits" => fun i=>(width A.degree A.cap b (Equiv.symm col i))
local notation "func" => fun i=>(contribution A.degree A.cap b (Equiv.symm col i))
local notation "flags" => Broadcast.result hubBank origin H G M
local notation "cable" => fun x j=>Expr.lookup (wires x j) Expr.row
local notation "src" => fun i=>(expr flags atom cable (Equiv.symm col i))
local notation "outBits" => (1+b+2*(2*A.cap))*radix
local notation "stamp" => DescentStaticWordColumn.program w origin (Broadcast.literal H G M) (2*n)
local notation "sumCPU" => DescentPackedColumnSum.program w start out u M outBits H G oldBits func src
local notation "first" => DescentStaticWordColumn.image origin (Broadcast.literal H G M)
local notation "second" => DescentPackedColumnSum.after start out u M outBits H G oldBits func src
local notation "signed_" => Prepare.signed A native S ready groups.toEmbedding hosts
local notation "slots_" => DescentSharedCableNames.Stage.signed A native S ready

theorem from_old (m : Memory w) (budget : max 1 (max b (DescentSignedCableCodec.width A.degree A.cap))≤u)
    (hubFit : hubBank.Fits w origin) (hspan : H≤hubBank.size)
    (hubRead : ∀h,m (hubBank.base+h.val)=((hub A hosts h).val:Word w))
    (aFit : ∀x,(atom x).Fits w origin) (aRead : ∀x,Source (atom x) (fun h g=>count A groups hosts b h g x) M m)
    (wFit : ∀x j,(wires x j).Fits w origin ∧ n≤(wires x j).size)
    (wRead : ∀x j,Reads (wires x j) (fun h g=>DescentSignedCableCodec.encode (signed_ x j h g)) M m)
    (later : DescentPackedColumnSum.finish start (columns radix A.cap) u M≤out) (room : out+n<2^w) :
    let done:=second (first m (2*n))
    ((stamp).seq sumCPU).Exec m done ((4+10*(2*n))+DescentPackedColumnSum.ticks start u M H G oldBits src) ∧
      (∀p : Row H G M,done (out+(row H G M p).val)=((data (A.rawCensus hosts groups slots_ b) p).val:Word w)) ∧
      (∀i,i<origin ∨ out+n ≤ i → done i=m i) ∧ CheapCode ((stamp).seq sumCPU) := by
  let m₁:=first m (2*n)
  have lower : origin ≤ start := (Nat.le_add_right origin (H*chunks G M)).trans
    (Nat.le_add_right _ (2^(Broadcast.widthBits H G M)))
  have next : start≤out := (Nat.le_add_right ..).trans later
  have wide : start<2^w:=next.trans_lt ((Nat.le_add_right ..).trans_lt room)
  have head := Broadcast.flag_source hubBank origin H G M (hub A hosts) m hubRead hubFit hspan wide
  obtain ⟨load,flag,fit,keep⟩:=head
  have before_ (i : ℕ) (hi : i<origin) : m₁ i=m i:=keep i (.inl hi)
  have present (x : Fin radix) : Source (atom x) (fun h g=>count A groups hosts b h g x) M m₁ :=
    fun p=>(eval_below (atom x) _ m m₁ (aFit x) before_).trans (aRead x p)
  have old (x : Fin radix) (j : Fin (2*A.cap)) :
      Source (cable x j) (fun h g=>DescentSignedCableCodec.encode (signed_ x j h g)) M m₁ := by
    have fitExpr : (cable x j).Fits w origin := ⟨(wFit x j).1,trivial⟩
    have data:=source_column (wires x j) origin (wFit x j).1 m _ (wFit x j).2 (wRead x j)
    exact fun p=>(eval_below (cable x j) _ m m₁ fitExpr before_).trans (data p)
  have passed:=issue A native S ready groups hosts b start out u flags atom cable m₁ budget fit
    (fun x=>ProtocolRAMGeneratedWrite.fits_mono _ lower (aFit x))
    (fun x j=>ProtocolRAMGeneratedWrite.fits_mono _ lower ⟨(wFit x j).1,trivial⟩) flag present old later room
  obtain ⟨run_,words,frame,cheap⟩:=passed
  refine ⟨?_,words,?_,@cheap_seq w stamp sumCPU
    (@DescentPackedColumnSum.mount_cheap w origin (Broadcast.literal H G M) (2*n)) @cheap⟩
  · intro P R K machine
    exact Procedure.Exec.then load run_ machine
  · intro i h
    rcases h with low|high
    · exact (frame i (.inl (low.trans_le lower))).trans (keep i (.inl low))
    · have padded : n≤2^(Broadcast.widthBits H G M) := (Nat.le_succ _).trans (Nat.le_pow_clog (by decide) _)
      have mounted : origin+2*n ≤ start := by
        change origin+2*n ≤ origin+n+2^(Broadcast.widthBits H G M)
        rw [Nat.two_mul,←Nat.add_assoc]
        exact Nat.add_le_add_left padded _
      exact (frame i (.inr high)).trans (keep i (.inr ((mounted.trans next).trans ((Nat.le_add_right out n).trans high))))

end
end Hierarchy.DescentPacking.PackedMatch.Local.Stage.Census

end OAI
