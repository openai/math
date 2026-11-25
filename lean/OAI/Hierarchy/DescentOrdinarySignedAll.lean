import OAI.Hierarchy.DescentOrdinarySignedWindows
import OAI.Hierarchy.DescentResetWindowTail

namespace OAI
/-! A single public ordinary program counts all three local positions before
formatting and rendering every signed slot in its padded destination sheet. -/
namespace Hierarchy.DescentOrdinarySignedAll
open DescentSixParty DescentColonies DescentSharedCableNames DescentParallelBase DescentNextSignedWindow
open DescentSIMDLookup DescentPackedColony DescentPackedZip DescentResetSignedScan
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open scoped Classical BigOperators Fin.CommRing
noncomputable section
variable {X K H gg b M w : ℕ}
abbrev Tail (base X K b M H gg : ℕ):=Ranks.endAddress base X K b M H gg
def ranks (base X K b M H gg : ℕ) (x : Fin X) (p:Fin 3) (j:Fin K) : Expr:=
  .lookup (Ranks.output base X K b M H gg x p j) .row
def endAddress (base X K cap b M H gg : ℕ):=
  DescentResetWindowTail.endAddress (Tail base X K b M H gg) X cap b M H gg
def page (base X K cap b M H gg : ℕ) (x:Fin X) (j:Fin (2*cap)):=
  DescentResetWindowTail.page (Tail base X K b M H gg) X cap b M H gg x j
variable (base : ℕ) (header:Fin X→Fin K→Expr) (q:Ranks.Request X K) (a:Ranks.Inputs X K)
def program (D cap b M H gg w : ℕ) :=
  (Ranks.program base b b M H gg w q a).seq
    (DescentResetWindowTail.program (Tail base X K b M H gg) X D cap b M H gg w header (ranks base X K b M H gg))
def memory (D cap b M H gg : ℕ) (m:Memory w) :=
  DescentResetWindowTail.memory (Tail base X K b M H gg) X D cap b M H gg header (ranks base X K b M H gg)
    (Ranks.memory base b b M H gg q a m)
def time (D cap b M H gg : ℕ) :=
  Ranks.time base b b M H gg q a+
    DescentResetWindowTail.time (Tail base X K b M H gg) X D cap b M H gg header (ranks base X K b M H gg)
theorem ordered {cap b M H gg : ℕ} :
    base≤Tail base X K b M H gg ∧ Tail base X K b M H gg≤endAddress base X K cap b M H gg:=by
  constructor
  · exact (Nat.le_add_right ..).trans (Nat.le_add_right ..)
  · exact (Nat.le_add_right ..).trans (DescentResetWindowTail.lower ..)

theorem any (D cap b M H gg : ℕ) (m:Memory w)
    (hf:∀x j,(header x j).Fits w base) (qf:∀x p j,(q x p j).Fits w base) (af:∀x p j t,(a x p j t).Fits w base)
    (space:endAddress base X K cap b M H gg<2^w):
    let done:=memory base header q a D cap b M H gg m
    (program base header q a D cap b M H gg w).Exec m done (time base header q a D cap b M H gg) ∧
    (∀u,u<base ∨ endAddress base X K cap b M H gg≤u→done u=m u) ∧ CheapCode (program base header q a D cap b M H gg w):=by
  intro done
  obtain ⟨lo,hi⟩:=ordered (X:=X) (K:=K) (b:=b) (M:=M) (H:=H) (gg:=gg) (cap:=cap) base
  have run₀:=Ranks.any (paid:=b) base q a m qf af (hi.trans_lt space)
  have fits (x p j):(ranks base X K b M H gg x p j).Fits w (Tail base X K b M H gg):=
    ⟨Ranks.output_fits base x p j (hi.trans_lt space),trivial⟩
  have run₁:=DescentResetWindowTail.any (Tail base X K b M H gg) X D cap b M H gg header (ranks base X K b M H gg) (Ranks.memory base b b M H gg q a m)
    (fun x j=>ProtocolRAMGeneratedWrite.fits_mono _ lo (hf x j)) fits space
  refine ⟨Procedure.Exec.then run₀.1 run₁.1,?_,ProtocolRAM.cheap_seq run₀.2.2 run₁.2.2⟩
  intro u h
  rcases h with low|high
  · exact (run₁.2.1 u (.inl (low.trans_le lo))).trans (run₀.2.1 u (.inl low))
  · exact (run₁.2.1 u (.inr high)).trans (run₀.2.1 u (.inr (hi.trans high)))

open DescentOrdinarySignedRanks DescentOrdinarySignedWindows
variable {F P V J E : Type} [Field F] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V] [Fintype E]
  {d k i Q T : ℕ} {bits:P→ℕ} {W:MarkedWorld F d P bits} {G:PoweredGadget F} {price ε:ℝ}
  (A:GroupStage W G price ε J V k) (native:W.graph.Edge↪ℕ) (S:DescentCompiler.AtomSchedule) (ready:A.StateBounds S i)
local notation "Host" => Stage.Host J V k
variable (names:Stage.Host J V k↪ℕ) (C:Blocks (Stage.source A native) E) (marked:E→Prop)
  (Z:Incidence.Census C Q T A.cap K) (P₀:∀h,Local C h→ℕ) (home:Fin X→Fin H→Fin gg→Option (Stage.Host J V k))
local notation "fit" => Stage.measured A native S ready
local notation "qry" => query C Z P₀ home
local notation "entries" => items C Z P₀ home
local notation "src" => DescentOrdinarySignedWindows.header A native S ready names C marked Z home
local notation "raw" => rows A native S ready names C marked Z home
local notation "aim" => target A native S ready names home
local notation "next" => Tail base X K b M H gg
local notation "T₀" => DescentResetWindowTail.next next b M
local notation "readers" => ranks base X K b M H gg

theorem issued_ranks (m:Memory w) (emit:DescentResetWindowFields.Emission A native C marked)
    (peers:∀h (e f:Local C h),P₀ h e=P₀ h f ↔ other C h e=other C h f)
    (hf:∀x j,(header x j).Fits w base) (qf:∀x p j,(q x p j).Fits w base) (af:∀x p j t,(a x p j t).Fits w base)
    (hq:∀x p j,Source (q x p j) (fun h g=>encode b 5 (literal b (qry x p j h g))) M m)
    (ha:∀x p j t,Source (a x p j t) (fun h g=>encode b 5 (literal b (entries x p j t h g))) M m)
    (hd:∀x j,Source (header x j) (fun h g=>DescentResetFieldAssembler.raw b (src x j h g)) M m)
    (qRoom:∀x p j h g,DescentResetSignedScan.Fits b (qry x p j h g))
    (aRoom:∀x p j t h g,DescentResetSignedScan.Fits b (entries x p j t h g))
    (rawRoom:∀x j h g f,DescentResetFieldAssembler.digits (src x j h g) f<2^b)
    (digits:max (A.degree+1) (A.cap+1)<2^b)
    (space:endAddress base X K A.cap b M H gg<2^w):
    let done:=memory base header q a A.degree A.cap b M H gg m
    (∀x p j,(readers x p j).Fits w (endAddress base X K A.cap b M H gg) ∧
      Source (readers x p j) (fun h g=>(result C Z home fit x p j h g:Cell b)) M done) ∧
    (program base header q a A.degree A.cap b M H gg w).Exec m done (time base header q a A.degree A.cap b M H gg) ∧
    (∀x j,Reads (page base X K A.cap b M H gg x j) (fun h g=>DescentSignedCableCodec.encode (aim x j h g)) M done) ∧
    (∀u,u<base ∨ endAddress base X K A.cap b M H gg≤u→done u=m u) ∧ CheapCode (program base header q a A.degree A.cap b M H gg w):=by
  intro done
  let mid:=Ranks.memory base b b M H gg q a m
  have core:=any base header q a A.degree A.cap b M H gg m hf qf af space
  obtain ⟨lo,hi⟩:=ordered (X:=X) (K:=K) (b:=b) (M:=M) (H:=H) (gg:=gg) (cap:=A.cap) base
  have br:=hi.trans_lt space
  have hr:= (DescentResetWindowTail.lower next X A.cap b M H gg).trans_lt space
  have capRoom : A.cap<2^b:=(Nat.le_succ _).trans_lt ((le_max_right _ _).trans_lt digits)
  have bound (x p j h g): (∑t,contribution (Ranks.parallelQuery p) (qry x p j h g) (entries x p j t h g))<2^b:=by
    rw [physical C Z P₀ home fit peers];exact result_small C Z home fit capRoom x p j h g
  have counted:=Ranks.run (paid:=b) base q a m qry entries qf af qRoom aRoom hq ha bound br
  let cell:=fun x p j h g=>(result C Z home fit x p j h g:Cell b)
  have rFit (x p j):(readers x p j).Fits w next:=⟨Ranks.output_fits base x p j br,trivial⟩
  have rRead (x p j):Source (readers x p j) (cell x p j) M mid:=by
    intro r
    have valid:=Ranks.output_fits base x p j br
    rw [show (readers x p j).eval mid _ = _ from bank_read _ mid
      ((row H gg M r).isLt.trans_le (DescentDyadicSpan.span_ge _)) valid]
    apply (counted.2.1 x p j r).trans
    congr 2
    apply congrArg (fun u=>DescentSIMDLookup.data u r)
    funext h g;apply Fin.ext
    change (∑t,contribution (Ranks.parallelQuery p) (qry x p j h g) (entries x p j t h g))=_
    rw [Fin.val_cast_of_lt (result_small C Z home fit capRoom x p j h g)]
    exact physical C Z P₀ home fit peers x p j h g
  have held (x j):Source (header x j) (fun h g=>DescentResetFieldAssembler.raw b (src x j h g)) M mid:=
    fun r=>(ProtocolRAM.eval_below (header x j) _ m mid (hf x j) (fun addr lt=>counted.2.2.1 addr (.inl lt))).trans (hd x j r)
  have format:=DescentResetFieldAssembler.run next header readers mid src cell
    (fun x j=>ProtocolRAMGeneratedWrite.fits_mono _ lo (hf x j)) rFit held rRead rawRoom hr
  have input (x j slot f):Source (DescentResetWindowTail.fields next b M A.cap header readers x j slot f)
      (fun h g=>(Native.fields (raw x h g slot) f:Cell b)) M (DescentResetFieldAssembler.memory next b M mid):=by
    simpa only [DescentResetWindowTail.fields,cell,Fin.val_cast_of_lt (result_small C Z home fit capRoom _ _ _ _ _),
      field_eq A native S ready names C marked Z home] using format.2.2.1 x slot f
  have now:=Native.All.run T₀ (DescentResetWindowTail.fields next b M A.cap header readers)
    (DescentResetFieldAssembler.memory next b M mid) raw aim (fun x _=>format.2.1 x) input
    (fun x h g slot f=>(small A native S ready names C marked Z home x h g slot f).trans_lt digits)
    (fun x j h g=>(scope A native S ready names C marked Z home emit x h g j).1)
    (fun x j h g=>(scope A native S ready names C marked Z home emit x h g j).2) space
  have tail:=DescentResetWindowTail.any next X A.degree A.cap b M H gg header readers mid
    (fun x j=>ProtocolRAMGeneratedWrite.fits_mono _ lo (hf x j)) rFit space
  refine ⟨?_,core.1,now.2.1,core.2⟩
  intro x p j
  refine ⟨ProtocolRAMGeneratedWrite.fits_mono _ hi (rFit x p j),?_⟩
  intro row
  exact (ProtocolRAM.eval_below (readers x p j) _ mid done (rFit x p j)
    (fun a small=>tail.2.1 a (.inl small))).trans (rRead x p j row)
theorem issued (m:Memory w) (emit:DescentResetWindowFields.Emission A native C marked)
    (peers:∀h (e f:Local C h),P₀ h e=P₀ h f ↔ other C h e=other C h f)
    (hf:∀x j,(header x j).Fits w base) (qf:∀x p j,(q x p j).Fits w base) (af:∀x p j t,(a x p j t).Fits w base)
    (hq:∀x p j,Source (q x p j) (fun h g=>encode b 5 (literal b (qry x p j h g))) M m)
    (ha:∀x p j t,Source (a x p j t) (fun h g=>encode b 5 (literal b (entries x p j t h g))) M m)
    (hd:∀x j,Source (header x j) (fun h g=>DescentResetFieldAssembler.raw b (src x j h g)) M m)
    (qRoom:∀x p j h g,DescentResetSignedScan.Fits b (qry x p j h g))
    (aRoom:∀x p j t h g,DescentResetSignedScan.Fits b (entries x p j t h g))
    (rawRoom:∀x j h g f,DescentResetFieldAssembler.digits (src x j h g) f<2^b)
    (digits:max (A.degree+1) (A.cap+1)<2^b)
    (space:endAddress base X K A.cap b M H gg<2^w):
    let done:=memory base header q a A.degree A.cap b M H gg m
    (program base header q a A.degree A.cap b M H gg w).Exec m done (time base header q a A.degree A.cap b M H gg) ∧
    (∀x j,Reads (page base X K A.cap b M H gg x j) (fun h g=>DescentSignedCableCodec.encode (aim x j h g)) M done) ∧
    (∀u,u<base ∨ endAddress base X K A.cap b M H gg≤u→done u=m u) ∧ CheapCode (program base header q a A.degree A.cap b M H gg w):=by
  exact (issued_ranks base header q a A native S ready names C marked Z P₀ home m emit peers hf qf af hq ha hd qRoom aRoom rawRoom digits space).2
end
end Hierarchy.DescentOrdinarySignedAll

end OAI
