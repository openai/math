import OAI.Hierarchy.DescentOrdinarySignedAll

namespace OAI
/-! # Retained successor peer and first-grain ordinal at the physically rooted parent -/
namespace Hierarchy.DescentOrdinarySignedAll
open DescentSixParty DescentColonies DescentSharedCableNames DescentParallelBase DescentNextSignedWindow
open DescentSIMDLookup DescentPackedColony DescentPackedZip DescentResetSignedScan
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open scoped Classical BigOperators Fin.CommRing
noncomputable section
variable {X K H gg b M w : ℕ}
variable (base : ℕ) (header:Fin X→Fin K→Expr) (q:Ranks.Request X K) (a:Ranks.Inputs X K)
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
/-- The ordinary signed formatter leaves all three native weighted rank banks in
RAM. Its earlier unformatted header contains both true endpoint directions. -/
theorem retained_parents (m:Memory w)
    (peers:∀h (e f:Local C h),P₀ h e=P₀ h f ↔ other C h e=other C h f)
    (hf:∀x j,(header x j).Fits w base) (qf:∀x p j,(q x p j).Fits w base) (af:∀x p j t,(a x p j t).Fits w base)
    (hq:∀x p j,Source (q x p j) (fun h g=>encode b 5 (literal b (qry x p j h g))) M m)
    (ha:∀x p j t,Source (a x p j t) (fun h g=>encode b 5 (literal b (entries x p j t h g))) M m)
    (hd:∀x j,Source (header x j) (fun h g=>DescentResetFieldAssembler.raw b (src x j h g)) M m)
    (qRoom:∀x p j h g,DescentResetSignedScan.Fits b (qry x p j h g))
    (aRoom:∀x p j t h g,DescentResetSignedScan.Fits b (entries x p j t h g))
    (digits:max (A.degree+1) (A.cap+1)<2^b)
    (space:endAddress base X K A.cap b M H gg<2^w):
    let done:=memory base header q a A.degree A.cap b M H gg m
    (∀x p j,Source (readers x p j) (fun h g=>(DescentOrdinarySignedRanks.result C Z home fit x p j h g:Cell b)) M done) ∧
      (∀x j,Source (header x j) (fun h g=>DescentResetFieldAssembler.raw b (src x j h g)) M done) := by
  intro done
  let mid:=Ranks.memory base b b M H gg q a m
  have core:=any base header q a A.degree A.cap b M H gg m hf qf af space
  obtain ⟨lo,hi⟩:=ordered (X:=X) (K:=K) (b:=b) (M:=M) (H:=H) (gg:=gg) (cap:=A.cap) base
  have br:=hi.trans_lt space
  have capRoom : A.cap<2^b:=(Nat.le_succ _).trans_lt ((le_max_right _ _).trans_lt digits)
  have bound (x p j h g): (∑t,contribution (Ranks.parallelQuery p) (qry x p j h g) (entries x p j t h g))<2^b:=by
    rw [physical C Z P₀ home fit peers];exact result_small C Z home fit capRoom x p j h g
  have counted:=Ranks.run (paid:=b) base q a m qry entries qf af qRoom aRoom hq ha bound br
  let cell:=fun x p j h g=>(DescentOrdinarySignedRanks.result C Z home fit x p j h g:Cell b)
  have rFit (x p j):(readers x p j).Fits w next:=⟨Ranks.output_fits base x p j br,trivial⟩
  have rRead (x p j):Source (readers x p j) (cell x p j) M mid:=by
    intro r
    have valid:=Ranks.output_fits base x p j br
    rw [show (readers x p j).eval mid _ = _ from bank_read _ mid
      ((row H gg M r).isLt.trans_le (DescentDyadicSpan.span_ge _)) valid]
    apply (counted.2.1 x p j r).trans
    congr 2
    apply congrArg (fun u=>data u r)
    funext h g;apply Fin.ext
    change (∑t,contribution (Ranks.parallelQuery p) (qry x p j h g) (entries x p j t h g))=_
    rw [Fin.val_cast_of_lt (result_small C Z home fit capRoom x p j h g)]
    exact physical C Z P₀ home fit peers x p j h g
  have tail:=DescentResetWindowTail.any next X A.degree A.cap b M H gg header readers mid
    (fun x j=>ProtocolRAMGeneratedWrite.fits_mono _ lo (hf x j)) rFit space
  constructor
  · intro x p j r
    exact (ProtocolRAM.eval_below (readers x p j) _ mid done (rFit x p j)
      (fun addr lt=>tail.2.1 addr (.inl lt))).trans (rRead x p j r)
  · intro x j r
    exact (ProtocolRAM.eval_below (header x j) _ m done (hf x j)
      (fun addr lt=>core.2.1 addr (.inl lt))).trans (hd x j r)

omit [Fintype E] in
/-- Axis one is the first common-grain serial of the surviving raw parent
at either endpoint. The other two ranks are directional incidence positions. -/
theorem first_serial_at (x:Fin X) (v:Fin H) (g:Fin gg) (h:Host)
    (found:home x v g=some h) (e:Local C h):
    DescentOrdinarySignedRanks.result C Z home fit x 1 (Z.addr h e) v g=
      (Stage.source A native).serial (C.src e.val) (C.dst e.val) (C.order ⟨e.val,⟨0,e.property.1⟩⟩) := by
  simp [DescentOrdinarySignedRanks.result, request, found, resident_at, point, Ranks.parallelQuery, DescentOrdinarySignedRanks.value]

omit [Fintype E] in
theorem peer_at (x:Fin X) (v:Fin H) (g:Fin gg) (h:Host)
    (found:home x v g=some h) (e:Local C h) (f:Roster.Face A native C h) (same:f.val.1=e.val):
    DescentResetFieldAssembler.peer (src x (Z.addr h e) v g)=
      (DescentResetWindowFields.neighbor A native S ready names C h f).val := by
  simp only [DescentOrdinarySignedWindows.header,found,Option.elim_some]
  rw [DescentOrdinarySignedMeta.meta_at]
  exact DescentOrdinarySignedMeta.live_peer A native S ready names C marked h e f same

end
end Hierarchy.DescentOrdinarySignedAll

end OAI
