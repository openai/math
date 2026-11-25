import OAI.Hierarchy.DescentDatedSeedInputText
import OAI.Hierarchy.DescentDatedSeedPublicCode
import OAI.Hierarchy.DescentDatedSeedBounds
import OAI.Hierarchy.DescentExteriorCountedTape

namespace OAI
/-! # Native seed initialization on the original private bit proposal -/
namespace Hierarchy.DescentDatedSeedStartup.Input
open DescentSeedRoot DescentPackedSeed DescentTerminalEpochChart DescentPackedEpochShelves DescentPackedProfileInstall
open DescentInitialHost DescentColonies DescentSIMDLookup DescentExteriorShelf DescentExterior
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM Catalyst Computability.BorderVNP.Crossing ThreeFlat.Diagonal
open ThreeFlat.RAM PhysicalProcedure DescriptorExpr
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {F J A : Type} [Field F] [Fintype J] [DecidableEq J] {k p R d G H e j r t : ℕ}
variable (X : Approximation F k p) (name : J≃Fin G) (digits : Fin R≃J×Block d)
  (host : Vertex X↪Fin H) (l : Layout) (w : ℕ)
variable (seed : Select X R l.seedWidth→ A) (lo C grain : ℕ) (ss : List (Source A))
variable (origin extra : ℕ) (x : Fin e→ Plane j r→ Fin t→ Bool) (z : A⊕Hidden e j r t→ Bool) (back : Memory w)
local notation "lowEnd" => end_ (lo+extent grain ss) C grain
local notation "front" => Root.packedImage X R l.seedWidth w seed lo C grain ss origin x z
local notation "frontSize" => origin+17*span j r t e
local notation "raw" => Root.appended frontSize extra front back
local notation "counted" => Root.countedAt X R l.seedWidth w seed z raw
local notation "verdictStart" => DescentTerminalPackedSeedFlags.endInput X R l.seedWidth w ([] : List (Source A))
local notation "nRows" => DescentPackedSeed.rows X R l.seedWidth w
local notation "checker" => DescentTerminalPackedSeedFlags.check X R l.seedWidth w ([] : List (Source A))
local notation "middle" => DescentDatedSeedStartup.program X name digits host l w
local notation "done" => output X name digits host l counted
local notation "top" => endAddress X l H G d

set_option maxHeartbeats 1200000 in
omit [Fintype J] [DecidableEq J] in
theorem run (wideSeed : 2*digitsNeeded l.seedWidth≤ w)
    (wideSigned : DescentSignedCableCodec.width 3 256*l.packedLanes≤ w)
    (wideOperand : l.operandBits*l.operandLanes≤ w)
    (seedFits : verdictStart+(nRows+1)<2^w)
    (seedBefore : verdictStart+(nRows+1)≤ lo) (shelvesBefore : lowEnd≤ origin)
    (baseAfter : frontSize+extra≤ l.base) (room : top<2^w) :
    (program (A:=A) X name digits host l w).Exec raw done (clock X l w H G d R) ∧
    CheapCode (program (A:=A) X name digits host l w) ∧
    (done (verdictStart+nRows)=0 ↔ DescentSeedRoot.valid X ((z∘Sum.inl)∘seed)) ∧
    Loaded origin (fun _=>LinearEquiv.refl _ _) x (z∘Sum.inr) done ∧
    (∀a,a< verdictStart ∨ verdictStart+(nRows+1)≤ a →
      a< l.base ∨ top≤ a → done a=raw a) := by
  have seedCheck:=Root.counted_on X R l.seedWidth w seed lo C grain ss origin x z raw
    (fun a h=>Root.append_low _ _ _ _ h) wideSeed seedFits seedBefore shelvesBefore
  have build : (middle).Exec counted done (DescentDatedSeedStartup.clock X l H G d) :=
    execute X name digits host l counted wideSigned wideOperand room
  have keep:=retain X name digits host l counted wideSigned wideOperand room
  have ahead : lo≤ lowEnd := by dsimp only [end_,DescentPackedProfileInstall.dict];omega
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro P regs K machine
    exact Procedure.Exec.then (A:=checker) (B:=middle) (a:=raw) (b:=counted) (c:=done)
      (ca:=4+(nRows+1)*66) (cb:=DescentDatedSeedStartup.clock X l H G d) seedCheck.1 build machine
  · change CheapCode ((checker).seq middle)
    exact @cheap_seq w checker middle (@And.left _ _ seedCheck.2)
      (@And.left _ _ (hardware X name digits host l w))
  · rw [keep _ (Or.inl (by omega))]
    exact seedCheck.2.2.1
  · intro col idx live
    have c:=col.isLt
    have high:=Nat.mul_le_mul_right (span j r t e) (show col.val+1≤17 by omega)
    rw [Nat.succ_mul] at high
    change done (origin+col.val*span j r t e+idx)=_
    rw [keep _ (Or.inl (by omega))]
    exact seedCheck.2.2.2.1 col idx live
  · intro a first second
    exact (keep a second).trans (seedCheck.2.2.2.2 a first)

omit [Fintype J] [DecidableEq J] in
/-- The native count in cell zero counts all original copies, including isolated sites. -/
theorem source_count (wideSeed : 2*digitsNeeded l.seedWidth≤ w)
    (wideSigned : DescentSignedCableCodec.width 3 256*l.packedLanes≤ w)
    (wideOperand : l.operandBits*l.operandLanes≤ w) (seedFits : verdictStart+(nRows+1)<2^w)
    (seedBefore : verdictStart+(nRows+1)≤ lo) (shelvesBefore : lowEnd≤ origin)
    (baseAfter : frontSize+extra≤ l.base) (room : top<2^w) :
    done 0=((R*Fintype.card (Vertex X):ℕ):Word w) := by
  have start : 0< DescentTerminalPackedSeedFlags.start X R l.seedWidth w := by
    unfold DescentTerminalPackedSeedFlags.start
    exact Nat.add_pos_right _ (Nat.two_pow_pos _)
  have dictionary : 0<(DescentTerminalPackedSeedFlags.dictionary X R l.seedWidth w ([] : List (Source A))).base := by
    change 0< DescentTerminalPackedSeedFlags.start X R l.seedWidth w+_
    omega
  have verdict : 0< verdictStart := by
    unfold DescentTerminalPackedSeedFlags.endInput
    omega
  have ahead : lo≤ lowEnd := by dsimp only [end_,DescentPackedProfileInstall.dict];omega
  have receipt:=run X name digits host l w seed lo C grain ss origin extra x z back
    wideSeed wideSigned wideOperand seedFits seedBefore shelvesBefore baseAfter room
  rw [receipt.2.2.2.2 0 (Or.inl verdict) (Or.inl (by omega)),
    Root.append_low _ _ _ _ (by omega),
    Root.packed_original X R l.seedWidth w seed lo C grain ss origin x z shelvesBefore (by omega)]
  unfold DescentPackedEpochShelves.original
  rw [DescentPackedEpochShelves.frame _ _ _ _ _ _ (by omega),
    DescentTerminalPackedSeedFlags.lower _ _ _ _ _ _ _ dictionary]
  unfold DescentTerminalPackedSeedFlags.before
  rw [DescentTerminalEpochHeader.initial_frame _ _ _ _ start]
  exact DescentPackedSeed.site_count X w _

end
end Hierarchy.DescentDatedSeedStartup.Input

end OAI
