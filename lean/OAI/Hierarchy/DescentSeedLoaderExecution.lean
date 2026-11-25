import OAI.Hierarchy.DescentSeedNativeCompleteCode
import OAI.Hierarchy.DescentSeedCompleteImage
import OAI.Hierarchy.DescentSeedTokenRun

namespace OAI
/-! # Fixed execution of the complete initial loader on arbitrary memory -/
namespace Hierarchy.DescentDatedSeedStartup.Input
open DescentSixParty DescentCompiler DescentInitialHost DescentSeedRoot DescentPackedSeed
open DescentSeedInitialTable DescentColonies DescentSIMDLookup DescentPackedColony DescentDyadicSpan
open Computability.VPVNP.BurstRAM PrivateRAM Catalyst Catalyst.Approximation ProtocolRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {F : Type} [Field F] {S : AtomSchedule} (G : PoweredGadget F) (op : RotorSpec)
  {k cp p H : ℕ} (X : Approximation F cp p)
  (digits : Fin S.copies ≃ Fin (S.groupCount 0)×Block k)
  (publicWide : Fintype.card (Vertex X) ≤ H) (l : Layout) (header payload Z : ℕ) {w : ℕ}
local notation "g₀" => S.groupCount 0
local notation "hs" => (Fintype.equivFin (Vertex X)).toEmbedding.trans (Fin.castLEEmb publicWide)
local notation "top" => endAddress X l H g₀ k
local notation "chart" => nodeChart l k H g₀
local notation "Q" => nodeArities X publicWide l
local notation "finish" => (chart).seedEnd top
local notation "lanes" => DescentDatedSeedStartup.Primitive.paletteLanes G op l.seedWidth Z payload k
local notation "limit" => DescentDatedSeedStartup.Primitive.initialEnd X S.copies l.seedWidth payload k H g₀ lanes finish
local notation "jobs" => DescentPackedSeed.Primitive.Source.jobs X S.copies l.seedWidth payload

theorem afterCount_cheap : CheapCode (afterCount X digits publicWide l header w) :=by
  let first := DescentDatedSeedStartup.program X (Equiv.refl _) digits hs l w
  let clear := DescentPrivateHeader.clearHeader w header
  let nodes := (chart).seedProgram top w Q
  change CheapCode ((first.seq clear).seq nodes)
  exact @cheap_seq w (first.seq clear) nodes
    (@cheap_seq w first clear (@And.left _ _ (hardware X (Equiv.refl _) digits hs l w))
      (DescentPrivateHeader.initialize_cheap w header))
    ((chart).seedCheap top w Q)

theorem completeAfter_cheap {w:ℕ}
    (source:publicWords X+DescentDyadicSpan.span jobs≤finish) (space:limit<2^w)
    (fits:payload≤w) (live:0<lanes) : ProtocolRAM.CheapCode (completeAfter G op X digits publicWide l header payload Z w) :=by
  let first := afterCount X digits publicWide l header w
  let roles := Primitive.program X G op S.copies l.seedWidth Z payload k H g₀ lanes finish hs w
  have issued := Primitive.any X G op S.copies l.seedWidth Z payload k H g₀ lanes finish hs
    ((fun _=>0) : Memory w) source space fits live
  change CheapCode (first.seq roles)
  exact @cheap_seq w first roles (afterCount_cheap (w:=w) X digits publicWide l header)
    (@And.left _ _ (@And.right _ _ issued))

/-- Run the signed and operand writers, initialize the private counter, and publish both node fields. -/
theorem after_count_any (m : Memory w)
    (signed : DescentSignedCableCodec.width 3 256*l.packedLanes ≤ w)
    (fields : l.operandBits*l.operandLanes ≤ w) (early : header < l.base) (room : finish < 2^w) :
    let out := afterCountImage X digits publicWide l header m
    (afterCount X digits publicWide l header w).Exec m out (afterCountTicks (S:=S) (H:=H) (k:=k) X l) ∧
    out header=0 ∧ ∀a,a≠header → a<l.base ∨ finish≤a → out a=m a :=by
  intro out
  let middle:=output X (Equiv.refl _) digits hs l m
  have bounds:=fences X l H g₀ k
  have first : l.base ≤ top:=bounds.1.trans (bounds.2.1.trans bounds.2.2)
  have second : top ≤ finish:=(Nat.le_add_right top _).trans (Nat.le_add_right ..)
  have build : (DescentDatedSeedStartup.program X (Equiv.refl _) digits hs l w).Exec
      m middle (DescentDatedSeedStartup.clock X l H g₀ k) :=
    execute X (Equiv.refl _) digits hs l m signed fields (second.trans_lt room)
  have kept:=retain X (Equiv.refl _) digits hs l m signed fields (second.trans_lt room)
  have clear : (DescentPrivateHeader.clearHeader w header).Exec middle
      (DescentPrivateHeader.initialized header middle) 10 :=
    DescentPrivateHeader.initialize_run header middle (by omega)
  obtain ⟨metaRun,framed,_⟩:=(chart).seedIssued top Q (DescentPrivateHeader.initialized header middle) room
  refine ⟨?_,(framed header (.inl (early.trans_le first))).trans (DescentPrivateHeader.initialized_read header middle),?_⟩
  · intro np nk nr machine pc reg pub exit install advice cfg ini status same
    exact Procedure.Exec.then (Procedure.Exec.then build clear) metaRun machine pc reg pub exit install advice cfg ini status same
  · intro a apart outside
    exact (framed a (by omega)).trans ((DescentPrivateHeader.initialized_frame header middle a apart).trans (kept a (by omega)))

/-- The complete fixed post-validation program also publishes the original packed primitive words. -/
theorem complete_any (m : Memory w) (signed : DescentSignedCableCodec.width 3 256*l.packedLanes ≤ w)
    (fields : l.operandBits*l.operandLanes ≤ w) (early : header < l.base) (sourceSpace : publicWords X+span jobs ≤ finish)
    (live : 0 < lanes) (machine : payload ≤ w) (space : limit < 2^w) :
    let out:=completeImage G op X digits publicWide l header payload Z m
    (completeAfter G op X digits publicWide l header payload Z w).Exec m out
      (completeTicks (S:=S) (k:=k) G op X publicWide l payload Z w) ∧
    out header=0 ∧ ∀a,a≠header → a<l.base ∨ limit≤a → out a=m a :=by
  intro out
  let prev:=afterCountImage X digits publicWide l header m
  have bounds:=fences X l H g₀ k
  have first : l.base ≤ top:=bounds.1.trans (bounds.2.1.trans bounds.2.2)
  have second : top ≤ finish:=(Nat.le_add_right top _).trans (Nat.le_add_right ..)
  obtain ⟨lo,hi⟩:=DescentDatedSeedStartup.Primitive.fences X S.copies l.seedWidth payload k H g₀ lanes finish
  have upper : finish ≤ limit:=lo.trans hi
  obtain ⟨build,zero,kept⟩:=after_count_any X digits publicWide l header m signed fields early (upper.trans_lt space)
  obtain ⟨arr,_,framed⟩:=DescentDatedSeedStartup.Primitive.any X G op S.copies l.seedWidth Z payload k H g₀ lanes finish hs
    prev sourceSpace space machine live
  refine ⟨?_, (framed header (.inl (early.trans_le (first.trans second)))).trans zero,?_⟩
  · intro np nk nr cpu pc reg pub exit install advice cfg ini status same
    exact Procedure.Exec.then build arr cpu pc reg pub exit install advice cfg ini status same
  · rintro a apart (low|high)
    · exact (framed a (.inl (low.trans_le (first.trans second)))).trans (kept a apart (.inl low))
    · exact (framed a (.inr high)).trans (kept a apart (.inr (upper.trans high)))

end
end Hierarchy.DescentDatedSeedStartup.Input

end OAI
