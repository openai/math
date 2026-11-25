import OAI.Hierarchy.DescentSeedLoaderExecution
import OAI.Hierarchy.DescentSeedExteriorVote
import OAI.Hierarchy.DescentExteriorAppendedWords
import OAI.Hierarchy.DescentSeedSourceExtent

namespace OAI
/-! # Executing the complete initializer on every original ballot and exterior witness -/
namespace Hierarchy.DescentDatedSeedStartup.Input
open DescentInitialHost DescentCompiler DescentSixParty DescentColonies
open DescentSeedRoot DescentPackedSeed DescentPackedColony DescentSIMDLookup DescentSeedInitialTable
open DescentExterior DescentGL DescentTerminalEpochChart DescentPackedEpochShelves DescentExteriorShelf
open DescentPackedProfileInstall Computability.VPVNP.BurstRAM PrivateRAM Catalyst Catalyst.Approximation Computability.BorderVNP.Crossing
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {F P : Type} [Field F] {S : AtomSchedule} (D : PoweredGadget F) (op : RotorSpec)
  {k cp p H e j r t w : ℕ} (X : Approximation F cp p) (radix : S.radix=2^k)
  (publicWide : Fintype.card (Vertex X) ≤ H) (l : Layout) (header payload Z : ℕ)
  (seed : Select X S.copies l.seedWidth → P) (lo C grain : ℕ) (ss : List (Source P)) (origin extra : ℕ)
  (ex : Fin e → Plane j r → Fin t → Bool) (z : P⊕Hidden e j r t → Bool) (back : Memory w)
local notation "G" => S.groupCount 0
local notation "digits" => S.initialDigits radix
set_option quotPrecheck false
local notation "hs" => (Fintype.equivFin (Vertex X)).toEmbedding.trans (Fin.castLEEmb publicWide)
local notation "top" => endAddress X l H G k
local notation "chart" => nodeChart l k H G
local notation "finish" => (chart).seedEnd top
local notation "lowEnd" => end_ (lo+extent grain ss) C grain
local notation "front" => origin+17*DescentExteriorShelf.span j r t e
local notation "raw" => Root.appended front extra (Root.widePackedImage X S.copies l.seedWidth payload w seed lo C grain ss origin ex z) back
local notation "counted" => DescentWideSeedFlags.countedAt X S.copies l.seedWidth payload seed (z∘Sum.inl) raw
local notation "flag" => DescentWideSeedFlags.endInput X S.copies l.seedWidth payload
local notation "entries" => DescentPackedSeed.rows X S.copies l.seedWidth payload
local notation "jobs" => DescentPackedSeed.Primitive.Source.jobs X S.copies l.seedWidth payload
local notation "lanes" => Primitive.paletteLanes D op l.seedWidth Z payload k
local notation "cap" => Primitive.initialEnd X S.copies l.seedWidth payload k H G lanes finish
local notation "done" => completeImage D op X digits publicWide l header payload Z counted
theorem profile_start_le_end (lo C grain : ℕ) (ss : List (Source P)) :
    lo ≤ end_ (lo+extent grain ss) C grain := by
  calc
    lo ≤ lo+extent grain ss := Nat.le_add_right ..
    _ ≤ (DescentPackedProfileInstall.dict (lo+extent grain ss) C grain).base := Nat.le_add_right ..
    _ ≤ end_ (lo+extent grain ss) C grain := Nat.le_add_right ..

omit [Field F] in
theorem role_space_after_header (width : 16*digitsNeeded l.seedWidth ≤ payload)
    (ordered : flag ≤ header) (early : header < l.base) :
    publicWords X+DescentDyadicSpan.span jobs ≤ finish :=by
  have rooms:=fences X l H G k
  have start : l.base ≤ top:=rooms.1.trans (rooms.2.1.trans rooms.2.2)
  have stop : top ≤ finish:=(Nat.le_add_right top _).trans (Nat.le_add_right ..)
  exact (Root.role_source_extent X S.copies l.seedWidth payload width).trans
    (ordered.trans (early.le.trans (start.trans stop)))

theorem execute_proposal (width : 16*digitsNeeded l.seedWidth ≤ payload)
    (live : 0 < lanes) (machine : payload ≤ w)
    (signed : DescentSignedCableCodec.width 3 256*l.packedLanes ≤ w) (fields : l.operandBits*l.operandLanes ≤ w)
    (seedFits : flag+(entries+1) < 2^w) (seedBefore : flag+(entries+1) ≤ lo)
    (shelves : lowEnd ≤ origin) (privateAfter : front+extra ≤ header) (early : header < l.base) (space : cap < 2^w) :
    let cpu:=completeProgram D op X publicWide l header payload Z radix (w:=w)
    cpu.Exec raw done (4+(entries+1)*66+completeTicks (S:=S) (k:=k) D op X publicWide l payload Z w) ∧
    ProtocolRAM.CheapCode cpu ∧ done header=0 ∧
    (done (flag+entries)=0 ↔ valid X ((z∘Sum.inl)∘seed)) ∧
    Loaded origin (fun _=>LinearEquiv.refl _ _) ex (z∘Sum.inr) done ∧
    ∀a,a≠header → (a < flag ∨ flag+(entries+1) ≤ a) → (a < l.base ∨ cap ≤ a) → done a=raw a :=by
  dsimp only
  have root:=Root.wideCounted_on X S.copies l.seedWidth payload w seed lo C grain ss origin ex z raw
    (fun _ h=>Root.append_low _ _ _ _ h) (by omega) seedFits seedBefore shelves
  have lowLo : lo ≤ lowEnd := profile_start_le_end lo C grain ss
  have source:=role_space_after_header X l (S:=S) (k:=k) (H:=H) header payload width (by omega) early
  obtain ⟨run,zero,kept⟩:=complete_any D op X digits publicWide l header payload Z counted signed fields early source live machine space
  have flagBelow : flag+entries < header:=by omega
  refine ⟨?_,?_,zero,?_,?_,?_⟩
  · intro np nk nr M pc reg pub exit install advice cfg ini status same
    exact Procedure.Exec.then root.1 run M pc reg pub exit install advice cfg ini status same
  · let check := DescentWideSeedFlags.check X S.copies l.seedWidth payload w
    let build := completeAfter D op X digits publicWide l header payload Z w
    change ProtocolRAM.CheapCode ((check).seq build)
    exact @ProtocolRAM.cheap_seq w check build (@And.left _ _ (@And.right _ _ root))
      (completeAfter_cheap D op X digits publicWide l header payload Z source space machine live)
  · rw [kept _ flagBelow.ne (.inl (flagBelow.trans early))]
    exact root.2.2.1
  · intro col i hi
    have bound:=Nat.mul_le_mul_right (DescentExteriorShelf.span j r t e) (show col.val+1 ≤ 17 by have:=col.isLt;omega)
    rw [Nat.add_mul,Nat.one_mul] at bound
    have below : origin+col.val*DescentExteriorShelf.span j r t e+i < header:=by omega
    exact (kept _ below.ne (.inl (below.trans early))).trans (root.2.2.2.1 col i hi)
  · intro a away outsideBallot outsideTables
    exact (kept a away outsideTables).trans (root.2.2.2.2 a outsideBallot)

end
end Hierarchy.DescentDatedSeedStartup.Input

end OAI
