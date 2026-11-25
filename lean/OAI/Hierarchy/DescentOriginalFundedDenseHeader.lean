import OAI.Hierarchy.DescentDatedSeedRetainedGrain
import OAI.Hierarchy.DescentFundedDateInputs
import OAI.Hierarchy.DescentLowCountBook
import OAI.Hierarchy.DescentRoleMountSpan
import OAI.Hierarchy.DescentWideSeedOriginalInvoice

namespace OAI
/-! # Dense terminal header words in the captured, role-mounted memory -/

namespace Hierarchy.DescentExteriorShelf.Root
open Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section

theorem appended_dense_header {K W q piece n w : ℕ} (front codes publicRows : ℕ) (raw : Memory w)
    (z : DescentTerminalPaidBoot.Input K W q piece n → Bool) (i : ℕ)
    (valid : i < DescentTerminalDenseHeaderBoot.extent q (W*piece)) :
    appended front (DescentTerminalPublicIdentity.total K W q piece codes n publicRows) raw
      (DescentTerminalPublicIdentity.back z w codes publicRows)
      (front+DescentTerminalChipBootWords.total K W q piece codes+i) =
        DescentTerminalDenseHeaderBoot.back w q (W*piece) i := by
  let chip := DescentTerminalChipBootWords.total K W q piece codes
  have within : chip+i < DescentTerminalBoot.total K W q piece codes := Nat.add_lt_add_left valid chip
  have paid : chip+i < DescentTerminalPaidBoot.total K W q piece codes n :=
    within.trans_le (Nat.le_add_right ..)
  have entire : chip+i < DescentTerminalPublicIdentity.total K W q piece codes n publicRows :=
    paid.trans_le (Nat.le_add_right ..)
  let j : Fin (DescentTerminalPublicIdentity.total K W q piece codes n publicRows) := ⟨chip+i,entire⟩
  rw [Nat.add_assoc]
  calc
    _ = DescentTerminalPublicIdentity.back z w codes publicRows (chip+i) :=
      suffix_read front _ raw (DescentTerminalPublicIdentity.back z w codes publicRows) j
    _ = DescentTerminalPaidBoot.back z w codes (chip+i) := by
      unfold DescentTerminalPublicIdentity.back
      exact append_low _ _ _ _ paid
    _ = DescentTerminalBoot.back (z ∘ Sum.inl) w codes (chip+i) := by
      unfold DescentTerminalPaidBoot.back
      exact append_low _ _ _ _ within
    _ = _ := DescentTerminalBoot.header (z ∘ Sum.inl) w codes valid

end
end Hierarchy.DescentExteriorShelf.Root

namespace Hierarchy.DescentSixParty.Chronology
open DescentCompiler Computability.VPVNP.BurstRAM PrivateRAM

theorem FundedDateInputs.before_header {w header capture roof : ℕ} {S : AtomSchedule}
    {date : ℕ → DateCode w} {start : Memory w} {floors count saved : ℕ → ℕ} {seen : Prop}
    (data : FundedDateInputs S date start header capture roof floors count saved seen)
    (a : ℕ) (low : a<header) (age : ℕ) (time : age≤S.length) :
    DateCode.history date start age a=start a := by
  induction age with
  | zero => rfl
  | succ age ih =>
    have enough : age<S.length := by omega
    exact (data.frame age enough a low.ne (low.trans (data.order age enough))).trans (ih enough.le)

end Hierarchy.DescentSixParty.Chronology

namespace Hierarchy.DescentDatedSeedStartup.Input
open DescentSixParty DescentCompiler DescentInitialHost DescentSeedRoot DescentPackedSeed
open DescentSeedInitialTable DescentRotor DescentColonies DescentSIMDLookup
open DescentTerminalEpochChart DescentPackedEpochShelves DescentPackedProfileInstall
open DescentExteriorShelf DescentExterior DescentTerminalFullPins Computability.BorderVNP.Crossing
open ThreeFlat Routing CorrectionBatch DescentGL DescentTerminalChipPins DescentTerminalPorts
open Catalyst ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.Diagonal
open ThreeFlat.RAM
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false

variable {F A : Type} [Field F] {S : AtomSchedule} (D : PoweredGadget F) (op : RotorSpec)
    {k cp p H w K W q piece rows : ℕ} (X : Approximation F cp p)
    (digits : Fin S.copies ≃ Fin (S.groupCount 0)×Block k) (publicWide : Fintype.card (Vertex X)≤H)
    (l : Layout) (header payload Z : ℕ)
local notation "g₀" => S.groupCount 0
local notation "top" => endAddress X l H g₀ k
local notation "chart" => nodeChart l k H g₀
local notation "finish" => (chart).seedEnd top
local notation "lanes" => Primitive.paletteLanes D op l.seedWidth Z payload k
local notation "cap" => Primitive.initialEnd X S.copies l.seedWidth payload k H g₀ lanes finish
local notation "jobs" => DescentPackedSeed.Primitive.Source.jobs X S.copies l.seedWidth payload
variable {seedWidth : ℕ}
local notation "flag" => DescentWideSeedFlags.endInput X S.copies seedWidth payload
local notation "entries" => DescentPackedSeed.rows X S.copies seedWidth payload

open DescentSixParty.Chronology
variable (seed : Select X S.copies seedWidth → A) (votes : A → Bool)
    (front codes publicRows : ℕ) (raw : Memory w)
    (z : DescentTerminalPaidBoot.Input K W q piece rows → Bool)
local notation "extra" => DescentTerminalPublicIdentity.total K W q piece codes rows publicRows
local notation "chip" => DescentTerminalChipBootWords.total K W q piece codes
local notation "boot" => Root.appended front extra raw (DescentTerminalPublicIdentity.back z w codes publicRows)
local notation "checked" => DescentWideSeedFlags.countedAt X S.copies seedWidth payload seed votes boot
local notation "started" => completeImage D op X digits publicWide l header payload Z checked
local notation "capture" => flag+entries+1

omit [Field F] in
/-- The capture prefix ends at the selector base when its ordinary dates are
the rows of the normalized epoch chart. The packed profile and exterior words
both follow that base. -/
theorem capture_before_public_front (s n : ℕ) (ss : List (Source A)) (grain C exterior : ℕ)
    (dates : n=ss.length) :
    DescentWideSeedFlags.endInput X S.copies s payload+DescentPackedSeed.rows X S.copies s payload+1+n ≤
      end_ (DescentWideSeedFlags.selectorBase X S.copies s payload ss.length+extent grain ss) C grain+exterior := by
  rw [dates]
  change DescentWideSeedFlags.selectorBase X S.copies s payload ss.length ≤ _
  unfold end_ dict
  dsimp only
  omega

/-- The first private calendar floor follows the complete startup allocation.
The role table follows every selected calendar floor. -/
theorem archive_before_role_start {archive initial rank other : ℕ}
    (early : header<l.base) (archived : archive≤header) (entry : cap=initial) (later : initial≤rank) :
    archive≤ max rank other := by
  have a:=fences X l H g₀ k
  have b:=Primitive.fences X S.copies l.seedWidth payload k H g₀ lanes finish
  have layoutEnd : l.base≤top := a.1.trans (a.2.1.trans a.2.2)
  have layoutBook : top≤finish := (Nat.le_add_right ..).trans (Nat.le_add_right ..)
  exact (((archived.trans early.le).trans layoutEnd).trans
    (layoutBook.trans (b.1.trans b.2))).trans (entry.le.trans (later.trans (Nat.le_max_left ..)))

/-- The capture book and the public role mount leave the immutable terminal header
in place throughout the executed funded calendar. -/
theorem captured_dense_header (date : ℕ → DateCode w) (source : ℕ → ℕ) (n : ℕ)
    {floor roof roleFloor roleRoof : ℕ} (roles : RoleMount w roleFloor roleRoof)
    {floors counts saved : ℕ → ℕ} {seen : Prop}
    (data : FundedDateInputs S date started header floor roof floors counts saved seen)
    (countEnd : capture+n≤front) (archived : front+extra≤header) (roleStart : front+extra≤roleFloor)
    (early : header<l.base) (sourceSpace : publicWords X+DescentDyadicSpan.span jobs≤finish)
    (live : 0<lanes) (native : payload≤w) (signed : DescentSignedCableCodec.width 3 256*l.packedLanes≤w)
    («fields» : l.operandBits*l.operandLanes≤w) (space : cap<2^w)
    (i : ℕ) (valid : i<DescentTerminalDenseHeaderBoot.extent q (W*piece)) :
    roles.phase.image (DescentLowCountBook.output capture source (DateCode.history date started S.length) n)
      (front+chip+i)=DescentTerminalDenseHeaderBoot.back w q (W*piece) i := by
  have chipEnd : chip+i < DescentTerminalBoot.total K W q piece codes := Nat.add_lt_add_left valid _
  have paidEnd : chip+i < DescentTerminalPaidBoot.total K W q piece codes rows :=
    chipEnd.trans_le (Nat.le_add_right ..)
  have whole : chip+i < extra := paidEnd.trans_le (Nat.le_add_right ..)
  have inside : front+chip+i < front+extra := by omega
  have below := inside.trans_le archived
  rw [roles.frame _ _ (.inl (inside.trans_le roleStart)),
    DescentLowCountBook.frame _ _ _ _ _ (.inr (by omega)),
    data.before_header _ below S.length le_rfl,
    complete_before_header D op X digits publicWide l header payload Z checked early sourceSpace live native
      signed «fields» space _ below]
  have seedOutside : ¬(flag≤front+chip+i ∧ front+chip+i<flag+(entries+1)) := by omega
  change fillSegment flag (entries+1) _ boot (front+chip+i)=_
  rw [fillSegment,ite_eq_right seedOutside]
  exact Root.appended_dense_header front codes publicRows raw z i valid

end
end Hierarchy.DescentDatedSeedStartup.Input

end OAI
