import OAI.Hierarchy.DescentRegisteredArchiveReturn
import OAI.Hierarchy.DescentRegisteredCutArchiveTags

namespace OAI
/-! # The complete operand archive and the tag of every padded cell along one accepted run -/
namespace Hierarchy.DescentSixParty.Chronology
open DescentCompiler Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F] [Fintype P] {G : PoweredGadget F} {S : AtomSchedule}
    {bits : P→ℕ} {d k wire hist len w : ℕ} {q ε : ℝ}

namespace RegisterTimeline
variable {t : RunTrace G q ε S k wire hist len bits d}

def withTags (claim : PrefixClaim t w) : PrefixClaim t w :=
  fun before p m=>claim before p m ∧ p.ports.ArchiveTags m

omit [Fintype P] in
private theorem age_bound {W₀ W₁ : MarkedWorld F d P bits} {i z D j n H : ℕ}
    {r : Reached W₀ G q ε S k i z D wire hist} {u : Reached W₁ G q ε S k j n H wire hist}
    (suffix : Path r u) : i≤j:=by
  induction suffix with
  | here=>exact le_rfl
  | ordinary _ _ ih=>exact ih.trans (Nat.le_succ _)
  | reset _ _ ih=>exact ih.trans (Nat.le_succ _)

omit [Fintype P] in
private theorem inside {i : ℕ} (e : t.path.Event i) : i<len:=by
  cases e with
  | ordinary _ _ after _=>exact age_bound after
  | reset _ _ after _=>exact age_bound after

omit [Fintype P] in
theorem previous_with_tags (claim : PrefixClaim t w) {i : ℕ} (e : t.path.Event i) (p : Position) (m : Memory w) :
    e.previousClaim (withTags claim) p m ↔ e.previousClaim claim p m ∧ p.ports.ArchiveTags m:=by
  cases e <;> rfl

omit [Fintype P] in
theorem next_with_tags (claim : PrefixClaim t w) {i : ℕ} (e : t.path.Event i) (p : Position) (m : Memory w) :
    e.nextClaim (withTags claim) p m ↔ e.nextClaim claim p m ∧ p.ports.ArchiveTags m:=by
  cases e <;> rfl

variable {C : Type*} (traces : C→RunTrace G q ε S k wire hist len bits d)
    {n degree : ℕ} (b : Menu n degree) (initial : Position) (c : C) (boot : Memory w)
local notation "t₀" => traces c
local notation "cursor" => calendar (w:=w) traces b initial
local notation "steps" => issued (w:=w) traces b
local notation "prog" => instruction (w:=w) traces b initial
local notation "ram" i => DateCode.history prog boot i
variable (limit : ℕ) (valid : Prop) (claim : PrefixClaim (traces c) w)
variable (fixed : ∀i (a z : RunTrace.Events traces i) x y,
  issued (w:=w) traces b i a (calendar (w:=w) traces b initial i) x →
  issued (w:=w) traces b i z (calendar (w:=w) traces b initial i) y → x=y)

include fixed in
omit [Fintype P] in
/-- Both publications use the incoming archive and its padded tag rows on exactly the same tape. -/
theorem posted_with_tags (i : ℕ) (e : (t₀).path.Event i)
    (venue : advances traces b initial c boot limit valid i e)
    (archiveFields : e.incoming (cursor i) (ram i) → e.previousClaim claim (cursor i) (ram i) →
      (cursor i).ports.ArchiveTags (ram i) → e.required limit valid →
      e.nextClaim claim (cursor (i+1)) (ram (i+1)))
    (issuedTags : e.incoming (cursor i) (ram i) → e.previousClaim claim (cursor i) (ram i) →
      (cursor i).ports.ArchiveTags (ram i) → e.required limit valid → TagInputs traces b initial c boot i e) :
    advancesArchive traces b initial c boot limit valid (withTags claim) i e:=by
  apply advances_with_archive traces b initial c boot limit valid (withTags claim) i e (fixed i) venue
  intro old pair alive
  obtain ⟨earlier,tags⟩:=(previous_with_tags claim e _ _).mp pair
  have live:=inside e
  have posted:=TagInputs.result traces b initial c boot e live (issuedTags old earlier tags alive)
  rw [history_from_cuts traces b initial c boot (i+1) live] at posted
  exact (next_with_tags claim e _ _).mpr ⟨archiveFields old earlier tags alive,posted⟩

include fixed in
omit [Fintype P] in
/-- One prefix induction, including the live part of a subsequently rejected ballot. -/
theorem fields_and_tags_prefix
    (seed : initial.ports.held (t₀).first initial.floor boot ∧ claim Path.here initial boot ∧ initial.ports.ArchiveTags boot)
    (venue : ∀i (e : (t₀).path.Event i), advances traces b initial c boot limit valid i e)
    (acquire : ∀i (e : (t₀).path.Event i),e.incoming (cursor i) (ram i) →
      e.previousClaim claim (cursor i) (ram i) → (cursor i).ports.ArchiveTags (ram i) → e.required limit valid →
      e.nextClaim claim (cursor (i+1)) (ram (i+1)) ∧ TagInputs traces b initial c boot i e)
    {U : MarkedWorld F d P bits} {i z D : ℕ} {r : Reached U G q ε S k i z D wire hist}
    (before : Path (t₀).first r) (after : Path r (t₀).last) (split : before.append after=(t₀).path)
    (alive : before.selections.length<limit ∨ valid) :
    (cursor i).ports.held r (cursor i).floor (ram i) ∧ claim before (cursor i) (ram i) ∧
      (cursor i).ports.ArchiveTags (ram i):=by
  apply held_archive_prefix traces b initial c boot limit valid (withTags claim) fixed seed _ before after split alive
  intro j e
  exact posted_with_tags traces b initial c boot limit valid claim fixed j e (venue j e)
    (fun old rows tags live=>(acquire j e old rows tags live).1)
    (fun old rows tags live=>(acquire j e old rows tags live).2)

end RegisterTimeline
end
end Hierarchy.DescentSixParty.Chronology

end OAI
