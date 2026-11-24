import OAI.Computability.VPVNP.RAMMemoryMessages
import OAI.Computability.VPVNP.RAMSuccessor

/-!
# Parsimonious distributed RAM transcripts

For a power-of-two number of sites and bucket capacity, the accepting binary
paths of the native RAM are in bijection with joint choices of successor and
sorting messages and one successful local path at each site. The local tests
read the site's header, its adjacent chain fields, and its sorting fields.
They enforce the private instruction clock, per-call cost cap, global cost cap,
and memory read consistency, without a global oracle at any processor.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace BurstRAM

open RAMMemory RAMSort

/-- Shared successor cuts and sorting-network messages of one transcript. -/
@[ext] structure Messages (d e w : ℕ) where
  /-- Successor cut at each boundary between consecutive sites. -/
  chain : Fin (2^d - 1) → Cut w
  /-- Shared sorting-network data for verifying memory consistency. -/
  memory : MemoryMessages (2+e) d w

variable {d e w : ℕ} {C : Type*}

/-- Padded initialization and probe records contributed by one processor. -/
def localRecords (header : ℕ → Word w) (e v start : ℕ) (rs : List (Report w)) :
    Wires (2+e) (OrderedSlot (Word w)) :=
  fun j => ⟨(siteRecordBlock header (2^e) v start rs)[j.val]?.getD none⟩

/-- One site's accepting reports. The header array is consulted only at
`v`, in the initialization record of `localRecords`. -/
def Validator (P : Program w C) (fuel : ℕ) (initial : Word w) (header : ℕ → Word w)
    (msg : Messages d e w) (v : Fin (2^d)) (rs : List (Report w)) : Prop :=
  let c := inputCut ⟨0, some initial⟩ msg.chain v
  SiteCheck P fuel (2^d) (2^e) v.val c (outputCut msg.chain v) rs ∧
    MemoryAt msg.memory v (localRecords header e v.val c.cost rs)

private theorem localRecords_eq_block {P : Program w C} {fuel : ℕ} {initial : Word w}
    {reports : Fin (2^d) → List (Report w)} {chain : Fin (2^d-1) → Cut w}
    (hp : SitesPass P fuel (2^d) (2^e) initial reports chain) (header : ℕ → Word w)
    (v : Fin (2^d)) :
    localRecords header e v.val (inputCut ⟨0, some initial⟩ chain v).cost (reports v) =
      block (2+e) v.val (recordWires header d e (List.ofFn reports).flatten) := by
  have caps := (successor_sound (Nat.two_pow_pos d) hp).2.2
  have hr := block_recordWires header caps.1 caps.2 v
  rw [getElem_canonicalRecordBlocks] at hr
  have he := sitesPass_eq_partition (Nat.two_pow_pos d) hp
  simp only [← he, List.getElem_ofFn] at hr
  rw [sitesPass_input_cost (Nat.two_pow_pos d) hp]
  funext j
  have hj := congrArg (fun l : List (OrderedSlot (Word w)) => l[j.val]?) hr
  have hlen := congrArg List.length hr
  simp only [List.length_ofFn, List.length_map] at hlen
  have hlt := lt_of_lt_of_eq j.isLt hlen
  have hof : j.val < (List.ofFn (block (2+e) v.val (recordWires header d e
      (List.ofFn reports).flatten))).length := by simpa only [List.length_ofFn] using j.isLt
  rw [List.getElem?_eq_getElem hof, List.getElem?_map, List.getElem?_eq_getElem hlt] at hj
  simpa [localRecords, List.getElem?_eq_getElem hlt] using hj.symm

/-- The independent tests at all sites, expressed using their unique global
execution and its correctly sorted memory history. -/
theorem validators_iff (P : Program w C) (fuel : ℕ) (initial : Word w) (header : ℕ → Word w)
    (msg : Messages d e w) (reports : Fin (2^d) → List (Report w)) :
    (∀ v, Validator P fuel initial header msg v (reports v)) ↔
      SitesPass P fuel (2^d) (2^e) initial reports msg.chain ∧
      msg.memory = actualMemoryMessages (2+e) d (recordWires header d e (List.ofFn reports).flatten) ∧
      Correct (initialMemory (2^d) header) (eventLog (List.ofFn reports).flatten) := by
  constructor
  · intro h
    have hs : SitesPass P fuel (2^d) (2^e) initial reports msg.chain := fun v => (h v).1
    have caps := (successor_sound (Nat.two_pow_pos d) hs).2.2
    refine ⟨hs, (report_memoryAt_iff header caps.1 caps.2 msg.memory).mp ?_⟩
    intro v
    rw [← localRecords_eq_block hs header v]
    exact (h v).2
  · rintro ⟨hs, hm, hread⟩
    have caps := (successor_sound (Nat.two_pow_pos d) hs).2.2
    have hm' := (report_memoryAt_iff header caps.1 caps.2 msg.memory).mpr ⟨hm, hread⟩
    intro v
    refine ⟨hs v, ?_⟩
    rw [localRecords_eq_block hs header v]
    exact hm' v

/-- Accepted shared messages together with one verified report list at every site. -/
abbrev TypedJointPaths (P : Program w C) (fuel : ℕ) (initial : Word w) (header : ℕ → Word w)
    (d e : ℕ) := {t : Messages d e w × (Fin (2^d) → List (Report w)) //
      ∀ v, Validator P fuel initial header t.1 v (t.2 v)}

private def jointReports (P : Program w C) (fuel : ℕ) (initial : Word w) (header : ℕ → Word w)
    (t : TypedJointPaths P fuel initial header d e) :
    VerifiedReports P fuel initial (initialMemory (2^d) header) (withinCaps (2^d) (2^e)) := by
  refine ⟨(List.ofFn t.val.2).flatten, ?_⟩
  obtain ⟨hs, _, hm⟩ := (validators_iff ..).mp t.property
  obtain ⟨hg, ha, hc⟩ := successor_sound (Nat.two_pow_pos d) hs
  exact ⟨hg, hm, ha, hc⟩

/-- Flattening the local reports is a bijection. The successor messages,
the bucket partition, all pre-comparison blocks, and every last-record field
are determined by the native path, even after an early halt. -/
private theorem jointReports_bijective (P : Program w C) (fuel : ℕ) (initial : Word w)
    (header : ℕ → Word w) :
    Function.Bijective (jointReports (d := d) (e := e) P fuel initial header) := by
  constructor
  · intro a b hab
    have hf : (List.ofFn a.val.2).flatten = (List.ofFn b.val.2).flatten := congrArg Subtype.val hab
    obtain ⟨ha, hma, _⟩ := (validators_iff ..).mp a.property
    obtain ⟨hb, hmb, _⟩ := (validators_iff ..).mp b.property
    obtain ⟨hseg, hend, hcap⟩ := successor_sound (Nat.two_pow_pos d) hb
    have hu := successor_unique _ _ _ _ _ _ (Nat.two_pow_pos d) (Nat.two_pow_pos e) hseg hend hcap
    have hpair : (a.val.2, a.val.1.chain) = (b.val.2, b.val.1.chain) :=
      hu.unique (show _ ∧ _ from ⟨hf, ha⟩) (show _ ∧ _ from ⟨rfl, hb⟩)
    apply Subtype.ext
    apply Prod.ext
    · exact Messages.ext (congrArg Prod.snd hpair) (hma.trans (hf ▸ hmb.symm))
    · exact congrArg Prod.fst hpair
  · intro r
    obtain ⟨p, ⟨hflat, hs⟩, _⟩ := successor_unique _ _ _ _ _ r.val (Nat.two_pow_pos d)
      (Nat.two_pow_pos e) r.property.1 r.property.2.2.1 r.property.2.2.2
    let msg : Messages d e w := ⟨p.2, actualMemoryMessages (2+e) d (recordWires header d e r.val)⟩
    refine ⟨⟨⟨msg, p.1⟩, (validators_iff ..).mpr ⟨hs, ?_, ?_⟩⟩, Subtype.ext hflat⟩
    · rw [hflat]
    · rw [hflat]
      exact r.property.2.1

/-- Lemma 10.1 at the level of typed transcript fields. Genuine paths are
indexed by their binary program choices. A validated read has exactly one
allowed word, and therefore adds no multiplicity. -/
noncomputable def transcriptEquiv (P : Program w C) (fuel : ℕ) (initial : Word w)
    (header : ℕ → Word w) (d e : ℕ) :
    ActualPaths P fuel initial (initialMemory (2^d) header) (withinCaps (2^d) (2^e)) ≃
      TypedJointPaths P fuel initial header d e :=
  (reportEquiv ..).trans (Equiv.ofBijective _ (jointReports_bijective ..)).symm

end BurstRAM

end VPVNP
end Computability
end OAI
