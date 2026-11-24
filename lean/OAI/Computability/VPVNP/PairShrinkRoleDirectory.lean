import OAI.Computability.VPVNP.PairOutputRowDirectory
import OAI.Computability.VPVNP.PairTraversalRoleDispatch

/-!
# Decoding a shrinking visit from the popped row address

Each output site belongs to one occurrence of a selected term. Distinct
occurrences remain distinct even when the same term is chosen twice. The
parser receives only the popped word and scratch state. Its physical row
selects both the term occurrence and the site in that term's output network.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.ShrinkRoleDirectory

open BurstRAM BurstRAM.PrivateRAM CompressorRecords Compression LocalHistory
open TraversalRows TraversalRoles DFS
open scoped Fin.CommRing

variable {k R : Type*} [_root_.Field k] [CommRing R] {S : BlockSchedule k}
variable {B : S.Templates} {f : B.Entry → R} {hf : B.IsSolution f}

/-- The order used when writing the rows of the chosen term's actual output network. -/
noncomputable def outputOrder (v : SelectedLevel B f hf) :
    Order (v.pass.step.term v.term).output.Site :=
  (v.pass.output_eq v.term).symm ▸ siteOrder (v.pass.next v.term)

/-- The second component is a site in the first component's term output. -/
abbrev Site (passes : List (SelectedLevel B f hf)) :=
  Σ j : Fin passes.length, (passes[j].pass.step.term passes[j].term).output.Site

/-- Only occurrences whose recorded kernel is a shrinking pass. -/
abbrev ShrinkSite (passes : List (SelectedLevel B f hf)) :=
  {x : Site passes // tagLevel B f hf passes[x.1] = .shrink}

/-- Turn the selected pass sequence into its output DFS layers, retaining the producing role of
each layer. -/
noncomputable def outputTags (passes : List (SelectedLevel B f hf)) : List TaggedLayer :=
  passes.map fun v => ⟨levelLayer B f hf v, tagLevel B f hf v⟩

/-- Numerical ordinals in a physical row are exactly the selected term's site order. -/
noncomputable def siteRows (passes : List (SelectedLevel B f hf)) :
    Site passes ≃ OutputRowDirectory.Row (outputTags passes) :=
  Equiv.sigmaCongr (finCongr (by simp [outputTags])) fun j =>
    (outputOrder passes[j]).entries.symm.trans <| finCongr <| by
      simp only [outputTags, Fin.getElem_fin, List.getElem_map]
      rfl

variable (cap base : ℕ) (leaf : TaggedLayer) (passes : List (SelectedLevel B f hf))

/-- Natural row address in the physical arena for a concrete chosen term and site. -/
noncomputable def address (x : Site passes) : ℕ :=
  TraversalRows.address cap (layerBase cap base (leaf :: outputTags passes) (x.1.val + 1))
    ((outputOrder passes[x.1]).entries.symm x.2).val

private theorem row_address (x : Site passes) :
    OutputRowDirectory.rowAddress cap base leaf (outputTags passes) (siteRows passes x) =
      address cap base leaf passes x := rfl

/-- Row addresses distinguish both the selected term occurrence and its output site. -/
theorem address_injective : Function.Injective (address cap base leaf passes) := by
  intro x y h
  apply (siteRows passes).injective
  apply OutputRowDirectory.rowAddress_injective cap base leaf (outputTags passes)
  rwa [row_address, row_address]

private def asShrink (x : Site passes) : Option (ShrinkSite passes) :=
  if h : tagLevel B f hf passes[x.1] = .shrink then some ⟨x, h⟩ else none

private theorem asShrink_eq_some_iff (x : Site passes) (s : ShrinkSite passes) :
    asShrink passes x = some s ↔ x = s.val := by
  unfold asShrink
  split
  · rw [Option.some.injEq, Subtype.ext_iff]
  · rename_i h
    simp only [reduceCtorEq, false_iff]
    exact fun e => h (e ▸ s.property)

variable {w endAddr : ℕ}

/-- Recover the shrink site from the physical node word. The decoder rejects
cursor rows, refresh rows, interiors of rows and addresses outside the row arena. -/
noncomputable def decode (node : Word w) : Option (ShrinkSite passes) :=
  (OutputRowDirectory.decode cap base leaf (outputTags passes) node).bind fun row =>
    asShrink passes ((siteRows passes).symm row)

/-- Successful decoding is equivalent to equality with the actual natural row address. -/
theorem decode_eq_some_iff
    (fit : layerBase cap base (leaf :: outputTags passes) (passes.length + 1) ≤ 2 ^ w)
    (node : Word w) (x : ShrinkSite passes) :
    decode cap base leaf passes node = some x ↔ node.val = address cap base leaf passes x.val := by
  have fits : layerBase cap base (leaf :: outputTags passes) ((outputTags passes).length + 1) ≤
      2 ^ w := by simpa only [outputTags, List.length_map] using fit
  rw [decode, Option.bind_eq_some_iff]
  constructor
  · rintro ⟨row, located, shrink⟩
    have he := (asShrink_eq_some_iff passes _ x).mp shrink
    have er : row = siteRows passes x.val := by rw [← he, Equiv.apply_symm_apply]
    rw [er] at located
    have e := (OutputRowDirectory.decode_eq_some_iff cap base leaf (outputTags passes) fits
      node (siteRows passes x.val)).mp located
    exact e.trans (row_address cap base leaf passes x.val)
  · intro ha
    refine ⟨siteRows passes x.val, ?_, ?_⟩
    · apply (OutputRowDirectory.decode_eq_some_iff cap base leaf (outputTags passes) fits
        node (siteRows passes x.val)).mpr
      exact ha.trans (row_address cap base leaf passes x.val).symm
    · apply (asShrink_eq_some_iff passes _ _).mpr
      exact Equiv.symm_apply_apply _ _

/-- The physical word of each valid shrink row round-trips to its typed site.
The end may equal the word modulus because the allocated interval is half-open. -/
theorem decode_address
    (fit : layerBase cap base (leaf :: outputTags passes) (passes.length + 1) ≤ 2 ^ w)
    (x : ShrinkSite passes) :
    decode cap base leaf passes (address cap base leaf passes x.val : Word w) = some x := by
  apply (decode_eq_some_iff cap base leaf passes fit _ x).mpr
  rw [Fin.val_natCast]
  apply Nat.mod_eq_of_lt
  have below := OutputRowDirectory.rowAddress_lt_end cap base leaf (outputTags passes)
    (siteRows passes x.val)
  rw [row_address] at below
  exact below.trans_le (by simpa only [outputTags, List.length_map] using fit)

/-- Select the parser for the actual shrinking site without passing any
level or owner as an additional input to the hook. -/
noncomputable def parser (readers : ShrinkSite passes → HookParser w endAddr) :
    HookParser w endAddr where
  read node saved bs := (decode cap base leaf passes node).bind fun x =>
    (readers x).read node saved bs

/-- The global reader returns exactly the local path and remaining bits
for the unique chosen site. This also identifies local and global rejection. -/
theorem read_at (readers : ShrinkSite passes → HookParser w endAddr)
    (fit : layerBase cap base (leaf :: outputTags passes) (passes.length + 1) ≤ 2 ^ w)
    (node : Word w) (x : ShrinkSite passes) (ha : node.val = address cap base leaf passes x.val)
    (saved : Scratch w endAddr) (bs : List Bool) :
    (parser cap base leaf passes readers).read node saved bs = (readers x).read node saved bs := by
  simp only [parser, (decode_eq_some_iff cap base leaf passes fit node x).mpr ha, Option.bind_some]

/-- Geometry and packet contents may vary with the selected output site. -/
def Domain (ready : ShrinkSite passes → Scratch w endAddr → Prop)
    (node : Word w) (saved : Scratch w endAddr) : Prop :=
  ∃ x : ShrinkSite passes, node.val = address cap base leaf passes x.val ∧ ready x saved

/-- The dispatcher's actual tag probe selects the recorded role of this site. -/
theorem dispatch_at_site {m : Memory w} {offset : ℕ}
    (published : TraversalRoles.Reads w m offset cap base (leaf :: outputTags passes))
    (codes : 2 < 2 ^ w) (fit : offset + base + tagWords cap (leaf :: outputTags passes) ≤ 2 ^ w)
    (node : Word w) (x : Site passes) (ha : node.val = address cap base leaf passes x) :
    NodeDispatch.role (m ((offset : Word w) + node).val) =
      (tagLevel B f hf passes[x.1]).dispatch := by
  let outputs := outputTags passes
  let row := siteRows passes x
  let j : Fin (leaf :: outputs).length := row.1.succ
  let id : Fin (leaf :: outputs)[j].layer.count := row.2
  have probe := published.dispatch codes fit j id
  change NodeDispatch.role (m ((offset : Word w) +
    (OutputRowDirectory.rowAddress cap base leaf (outputTags passes) row : Word w)).val) = _
    at probe
  rw [show OutputRowDirectory.rowAddress cap base leaf (outputTags passes) row =
    address cap base leaf passes x from row_address cap base leaf passes x, ← ha] at probe
  have role : (leaf :: outputs)[j].role = tagLevel B f hf passes[x.1] := by
    simp [j, row, siteRows, outputs, outputTags]
    rfl
  rw [show (node.val : Word w) = node from Fin.ext (Nat.mod_eq_of_lt node.isLt)] at probe
  exact probe.trans (congrArg Role.dispatch role)

/-- On genuine output rows, the typed shrink domain is the same domain as
the physical role guard, with the site's packet invariant preserved. -/
theorem domain_iff_dispatch {m : Memory w} {offset : ℕ}
    (published : TraversalRoles.Reads w m offset cap base (leaf :: outputTags passes))
    (codes : 2 < 2 ^ w) (fit : offset + base + tagWords cap (leaf :: outputTags passes) ≤ 2 ^ w)
    (ready : Site passes → Scratch w endAddr → Prop) (node : Word w) (saved : Scratch w endAddr)
    (genuine : ∃ x : Site passes, node.val = address cap base leaf passes x ∧ ready x saved) :
    Domain cap base leaf passes (fun x => ready x.val) node saved ↔
      NodeDispatch.role (m ((offset : Word w) + node).val) = .shrink := by
  constructor
  · rintro ⟨x, ha, _⟩
    rw [dispatch_at_site cap base leaf passes published codes fit node x.val ha, x.property]
    rfl
  · intro role
    obtain ⟨x, ha, ok⟩ := genuine
    rw [dispatch_at_site cap base leaf passes published codes fit node x ha] at role
    have shrink : tagLevel B f hf passes[x.1] = .shrink := by
      cases h : tagLevel B f hf passes[x.1] <;> simp_all [Role.dispatch]
    exact ⟨⟨x, shrink⟩, ha, ok⟩

/-- Assemble the genuine per-site native equivalences at their common
shrink entry and DFS continuation. Success and rejection use the same site. -/
theorem exactOn {p r k' : ℕ} (M : Machine w p r k') (visit ret : Fin p)
    (dfs : Fin 9 ↪ Fin r) (m : Memory w)
    (readers : ShrinkSite passes → HookParser w endAddr)
    (ready : ShrinkSite passes → Scratch w endAddr → Prop)
    (fit : layerBase cap base (leaf :: outputTags passes) (passes.length + 1) ≤ 2 ^ w)
    (localExact : ∀ x : ShrinkSite passes, (readers x).ExactOn
      (fun node saved => node.val = address cap base leaf passes x.val ∧ ready x saved)
      M visit ret dfs m) :
    (parser cap base leaf passes readers).ExactOn
      (Domain cap base leaf passes ready) M visit ret dfs m := by
  constructor
  · intro node saved domain bs job tail got
    obtain ⟨x, atRow, good⟩ := domain
    rw [read_at cap base leaf passes readers fit node x atRow] at got
    exact (localExact x).success node saved ⟨atRow, good⟩ bs job tail got
  · intro node bs c top pending domain pc current stack ptr h5 h6 one failed
    obtain ⟨x, atRow, good⟩ := domain
    rw [read_at cap base leaf passes readers fit node x atRow] at failed
    exact (localExact x).reject node bs c top pending ⟨atRow, good⟩
      pc current stack ptr h5 h6 one failed

end PairSimulation.ShrinkRoleDirectory

end VPVNP
end Computability
end OAI
