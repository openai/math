import OAI.Computability.BorderVNP.CubeScatterAssignment
import OAI.Computability.BorderVNP.PackedCellAddressExecution
import OAI.Computability.BorderVNP.DiagonalNativeCellProduct

/-! # Reconstructing one physical cube path from routed payloads and staged private cell bits

A cell's flat private vector consists of internal cable lanes followed by the site's
staging slabs. Once the delivered exterior data and internal cables are known, the
passing staging checks fix each of the latter words. Combining this bijection with the
selector-dependent division of cube payloads leaves exactly one full assignment per path.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Physical.NativeAssignments

open Crossing Packing.CellAddresses Cube.Scatter.Assignment
open scoped BigOperators Classical

variable {D m vMax : ℕ} {P : Type*} {bits : P → ℕ} {Cell : Type} (N : Network D P bits)
    (cell : N.Site → Cell) (edgeID : N.Edge ↪ Fin m) (siteID : N.Site ↪ Fin vMax) (aux : N.Site → ℕ)

/-- The internal-wire part of the actual flat choice vector of a cell. -/
noncomputable def privateWires (c : Cell) (raw : Fin (externalBase N cell c aux) → Bool) :
    Fin (guessedSize N cell c) → Bool := fun i => raw (Fin.castAdd (siteSize N cell c aux) i)

/-- The site-staging part of the same choice vector. -/
noncomputable def privateStaging (c : Cell) (raw : Fin (externalBase N cell c aux) → Bool) :
    Fin (siteSize N cell c aux) → Bool := fun i => raw (Fin.natAdd (guessedSize N cell c) i)

@[simp] private theorem privateWires_append (c : Cell) (g : Fin (guessedSize N cell c) → Bool)
    (st : Fin (siteSize N cell c aux) → Bool) : privateWires N cell aux c (Fin.append g st) = g := by
  funext i
  exact Fin.append_left ..

@[simp] private theorem privateStaging_append (c : Cell) (g : Fin (guessedSize N cell c) → Bool)
    (st : Fin (siteSize N cell c aux) → Bool) : privateStaging N cell aux c (Fin.append g st) = st := by
  funext i
  exact Fin.append_right ..

/-- Site staging words required for this fixed outside data and choice of internal wires. -/
abbrev Expected := (c : Cell) → (Fin (guessedSize N cell c) → Bool) →
  ∀ v : {v : N.Site // cell v = c}, Fin (aux v.val) → Bool

/-- The flat native private wires accepted by the site staging checks, before filtering
by the actual arithmetic and Boolean local table entries. -/
abbrev Staged (expected : Expected N cell aux) :=
  {raw : (c : Cell) → Fin (externalBase N cell c aux) → Bool // ∀ c,
    siteWords N cell c siteID aux (privateStaging N cell aux c (raw c)) =
      expected c (privateWires N cell aux c (raw c))}

/-- The staged physical private vectors and the internal edge assignments are in
bijection for this outside data. Both directions use the actual slab index maps. -/
noncomputable def insideEquiv (expected : Expected N cell aux) :
    Staged N cell siteID aux expected ≃ ((c : Cell) → N.InsideAssignment cell c) where
  toFun z c := guessedWords N cell c edgeID (privateWires N cell aux c (z.val c))
  invFun inside := ⟨fun c => let wire := (guessedWords N cell c edgeID).symm (inside c)
    Fin.append wire ((siteWords N cell c siteID aux).symm (expected c wire)),by
      intro c
      simp⟩
  left_inv z := by
    apply Subtype.ext
    funext c i
    simp only [Equiv.symm_apply_apply]
    have he := (siteWords N cell c siteID aux).symm_apply_eq.mpr (z.property c).symm
    cases i using Fin.addCases with
    | left i => simp [privateWires,Fin.append_left]
    | right i => rw [Fin.append_right,he]; rfl
  right_inv inside := by
    funext c
    simp

variable {n d blocks b h K s : ℕ} {Team : Type*} [DecidableEq Cell]
variable (owners : (Packet n d blocks → Selector n K h) → Fin d → Team)

/-- The public cube selectors followed by the actual shared and team-private payload
indices. The assignment of symbols to teams can depend on the entire selector tuple. -/
abbrev Routed := (u : Packet n d blocks → Selector n K h) × Choices b s u (chosen b s u) (owners u)

/-- Physical chronological assignment space after fixing the outer epoch and bottom-grid
choices: routed packet data first, then one flat, correctly staged private vector per cell. -/
abbrev ChoicesWithCells (expected : Routed (b := b) (s := s) owners → Expected N cell aux) :=
  (q : Routed (b := b) (s := s) owners) × Staged N cell siteID aux (expected q)

/-- Every reconstructed physical path has exactly one set of routed choices and correctly
staged private cell bits, and conversely. The exterior term and team owners are read from
its own selectors. -/
noncomputable def pathEquiv (expected : Routed (b := b) (s := s) owners → Expected N cell aux) :
    ChoicesWithCells N cell siteID aux owners expected ≃ Path N cell n d blocks b h K s := by
  let e : ChoicesWithCells N cell siteID aux owners expected ≃
      AdaptiveDistributedPath N cell n d blocks b h K s owners :=
    { toFun z := (insideEquiv N cell edgeID siteID aux (expected z.1) z.2,z.1)
      invFun z := ⟨z.2,(insideEquiv N cell edgeID siteID aux (expected z.2)).symm z.1⟩
      left_inv := fun ⟨q,z⟩ => by simp
      right_inv := fun ⟨inside,q⟩ => by simp }
  exact e.trans (adaptivePathEquiv N cell n d blocks b h K s owners).symm

omit [DecidableEq Cell] in
/-- Reindex the signed sum on the actual staged-wire choice space by all physical
paths, carrying arbitrary further path-dependent tally or residue factors along. -/
theorem sum_paths {A : Type*} [AddCommMonoid A] (expected : Routed (b := b) (s := s) owners → Expected N cell aux)
    [Fintype (ChoicesWithCells N cell siteID aux owners expected)]
    [Fintype (Path N cell n d blocks b h K s)] (f : Path N cell n d blocks b h K s → A) :
    (∑ z : ChoicesWithCells N cell siteID aux owners expected,
      f (pathEquiv N cell edgeID siteID aux owners expected z)) = ∑ a, f a :=
  (pathEquiv N cell edgeID siteID aux owners expected).sum_comp f

variable {Hidden : Type*}

/-- The original bottom-grid choices are read from actual flat private vectors before
the remaining staging words are checked against the appropriate completion. -/
abbrev CheckedCells (expected : Hidden → Routed (b := b) (s := s) owners → Expected N cell aux)
    (extract : Routed (b := b) (s := s) owners → ((c : Cell) → Fin (externalBase N cell c aux) → Bool) → Hidden) :=
  (q : Routed (b := b) (s := s) owners) × {raw : (c : Cell) → Fin (externalBase N cell c aux) → Bool //
    ∀ c, siteWords N cell c siteID aux (privateStaging N cell aux c (raw c)) =
      expected (extract q raw) q c (privateWires N cell aux c (raw c))}

/-- Factoring out the independent bottom-grid witnesses is a bijection whenever their
bits can be recovered from the actual completed private slabs. Thus the native ordering
of selector, routed bits and private cell guesses yields one bottom witness and one
physical path, with no duplicate completions. -/
noncomputable def checkedPathEquiv
    (expected : Hidden → Routed (b := b) (s := s) owners → Expected N cell aux)
    (extract : Routed (b := b) (s := s) owners → ((c : Cell) → Fin (externalBase N cell c aux) → Bool) → Hidden)
    (recovered : ∀ q z (raw : Staged N cell siteID aux (expected z q)), extract q raw.val = z) :
    CheckedCells N cell siteID aux owners expected extract ≃ (Hidden × Path N cell n d blocks b h K s) := by
  let recover : CheckedCells N cell siteID aux owners expected extract ≃
      (Σ z, ChoicesWithCells N cell siteID aux owners (expected z)) :=
    { toFun := fun ⟨q,raw⟩ => ⟨extract q raw.val,q,raw.val,raw.property⟩
      invFun := fun ⟨z,q,raw⟩ => ⟨q,raw.val,by
        rw [recovered q z raw]
        exact raw.property⟩
      left_inv := fun _ => rfl
      right_inv := by
        rintro ⟨z,q,⟨raw,stage⟩⟩
        have eq : extract q raw = z := recovered q z ⟨raw,stage⟩
        subst z
        rfl }
  exact (recover.trans (Equiv.sigmaCongrRight fun z => pathEquiv N cell edgeID siteID aux owners (expected z))).trans
    (Equiv.sigmaEquivProd Hidden (Path N cell n d blocks b h K s))

end Cube.Physical.NativeAssignments

end BorderVNP
end Computability
end OAI
