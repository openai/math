import OAI.Computability.BorderVNP.CubeScatterRowCrossKeys
import OAI.Computability.BorderVNP.CubeScatterSelectorPrefix

/-! # The complete shared lists of one advertised declaration

The selector prefix is decoded before the dependent crossing suffix. A passing
declaration fixes the grouping coordinate and the advertised lengths in all
rows. Each accepted collection of shared words corresponds to exactly one
complete selector tuple and one assignment to every shared cut bit.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Scatter

open Physical

variable {n d blocks b h K s : ℕ}

/-- Payload of a valid declaration before any group-private bits are read. -/
abbrev DeclaredShared (blocks b h K s : ℕ) (D : LengthDeclaration n d) :=
  (u : {u : Packet n d blocks → Selector n K h // passesLengths b s u D}) ×
    ((sym : Symbols d) → RowCrossBit b s u.val D.1 sym → Bool)

/-- Actual shared words in native execution order, one selector prefix and one cut suffix per strict row. -/
def sharedWords (D : LengthDeclaration n d) (a : DeclaredShared blocks b h K s D) (sym : Symbols d) : List Bool :=
  commonSelectors a.1.val D.1 sym ++ (rowCrossKeys b s a.1.val D.1 sym).map (a.2 sym)

/-- Format checks on the complete raw lists followed by the physical row and coordinate tests on decoded selectors. -/
structure AcceptsShared (blocks b h K s : ℕ) (D : LengthDeclaration n d) (raw : Symbols d → List Bool) : Prop where
  /-- The raw width is exactly that of the shared transmission row. -/
  lengths : ∀ sym, (raw sym).length = rowSelectorBits n d blocks K h D.1 (Sym2.mk sym.val.1 sym.val.2) +
    D.2 (Sym2.mk sym.val.1 sym.val.2) D.1
  /-- Each of the native selector reads returns a valid in-range ordinal. -/
  selectors : ∀ sym, (decodeSelectors n K h (packetVisits blocks D.1 sym).length
    ((raw sym).take (rowSelectorBits n d blocks K h D.1 (Sym2.mk sym.val.1 sym.val.2)))).isSome
  /-- Once the selector prefixes fix the summands, their true widths and first minimum are checked. -/
  declaration : ∀ select : Packet n d blocks → Selector n K h,
    (∀ sym : Symbols d, (raw sym).take (rowSelectorBits n d blocks K h D.1 (Sym2.mk sym.val.1 sym.val.2)) =
      commonSelectors select D.1 sym) → passesLengths b s select D

private theorem sharedPrefix (D : LengthDeclaration n d) (a : DeclaredShared blocks b h K s D) (sym : Symbols d) :
    (sharedWords D a sym).take (rowSelectorBits n d blocks K h D.1 (Sym2.mk sym.val.1 sym.val.2)) =
      commonSelectors a.1.val D.1 sym := by
  rw [sharedWords,← commonSelectors_length a.1.val D.1 sym,List.take_append_length]

private theorem sharedSuffix (D : LengthDeclaration n d) (a : DeclaredShared blocks b h K s D) (sym : Symbols d) :
    (sharedWords D a sym).drop (rowSelectorBits n d blocks K h D.1 (Sym2.mk sym.val.1 sym.val.2)) =
      (rowCrossKeys b s a.1.val D.1 sym).map (a.2 sym) := by
  rw [sharedWords,← commonSelectors_length a.1.val D.1 sym,List.drop_append_length]

/-- Encoding a physical shared payload passes all actual shared-list and declaration tests. -/
theorem sharedWords_accept (D : LengthDeclaration n d) (a : DeclaredShared blocks b h K s D) :
    AcceptsShared blocks b h K s D (sharedWords D a) := by
  constructor
  · intro sym
    simp only [sharedWords,List.length_append,List.length_map,commonSelectors_length,rowCrossKeys_length,a.1.property.1]
  · intro sym
    rw [sharedPrefix,commonSelectors_decode]
    rfl
  · intro select prefixes
    have eq := commonSelectors_injective D.1 (fun sym => (prefixes sym).symm.trans (sharedPrefix D a sym))
    exact eq ▸ a.1.property

/-- Each accepted set of routed raw lists has one physical shared payload, with
its full selector tuple and its exact active cut-lane values. -/
theorem sharedWords_iff (D : LengthDeclaration n d) (raw : Symbols d → List Bool) :
    AcceptsShared blocks b h K s D raw ↔ ∃! a : DeclaredShared blocks b h K s D, sharedWords D a = raw := by
  constructor
  · intro accepted
    let width (sym : Symbols d) := rowSelectorBits n d blocks K h D.1 (Sym2.mk sym.val.1 sym.val.2)
    let prefixBits (sym : Symbols d) := (raw sym).take (width sym)
    obtain ⟨select,sel,unique⟩ := (validPrefixes_iff_existsUnique (blocks := blocks) (K := K) (h := h)
      D.1 prefixBits).mp accepted.selectors
    have passing := accepted.declaration select sel
    have slen (sym : Symbols d) :
        ((raw sym).drop (width sym)).length = subtotals itemRow (crossCount b s select) D.1
          (Sym2.mk sym.val.1 sym.val.2) D.1 := by
      rw [List.length_drop,accepted.lengths,← passing.1]
      exact Nat.add_sub_cancel_left ..
    let payload (sym : Symbols d) := (rowCrossEquiv b s select D.1 sym).symm
      ⟨(raw sym).drop (width sym),slen sym⟩
    let a : DeclaredShared blocks b h K s D := ⟨⟨select,passing⟩,payload⟩
    have emits : sharedWords D a = raw := by
      funext sym
      have suffix := congrArg Subtype.val ((rowCrossEquiv b s select D.1 sym).apply_symm_apply
        ⟨(raw sym).drop (width sym),slen sym⟩)
      change commonSelectors select D.1 sym ++ (rowCrossKeys b s select D.1 sym).map (payload sym) = _
      change (rowCrossKeys b s select D.1 sym).map (payload sym) = (raw sym).drop (width sym) at suffix
      rw [← sel sym,suffix]
      exact List.take_append_drop ..
    refine ⟨a,emits,?_⟩
    rintro ⟨⟨select',passing'⟩,pay'⟩ he
    let a' : DeclaredShared blocks b h K s D := ⟨⟨select',passing'⟩,pay'⟩
    have hsel := unique select' (fun sym => by
      change (raw sym).take (width sym) = _
      rw [← congrFun he sym]
      exact sharedPrefix D a' sym)
    subst select'
    have eq : pay' = payload := by
      funext sym
      apply (rowCrossEquiv b s select D.1 sym).injective
      apply Subtype.ext
      have hh := congrArg (List.drop (width sym)) (congrFun (he.trans emits.symm) sym)
      exact (sharedSuffix D _ sym).symm.trans (hh.trans (sharedSuffix D a sym))
    subst pay'
    rfl
  · rintro ⟨a,he,_⟩
    exact he ▸ sharedWords_accept D a

/-- Bijection used to replace the sum over passing physical shared words with the sum over the mathematical payloads. -/
noncomputable def declaredSharedEquiv (blocks b h K s : ℕ) (D : LengthDeclaration n d) :
    DeclaredShared blocks b h K s D ≃ {raw : Symbols d → List Bool // AcceptsShared blocks b h K s D raw} := by
  refine Equiv.ofBijective (fun a => ⟨sharedWords D a,sharedWords_accept D a⟩) ⟨?_,?_⟩
  · intro a a' he
    have ha := (sharedWords_iff D (sharedWords D a)).mp (sharedWords_accept D a)
    exact ha.unique rfl (congrArg Subtype.val he).symm
  · intro raw
    obtain ⟨a,he,_⟩ := (sharedWords_iff D raw.val).mp raw.property
    exact ⟨a,Subtype.ext he⟩

end Cube.Scatter

end BorderVNP
end Computability
end OAI
