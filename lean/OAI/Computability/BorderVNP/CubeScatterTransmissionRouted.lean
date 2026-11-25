import OAI.Computability.BorderVNP.CubeScatterCommonDecoder
import OAI.Computability.BorderVNP.CubeTeamPrivateKeysPath
import OAI.Computability.BorderVNP.CubePhysicalNativeAssignments

/-! # The complete native transmission and private tapes of a routed cube

The received data includes one checked declaration and the selector prefix
and crossing suffix of every strict row. Those prefixes fix the tuple of
selectors, hence also its greedy owners and the lengths of all their private
tapes. Every accepted collection of words has one routed physical assignment.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Scatter.Assignment.Routed

open Physical Physical.NativeAssignments

variable {n d blocks b h K s : ℕ} {Team : Type*} [DecidableEq Team]
variable (owners : (Packet n d blocks → Selector n K h) → Fin d → Team)

/-- The three physically observable components of a routed execution. -/
@[ext] structure Words (n d : ℕ) (Team : Type*) where
  /-- Public grouping coordinate and all claimed directional widths. -/
  declaration : LengthDeclaration n d
  /-- Each entire shared raw list, including its selector prefix. -/
  shared : Symbols d → List Bool
  /-- The private chronological bits of each executing team. -/
  tapes : Team → List Bool

/-- The true public lengths and least minimizing grouping coordinate of this selector tuple. -/
def trueDeclaration (b s : ℕ) (u : Packet n d blocks → Selector n K h) : LengthDeclaration n d :=
  (chosen b s u,subtotals itemRow (crossCount b s u) (chosen b s u))

/-- Encoding the full declaration, selector-bearing shared transmission and
all chronological team tapes of one routed assignment. -/
noncomputable def encode (q : NativeAssignments.Routed (b := b) (s := s) owners) : Words n d Team :=
  let i := chosen b s q.1
  let words := nativeWordsEquiv b s q.1 i (owners q.1) q.2
  ⟨trueDeclaration b s q.1,fun pair => commonSelectors q.1 i pair ++ (words.1 pair).val,
    fun t => (words.2 t).val⟩

/-- The mathematical payload read from the native declaration and full shared words. -/
def physicalShared (q : NativeAssignments.Routed (b := b) (s := s) owners) :
    DeclaredShared blocks b h K s (trueDeclaration b s q.1) :=
  ⟨⟨q.1,(passesLengths_iff ..).mpr rfl⟩,fun _ => rowCrossValue (supplies q.2) (fun z => lookup q.2 (.inl z))⟩

/-- Encoding uses exactly the physical selector and active crossing bits in every received row. -/
theorem encode_shared (q : NativeAssignments.Routed (b := b) (s := s) owners) :
    (encode owners q).shared = sharedWords (trueDeclaration b s q.1) (physicalShared owners q) := by
  funext pair
  exact congrArg (commonSelectors q.1 (chosen b s q.1) pair ++ ·)
    ((nativeWordsEquiv_shared q.2 pair).trans (commonCrossings_eq_keys ..))

/-- Checking the widths of the private words takes place after decoding the entire selector-bearing common input. -/
structure Accepts (b s : ℕ) (owners : (Packet n d blocks → Selector n K h) → Fin d → Team)
    (words : Words n d Team) : Prop where
  /-- Native selector bounds, row lengths and declaration checks on all shared words. -/
  common : AcceptsShared blocks b h K s words.declaration words.shared
  /-- Actual private tape lengths in the dispatcher order of the unique decoded selectors. -/
  sizes : ∀ a : DeclaredShared blocks b h K s words.declaration, sharedWords words.declaration a = words.shared →
    ∀ t, (words.tapes t).length = (teamPrivateKeys b s a.1.val words.declaration.1 (owners a.1.val) t).length

/-- Physical encoding passes the real decoder and the team-tape length checks. -/
theorem encode_accepts (q : NativeAssignments.Routed (b := b) (s := s) owners) :
    Accepts b s owners (encode owners q) := by
  have he := encode_shared owners q
  have pass := sharedWords_accept _ (physicalShared owners q)
  constructor
  · exact he ▸ pass
  · intro a ha t
    have unique := (sharedWords_iff _ _).mp pass
    have eq := unique.unique (ha.trans he) (show sharedWords _ (physicalShared owners q) = _ from rfl)
    subst a
    exact (((nativeWordsEquiv b s q.1 (chosen b s q.1) (owners q.1)) q.2).2 t).property

private theorem native_injective : Function.Injective (encode (b := b) (s := s) owners) := by
  rintro ⟨u,f⟩ ⟨v,g⟩ eq
  have hd : trueDeclaration b s u = trueDeclaration b s v := congrArg Words.declaration eq
  have hi := congrArg Prod.fst hd
  change chosen b s u = chosen b s v at hi
  have raw := congrArg Words.shared eq
  have prefixes (pair : Symbols d) : commonSelectors u (chosen b s u) pair = commonSelectors v (chosen b s u) pair := by
    let width := rowSelectorBits n d blocks K h (chosen b s u) (Sym2.mk pair.val.1 pair.val.2)
    have left : (commonSelectors u (chosen b s u) pair).length = width := commonSelectors_length ..
    have right : (commonSelectors v (chosen b s v) pair).length = width := by rw [← hi]; exact commonSelectors_length ..
    have bits := congrArg (List.take width) (congrFun raw pair)
    change (commonSelectors u (chosen b s u) pair ++ _).take width =
      (commonSelectors v (chosen b s v) pair ++ _).take width at bits
    have take {x y : List Bool} (hx : x.length = width) : (x++y).take width = x := hx ▸ List.take_append_length
    exact (take left).symm.trans (bits.trans ((take right).trans (congrArg (fun j => commonSelectors v j pair) hi.symm)))
  have uv := commonSelectors_injective (chosen b s u) prefixes
  subst v
  congr 1
  apply (nativeWordsEquiv b s u (chosen b s u) (owners u)).injective
  apply Prod.ext
  · funext pair
    apply Subtype.ext
    exact List.append_cancel_left (congrFun raw pair)
  · funext t
    exact Subtype.ext (congrFun (congrArg Words.tapes eq) t)

/-- A valid declaration with complete native lists and arbitrary proper-length
private tapes decodes to exactly one routed assignment, with the correct
selector-dependent owners even when both sides of a row are co-owned. -/
theorem accepts_iff_existsUnique (words : Words n d Team) :
    Accepts b s owners words ↔ ∃! q : NativeAssignments.Routed (b := b) (s := s) owners, encode owners q = words := by
  constructor
  · rcases words with ⟨decl,raw,tapes⟩
    intro ok
    obtain ⟨⟨⟨u,pass⟩,pay⟩,emit,_⟩ := (sharedWords_iff _ _).mp ok.common
    have canonical : decl = trueDeclaration b s u := (passesLengths_iff ..).mp pass
    subst decl
    let i := chosen b s u
    let cross : StrictCrossWords b s u i := fun p => rowCrossEquiv b s u i p (pay p)
    let localWords : TeamPrivateWords b s u i (owners u) :=
      fun t => ⟨tapes t,ok.sizes ⟨⟨u,pass⟩,pay⟩ emit t⟩
    let e := nativeWordsEquiv b s u i (owners u)
    let f := e.symm (cross,localWords)
    have ef : e f = (cross,localWords) := e.apply_symm_apply _
    have enc : encode owners (⟨u,f⟩ : NativeAssignments.Routed owners) =
        (⟨trueDeclaration b s u,raw,tapes⟩ : Words n d Team) := by
      apply Words.ext
      · rfl
      · funext p
        change commonSelectors u i p ++ ((e f).1 p).val = raw p
        rw [ef]
        exact congrFun emit p
      · funext t
        change ((e f).2 t).val = tapes t
        rw [ef]
    exact ⟨⟨u,f⟩,enc,fun q hq => native_injective owners (hq.trans enc.symm)⟩
  · rintro ⟨q,rfl,_⟩
    exact encode_accepts owners q

/-- Exact replacement of the routed first coordinate of the native cell evaluator
by the actual valid common transmissions and independent team tapes. -/
noncomputable def wordsEquiv (b s : ℕ) :
    NativeAssignments.Routed (b := b) (s := s) owners ≃ {z : Words n d Team // Accepts b s owners z} := by
  apply Equiv.ofBijective (fun q => ⟨encode owners q,encode_accepts owners q⟩)
  constructor
  · exact fun _ _ he => native_injective owners (congrArg Subtype.val he)
  · intro z
    obtain ⟨q,eq,_⟩ := (accepts_iff_existsUnique owners z.val).mp z.property
    exact ⟨q,Subtype.ext eq⟩

end Cube.Scatter.Assignment.Routed

end BorderVNP
end Computability
end OAI
