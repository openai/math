import OAI.Computability.BorderVNP.DiagonalPositiveExteriorRoutes
import OAI.Computability.BorderVNP.DiagonalPositiveHeaderReturns
import OAI.Computability.BorderVNP.DiagonalJointExterior

/-! # Reindexing all positive physical exteriors by their exact received fields -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction

open VPVNP BurstRAM Diagonal.Layout RoutingISA RoutingISA.Evaluator Routing ProcessorSlots JointHeader

variable {R r t d link inner n w reserve axes groups cap dim tally : ℕ} {Edge : Type}
variable (G : Wiring R r t d link inner n Edge) (args : Fin (R+1) → UnitAddresses)
variable (pin : Fin d → Bool) (L : WireLayout (R+1) r link) (fixed : Block (R+1))
variable (hw : 0<w) (size : ∀ i, (args i).header = L.header) (base : Fin (R+1) → ℕ)
variable (fit : ∀ i, (G.transferFrame i (args i).header (args i).dst).Fits w (base i))
variable (width : L.header = PositiveFields.width reserve axes groups cap (R+1) dim tally)
local notation "Fields" => PositiveFields reserve axes groups cap (R+1) dim tally

include fixed hw size base fit width

/-- The positive physical predicate tests exactly one common positive bit string
of the complete specified width. It has no dependency on subsequent run weights. -/
theorem positiveExterior_iff_fields (ext : Exterior R r link → Bool) :
    ProcessorSlots.PositiveExterior G args pin w ext ↔ ∃! p : Fields, ∀ b, observed L ext b = p.bits := by
  constructor
  · intro good
    obtain ⟨common,tag,_⟩ := observed_positive G args pin ext L hw size base fit (fun u => (good u).2) (good 0).1 fixed
    obtain ⟨p,parse,unique⟩ := PositiveFields.unique_parse (observed L ext fixed) ((observed_length ..).trans width) tag
    exact ⟨p,fun b => (congrArg List.ofFn (common b)).trans parse.symm,fun q h => unique q (h fixed).symm⟩
  · rintro ⟨p,common,_⟩ u
    let f := G.transferFrame u (args u).header (args u).dst
    let F := G.processorFields u pin ext (args u).ibase (args u).hbase (args u).starbase
    obtain ⟨ne,lt⟩ := f.partner_spec L.three
    let partner : Fin (R+1) := ⟨f.partner,lt⟩
    have diff : u ≠ partner := fun eq => ne (congrArg Fin.val eq.symm)
    have read (v : Fin (R+1)) (different : u ≠ v) (i : Fin L.header) :
        readings (modeMemory (w:=w) G args pin ext u) (f.addr v i) =
          ((L.exteriorEquiv ext).broadcast (blockOf u v different) i).toNat :=
      G.read_message_header L u v different pin ext _ _ _ (processorMemory F w) (F.containsInput_initial w) hw i
    have room := (fit u).branch.trans_eq (size u)
    let block := blockOf u partner diff
    have start := congrArg List.head? (common block)
    change (List.ofFn ((L.exteriorEquiv ext).broadcast block)).head? = some true at start
    rw [List.head?_eq_some_head (by simp [room.ne']),List.head_ofFn,Option.some.injEq] at start
    refine ⟨?_,?_⟩
    · have tag := read partner diff ⟨0,room⟩
      change modeTag (w:=w) G args pin ext u = ((L.exteriorEquiv ext).broadcast block ⟨0,room⟩).toNat at tag
      rw [start] at tag
      exact tag.trans_ne (by decide)
    · intro v hv different j hj
      let v' : Fin (R+1) := ⟨v,hv⟩
      have vu : u ≠ v' := fun eq => different (congrArg Fin.val eq.symm)
      let i : Fin L.header := ⟨j,hj.trans_eq (size u)⟩
      have all : (L.exteriorEquiv ext).broadcast (blockOf u v' vu) = (L.exteriorEquiv ext).broadcast block :=
        List.ofFn_inj.mp ((common _).trans (common block).symm)
      exact (read v' vu i).trans ((congrArg Bool.toNat (congrFun all i)).trans (read partner diff i).symm)

/-- Every genuine positive exterior occurs once, indexed by its parsed fields
and its assignment to the remaining physical positions. -/
noncomputable def positiveExteriorFieldsEquiv :
    {ext : Exterior R r link → Bool // ProcessorSlots.PositiveExterior G args pin w ext} ≃
      (Σ p : Fields, HeaderExterior L p.bits) := by
  let domain := {ext : Exterior R r link → Bool // ProcessorSlots.PositiveExterior G args pin w ext}
  let back (z : Σ p : Fields, HeaderExterior L p.bits) : domain :=
    ⟨z.2.val,(positiveExterior_iff_fields G args pin L fixed hw size base fit width z.2.val).mpr
      ⟨z.1,z.2.property,fun q h => PositiveFields.bits_injective ((h fixed).symm.trans (z.2.property fixed))⟩⟩
  refine (Equiv.ofBijective back ⟨?_,?_⟩).symm
  · rintro ⟨a,x⟩ ⟨b,y⟩ same
    have actual : x.val = y.val := congrArg Subtype.val same
    have equal : a=b := PositiveFields.bits_injective ((x.property fixed).symm.trans
      ((congrArg (fun ext => observed L ext fixed) actual).trans (y.property fixed)))
    subst b
    exact congrArg (Sigma.mk a) (Subtype.ext actual)
  · intro x
    obtain ⟨p,common,_⟩ := (positiveExterior_iff_fields G args pin L fixed hw size base fit width x.val).mp x.property
    exact ⟨⟨p,⟨x.val,common⟩⟩,rfl⟩

/-- Forgetting the parsed fields preserves the original value of every physical wire. -/
theorem positiveExteriorFieldsEquiv_symm_val (z : Σ p : Fields, HeaderExterior L p.bits) :
    ((positiveExteriorFieldsEquiv G args pin L fixed hw size base fit width).symm z).val = z.2.val := rfl

/-- Reindex the actual accepted exterior and all its original dependent team
and private-cell witnesses by their parsed fields. Zero-valued continuations
stay in precisely the same acceptance fiber. -/
noncomputable def acceptedExteriorFieldsEquiv {box lanes selectors symbols : ℕ}
    {id : Cube.TableEntry axes box lanes selectors symbols → ℕ} {gen : CellMacro.Generator.Fragment CellMacro.Generator.IO}
    (S : {ext : Exterior R r link → Bool // ProcessorSlots.PositiveExterior G args pin w ext} →
      Fin (R+1) → PositiveTeam id gen n w)
    (joined : ∀ x (a : (u : Fin (R+1)) → (S x u).Prefix), JoinedCells (fun u => (S x u).pub)
      (fun u => (S x u).postMemory) (fun u => (S x u).generated) a) :
    let E := positiveExteriorFieldsEquiv G args pin L fixed hw size base fit width
    AcceptedExterior S joined ≃ Σ p : Fields, (x : HeaderExterior L p.bits) ×
      {a : PositiveAssignment (S (E.symm ⟨p,x⟩)) (joined (E.symm ⟨p,x⟩)) //
        positivePass (S (E.symm ⟨p,x⟩)) (joined (E.symm ⟨p,x⟩)) a} := by
  intro E
  let path (u : Σ p : Fields, HeaderExterior L p.bits) :=
    {a : PositiveAssignment (S (E.symm u)) (joined (E.symm u)) // positivePass (S (E.symm u)) (joined (E.symm u)) a}
  exact (Equiv.sigmaCongrLeft' E).trans (Equiv.sigmaAssoc fun p x => path ⟨p,x⟩)

end TeamContraction

end BorderVNP
end Computability
end OAI
