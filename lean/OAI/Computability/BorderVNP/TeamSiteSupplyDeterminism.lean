import OAI.Computability.BorderVNP.TeamSiteSupply

/-! # Uniqueness of finite signed processor paths

The complete finite spelling of a stopped processor path determines its events,
end state, final countdown and verdict. All extensions of that spelling follow
the same path, including when the terminal callback rejects.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamSite.SupplyRun

open VPVNP RAMTape BurstRAM TeamSiteEvents TeamSiteChoices

variable {Q Γ : Type} {w p r k a m g : ℕ} {P : TeamOpcode.Program p r k a}
  {pub : Fin k → Word w} {lib : Fin a → Macro Q Γ m g} {fuel cap : ℕ}
  {s last : TeamOpcode.State w p r} {c fin : Window w} {supply : Supply}
  {es : List (TeamRAM.Event w)} {verdict : Verdict}

/-- A failed callback is independent of the infinite choices beyond the stopped trace. -/
theorem Invalid.generate_none {bank : PrivateRAM.LogConfig w p r} {out : TeamOpcode.Exit p r a}
    (reason : Invalid bank out) (sup : Supply) : generate lib fuel cap bank out sup = none := by
  cases reason with
  | nativeReject | nativeReturn => rfl
  | badAddress j addr len pc bad =>
    simp [generate,TeamOpcode.Exit.action, TeamRAM.Instr.action,Nat.not_le.mpr bad]

/-- Any other branch supply with the consumed spelling has the identical stopped execution. -/
theorem Run.on_prefix (h : Run P pub lib fuel s c supply es last fin verdict) (other : Supply)
    (hp : Prefix other (chunkBits es)) : Run P pub lib fuel s c other es last fin verdict := by
  induction h generalizing other with
  | accept t => exact .accept t
  | handoff t => exact .handoff t
  | rejectGuard t => exact .rejectGuard t
  | rejectCallback t _ reason => exact .rejectCallback t (reason.generate_none other) reason
  | cons admit decoded fits _ ih =>
    obtain ⟨this, rest⟩ := (prefix_append ..).mp hp
    obtain ⟨act,advance,cap,_⟩ := (decode_iff ..).mp decoded
    exact .cons admit ((decode_iff ..).mpr ⟨act,advance,cap,this⟩) fits (ih _ rest)

/-- A supplied stream determines one event history, architectural endpoint, clock and verdict. -/
theorem Run.determined (first : Run P pub lib fuel s c supply es last fin verdict)
    {es' last' fin' verdict'} (other : Run P pub lib fuel s c supply es' last' fin' verdict') :
    es = es' ∧ last = last' ∧ fin = fin' ∧ verdict = verdict' := by
  induction first generalizing es' last' fin' verdict' with
  | accept t =>
    cases other <;> first | exact ⟨rfl,rfl,rfl,rfl⟩ | grind only
  | handoff t =>
    cases other <;> first | exact ⟨rfl,rfl,rfl,rfl⟩ | grind only
  | rejectGuard t =>
    cases other <;> first | exact ⟨rfl,rfl,rfl,rfl⟩ | grind only
  | rejectCallback t f inv =>
    cases other <;> first | exact ⟨rfl,rfl,rfl,rfl⟩ | grind only
  | cons t hd fits run ih =>
    cases other with
    | accept | handoff | rejectGuard | rejectCallback => grind only
    | cons t' hd' fits' tail =>
      obtain rfl := Option.some.inj (hd.symm.trans hd')
      obtain ⟨rfl,rfl,rfl,rfl⟩ := ih tail
      exact ⟨rfl,rfl,rfl,rfl⟩

/-- Equal complete physical choice spellings give equal native stopped traces even
when they are witnessed with different infinite extensions. -/
theorem Run.of_same_bits (first : Run P pub lib fuel s c supply es last fin verdict)
    {otherSupply es' last' fin' verdict'} (other : Run P pub lib fuel s c otherSupply es' last' fin' verdict')
    (bits : chunkBits es = chunkBits es') : es = es' ∧ last = last' ∧ fin = fin' ∧ verdict = verdict' :=
  (first.on_prefix otherSupply (bits ▸ other.prefix)).determined other

end TeamSite.SupplyRun

end BorderVNP
end Computability
end OAI
