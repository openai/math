import OAI.Computability.VPVNP.RAMTapeSiteEntryFrame
import OAI.Computability.VPVNP.RAMTapeSiteCutSnapshot

/-!
# The call controller's physical input view

Every port of the bare snapshot has its declared value after a successful guard, the zero
word copy, and the nomination of a choice string. Shared flags and words come from the
actual guard output. The initialization record's address and value come from the padded
site words. Both private scratch and the shadow labels of shared registers start empty.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.SiteProcessorPorts

open BurstRAM PrivateRAM LiveProgram Function SiteProcessor

variable {k r p d e w : ℕ} (expr : Fin k → PublicExpr) (x : SiteCutBank.Input d e w)
  {args : Fin k → Word w} {s : Stacks (Port r expr)}

private theorem entry_aux (bits : List Bool) (j : SiteCutBank.Aux) :
    entryBank r expr x s bits (cut r expr (.inr j)) = x.guarded (.inr j) := by
  rw [entryBank, update_of_ne (by simp [cut, native]), update_of_ne (by simp [cut, pub]),
    zeroBank, update_of_ne (by simp [cut, native]), guardBank_at]

private theorem entry_public (bits : List Bool) (j : ProcessorPublic.Port)
    (hb : j ≠ ProcessorPublic.budgetPort) (hi : j ≠ ProcessorPublic.incidentPort) :
    entryBank r expr x s bits (pub r expr j) = x.prepared (.inl j) := by
  rw [entryBank, update_of_ne (by simp [pub, native]), update_of_ne (by simpa [pub] using hb),
    zeroBank, update_of_ne (by simp [pub, native])]
  exact (guardBank_at r expr x s (.inl j)).trans (guarded_public_ne x j hi)

private theorem entry_native (hf : Frame r expr x args s) (bits : List Bool) (i : SiteProcessor.Port r k) :
    entryBank r expr x s bits (native r expr i) =
      if i = .test .choices then bits else if i = .credit (.budget .globalLeft) then wordBits (0 : Word w) else
      match i with | .isa (.pub j) => wordBits (args j) | _ => [] := by
  by_cases hc : i = .test .choices
  · subst i; simp [entryBank]
  · by_cases hg : i = .credit (.budget .globalLeft)
    · subst i; simp [entryBank, zeroBank, native, pub]
    · rw [entryBank, update_of_ne (by simpa [native] using hc), update_of_ne (by simp [native, pub]),
        zeroBank, update_of_ne (by simpa [native] using hg), guardBank_native, hf.natives]
      simp [hc, hg]
      cases i with
      | isa j => cases j <;> rfl
      | _ => rfl

/-- The physical call ports are the complete bare snapshot, for every nominated bit list. -/
theorem entry_view (T : Template p r k) (hf : Frame r expr x args s) (h : x.valid) (bits : List Bool) :
    entryBank r expr x s bits ∘ callPorts r expr = (x.bare T args bits).bare := by
  have hn := entry_native expr x hf bits
  have hp := entry_public (s := s) expr x bits
  have ha := entry_aux (s := s) expr x bits
  have regs := SiteCutBank.guarded_registers x h
  funext i
  change entryBank r expr x s bits (callPorts r expr i) = _
  cases i with
  | isa i =>
    cases i with
    | persistent => exact (ha _).trans (regs.state .receive)
    | logPort q => cases q <;> exact hn _
    | reg | pub | work => exact hn _
  | credit i =>
    cases i with
    | publicH | publicFuel | globalCap => exact hp _ (by decide) (by decide)
    | budget j =>
      cases j with
      | site => exact hp _ (by decide) (by decide)
      | cost => exact (ha _).trans (x.guarded_cost h .receive)
      | fuel | call | globalLeft | tmp => exact hn _
    | savedStart | ordinal | copyA | copyB | arithA | arithB => exact hn _
  | test i =>
    cases i with
    | word j =>
      cases j with
      | lower | boundary => exact hp _ (by decide) (by decide)
      | targetCost => exact (ha _).trans (x.guarded_cost h .send)
      | targetState => exact (ha _).trans (regs.state .send)
      | cost | cap | state => exact hn _
    | bit j =>
      cases j with
      | running => exact (ha _).trans (regs.running .receive)
      | hasTarget => exact (ha _).trans regs.outPresent
      | targetRunning => exact (ha _).trans (regs.running .send)
    | choices | verdict | left | right | tmp | out | sourceTmp | copyTmp => exact hn _
  | record i =>
    cases i with
    | field j =>
      fin_cases j
      · exact hn _
      · exact hp _ (by decide) (by decide)
      · exact hp _ (by decide) (by decide)
      · exact hn _
      · exact hn _
    | zeros =>
      refine (hp _ (by decide) (by decide)).trans ?_
      exact congrArg (fun m => List.replicate m false) x.width_eq.symm
    | remaining => exact hp _ (by decide) (by decide)
    | temp | reverseBuffer | output => exact hn _
  | scratch j => exact hn _

end RAMTape.SiteProcessorPorts

end VPVNP
end Computability
end OAI
