import OAI.Computability.BorderVNP.PackedHistoryBirthCases

/-! # Complete birth-box classification at every host of the actual outer machine -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.EnrichedOuter

open Crossing Cover Epoch.Round Shortening Shortening.Adaptive Packing Packing.Inherited
open Diagonal.ExternalSew Diagonal.CellEntries PublicCapacity
open scoped Classical BorderVNP.Epoch.Cube
attribute [local instance] portFintype
set_option maxHeartbeats 2400000
set_option maxRecDepth 2500

universe u

variable {D : ℕ} {P : Type} [Fintype P] {bits : P → ℕ}

omit [Fintype P] in
private theorem sameHost_surj {N M : Network D P bits} (eq : N = M) : Function.Surjective (Retains.ofEq eq).site := by
  subst M
  exact fun x => ⟨x,rfl⟩

variable {m start T : ℕ} [NeZero D] {K : Type} [Field K]
    {e : PaidIdentity K D m} {S : Normalized.SiteSchedule e} {shape : ℕ → Shape}
    {W : ℕ → Type} [∀ t, Fintype (W t)] {good : ∀ t, State S start P bits shape W t → Prop}
    {deep : S.floor+1+S.drop*T ≤ start}

namespace Epoch

variable {t : ℕ} {ht : t<T} {V : ℕ → Type} [∀ j, Fintype (V j)] {w : ℕ → ℕ}
    (E : Epoch.{u} deep ht good V w) (rows : E.F.SiteRows)
    (c : Fin (fan S) → Admissible good t) (old : ∀ i, Site.Programs (c i).val.pack.layout) (number : e.Entry → ℕ)

/-- Each newly inserted subdivision vertex has no box. Every other vertex is the retained
endpoint of one of the actual child's original hosts. -/
theorem installedPrivateBirthCases (i : Fin (fan S)) (v : (E.view 0 ((E.run c).flat i)).pack.layout.Site) :
    (∃ u, (enrichedInstalledHosts (E.run c).flat (E.run c).initialSites (E.run c).originalPack i).site u = v) ∨
      FreshBirth e number (E.installedPrivatePrograms rows c old i v).birth := by
  let run := E.run c
  let a := run.initialSites i
  let orig := congrArg Pack.layout (run.originalPack i).symm
  let saved := congrArg (fun p => p.pack.layout) a.realizes.symm
  let raw := RowTrace.sameRows orig (c i).val.rows
  let new := raw.siteRoutes a.routes S.radius
  let prior := samePrivatePrograms orig (old i)
  let installed := Subdivision.subdividePrivatePrograms a.pack.layout (a.routes.routes S.radius)
    raw.edge new.edge (rows.ports 0) (changePrivateInstance _ prior)
  obtain ⟨u,rfl⟩ := sameHost_surj saved v
  rcases u with u | relay
  · obtain ⟨w,rfl⟩ := sameHost_surj orig u
    exact .inl ⟨w,rfl⟩
  · apply Or.inr
    exact (congrArg (FreshBirth e number) (samePrivatePrograms_birth saved installed (.inr relay))).mpr
      ⟨Subdivision.relay_local a.pack.layout (a.routes.routes S.radius) new.edge (rows.ports 0) relay,.inl rfl⟩

/-- A complete selected inner epoch retains actual input hosts or starts a new
empty or paid template, including those arising from its initial subdivision. -/
theorem privateBirthCases (q : E.F.Hist (E.run c).flat) (v : ((E.term c q).val.pack).layout.Site) :
    (∃ u, (enrichedEpochHosts (E.run c) E.saveNames q).site u = v) ∨
      FreshBirth e number (E.privatePrograms rows c old number q v).birth := by
  rcases E.F.flatPrivateBirthCases E.saveNames rows number (E.run c).flat (E.installedPrivatePrograms rows c old) q v with
    ⟨⟨i,w⟩,rfl⟩ | h
  · rcases E.installedPrivateBirthCases rows c old number i w with ⟨u,rfl⟩ | h
    · exact .inl ⟨⟨i,u⟩,rfl⟩
    · exact .inr ((congrArg (FreshBirth e number) (E.F.flatPrivatePrograms_birth E.saveNames rows number
        (E.run c).flat (E.installedPrivatePrograms rows c old) q i w)).mpr h)
  · exact .inr h

end Epoch

namespace Machine

variable {V : ℕ → ℕ → Type} [∀ t i, Fintype (V t i)] {w : ℕ → ℕ → ℕ}
    (M : Machine.{0,u} deep good V w) (rows : ∀ n hn, (M n hn).F.SiteRows) (number : e.Entry → ℕ)

/-- Classify the true outer profile index before recurring down its child addresses. -/
theorem stepPrivateBirthCases {n : ℕ} (hn : n<T) (c : Fin (fan S) → Admissible good n)
    (old : ∀ j, Site.Programs (c j).val.pack.layout) (q : (M.epoch n c).Index)
    (v : ((M.epoch n c).term q).val.pack.layout.Site) :
    (∃ u, (enrichedStepHosts M hn c q).site u = v) ∨
      FreshBirth e number (M.stepPrivatePrograms rows number hn c old q v).birth := by
  let family (z : ProfileSum (Admissible good (n+1))) := (j : z.Index) → Site.Programs (z.term j).val.pack.layout
  let hosts (z : ProfileSum (Admissible good (n+1))) := (j : z.Index) →
    Retains (parallelPacks fun i => (c i).val.pack).layout (z.term j).val.pack.layout
  have carry {z y : ProfileSum (Admissible good (n+1))} (he : z=y) (f : family y) (g : hosts y)
      (h : ∀ j v, (∃ u, (g j).site u = v) ∨ FreshBirth e number (f j v).birth) :
      ∀ j : z.Index, ∀ v, (∃ u, ((Eq.mpr (congrArg hosts he) g) j).site u = v) ∨
        FreshBirth e number ((Eq.mpr (congrArg family he) f) j v).birth := by
    subst y
    exact h
  have he : M.epoch n c = (M n hn).choice c := dite_eq_left hn
  exact carry he ((M n hn).privatePrograms (rows n hn) c old number)
    (enrichedEpochHosts ((M n hn).run c) (M n hn).saveNames)
    ((M n hn).privateBirthCases (rows n hn) c old number) q v

variable (bottom : Admissible good 0) (base : Site.Programs bottom.val.pack.layout)

/-- Every host of an attained outer history has an original bottom address or a
genuine empty or paid-identity birth box. -/
theorem historyPrivateBirthCases (n : ℕ) (hn : n ≤ T) (q : (packHistory bottom M.epoch n).Index)
    (v : ((packHistory bottom M.epoch n).term q).val.pack.layout.Site) :
    (∃ u, (enrichedNestedHosts M bottom n hn q).site u = v) ∨
      FreshBirth e number (M.historyPrivatePrograms rows number bottom base n hn q v).birth := by
  induction n with
  | zero => exact .inl ⟨v,rfl⟩
  | succ n ih =>
    let hl := Nat.lt_of_succ_le hn
    let H := packHistory bottom M.epoch n
    let c := fun j : Fin (fan S) => H.term (q.1 j)
    let old := fun j : Fin (fan S) => M.historyPrivatePrograms rows number bottom base n hl.le (q.1 j)
    rcases M.stepPrivateBirthCases rows number hl c old q.2 v with ⟨⟨j,w⟩,rfl⟩ | h
    · rcases ih hl.le (q.1 j) w with ⟨u,rfl⟩ | h
      · exact .inl ⟨⟨j,u⟩,rfl⟩
      · exact .inr ((congrArg (FreshBirth e number) (M.stepPrivatePrograms_birth rows number hl c old q.2 j w)).mpr h)
    · exact .inr h

/-- At any actual flattened host, either a unique row-major bottom source is retained
there, or its complete birth box list is empty or the singleton fixed paid template. -/
theorem terminalPrivateBirthInfo (q : (packHistory bottom M.epoch T).Index)
    (v : (flattenPack T ((packHistory bottom M.epoch T).term q).val.pack).layout.Site) :
    (∃ u, (enrichedOuterHosts M bottom q).site u = v) ∨
      FreshBirth e number (M.terminalPrivatePrograms rows number bottom base q v).birth := by
  rcases M.historyPrivateBirthCases rows number bottom base T le_rfl q v with ⟨u,rfl⟩ | h
  · let orig := originalNames (k := fan S) (fun _ : Unit => bottom.val.pack) T (fun _ => ())
    exact .inl ⟨orig u,congrArg (enrichedNestedHosts M bottom T le_rfl q).site (orig.symm_apply_apply u)⟩
  · exact .inr h

/-- Every terminal birth either retains a bottom site or has precisely the
factor list of a newly introduced relay or paid site. -/
theorem terminalPrivateBirthCases (q : (packHistory bottom M.epoch T).Index)
    (v : (flattenPack T ((packHistory bottom M.epoch T).term q).val.pack).layout.Site) :
    (∃ u, (enrichedOuterHosts M bottom q).site u = v) ∨
      FreshBoxes e number (M.terminalPrivatePrograms rows number bottom base q v).birth :=
  (M.terminalPrivateBirthInfo rows number bottom base q v).imp_right And.right

end Machine
end PackedHistoryCircuit.Normalized.EnrichedOuter

end BorderVNP
end Computability
end OAI
