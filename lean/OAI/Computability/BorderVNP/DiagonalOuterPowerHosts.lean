import OAI.Computability.BorderVNP.DiagonalTrackedPowerHosts

/-! # Tracked unary owner addresses on the genuine enriched outer machine -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal.CellEntries.EnrichedOuterReplay

open Crossing Shortening Adaptive Packing Cover Epoch Epoch.Round PackedHistoryCircuit
open PackedHistoryCircuit.Normalized PackedHistoryCircuit.Normalized.EnrichedOuter PublicCapacity Diagonal.ExternalSew
open private sameStorage from OAI.Computability.BorderVNP.DiagonalSiteExecution
open private move from OAI.Computability.BorderVNP.DiagonalFactoryReplay
open scoped Classical BorderVNP.Epoch.Cube
attribute [local instance] portFintype
set_option maxHeartbeats 2000000
universe u

private theorem sameHost {D : ℕ} {P : Type} {bits : P → ℕ} {N M : Network D P bits}
    (h : N = M) (v : N.Site) : (sameStorage h).site v = (Retains.ofEq h).site v := by subst M; rfl

variable {D m start T exp : ℕ} [NeZero D] {K E P Team Param Gadget : Type} [Field K] [Field E]
    [Fintype P] [Fintype Team] [Fintype Param] {bits : P → ℕ} {e : PaidIdentity K D m}
    {S : Normalized.SiteSchedule e} {shape : ℕ → Shape} {W : ℕ → Type} [∀ t, Fintype (W t)]
    {good : ∀ t, EnrichedOuter.State S start P bits shape W t → Prop}
    {deep : S.floor+1+S.drop*T ≤ start}
    (y : e.Entry → E) (hy : ∀ f : MvPolynomial e.Entry ℤ, MvPolynomial.eval₂Hom (Int.castRingHom K) e.entry f = 0 →
      MvPolynomial.eval₂Hom (Int.castRingHom E) y f = 0) (pos : e.Entry → Gadget)

/-- The nested team digits naming the retained owner at an outer level. -/
noncomputable local instance outerHostPowerTeams {n : ℕ} : Fintype (Port (fan S) Team n) := Replay.batchFinite (fan S) Team n

section Step
variable {t : ℕ} {ht : t<T} {V : ℕ → Type} [∀ j, Fintype (V j)] {w : ℕ → ℕ}
    (M : EnrichedOuter.Epoch.{u} deep ht good V w) (c : Fin (fan S) → Admissible good t)
    (tags : ∀ i, Tracked (Port (fan S) Team t) Param Gadget exp (c i).val.pack.layout)

/-- Subdivision preserves each actual slot at the left-summand endpoint of its old host. -/
theorem installed_power_site (i : Fin (fan S)) (w : PowerSlot (Port (fan S) Team t) Param exp) :
    let : Fintype (Port (fan S) P t) := portFintype
    (EnrichedSiteReplay.installed (M.run c) i (tags i)).words.site w =
      (enrichedInstalledHosts (M.run c).flat (M.run c).initialSites (M.run c).originalPack i).site ((tags i).words.site w) := by
  let : Fintype (Port (fan S) P t) := portFintype
  let run := M.run c
  let orig := congrArg Pack.layout (run.originalPack i).symm
  let saved := congrArg (fun p => p.pack.layout) (run.initialSites i).realizes.symm
  exact (sameHost saved _).trans (congrArg (fun v => (Retains.ofEq saved).site (.inl v)) (sameHost orig _))

/-- The genuine flattened normalized epoch retains the correct original child and unary host. -/
theorem emit_power_site (q : (M.choice c).Index) (w : PowerSlot (Port (fan S) Team (t+1)) Param exp) :
    let : Fintype (Port (fan S) P t) := portFintype
    (emit M y hy pos c tags q).words.site w =
      (enrichedEpochHosts (M.run c) M.saveNames q).site ⟨w.1.1,(tags w.1.1).words.site (w.1.2,w.2)⟩ := by
  let : Fintype (Port (fan S) P t) := portFintype
  let run := M.run c
  have h := DenseReplay.flat_power_site M.F y hy pos (EnrichedSiteReplay.storage M.saveNames) run.flat
    (fun i => EnrichedSiteReplay.installed run i (tags i)) q w
  exact h.trans (congrArg (fun v => (normalizedHosts M.F (namesStorage M.F M.saveNames) run.flat q).site ⟨w.1.1,v⟩)
    (installed_power_site M c tags w.1.1 (w.1.2,w.2)))

end Step

variable {V : ℕ → ℕ → Type} [∀ t i, Fintype (V t i)] {width : ℕ → ℕ → ℕ}
    (M : EnrichedOuter.Machine.{0,u} deep good V width)

/-- Owner address of the actual outer transition, transported across its native branch index. -/
theorem advance_power_site (n : ℕ) (hn : n<T) (c : Fin (fan S) → Admissible good n)
    (tag : ∀ i, Tracked (Port (fan S) Team n) Param Gadget exp (c i).val.pack.layout)
    (q : (M.epoch n c).Index) (w : PowerSlot (Port (fan S) Team (n+1)) Param exp) :
    (advance M y hy pos n c tag q).words.site w =
      (enrichedStepHosts M hn c q).site ⟨w.1.1,(tag w.1.1).words.site (w.1.2,w.2)⟩ := by
  let : Fintype (Port (fan S) P n) := portFintype
  let state := fun a : Admissible good (n+1) => Tracked (Port (fan S) Team (n+1)) Param Gadget exp a.val.pack.layout
  let hosts (z : ProfileSum (Admissible good (n+1))) := (j : z.Index) →
    Retains (parallelPacks fun i => (c i).val.pack).layout (z.term j).val.pack.layout
  have carry {z z' : ProfileSum (Admissible good (n+1))} (he : z=z') (f : ∀ j, state (z'.term j)) (g : hosts z')
      (hf : ∀ j, (f j).words.site w = (g j).site ⟨w.1.1,(tag w.1.1).words.site (w.1.2,w.2)⟩) :
      ∀ j : z.Index, (move (V := state) he.symm f j).words.site w =
        ((Eq.mpr (congrArg hosts he) g) j).site ⟨w.1.1,(tag w.1.1).words.site (w.1.2,w.2)⟩ := by
    subst z'
    exact hf
  have he : M.epoch n c = (M n hn).choice c := dite_eq_left hn
  unfold advance
  rw [dite_eq_left hn]
  exact carry he (emit (M n hn) y hy pos c tag) (enrichedEpochHosts ((M n hn).run c) (M n hn).saveNames)
    (fun q => emit_power_site y hy pos (M n hn) c tag q w) q

variable {Hidden : Type} (bottom : Admissible good 0)
    (base : Hidden → Tracked Team Param Gadget exp bottom.val.pack.layout)

/-- The host of a power slot after every chosen outer epoch is the genuine retained
leaf host of the same hidden assignment and original parameter/bit. -/
theorem terminal_power_site (q : (packHistory bottom M.epoch T).Index) (z : Fin ((fan S)^T) → Hidden)
    (w : PowerSlot (Port (fan S) Team T) Param exp) :
    let idx := portEquiv (fan S) Team T w.1
    (terminal M y hy pos bottom base q z).words.site w =
      (enrichedOuterHosts M bottom q).site ⟨idx.1,(base (z idx.1)).words.site (idx.2,w.2)⟩ := by
  let layout := fun (n : ℕ) (c : Admissible good n) => c.val.pack.layout
  let leaf := fun _ : Unit => bottom.val.pack
  have nested (n : ℕ) (hn : n≤T) (q' : (packHistory bottom M.epoch n).Index) (z' : Fin ((fan S)^n) → Hidden)
      (w' : PowerSlot (Port (fan S) Team n) Param exp) :
      let idx := portEquiv (fan S) Team n w'.1
      (Outer.term layout bottom M.epoch base (advance M y hy pos) n z' q').words.site w' =
        (enrichedNestedHosts M bottom n hn q').site ((originalNames leaf n (fun _ => ())).symm
          ⟨idx.1,(base (z' idx.1)).words.site (idx.2,w'.2)⟩) := by
    induction n with
    | zero => rfl
    | succ n ih =>
      let h := Nat.lt_of_succ_le hn
      let H := packHistory bottom M.epoch n
      let c := fun j : Fin (fan S) => H.term (q'.1 j)
      let sub := fun j : Fin (fan S) => fun i => z' (copyIndex (fan S) n (j,i))
      let tag := fun j => Outer.term layout bottom M.epoch base (advance M y hy pos) n (sub j) (q'.1 j)
      have hb := advance_power_site y hy pos M n h c tag q'.2 w'
      have hc := ih h.le (q'.1 w'.1.1) (sub w'.1.1) (w'.1.2,w'.2)
      refine hb.trans ((congrArg (fun v => (enrichedStepHosts M h c q'.2).site ⟨w'.1.1,v⟩) hc).trans ?_)
      let orig := originalNames (k := fan S) leaf n (fun _ => ())
      let big := originalNames (k := fan S) leaf (n+1) (fun _ => ())
      let idx := portEquiv (fan S) Team n w'.1.2
      let v : (parallelPacks fun _ : Fin ((fan S)^n) => bottom.val.pack).layout.Site :=
        ⟨idx.1,(base (sub w'.1.1 idx.1)).words.site (idx.2,w'.2)⟩
      let includeSite (z : (parallelPacks fun _ : Fin ((fan S)^n) => bottom.val.pack).layout.Site) :
          (parallelPacks fun _ : Fin ((fan S)^(n+1)) => bottom.val.pack).layout.Site :=
        ⟨copyIndex (fan S) n (w'.1.1,z.1),z.2⟩
      have he : big ⟨w'.1.1,orig.symm v⟩ = includeSite v := congrArg includeSite (orig.apply_symm_apply v)
      exact congrArg (enrichedNestedHosts M bottom (n+1) hn q').site (big.eq_symm_apply.mpr he)
  exact nested T le_rfl q z w

end Diagonal.CellEntries.EnrichedOuterReplay

end BorderVNP
end Computability
end OAI
