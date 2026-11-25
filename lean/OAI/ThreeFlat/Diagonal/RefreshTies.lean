import OAI.ThreeFlat.Diagonal.RefreshDense

namespace OAI
/-! # The dense port ties of the refresh step

An old outgoing incidence is `(block, port, slot)`. The permutation `arrival`
gives the corresponding incoming incidence. The new external wire fixes
one tuple of all source-port fields for a given block and outgoing slot.
Both ends read segments in source-port order, even when the destination
port was translated. Each end is tied locally by the dense graph, with
one complete directed set of ties for each direction. -/

namespace ThreeFlat.Diagonal.RefreshTies

open LinearAlgebra.SpectralBooks
open scoped Classical BigOperators
noncomputable section

variable {U : Type} [Fintype U] {m : ℕ} {K : Type*} [Field K]

abbrev Address (U : Type) (m : ℕ) := U × Fin m × Fin m

/-- The one field grouped on a new external wire. -/
abbrev Bundle (A : Address U m → Type) (u : U) (s : Fin m) := ∀ i : Fin m, A (u,i,s)

/-- Global assignment to the external bundle wires. -/
abbrev External (A : Address U m → Type) := ∀ u s, Bundle A u s

/-- Each dense outgoing tie is named in source coordinates. Each incoming
tie recovers its source coordinate by inverting the old slot matching. -/
def addr (arrival : Equiv.Perm (Address U m)) (u : U) (e : Bool × Fin m × Fin m) : Address U m :=
  if e.1 then arrival.symm (u, e.2) else (u, e.2)

/-- Reindexing the bundle from the destination does not change the order
of its fields. -/
def readExternal {A : Address U m → Type} (z : External A) (e : Address U m) : A e :=
  z e.1 e.2.2 e.2.1

/-- Fix independent half-wire values at the old ports and a shared tuple
on each new external wire. At the tail of each dense tie the original port
supplies its half-index. At the head the designated bundle port reads the
corresponding external field. -/
def tieState {A : Address U m → Type} (arrival : Equiv.Perm (Address U m))
    (x y : ∀ e, A e) (z : External A) (u : U) (i : Fin m) :
    (RefreshMotif.denseGraph m).State (fun e => A (addr arrival u e)) i := fun p =>
  let e := p.1.1
  if p.1.2 then readExternal z (addr arrival u e)
  else if e.1 then y (addr arrival u e) else x (addr arrival u e)

/-- Old external half-indices at a single port, in its own outgoing and
incoming slot orders. -/
abbrev OldPort (A : Address U m → Type) (arrival : Equiv.Perm (Address U m)) (u : U) (i : Fin m) :=
  ((s : Fin m) → A (u,i,s)) × ((s : Fin m) → A (arrival.symm (u,i,s)))

/-- Two external bundle halves at their designated port. Incoming fields
are projected into receiving-port order by the inverse slot permutation. -/
abbrev BundlePort (A : Address U m → Type) (arrival : Equiv.Perm (Address U m)) (u : U) (s : Fin m) :=
  ((i : Fin m) → A (u,i,s)) × ((i : Fin m) → A (arrival.symm (u,i,s)))

def readOld {A : Address U m → Type} (arrival : Equiv.Perm (Address U m))
    (x y : ∀ e, A e) (u : U) (i : Fin m) : OldPort A arrival u i :=
  (fun s => x (u,i,s),fun s => y (arrival.symm (u,i,s)))

def readBundle {A : Address U m → Type} (arrival : Equiv.Perm (Address U m))
    (z : External A) (u : U) (s : Fin m) : BundlePort A arrival u s :=
  (fun i => z u s i,fun i => readExternal z (arrival.symm (u,i,s)))

/-- A local contraction entry uses only the old indices at this port and
the fields on its two incident external bundle ends. -/
def portFields {A : Address U m → Type} (arrival : Equiv.Perm (Address U m)) (u : U) (v : Fin m)
    (old : OldPort A arrival u v) (ext : BundlePort A arrival u v) :
    (RefreshMotif.denseGraph m).State (fun e => A (addr arrival u e)) v := by
  rintro ⟨⟨⟨dir,i,s⟩,side⟩,h⟩
  cases side with
  | false =>
    change i = v at h
    subst v
    cases dir with
    | false => exact old.1 s
    | true => exact old.2 s
  | true =>
    change s = v at h
    subst v
    cases dir with
    | false => exact ext.1 i
    | true => exact ext.2 i

omit [Fintype U] in
theorem tieState_local {A : Address U m → Type} (arrival : Equiv.Perm (Address U m))
    (x y : ∀ e, A e) (z : External A) (u : U) (v : Fin m) :
    tieState arrival x y z u v = portFields arrival u v (readOld arrival x y u v) (readBundle arrival z u v) := by
  funext p
  rcases p with ⟨⟨⟨dir,i,s⟩,side⟩,h⟩
  cases side <;> cases dir <;> subst v <;> rfl

omit [Fintype U] in
private theorem match_iff {A : Address U m → Type} (arrival : Equiv.Perm (Address U m))
    (x y : ∀ e, A e) (z : External A) (u : U) :
    (∀ e, (tieState arrival x y z u ((RefreshMotif.denseGraph m).tail e) ⟨(e,false),rfl⟩) =
      tieState arrival x y z u ((RefreshMotif.denseGraph m).head e) ⟨(e,true),rfl⟩) ↔
    (∀ i s, x (u,i,s) = z u s i) ∧
      ∀ i s, y (arrival.symm (u,i,s)) = readExternal z (arrival.symm (u,i,s)) := by
  constructor
  · intro h
    exact ⟨fun i s => h (false,i,s), fun i s => h (true,i,s)⟩
  · rintro ⟨hx,hy⟩ ⟨dir,i,s⟩
    cases dir with
    | false => exact hx i s
    | true => exact hy i s

/-- Summing the ports' new bundle words gives the old wire equality. The
outgoing ties uniquely force every source-port field; the incoming ties
check each old wire once through the actual incoming slot permutation. -/
theorem old_wiring_eq_bundles {A : Address U m → Type} [∀ e, Fintype (A e)]
    (arrival : Equiv.Perm (Address U m)) (x y : ∀ e, A e) :
    (if x = y then (1 : K) else 0) =
      ∑ z : External A, ∏ u, (RefreshMotif.denseGraph m).wiring (fun e => A (addr arrival u e))
        (tieState arrival x y z u) := by
  let packed : External A := fun u s i => x (u,i,s)
  rw [Finset.sum_eq_single packed]
  · by_cases he : x = y
    · subst y
      have good u := (match_iff arrival x x packed u).mpr ⟨fun _ _ => rfl, fun _ _ => rfl⟩
      simp [PortGraph.wiring, good]
    · obtain ⟨e, hne⟩ : ∃ e, x e ≠ y e := by simpa only [funext_iff, not_forall] using he
      let q := arrival e
      have bad := mt (match_iff arrival x y packed q.1).mp (fun h => hne (by
        have h' := h.2 q.2.1 q.2.2
        change y (arrival.symm (arrival e)) = x (arrival.symm (arrival e)) at h'
        exact Eq.mp (congrArg (fun z => x z = y z) (arrival.symm_apply_apply e)) h'.symm))
      rw [ite_eq_right he, Finset.prod_eq_zero (Finset.mem_univ q.1) (ite_eq_right bad)]
  · intro z _ hz
    obtain ⟨u,s,i,h⟩ : ∃ u s i, z u s i ≠ packed u s i := by
      by_contra! agree
      apply hz
      funext u s i
      exact agree u s i
    have bad := mt (match_iff arrival x y z u).mp (fun hab => h (hab.1 i s).symm)
    exact Finset.prod_eq_zero (Finset.mem_univ u) (ite_eq_right bad)
  · simp

end
end ThreeFlat.Diagonal.RefreshTies

end OAI
