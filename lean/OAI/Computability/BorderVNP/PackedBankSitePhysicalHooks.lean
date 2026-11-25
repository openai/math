import OAI.Computability.BorderVNP.PackedBankSiteOperands

/-! # Terminal hook tests on the canonical sewn assignment

The terminal-side equality descriptors use the true hook cable starts in the
owning cell. Their destination staging area is the terminal bank's original
input row. Thus the tested word is the concatenation in the sewn table.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.BankSite

open Crossing Shortening Shortening.SeedIntervals Shortening.StaticRows Shortening.CombiningStep
open Crossing.Profile.Cell CellSparse BankCircuit BankJoint
open scoped Classical

private theorem stage_direct (d : CutDescriptor) (off base stride wire : ℕ) (boxes : List (List Factor))
    (bank : ℕ → Bool) :
    (d.hookRow false 1 ⟨off+base,0,1⟩ ⟨wire,0,1⟩).Valid boxes bank ↔
      (directHook d ⟨wire,0,1⟩ ((⟨base,stride,1⟩ : Port).shift off)).Valid boxes bank := by
  constructor <;> intro h i hi k hk <;> obtain rfl : i = 0 := by omega
  all_goals
    simpa [Port.atBit,CutDescriptor.terminalPort,CutDescriptor.slice,Port.shift] using (h 0 Nat.zero_lt_one k hk).symm

variable {D m : ℕ} [NeZero D] {K : Type*} [Field K] (e : PaidIdentity K D m)
variable {P S : Type} [Fintype P] {bits : P → ℕ} [Fintype S] (p : Pack D P bits K)
variable (bin : p.layout.Edge → Option S) (perm : Fin D → Equiv.Perm S)
variable (positive : p.layout.Edge → Bool) (first : Fin D × Bool) (q : Counts e p bin perm)
private noncomputable abbrev G := (output e p bin perm positive first q).layout
variable (a : S)
private noncomputable abbrev J := blocks p.layout bin perm m a
variable {C : Type} (cell : (G e p bin perm positive first q).Site → C)
variable (aux : (G e p bin perm positive first q).Site → ℕ)
variable {ns ne np : ℕ} (siteID : (G e p bin perm positive first q).Site ↪ Fin ns)
variable (edgeID : (G e p bin perm positive first q).Edge ↪ Fin ne) (portID : P ↪ Fin np)
variable (boxID : TemplateSite e → ℕ)
variable (W : CellBanks (G e p bin perm positive first q) cell aux)
private noncomputable abbrev raw := physicalRaw e p bin perm positive first q a cell aux siteID edgeID portID boxID

variable (binName : S → ℕ) (siteName : p.layout.Site → ℕ)
private abbrev Old (d : Fin D) := {z : p.layout.Edge // bin z = some (perm d a)}
private noncomputable abbrev tSite (t : Fin D × Bool) := seedSite e p bin perm positive first q a (.inr (.inl t))
private noncomputable abbrev loc := (terminalLayout (J p bin perm (m := m) a) m (q a).val).port (.inr (.inl ()))

/-- The actual incident equality row of the physical hook at its terminal end. -/
noncomputable def terminalHook (d : Fin D) (z : Old p bin perm a d) (src : Bool) : Record :=
  let G := G e p bin perm positive first q
  let u := seedHook e p bin perm a d z src
  let v := incidentSite G u false
  let row := descriptor p.layout bin perm m binName z (some (d,true))
  stagedHookRecord G cell (cell v) edgeID portID siteID aux ⟨v,rfl⟩ (incidentWire G u false) row false
    (loc e p bin perm q a).base

/-- A terminal's own physical hook equalities fill every gathered lane from its
actual network assignment, for arbitrary internal, staged, and supplied bits. -/
theorem terminal_hook_reads (t : Fin D × Bool) (boxes : List (List Factor)) :
    let v := tSite e p bin perm positive first q a t
    let y := W.wires edgeID portID v
    let x := raw e p bin perm positive first q a cell aux siteID edgeID portID boxID
    (∀ d z src, let r := endpointRecord p.layout bin perm m binName siteName positive a d z src
      (d,r.side) = t → (terminalHook e p bin perm positive first q a cell aux siteID edgeID portID binName d z src).Valid
        boxes (W.read v)) ↔
      ∀ k, W.read v ((gatheredPort e x (J p bin perm (m := m) a) (q a).val t).atBit 0 k.val) =
        (bundle p.layout bin perm m positive a).gather (cuts e p bin perm positive first q a y) t k := by
  intro v y x
  let G := G e p bin perm positive first q
  let h (d : Fin D) (z : Old p bin perm a d) (src : Bool) : Port :=
    ⟨cableBase G cell aux edgeID portID (seedHook e p bin perm a d z src) false,0,1⟩
  let atTerm := gatheredPort e x (J p bin perm (m := m) a) (q a).val
  let b := cuts e p bin perm positive first q a y
  have owner (d : Fin D) (z : Old p bin perm a d) (src : Bool) :
      let r := endpointRecord p.layout bin perm m binName siteName positive a d z src
      (d,r.side) = t → incidentSite G (seedHook e p bin perm a d z src) false = v := by
    intro r ht
    exact (hook_fields e p bin perm positive first q binName a d z src).2.1.trans
      (congrArg (tSite e p bin perm positive first q a) ht)
  have hr (d : Fin D) (z : Old p bin perm a d) (src : Bool) :
      let r := endpointRecord p.layout bin perm m binName siteName positive a d z src
      (d,r.side) = t → ∀ k, W.read v ((h d z src).atBit 0 k.val) = hookBit p.layout bin perm m a b d z src k := by
    intro r ht k
    let u := seedHook e p bin perm a d z src
    have hw : G.width u = (layout p.layout bin perm m).width (z.val,some (d,true)) := by cases src <;> rfl
    have read := cable_read G cell aux W edgeID portID u false (Fin.cast hw.symm k)
    rw [owner d z src ht] at read
    change W.read v ((⟨cableBase G cell aux edgeID portID u false,0,1⟩ : Port).atBit 0 k.val) = _
    simp only [Port.atBit,zero_mul,add_zero,mul_one]
    apply read.trans
    cases src <;> rfl
  rw [← directHooksOne_iff p.layout bin perm m binName siteName positive a b h atTerm t boxes (W.read v) hr]
  apply forall_congr'
  intro d
  apply forall_congr'
  intro z
  apply forall_congr'
  intro src
  apply imp_congr_right
  intro ht
  let u := seedHook e p bin perm a d z src
  let r := descriptor p.layout bin perm m binName z (some (d,true))
  let slot := (loc e p bin perm q a).base
  let w := cableBase G cell aux edgeID portID u false
  let pos (s : G.Site) := CellAddresses.siteBase G cell (cell s) siteID aux ⟨s,rfl⟩
  change (r.hookRow false 1 ⟨pos (incidentSite G u false)+slot,0,1⟩ ⟨w,0,1⟩).Valid boxes (W.read v) ↔
    (directHook r ⟨w,0,1⟩ ((⟨slot,m,1⟩ : Port).shift (pos v))).Valid boxes (W.read v)
  rw [owner d z src ht]
  exact stage_direct r (pos v) slot m w boxes (W.read v)

end Packing.BankSite

end BorderVNP
end Computability
end OAI
