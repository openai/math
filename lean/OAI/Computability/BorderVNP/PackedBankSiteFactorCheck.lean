import OAI.Computability.BorderVNP.PackedBankSitePhysicalHooks

/-! # Exact field factors checked by the emitted profile-site records

On the arbitrary three-block assignment in each owning cell, the actual
origin and terminal tapes accept exactly when their sewn field factor is one
and the allocated site words are the unique padded physical staging words.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.BankSite

open Crossing Shortening Shortening.SeedIntervals Shortening.StaticRows Shortening.CombiningStep
open Crossing.Profile.Cell BankPacket BankCircuit BankJoint CellSparse
open scoped Classical

private theorem finite_stages {D ns : ℕ} {C R P : Type} [Fintype R] [Fintype P] {bits : P → ℕ}
    (N : Network D P bits) (cell : N.Site → C) (aux : N.Site → ℕ) (W : CellBanks N cell aux)
    (siteID : N.Site ↪ Fin ns) (v : N.Site) (L : BankLayout R) (data : L.Data)
    (hcap : aux v = Fintype.card R * L.stride) :
    let c := cell v
    Stages L (fun t => W.read v (CellAddresses.siteBase N cell c siteID aux ⟨v,rfl⟩+t)) data ↔
      ∀ i : Fin (aux v), CellAddresses.siteWords N cell c siteID aux (W.staged c) ⟨v,rfl⟩ i =
        paddedBank L data i.val := by
  intro c
  have read (i : Fin (aux v)) := CellAddresses.site_at N cell c aux siteID (W.guessed c) (W.staged c)
    (W.supplied c) ⟨v,rfl⟩ i
  constructor
  · intro h i
    exact (read i).symm.trans (h (Fin.cast hcap i))
  · intro h i
    exact (read (Fin.cast hcap.symm i)).trans (h (Fin.cast hcap.symm i))

variable {D m : ℕ} [NeZero D] {K : Type*} [Field K] (e : PaidIdentity K D m)
variable {P S : Type} [Fintype P] {bits : P → ℕ} [Fintype S] (p : Pack D P bits K)
variable (bin : p.layout.Edge → Option S) (perm : Fin D → Equiv.Perm S)
variable (positive : p.layout.Edge → Bool) (first : Fin D × Bool) (q : Counts e p bin perm)
private noncomputable abbrev G := (output e p bin perm positive first q).layout
variable (a : S)
variable {C : Type} (cell : (G e p bin perm positive first q).Site → C)
variable (aux : (G e p bin perm positive first q).Site → ℕ)
variable {ns ne np : ℕ} (siteID : (G e p bin perm positive first q).Site ↪ Fin ns)
variable (edgeID : (G e p bin perm positive first q).Edge ↪ Fin ne) (portID : P ↪ Fin np)
variable (boxID : TemplateSite e → ℕ)
variable (W : CellBanks (G e p bin perm positive first q) cell aux) (boxes : List (List Factor))
variable (ext : Ports bits)

local notation3 "G₀" => G e p bin perm positive first q
local notation3 "j₀" => blocks p.layout bin perm m a
local notation3 "raw₀" => physicalRaw e p bin perm positive first q a cell aux siteID edgeID portID boxID
local notation3 "v₀" => seedSite e p bin perm positive first q a
local notation3 "pack₀" => output e p bin perm positive first q
local notation3 "y₀" => W.wires edgeID portID

/-- The exact sparse origin check, its unique finite staging vector, and the
actual field factor of the same sewn site. -/
theorem physical_origin_iff
    (hcap : aux (v₀ (.inl ())) = Fintype.card (Fin D × Bool) * (originLayout (Fin D × Bool) j₀ e.count).stride) :
    let v := v₀ (.inl ())
    let y := y₀ v
    let data := fun u i k => finTwoEquiv (selectors e p bin perm positive first q a y u i k)
    (∀ r ∈ emitted e first raw₀ (.inl ()),r.Valid boxes (W.read v)) ↔
      (∀ i : Fin (aux v), CellAddresses.siteWords G₀ cell (cell v) siteID aux (W.staged (cell v)) ⟨v,rfl⟩ i =
        paddedBank (originLayout (Fin D × Bool) j₀ e.count) data i.val) ∧ (G₀).read (pack₀).table y ext v = 1 := by
  intro v y data
  have ht := emitted_origin_accept e raw₀ first j₀ (q a).val (fun _ => rfl) boxes (W.read v)
  dsimp only at ht
  have hs := funext (origin_spoke e p bin perm positive first q a cell aux siteID edgeID portID boxID W)
  let L := originLayout (Fin D × Bool) j₀ e.count
  let actual : L.Data := fun u i k => W.read v ((physicalPort m (originWords e raw₀) (.inl u)).atBit i k)
  have hd : actual = data := by
    funext u i k
    exact (finTwoEquiv.apply_symm_apply _).symm.trans
      (congrArg finTwoEquiv (congrFun (congrFun (congrFun hs u) i) k))
  rw [ht,hs]
  apply and_congr
  · change Stages L _ actual ↔ _
    rw [hd]
    exact finite_stages G₀ cell aux W siteID v L data hcap
  · change _ ↔ (G₀).read (pack₀).table y ext (.inr ⟨a,.inl ()⟩) = 1
    rw [origin_factor e p bin perm positive first q a y ext]
    simp
    rfl

variable (binName : S → ℕ) (siteName : p.layout.Site → ℕ)

/-- The emitted terminal tape and its actual incident hook equalities evaluate
the sewn field factor on its canonical cable bits, with exactly one possible
auxiliary word at every bit of the site's slab. -/
theorem physical_terminal_iff (t : Fin D × Bool)
    (hcap : aux (v₀ (.inr (.inl t))) = Fintype.card (Unit ⊕ Unit ⊕ Fin e.count) *
      (terminalLayout j₀ m (q a).val).stride) :
    let v := v₀ (.inr (.inl t))
    let y := y₀ v
    let gathered := (bundle p.layout bin perm m positive a).gather (cuts e p bin perm positive first q a y) t
    let data := terminalData (q a).val (selectors e p bin perm positive first q a y t)
      (feederBlocks e p bin perm positive first q a y t) gathered
    ((∀ r ∈ emitted e first raw₀ (.inr (.inl t)),r.Valid boxes (W.read v)) ∧
      ∀ d z src, let r := endpointRecord p.layout bin perm m binName siteName positive a d z src
        (d,r.side) = t → (terminalHook e p bin perm positive first q a cell aux siteID edgeID portID binName d z src).Valid
          boxes (W.read v)) ↔
      (∀ i : Fin (aux v), CellAddresses.siteWords G₀ cell (cell v) siteID aux (W.staged (cell v)) ⟨v,rfl⟩ i =
        paddedBank (terminalLayout j₀ m (q a).val) data i.val) ∧ (G₀).read (pack₀).table y ext v = 1 := by
  intro v y gathered data
  have hhooks := terminal_hook_reads e p bin perm positive first q a cell aux siteID edgeID portID boxID W binName siteName t boxes
  dsimp only at hhooks
  rw [hhooks]
  let x := terminalWords e raw₀ t
  have hx : localHeader x = headerWord m (fun i => i.elim j₀ (q a).val) := rfl
  have ht := terminal_accept_iff m j₀ (q a).val x hx boxes (W.read v)
    (profileCounts_total e _ q a) gathered
  dsimp only at ht
  have hs := terminal_spoke e p bin perm positive first q a cell aux siteID edgeID portID boxID W t
  have hf := terminal_feeders e p bin perm positive first q a cell aux siteID edgeID portID boxID W t
  dsimp only at hs hf
  apply ht.trans
  dsimp only [x]
  rw [hs,hf]
  apply and_congr
  · exact finite_stages G₀ cell aux W siteID v _ data hcap
  · change _ ↔ (G₀).read (pack₀).table y ext (.inr ⟨a,.inr (.inl t)⟩) = 1
    rw [terminal_factor e p bin perm positive first q a y ext t]
    simp
    rfl

end Packing.BankSite

end BorderVNP
end Computability
end OAI
