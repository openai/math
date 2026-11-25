import OAI.Computability.BorderVNP.TransmissionPairViews
import OAI.Computability.BorderVNP.CubeScatterCommonPrepared
import OAI.Computability.BorderVNP.CubeSharedRowsPhysical

/-! # Shared selector and crossing words in the returned transmission RAM

The pair word is read directly from the forward ordered buffer. The original
shared writer and scheduler identify its width and owners. For co-located
owners its bits are the single chronological guesses. For distinct owners
they are the specified exterior hops, including their relay and ordinal.
The reverse view contains the same word. -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction

open VPVNP BurstRAM Diagonal.Layout RoutingISA RoutingISA.Transmission Routing
open DiagonalResidueRAM BorderVNP.Cube BorderVNP.Cube.Scatter

open private square_key from OAI.Computability.BorderVNP.CubeSharedRowsLoad

variable {R r t d link inner n w : ℕ} {Edge : Type} {G : Wiring R r t d link inner n Edge}
variable {pin : Fin d → Bool} {ext : Exterior R r link → Bool} {L : WireLayout (R+1) r link}
variable {D : Packing.Directory.Layout} {pp lp : ℕ → ℕ × ℕ} {owner : ℕ → Fin (R+1)} {origin stride : ℕ}
variable {H : Fin (R+1) → TeamHistory w} {pins : Fin (R+1) → Pins.Layout}
local notation "Delivery" => ReturnedDelivery G pin ext L D pp lp owner origin stride H pins

/-- Read the bit digits at the given addresses of an actual team history. -/
def receivedWord (m : Memory w) (base width : ℕ) : List Bool :=
  List.ofFn fun j : Fin width => decide ((m (base+j.val)).val = 1)

@[simp] theorem receivedWord_length (m : Memory w) (base width : ℕ) :
    (receivedWord m base width).length = width := List.length_ofFn

private theorem receivedDigit {m : Memory w} {a : ℕ} {b : Bool} (word : 0 < w)
    (readAt : m a = wordBit w b) : decide ((m a).val = 1) = b := by
  rw [readAt,wordBit_val (Nat.one_lt_pow word.ne' (by decide))]
  cases b <;> rfl

/-- Actual per-team images of the emitted shared records immediately before the
common scheduler, together with the scheduler's record base and count. -/
structure SharedWriters (f : Delivery) (g : SharedRows.Layout) (src : Fin (R+1) → ℕ → ℕ) : Prop where
  emitted : ∀ u, g.Emitted (src u) (f.before u)
  fitted : ∀ u, g.Fits w (src u)
  records : f.table.records = g.records
  count : f.table.count = g.dataCount+g.groups.choose 2
  room : g.banks+g.stride*g.groups^2 ≤ 2^w

/-- All ordered pair buffers lie in this protected memory interval. -/
def pairRegion (g : SharedRows.Layout) : Set ℕ :=
  Set.Ico g.banks (g.banks+g.stride*g.groups^2)

private theorem view_inside (g : SharedRows.Layout) {a b j width : ℕ}
    (ha : a < g.groups) (hb : b < g.groups) (fits : width ≤ g.stride) (hj : j < width) :
    g.view a b+j ∈ pairRegion g := by
  have key := square_key ha hb
  have enough := Nat.mul_le_mul_left g.stride key
  rw [Nat.mul_succ] at enough
  change g.banks ≤ g.banks+g.stride*(a*g.groups+b)+j ∧
    g.banks+g.stride*(a*g.groups+b)+j < g.banks+g.stride*g.groups^2
  omega

/-- The three scheduled record words used by the receiver are precisely the
two actual symbol-owner entries and the emitted selector-plus-cut width. -/
theorem SharedWriters.fields {f : Delivery} {g : SharedRows.Layout} {src : Fin (R+1) → ℕ → ℕ}
    (writer : SharedWriters f g src) (u : Fin (R+1)) {a b : ℕ} (ab : a < b) (bg : b < g.groups) :
    let row := f.row (g.rowIndex a b)
    row.first = src u (g.owners+a) ∧ row.second = src u (g.owners+b) ∧
    row.width = g.selectors+g.crossWidth (src u) a b := by
  let actual := g.shared_range_fields (f.image u) f.allocated writer.records writer.count
    (writer.emitted u).rows ab bg
  let scheduled := tableRange_fields (f.image u) f.allocated (f.records u) (writer.count ▸ g.index_lt ab bg)
  exact ⟨scheduled.2.1.symm.trans actual.2.1,scheduled.2.2.1.symm.trans actual.2.2.1,
    scheduled.2.2.2.1.symm.trans actual.2.2.2.1⟩

/-- Every bit of a co-located pair's forward raw word is the unique chronological
guess for that row and position. -/
theorem SharedWriters.local_digit {f : Delivery} {g : SharedRows.Layout} {src : Fin (R+1) → ℕ → ℕ}
    (writer : SharedWriters f g src) (u : Fin (R+1)) {a b j : ℕ} (ab : a < b) (bg : b < g.groups)
    (first : (f.row (g.rowIndex a b)).first = u.val) (second : (f.row (g.rowIndex a b)).second = u.val)
    (inside : j < (f.row (g.rowIndex a b)).width) :
    decide (((H u).history.val.2.2 (g.view a b+j)).val = 1) = (H u).bits (g.rowIndex a b) j := by
  have read := f.local_pair g u (writer.emitted u) (writer.fitted u) writer.records writer.count writer.room
    ab bg first second inside
  apply receivedDigit f.word
  exact read.1.trans (by cases (H u).bits (g.rowIndex a b) j <;> rfl)

/-- Every bit of a remotely transmitted pair's raw word is the exterior bit at
the true scheduled relay and hop ordinal. -/
theorem SharedWriters.remote_digit {f : Delivery} {g : SharedRows.Layout} {src : Fin (R+1) → ℕ → ℕ}
    (writer : SharedWriters f g src) (u z : Fin (R+1)) (diff : u ≠ z) {a b j : ℕ}
    (ab : a < b) (bg : b < g.groups) (first : (f.row (g.rowIndex a b)).first = u.val)
    (second : (f.row (g.rowIndex a b)).second = z.val) (inside : j < (f.row (g.rowIndex a b)).width) :
    let k := f.table.ordinal f.row (g.rowIndex a b)+j
    let v := Routing.relay L.three diff k
    ∃ p : Hop L.three L.width u v, p.1 = z ∧ p.2.val = k ∧
      decide (((H u).history.val.2.2 (g.view a b+j)).val = 1) = (L.exteriorEquiv ext).hop u v p := by
  obtain ⟨p,hz,hk,read,_⟩ := f.remote_pair g u z diff src writer.emitted writer.fitted writer.records
    writer.count writer.room ab bg first second inside
  exact ⟨p,hz,hk,receivedDigit f.word read⟩

/-- Both distinct ordered views contain the entire physical word, including
when the two symbols belong to one team. Every input read lies inside the
reserved source banks and fits the machine word width. -/
theorem SharedWriters.pair_resident {f : Delivery} {g : SharedRows.Layout} {src : Fin (R+1) → ℕ → ℕ}
    (writer : SharedWriters f g src) (u z : Fin (R+1)) {a b : ℕ} (ab : a < b) (bg : b < g.groups)
    (first : (f.row (g.rowIndex a b)).first = u.val) (second : (f.row (g.rowIndex a b)).second = z.val) :
    let width := (f.row (g.rowIndex a b)).width
    let raw := receivedWord (H u).history.val.2.2 (g.view a b) width
    Resident (pairRegion g) (H u).history.val.2.2 (g.view a b) raw ∧
      Resident (pairRegion g) (H z).history.val.2.2 (g.view b a) raw := by
  intro width raw
  have widthFit : width ≤ g.stride := by
    dsimp only [width]
    rw [(writer.fields u ab bg).2.2]
    exact (writer.fitted u).widthFit b bg a ab
  have words (j : ℕ) (hj : j < width) : ∃ bit : Bool,
      (H u).history.val.2.2 (g.view a b+j) = wordBit w bit ∧
      (H z).history.val.2.2 (g.view b a+j) = wordBit w bit := by
    by_cases h : u = z
    · subst z
      let bit := (H u).bits (g.rowIndex a b) j
      have eq : (if bit then (1 : Word w) else 0) = wordBit w bit := by cases bit <;> rfl
      have read := f.local_pair g u (writer.emitted u) (writer.fitted u) writer.records writer.count writer.room
        ab bg first second hj
      exact ⟨bit,read.1.trans eq,read.2.trans eq⟩
    · obtain ⟨p,_,_,x,y⟩ := f.remote_pair g u z h src writer.emitted writer.fitted writer.records writer.count
        writer.room ab bg first second hj
      exact ⟨_,x,y⟩
  have len : raw.length = width := receivedWord_length ..
  have read (j : Fin raw.length) :
      (H u).history.val.2.2 (g.view a b+j.val) = wordBit w raw[j] ∧
      (H z).history.val.2.2 (g.view b a+j.val) = wordBit w raw[j] := by
    obtain ⟨bit,hx,hy⟩ := words j.val (len ▸ j.isLt)
    have digit : raw[j] = bit := by
      change (List.ofFn fun k : Fin width => decide (((H u).history.val.2.2 (g.view a b+k.val)).val=1))[j.val] = bit
      rw [List.getElem_ofFn]
      exact receivedDigit f.word hx
    rw [digit]; exact ⟨hx,hy⟩
  have bounds {x y : ℕ} (hx : x < g.groups) (hy : y < g.groups) (j : ℕ) (hj : j < raw.length) :
      g.view x y+j ∈ pairRegion g ∧ g.view x y+j < 2^w := by
    have inside := view_inside g hx hy widthFit (len ▸ hj)
    exact ⟨inside,inside.2.trans_le writer.room⟩
  exact ⟨⟨fun j => (read j).1,bounds (ab.trans bg) bg⟩,⟨fun j => (read j).2,bounds bg (ab.trans bg)⟩⟩

end TeamContraction

end BorderVNP
end Computability
end OAI
