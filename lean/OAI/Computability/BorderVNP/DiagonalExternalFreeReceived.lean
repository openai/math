import OAI.Computability.BorderVNP.DiagonalExternalFreeGroups
import OAI.Computability.BorderVNP.TransmissionReceivedFields
import OAI.Computability.BorderVNP.DiagonalPins

/-! # Used grouped inputs in the returning transmission memories

The directory supplies a cell and base for each original team and tile.
Reading that cell's final physical memory at the selected lane recovers
the programmed literal or the chosen substituted index of the route.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal.ExternalSew

open Crossing TeamContraction RoutingISA RoutingISA.Transmission RoutingISA.Pins
open VPVNP.BurstRAM
open scoped Classical

variable {R r t pins link inner n w V g : ℕ} {Edge : Type} {G : Wiring R r t pins link inner n Edge}
    {inputPin : Fin pins → Bool} {ext : Exterior R r link → Bool} {wire : Routing.WireLayout (R+1) r link}
    {entries desc : ℕ} {pp lp : ℕ → ℕ × ℕ} {owner : ℕ → Fin (R+1)} {origin stride : ℕ}
    {H : Fin (R+1) → TeamHistory w} {ib hb sb : Fin (R+1) → ℕ}

local notation "PL" => fun u => G.pinLayout u (ib u) (hb u) (sb u)
local notation "D" => freeDirectory R r (G.program.length+t) link V g entries desc
local notation "Delivery" => ReturnedDelivery G inputPin ext wire D pp lp owner origin stride H PL

/-- The grouped input read from the actual receiver of this original team's
tile. Its base slot is the location populated by the live directory. -/
def receivedWord (lp : ℕ → ℕ × ℕ) (owner : ℕ → Fin (R+1)) (origin stride : ℕ)
    (H : Fin (R+1) → TeamHistory w) (a : FreeBlock R V) (j : Fin g) : Word w :=
  let dst := lp (a.1.val*V+a.2.val)
  (H (owner dst.1)).history.val.2.2 (origin+dst.1*stride+dst.2+j.val)

/-- Grouped Boolean ports as observed in the returned consumer memories.
Only the genuine literal and pin coordinates have prescribed contents. -/
def receivedBank (lp : ℕ → ℕ × ℕ) (owner : ℕ → Fin (R+1)) (origin stride : ℕ)
    (H : Fin (R+1) → TeamHistory w) : Ports (fun _ : FreeBlock R V => g) :=
  fun a j => decide ((receivedWord lp owner origin stride H a j).val = 1)

private theorem word_at_field (hg : 0 < g) (room : r*(2*(G.program.length+t)+R*link) ≤ V*g)
    (u : Fin (R+1)) (p : Fin r) (f : Fin 2) (j : Fin (G.program.length+t)) :
    let a := freeLane hg room (fromField u p f j)
    let x := freeFieldOrdinal p f j R link
    let dst := lp (u.val*V+x/g)
    receivedWord lp owner origin stride H a.1 a.2 =
      (H (owner dst.1)).history.val.2.2 (origin+dst.1*stride+dst.2+x%g) := by
  obtain ⟨hu,hs,hl⟩ := freeLane_field hg room u p f j
  dsimp only
  unfold receivedWord
  rw [hu,hs,hl]

private theorem substitute_word (i : Fin pins → Bool) (u : Fin (R+1)) (x : ℕ) :
    (if (PL u).active x then Fin.ofNat (2^w) (extendGuess i x).toNat else 0) =
      Fin.ofNat _ (liveBit u i x).toNat := by
  by_cases h : u = 0
  · subst u
    by_cases hx : x < pins <;> simp [Layout.active,Wiring.pinLayout,extendGuess,liveBit,hx]
  · have hu : u.val ≠ 0 := fun hu => h (Fin.ext hu)
    simp [Layout.active,Wiring.pinLayout,hu,h,liveBit]

/-- A returning native route delivers every used group coordinate, in the
actual machine-word encoding, for both programmed literals and prepared
substitution bits. The external live pin of the calling team may differ
from the index being substituted into the parse family. -/
theorem received_free_word (delivery : Delivery) (hg : 0 < g)
    (room : r*(2*(G.program.length+t)+R*link) ≤ V*g) (i : Fin pins → Bool)
    (subst : ∀ u, SubstitutionAt (PL u) (extendGuess i) (H u).initial)
    (z : FreePort R r (G.program.length+t)) :
    let a := freeLane hg room z
    receivedWord lp owner origin stride H a.1 a.2 = Fin.ofNat _ (freeBits G i z).toNat := by
  rcases z with ⟨u,p,j | j⟩
  · let observe (x : ℕ) : Word w :=
      let dst := lp (u.val*V+x/g)
      (H (owner dst.1)).history.val.2.2 (origin+dst.1*stride+dst.2+x%g)
    have obs := word_at_field (lp := lp) (H := H) (owner := owner) (origin := origin)
      (stride := stride) hg room u p 0 j
    have pos : freeFieldOrdinal p 0 j R link = p.val*(D).stride+j.val := by
      simp [freeFieldOrdinal,freeDirectory,Packing.Directory.Layout.stride]
    have result := delivery.live_literal hg (by change 0 < 2; decide) u u rfl p j
    exact (obs.trans (congrArg observe pos)).trans (result.trans (by
      change TeamTapeInputEmit.headerWord w (G.program ++ List.ofFn (G.literal u p)) j.val = _
      simp [TeamTapeInputEmit.headerWord,freeBits]))
  · let observe (x : ℕ) : Word w :=
      let dst := lp (u.val*V+x/g)
      (H (owner dst.1)).history.val.2.2 (origin+dst.1*stride+dst.2+x%g)
    have obs := word_at_field (lp := lp) (H := H) (owner := owner) (origin := origin)
      (stride := stride) hg room u p 1 j
    have pos : freeFieldOrdinal p 1 j R link =
        p.val*(D).stride+((D).literal+((D).teams-1)*(D).link)+j.val := by
      simp [freeFieldOrdinal,freeDirectory,Packing.Directory.Layout.stride]
    have result := delivery.live_substitute hg (by change 1 < 2; decide) u u rfl p j (extendGuess i) (subst u)
    have field : (finProdFinEquiv (p,j)).val = p.val*(D).literal+j.val := by
      change j.val+(G.program.length+t)*p.val = p.val*(G.program.length+t)+j.val
      ac_rfl
    refine (obs.trans (congrArg observe pos)).trans (result.trans ?_)
    simp only [freeBits,field]
    exact substitute_word (G := G) (ib := ib) (hb := hb) (sb := sb) i u _

/-- Reading a genuine used lane as a Boolean recovers the original raw
substitution, including inputs outside the residue box. -/
theorem received_raw_bank (delivery : Delivery) (hg : 0 < g)
    (room : r*(2*(G.program.length+t)+R*link) ≤ V*g) (bits : Fin pins → Bool)
    (subst : ∀ u, SubstitutionAt (PL u) (extendGuess bits) (H u).initial)
    (z : FreePort R r (G.program.length+t)) :
    let a := freeLane hg room z
    receivedBank lp owner origin stride H a.1 a.2 = freeBits G bits z := by
  have read := received_free_word delivery hg room bits subst z
  change decide ((receivedWord lp owner origin stride H (freeLane hg room z).1 (freeLane hg room z).2).val = 1) = _
  rw [read]
  have lim : 1 < 2^w := Nat.one_lt_pow delivery.word.ne' (by decide)
  cases freeBits G bits z <;> simp [Nat.mod_eq_of_lt lim]

/-- The free-bank premise of the numbered tensor expansion follows from the
native transmission memories for any successfully decoded canonical pin. -/
theorem received_free_bank {I : Type*} (codec : PinCodec I pins) (delivery : Delivery)
    (hg : 0 < g) (room : r*(2*(G.program.length+t)+R*link) ≤ V*g)
    {bits : Fin pins → Bool} {i : I} (decoded : codec.decode bits = some i)
    (subst : ∀ u, SubstitutionAt (PL u) (extendGuess bits) (H u).initial)
    (z : FreePort R r (G.program.length+t)) :
    let a := freeLane hg room z
    receivedBank lp owner origin stride H a.1 a.2 = freeBits G (codec.encode i) z := by
  rw [← (codec.decode_eq_some bits i).mp decoded]
  exact received_raw_bank delivery hg room bits subst z

end Diagonal.ExternalSew

end BorderVNP
end Computability
end OAI
