import OAI.Computability.BorderVNP.CellPacketGeometryTerminalFeeds
import OAI.Computability.BorderVNP.PackedFinalTieCost

/-! # Charging the concrete retained-history feeds and physical site lookup -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellPacketGeometry.History.Native

open LiveWords Packing.Inherited FrozenTape CellSparse Packet VPVNP.VerifierNetwork

/-- One sparse lookup with three packed payload fields costs a cubic factor
in the largest address, field, and sort depth, per true reserved row. -/
theorem siteCost_cubic (a slots q k w W : ℕ) (hb : Nat.clog 2 ((a+1)+slots) ≤ W)
    (hq : q≤W) (hk : k≤W) (hw : w≤W) :
    siteCost a slots q k w ≤ 2000*((a+1)+slots+1)*(W+1)^3 := by
  let b := Nat.clog 2 ((a+1)+slots)
  have h : b≤W := hb
  have u : k+2*w ≤ 3*W := by omega
  have work : (q+1+(k+2*w))*8 + (((k+2*w)+b)+1+q) + b^2*(24*(((k+2*w)+b)+1+q)+1) +
      (k+2*w)*(60*q+16*(k+2*w)+33) + b^2*(24*((k+2*w)+b)+1) ≤ 1000*(W+1)^3 := by
    calc
      _ ≤ (W+1+(3*W))*8 + (((3*W)+W)+1+W) + W^2*(24*(((3*W)+W)+1+W)+1) +
          (3*W)*(60*W+16*(3*W)+33) + W^2*(24*((3*W)+W)+1) := by gcongr
      _ ≤ _ := by nlinarith [Nat.zero_le (W^2),Nat.zero_le (W^3)]
  exact (Nat.mul_le_mul (pow_clog_le ((a+1)+slots)) work).trans (by ring_nf; rfl)

variable {a C cap k w d t q : ℕ} {R B U V E Orig σ : Type}
variable [Fintype R] [Fintype B] [Fintype U] [Fintype V] [Fintype E] [Fintype σ]
variable (F : Feeds σ R B U V E a d t k w) (S : Schema R B) (L : Schema U V)
variable (boxes : Fin a → List (Source.Box Orig)) (sh : ∀ r, (S.tags r).length≤cap) (lh : ∀ u, (L.tags u).length≤cap)
variable (priv : Fin (C+1) → E) (rep : Fin (C+1) → List (List E))
variable (hd : d≤q) (ht : t≤q) (room : a<2^q) (croom : C<2^k)
variable (hs : ∀ r, S.width r≤w) (hl : ∀ u, L.width u≤w)
variable (base : Fin (roster a S L).length → Fin (C+1))
variable (pointer : Orig → (template S L boxes sh lh priv rep).Fields)
variable (pad : (roster a S L).length < 2^q) (dest H : ℕ)
local notation3 "T₀" => template S L boxes sh lh priv rep
local notation3 "vol₀" => sourceVolume S L boxes rep

/-- The true chronological packet circuit, including its actual cell/bit/box
lookup, has only a cubic logarithmic overhead on the fixed public source
volume in addition to the producing frames themselves. -/
theorem Feeds.ordered_cubic (W : ℕ) (wk : k≤W) (ww : w≤W) (wq : q≤W)
    (wp : (T₀).publicDepth≤W) (wd : (T₀).chunkDepth≤W) (wb : (T₀).recordDepth≤W)
    (wh : Nat.clog 2 ((roster a S L).length+(C+1))≤W)
    (ws : Nat.clog 2 ((a+1)+(roster a S L).length)≤W) :
    (F.ordered S L boxes sh lh priv rep hd ht room croom hs hl base pointer pad dest H).size ≤
      F.history.size+F.binding.size+F.table.size+F.field.size+16006010*vol₀*(W+1)^3 := by
  have coarse := F.ordered_size S L boxes sh lh priv rep hd ht room croom hs hl base pointer pad dest H W wk ww wq wp wd wb wh
  have mass : (a+1)+(roster a S L).length+1≤3*vol₀ := by simp only [sourceVolume,roster,List.length_append,List.length_map,List.length_cons,List.length_nil,List.length_finRange]; omega
  have slots : (roster a S L).length ≤ vol₀ := by simp only [sourceVolume,roster,List.length_append,List.length_map,List.length_cons,List.length_nil,List.length_finRange]; omega
  have lookup := (siteCost_cubic a (roster a S L).length q k w W ws wq wk ww).trans
    (Nat.mul_le_mul_right ((W+1)^3) (Nat.mul_le_mul_left 2000 mass))
  have width : q ≤ (W+1)^3 := by nlinarith [Nat.zero_le (W^2),Nat.zero_le (W^3)]
  have anchors := Nat.mul_le_mul_right 8 (Nat.mul_le_mul slots width)
  have pos : 0<vol₀ := by unfold sourceVolume; omega
  have one : 0 < vol₀*(W+1)^3 := Nat.mul_pos pos (pow_pos (Nat.succ_pos _) _)
  simp only [Nat.mul_assoc] at lookup ⊢
  rw [show 16000000*vol₀*(W+1)^3 = 16000000*(vol₀*(W+1)^3) from Nat.mul_assoc ..] at coarse
  omega

end CellPacketGeometry.History.Native

end BorderVNP
end Computability
end OAI
