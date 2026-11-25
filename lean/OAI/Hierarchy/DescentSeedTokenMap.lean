import OAI.Hierarchy.DescentSeedSignedBroadcast

namespace OAI
/-! # One-based donor tokens on each live lane of a packed seed word -/
namespace Hierarchy.DescentSeedTokenColumns
open DescentSIMDLookup
open scoped Fin.CommRing

def bump {a : ℕ} (b : ℕ) (x : Cell a) : Cell b := (x.val+1 : ℕ)

theorem mask_bump {a b O G M : ℕ} (xs : Fin O→Fin G→Cell a) (p : Row O G M) :
    ((table (M:=M) (bump b) (data xs p)).val &&& maskWord b M G p.2.val)=
      (data (fun v g=>bump b (xs v g)) p).val := by
  rw [maskWord,Nat.and_two_pow_sub_one_eq_mod]
  exact DescentSixParty.PackedCensus.masked_data (bump b) xs p

def values {a b X O H G : ℕ} (src : Fin H→Option (Option (Fin O))) (hub : Cell b)
    (xs : Fin X→Fin O→Fin G→Cell a) (q : Fin X) (v : Fin H) (g : Fin G) : Cell b :=
  match src v with
  | none => 0
  | some none => hub
  | some (some i) => bump b (xs q i g)

end Hierarchy.DescentSeedTokenColumns

end OAI
