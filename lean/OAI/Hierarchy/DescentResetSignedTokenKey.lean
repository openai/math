import OAI.Hierarchy.DescentResetSignedTokenWidth
import OAI.Hierarchy.DescentResetSignedTokenInputs
import OAI.Hierarchy.DescentClosedReset

namespace OAI
/-! # Genuine dated signed-cable and marked-token table sizes at a reached reset -/
namespace Hierarchy.DescentResetSignedTokens
open DescentSixParty DescentCompiler DescentPackedWalsh
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F] {d k i D n C f g cut tail h₀ z wire hist : ℕ}
    {bs : P→ℕ} {W : MarkedWorld F d P bs} {G : PoweredGadget F} {S : AtomSchedule} {q ε : ℝ}
    (r : Reached W G q ε S k i z D wire hist)
    (rates : ResetRates G S k D n h₀ C f g cut tail)
local notation "m" => (S.groupWidth k tail i+k)
local notation "b" p => (S.localWalshBits p m f (quota S.rounds))

include rates

theorem reached_quarter (p h oldCut : ℕ) (age : i≤S.length)
    (small : 8*(b p)≤h) (previous : oldCut≤laneBits m h (b p)) :
    DescentSignedCableCodec.width r.placement.degree r.placement.cap*2^oldCut≤h/4 := by
  have deg : r.placement.degree≤quota S.rounds := by
    rw [r.branch]
    exact (Nat.le_mul_of_pos_right D (Nat.two_pow_pos _)).trans rates.degree
  exact signed_quarter_at S p rates.height age r.valid.capacity deg small previous

theorem reached_key (p h hosts groups source short : ℕ) (age : i≤S.length)
    (small : 8*(b p)≤h) :
    let M:=2^(laneBits m h (b p)-k)
    let s:=datedLayout r.placement hosts groups source M short
    s.bits*s.targetLanes≤h/2 ∧ 2^(s.bits*s.targetLanes)≤2^(h/2) := by
  have deg : r.placement.degree≤quota S.rounds := by
    rw [r.branch]
    exact (Nat.le_mul_of_pos_right D (Nat.two_pow_pos _)).trans rates.degree
  have fit:=signed_key_at S p rates.height age r.valid.capacity deg small
    (Nat.sub_le (laneBits m h (b p)) k)
  exact ⟨fit,Nat.pow_le_pow_right (by decide) fit⟩


/-- The preceding venue publishes its normalized signed shelf at a public pitch
no larger than the upcoming Walsh word. Both table exponents are charged here. -/
theorem reached_both_keys (p h hosts groups oldCut short : ℕ) (age : i≤S.length)
    (small : 8*(b p)≤h) (previous : oldCut≤laneBits m h (b p)) :
    let M:=2^(laneBits m h (b p)-k)
    let s:=datedLayout r.placement hosts groups (2^oldCut) M short
    s.bits*s.sourceLanes≤h/2 ∧ s.bits*s.targetLanes≤h/2 := by
  have deg : r.placement.degree≤quota S.rounds := by
    rw [r.branch]
    exact (Nat.le_mul_of_pos_right D (Nat.two_pow_pos _)).trans rates.degree
  exact ⟨signed_key_at S p rates.height age r.valid.capacity deg small previous,
    (reached_key r rates p h hosts groups (2^oldCut) short age small).1⟩

end
end Hierarchy.DescentResetSignedTokens

end OAI
