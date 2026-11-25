import OAI.Computability.BorderVNP.TeamSiteProcessorRoles
import OAI.Computability.BorderVNP.TeamSiteBudget
import OAI.Computability.BorderVNP.TeamSiteProcessorSort
import OAI.Computability.BorderVNP.TeamLocalClockStartupExact

/-! # Clock for an entire physical team processor

The bound includes reading the raw input, emitting time-zero records, loading the
public words, extracting the handoffs, executing the signed instruction block,
checking its endpoint, closing the shared buffer, and verifying both sorting lanes.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamSite.Processor.Budget

open Filter TeamTapeSorting

/-- Upper bound from the real input parser and time-zero emitter. The sorter uses words
one bit wider than the ISA so the two phases of the last address fit. -/
def inputCost (n w capacity dataLength : ℕ) : ℕ :=
  46*n+19 + (3*(w+1)+9*Nat.clog 2 (n+1)+7*capacity+4) +
    (10*(w+1)+20*capacity+13+TeamTapeInputEmit.budget (w+1) dataLength)

/-- Exact startup instruction count after time-zero emission and before frame decoding. -/
def prefixCost (r k w : ℕ) (last : Bool) : ℕ :=
  ((5*(w+1)+2+2) + ((k+8)*(6*w+2)+1)) +
    ((r+2)*(5*w+2)+1) + roleTime last (Layout.frameSize r w)

/-- Physical clock envelope for either a live block or a propagated halt, including
the final transition from an accepted endpoint to buffer closure. -/
def endpoint (r w body : ℕ) : ℕ :=
  TeamLocalClock.Startup.budget r w + 1 + body + (7*r+45)*(w+1) + 1

/-- Exact closure cost for the shared record buffer. -/
def close (w capacity rowCount : ℕ) : ℕ :=
  (4*capacity-rowCount)*(25*(w+1)+12)+1+(2*(4*capacity*5*(w+1))+1)

/-- Both sorting lanes of the real owner, with their actual routing-table startup. -/
def sort (n d e w : ℕ) : ℕ :=
  600*(n+1)^2+2*siteBudget d e (w+1)+1

/-- The whole processor path, including the sorter fuel needed after the last
deterministic transition. -/
def total (r k n d e w dataLength body rowCount : ℕ) (last : Bool) : ℕ :=
  inputCost n w (2^e) dataLength + prefixCost r k w last + endpoint r w body +
    close w (2^e) rowCount + sort n d e w

/-- All phases fit below the chosen elementary clock, uniformly in the site, its
handoff contents, the number of emitted records, and the chosen RAM path. -/
theorem total_le {r k n d e w dataLength body : ℕ} (rowCount : ℕ) (last : Bool)
    (hn : 4000010 ≤ n) (hr : r+2 ≤ n) (hk : k+8 ≤ n) (hw : w+1 ≤ n) (hB : 2^e ≤ n)
    (hd : 2+e+d ≤ n) (hdata : dataLength ≤ n) (hbody : body ≤ n^28) :
    total r k n d e w dataLength body rowCount last ≤ n^29 := by
  have pos : 1 ≤ n := by omega
  have lin : n ≤ n^2 := Nat.le_self_pow (by decide) n
  have one : 1 ≤ n^2 := pos.trans lin
  have log : Nat.clog 2 (n+1) ≤ n := Nat.clog_le_of_le_pow (Nat.lt_two_pow_self (n := n))
  have init : inputCost n w (2^e) dataLength ≤ 400*n^2 := by
    calc
      _ ≤ 46*n+19+(3*n+9*n+7*n+4)+(10*n+20*n+13+(n*(138*n+60)+1)) := by
        unfold inputCost TeamTapeInputEmit.budget; gcongr
      _ ≤ _ := by nlinarith
  have width : w ≤ n := by omega
  have role : roleTime last (Layout.frameSize r w) ≤ 30*n^2 := by
    have size : Layout.frameSize r w ≤ 1+n*n :=
      Nat.add_le_add_left (Nat.mul_le_mul hr width) 1
    cases last <;> simp only [roleTime, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] <;> nlinarith
  have front : prefixCost r k w last ≤ 60*n^2 := by
    calc
      _ ≤ ((5*n+2+2)+(n*(6*n+2)+1))+(n*(5*n+2)+1)+30*n^2 := by
        unfold prefixCost; gcongr
      _ ≤ _ := by nlinarith
  have cube : n^2 ≤ n^3 := Nat.pow_le_pow_right pos (by decide)
  have bound : endpoint r w body ≤ n^28+262*n^3 := by
    have reg : 8*r+200 ≤ 208*n := by omega
    have finish : 7*r+45 ≤ 52*n := by omega
    calc
      _ ≤ 208*n*n^2+1+n^28+52*n*n+1 := by
        unfold endpoint TeamLocalClock.Startup.budget; gcongr
      _ ≤ _ := by nlinarith
  have closed : close w (2^e) rowCount ≤ 190*n^2 := by
    have slots : 4*2^e-rowCount ≤ 4*n := (Nat.sub_le ..).trans (Nat.mul_le_mul_left 4 hB)
    calc
      _ ≤ 4*n*(25*n+12)+1+(2*(4*n*5*n)+1) := by unfold close; gcongr
      _ ≤ _ := by nlinarith
  have sorter := TeamTapeSorting.siteBudget_le hn (hB.trans (by omega)) hd hw
  have add : (n+1)^2 ≤ 4*n^2 := by nlinarith
  have sorted : sort n d e w ≤ 2400*n^2+2*n^8+1 := by unfold sort; omega
  have p2 : n^2 ≤ n^28 := Nat.pow_le_pow_right pos (by decide)
  have p3 : n^3 ≤ n^28 := Nat.pow_le_pow_right pos (by decide)
  have p8 : n^8 ≤ n^28 := Nat.pow_le_pow_right pos (by decide)
  calc
    _ ≤ 4000*n^28 := by unfold total; omega
    _ ≤ n*n^28 := Nat.mul_le_mul_right _ (by omega)
    _ = _ := by ring

/-- The fixed source and register table determine the threshold. The same threshold
covers all processor counts, choices and inputs satisfying the geometry bounds. -/
theorem eventually_clock (r k : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ {d e w dataLength body : ℕ} (rowCount : ℕ) (last : Bool),
      w+1 ≤ n → 2^e ≤ n → 2+e+d ≤ n → dataLength ≤ n → body ≤ n^28 →
      total r k n d e w dataLength body rowCount last ≤ n^36 := by
  filter_upwards [eventually_ge_atTop 4000010, eventually_ge_atTop (r+2),
    eventually_ge_atTop (k+8)] with n hn hr hk
  intro d e w dataLength body rowCount last hw hB hd hdata hbody
  exact (total_le rowCount last hn hr hk hw hB hd hdata hbody).trans
    (Nat.pow_le_pow_right (by omega) (by decide))


/-- The source's native private-machine clock and the block's logical tick charge
already suffice for the whole processor. There is one threshold for every word
width, processor index, record count and native path of the fixed table. -/
theorem eventually_chunk_clock (r k m g : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ {d e w dataLength fuel : ℕ} (es : List (TeamRAM.Event w))
      (rowCount : ℕ) (last : Bool), w+1 ≤ n → 2^e ≤ n → 2+e+d ≤ n → dataLength ≤ n →
      fuel ≤ n^25+1 → TeamTapeHandoff.cost es ≤ n →
      total r k n d e w dataLength (Work.chunkBudget w m g fuel es + Work.closeBudget w)
        rowCount last ≤ n^36 := by
  filter_upwards [eventually_clock r k, Work.eventually_chunk_budget m g, eventually_ge_atTop 1]
    with n full chunk pos
  intro d e w dataLength fuel es rowCount last hw hB hd hdata hf charge
  exact full rowCount last hw hB hd hdata
    ((chunk es (by omega) hf charge).trans (Nat.pow_le_pow_right pos (by decide)))

/-- Subtracting the steps actually taken before the sorter leaves its full required
fuel. This includes the transition into record closure. -/
theorem sorter_fuel {r k n d e w dataLength body rowCount elapsed clock : ℕ} {last : Bool}
    (fits : total r k n d e w dataLength body rowCount last ≤ clock)
    (spent : elapsed ≤ inputCost n w (2^e) dataLength + prefixCost r k w last +
      endpoint r w body + close w (2^e) rowCount) :
    sort n d e w ≤ clock-elapsed := by
  unfold total at fits
  omega

end TeamSite.Processor.Budget

end BorderVNP
end Computability
end OAI
