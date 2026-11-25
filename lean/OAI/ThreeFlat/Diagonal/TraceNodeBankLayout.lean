import OAI.ThreeFlat.Diagonal.PhysicalNodeBankLayout

namespace OAI
/-! # Fixed machine addresses of the compact trace-node publisher -/

namespace ThreeFlat.Diagonal.NavigationPass.NodePublication

open RAM.NavigationNodeRows

def traceBase (w : ℕ) := 16*2^(32*w)
def traceUnit (w : ℕ) := (2^w)^4
def traceLimit (w : ℕ) := traceBase w+2^(16*w)
def compactControl (w : ℕ) := traceBase w+7*traceUnit w
def compactHead (w : ℕ) := compactControl w+1

/-- The compact publisher keeps its pointer, thirteen arguments and two loop counters
adjacent, followed by three supplied array bases. -/
def spacedArchive (ctrl header charges nodes lanes perLane pairs trace tariff cc hc mc : ℕ) : NodeArchive :=
  {banks := ⟨ctrl+14,charges,nodes,lanes,perLane,pairs,trace,tariff⟩
   headerBase := header
   rawHeader := header
   phase := ctrl
   counter := ctrl+15
   childCap := cc
   halfCap := hc
   motifCap := mc}

def traceArchive (w lanes perLane pairs trace tariff cc hc mc : ℕ) : NodeArchive :=
  spacedArchive (compactControl w) (traceBase w+8*traceUnit w) (traceBase w+12*traceUnit w)
    (traceBase w+16*traceUnit w) lanes perLane pairs trace tariff cc hc mc

/-- Space for one protected prefix, the compact header, both charge columns and the eight node fields. -/
structure BankSpace (W ctrl header charges nodes limit unit : ℕ) : Prop where
  minUnit : 16≤unit
  controls : ctrl+16≤header
  headerRoom : header+unit≤charges
  chargeRoom : charges+unit≤nodes
  nodeRoom : nodes+unit≤limit
  top : limit<2^W

theorem trace_sector {w : ℕ} (hw : 1≤w) :
    16≤traceUnit w ∧ traceBase w+32*traceUnit w≤traceLimit w ∧ traceLimit w<2^(64*w) := by
  have small : 2^4≤2^(w*4) := Nat.pow_le_pow_right (by decide) (by omega)
  have sub : 32*traceUnit w≤2^(16*w) := calc
    _ = 2^(5+w*4) := by
      change 2^5*(2^w)^4=2^(5+w*4)
      simp only [pow_add,pow_mul]
    _ ≤ _ := Nat.pow_le_pow_right (by decide) (by omega)
  have high : 2^(16*w)≤2^(32*w) := Nat.pow_le_pow_right (by decide) (by omega)
  have room : 17*2^(32*w)<2^(64*w) := calc
    _ ≤ 2^5*2^(32*w) := Nat.mul_le_mul_right _ (by decide)
    _ = _ := (pow_add ..).symm
    _ < _ := Nat.pow_lt_pow_right (by decide) (by omega)
  have small16 : 16≤2^(w*4) := (show 16=2^4 by decide).le.trans small
  refine ⟨by simpa only [traceUnit,←pow_mul] using small16,Nat.add_le_add_left sub _,?_⟩
  unfold traceLimit traceBase
  omega

end ThreeFlat.Diagonal.NavigationPass.NodePublication

end OAI
