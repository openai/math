import OAI.Hierarchy.DescentMatcherRateNumbers
import OAI.Hierarchy.DescentPackedCensusRAM
import OAI.Hierarchy.DescentPackedPhase
import OAI.Hierarchy.DescentPackedMinimumHardware
import OAI.Hierarchy.DescentPackedPayloadBudget

namespace OAI
/-! # Bit-price and finite hardware of the whole native packed chooser -/

namespace Hierarchy.DescentPackedColony.Phase
open DescentColonies DescentSIMDLookup ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical
variable {k Δ : ℕ}

theorem bit_price (L : Shelves k Δ) (w H G b : ℕ) (wide : 2*unit k b≤w) :
    cost L w H G (lanes w (unit k b))*w≤factor k Δ*(w+H*w+4*H*G*unit k b) := by
  let a:=unit k b
  let M:=lanes w a
  let n:=H*chunks G M
  let A:=w+H*w+4*H*G*a
  have positive : 0<a := by dsimp [a,unit];omega
  have wr : w≤A := by dsimp [A];omega
  have nw : n*w≤A := (volume H G w a positive wide).trans (by dsimp [A];omega)
  have gather : (4+n*(2*(1+33*(2^k-1))+4))*w ≤ (8+2*(1+33*(2^k-1)))*A := by
    calc
      _ = 4*w+n*w*(2*(1+33*(2^k-1))+4) := by ring
      _ ≤ 4*A+A*(2*(1+33*(2^k-1))+4) := by gcongr
      _ = _ := by ring
  have first:=AllSeeds.bit_price L.layers w H G k a positive wide
  have second:=DescentPackedMinimum.bit_price L.split w a H G positive wide
  have fourth:=DescentPackedMinimum.bit_price L.color w a H G positive wide
  have last:=PackedWinnerRAM.bit_price_at k w L.paintTable L.output H G L.mu L.paint a L.panels positive wide
  simpa only [cost,PackedChoices.ticks,factor,A,n,M,a,Nat.add_mul] using
    Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add first second) gather) fourth) last

private theorem batch_ticks {n W h : ℕ} (f : Fin n→NativeBatch.Code W) (g : Fin n→NativeBatch.Code h)
    (same : ∀i,(f i).ticks=(g i).ticks) (t : ℕ) (ht:t≤n) :
    (NativeBatch.Code.seq f t ht).ticks=(NativeBatch.Code.seq g t ht).ticks := by
  induction t with
  | zero=>rfl
  | succ t ih=>exact congrArg₂ Nat.add (ih (by omega)) (same ⟨t,ht⟩)

theorem cost_width (L : Shelves k Δ) (W h H G M : ℕ) : cost L W H G M=cost L h H G M := by
  have start:=batch_ticks (fun i=>AllSeeds.trial W H G M k (L.layers i))
    (fun i=>AllSeeds.trial h H G M k (L.layers i)) (fun _=>rfl) (2^k-1) le_rfl
  have last:=batch_ticks (PackedWinnerRAM.step (k:=k) W L.paintTable L.output (H*chunks G M) M L.mu L.paint L.panels)
    (PackedWinnerRAM.step (k:=k) h L.paintTable L.output (H*chunks G M) M L.mu L.paint L.panels) (fun _=>rfl) (2^k) le_rfl
  let gather := 4 + H*chunks G M*(2*(1+33*(2^k-1))+4)
  exact congrArg₂ (fun trials winner =>
    trials + PackedChoices.ticks L.split H G M + gather + PackedChoices.ticks L.color H G M + winner)
    start last

theorem payload_price (L : Shelves k Δ) (W h H G b K : ℕ) (wide : 2*unit k b≤h) (hardware : W≤K*h) :
    cost L W H G (lanes h (unit k b))*W≤K*(factor k Δ*(h+H*h+4*H*G*unit k b)) := by
  apply DescentPackedPayloadBudget.clock hardware
  rw [cost_width L W h]
  exact bit_price L h H G b wide

theorem storage (L : Shelves k Δ) (w H G M : ℕ) (live : 0<H*chunks G M) :
    CandidateRAM.Bounded (program L w H G M) (cost L w H G M) := by
  have third := CandidateRAM.scan_bound w L.selected (H*chunks G M) L.field live
  have work : L.field.work=1+33*(2^k-1) := chosen_work L.mu L.panels L.amount L.zip
  rw [work] at third
  exact CandidateRAM.seq_bound (CandidateRAM.seq_bound (CandidateRAM.seq_bound (CandidateRAM.seq_bound
    (AllSeeds.storage L.layers w H G M k live) (DescentPackedMinimum.search_hardware L.split w H G M)) third)
    (DescentPackedMinimum.search_hardware L.color w H G M))
    (PackedWinnerRAM.storage k w L.paintTable L.output H G M L.mu L.paint L.panels live)

private theorem batch_cheap {N w : ℕ} (steps : Fin N→NativeBatch.Code w)
    (each : ∀i,CheapCode (steps i).text) (n : ℕ) (hn : n≤N) :
    CheapCode (NativeBatch.Code.seq steps n hn).text := by
  induction n with
  | zero=>exact @ProtocolRAM.program_cheap w []
  | succ n ih=>
    have before : n≤N := Nat.le_of_lt hn
    change CheapCode ((NativeBatch.Code.seq steps n before).text.seq (steps ⟨n,hn⟩).text)
    exact @cheap_seq w (NativeBatch.Code.seq steps n before).text (steps ⟨n,hn⟩).text (@ih before) (@each ⟨n,hn⟩)

theorem cheap (L : Shelves k Δ) (w H G M : ℕ) : CheapCode (program L w H G M) := by
  let rows := H*chunks G M
  let trials := AllSeeds.search w H G M k L.layers
  let split := DescentPackedMinimum.search L.split w H G M
  let gather := scan w L.selected rows L.field
  let color := DescentPackedMinimum.search L.color w H G M
  let output := PackedWinnerRAM.program k w L.paintTable L.output H G M L.mu L.paint L.panels
  have first : CheapCode trials.text :=
    batch_cheap (fun i=>AllSeeds.trial w H G M k (L.layers i))
      (fun i=>@ProtocolRAM.program_cheap w (passes (L.layers i) H G M k)) (2^k-1) le_rfl
  have last : CheapCode output.text :=
    batch_cheap (PackedWinnerRAM.step (k:=k) w L.paintTable L.output rows M L.mu L.paint L.panels)
      (fun x=>@scan_cheap w (PackedWinnerRAM.slot L.output rows x) rows
        (PackedWinnerRAM.term L.paintTable M L.mu L.paint L.panels x)) (2^k) le_rfl
  change CheapCode ((((trials.text.seq split).seq gather).seq color).seq output.text)
  refine @cheap_seq w (((trials.text.seq split).seq gather).seq color) output.text ?_ @last
  refine @cheap_seq w ((trials.text.seq split).seq gather) color ?_
    (DescentPackedMinimum.search_hardware L.color w H G M).cheap
  refine @cheap_seq w (trials.text.seq split) gather ?_ (@scan_cheap w L.selected rows L.field)
  exact @cheap_seq w trials.text split @first (DescentPackedMinimum.search_hardware L.split w H G M).cheap

theorem output_lanes (k b w : ℕ) : (k+3)*lanes w (unit k b)≤w := by
  calc
    _ ≤ unit k b*lanes w (unit k b) := Nat.mul_le_mul_right _ (Nat.le_add_left _ _)
    _ = lanes w (unit k b)*unit k b := Nat.mul_comm _ _
    _ ≤ w := (lanes_fit w (unit k b)).trans (Nat.div_le_self w 2)

end Hierarchy.DescentPackedColony.Phase

namespace Hierarchy.DescentSixParty.PackedCensus
open DescentColonies DescentSIMDLookup

theorem histograms_storage (first second : Banks) (lo hi H J M w : ℕ) (live : 0<H*chunks J M) :
    CandidateRAM.Bounded (histograms first second lo hi H J M w) (clocks first second H J M) :=
  CandidateRAM.seq_bound (CandidateRAM.scan_bound w lo (H*chunks J M) (DescentSIMDLookup.lookup first) live)
    (CandidateRAM.scan_bound w hi (H*chunks J M) (DescentSIMDLookup.lookup second) live)

open ProtocolRAM
theorem histograms_cheap (first second : Banks) (lo hi H J M w : ℕ) :
    CheapCode (histograms first second lo hi H J M w) := by
  let a := scan w lo (H*chunks J M) (DescentSIMDLookup.lookup first)
  let b := scan w hi (H*chunks J M) (DescentSIMDLookup.lookup second)
  change CheapCode (a.seq b)
  exact @cheap_seq w a b
    (@scan_cheap w lo (H*chunks J M) (DescentSIMDLookup.lookup first))
    (@scan_cheap w hi (H*chunks J M) (DescentSIMDLookup.lookup second))

end Hierarchy.DescentSixParty.PackedCensus

end OAI
