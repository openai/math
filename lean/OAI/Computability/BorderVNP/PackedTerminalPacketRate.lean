import OAI.Computability.BorderVNP.PackedTerminalPacketCost
import OAI.Computability.BorderVNP.PackedTerminalShape
import OAI.Computability.BorderVNP.PackedTerminalProgramRate

/-! # Physical time of the shared terminal packet and routing emitter -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.SelectedSchedule

open Crossing Cover Cover.AddressCircuit BorderVNP.Epoch Packing Shortening Shortening.PublicCapacity Diagonal TeamScales Filter
open VPVNP.VerifierNetwork GeometryAdviceRate CellPacketGeometry CellPacketGeometry.LiveWords
open TerminalCells Diagonal.ExternalSew Diagonal.ExternalSew.FieldExport
open scoped Classical BorderVNP.Epoch.Cube

/-- A sparse scalar volume bounded per routing rectangle converts the complete
one-table terminal emitter's cubic cost into a single power of the physical
logarithmic word width. -/
theorem packet_cost_polynomial {R volume controls L h A K d : ℕ}
    (positive : 1≤h) (width : L ≤ K*h) (shape : volume+controls ≤ A*R*h^d) :
    (20000*R+250050*volume+controls)*(L+1)^3 ≤
      ((20000+250050*A)*(K+1)^3)*R*h^(d+3) := by
  have power : 1≤h^d := Nat.succ_le_of_lt (pow_pos positive d)
  have hr : R ≤ R*h^d := Nat.le_mul_of_pos_right _ power
  have linear : 20000*R+250050*volume+controls ≤ (20000+250050*A)*R*h^d := by
    calc
      _ ≤ 20000*(R*h^d)+250050*(volume+controls) := by
        have bound := Nat.mul_le_mul_left 20000 hr
        omega
      _ ≤ 20000*(R*h^d)+250050*(A*R*h^d) := Nat.add_le_add_left (Nat.mul_le_mul_left _ shape) _
      _ = _ := by ring
  have len : L+1 ≤ (K+1)*h := by rw [Nat.add_mul]; omega
  exact (Nat.mul_le_mul linear (Nat.pow_le_pow_left len 3)).trans_eq (by rw [pow_add]; ring)

/-- The three sort depths and the input-owner histogram fit the same physical
word once the actual public scalar volume fits. -/
theorem packet_depths {EPin IPin Orig : Type} [Fintype EPin] {s C L : ℕ}
    (T : Template EPin IPin Orig s C) (room : 4*T.publicVolume ≤ 2^L) :
    T.publicDepth≤L ∧ T.chunkDepth≤L ∧ T.recordDepth≤L ∧ Nat.clog 2 (s+C)≤L := by
  dsimp only [Template.publicDepth,Template.chunkDepth,Template.recordDepth]
  dsimp only [Template.publicVolume] at room
  exact ⟨Nat.clog_le_of_le_pow (by omega),Nat.clog_le_of_le_pow (by omega),
    Nat.clog_le_of_le_pow (by omega),Nat.clog_le_of_le_pow (by omega)⟩

variable {D m : ℕ} [NeZero D] {K : Type*} [Field K] {e : PaidIdentity K D m}
  (S : SiteSchedule e) {alpha xx : ℕ} (scale : EpochScales S alpha xx)

/-- The native geometry clock and its entire serialized table at the true
terminal grid shape. The remaining numerical inputs are the source-pin DAG
charge and the sparse packet scalar volume; the joint emitter's size, all row
references and the number of output bits are derived from the constructed frame. -/
theorem eventually_terminal_packet_program (degree : ℕ) :
    ∃ ω : ℝ, 0<ω ∧ ∀ H : ℝ, 0≤H → ∀ A : ℕ,
    ∀ᶠ n : ℕ in atTop, ∀ r : ℕ, 1≤r → (r:ℝ)≤2^((n:ℝ)^ω) →
    let start := CoverScale.initialDepth (Cube D) r n
    let tiles := CoverScale.sites (Cube D) start
    let epochsN := epochs scale.τ n
    let depth := EnrichedOuter.depth S start epochsN
    let shape := boundary S start epochsN
    let cells := CoverScale.sites (Cube D) depth
    let live := teams scale.α scale.τ (S.fanIn^S.rounds) n*tiles
    let originals := (S.fanIn^S.rounds)^epochsN*tiles
    let rows := routingRows shape cells originals live
    let L := (360*Fintype.card (Cube D)+60)*logWidth r n
    ∀ {X G Y Move EPin IPin Orig HistoryPins : Type} [Fintype HistoryPins] [Fintype X] [Fintype G] [Fintype Y] [Fintype Move] [Fintype EPin] [Fintype IPin]
      {reserve active b w ports v s k a pcells : ℕ}
      (hist : Frame (X ⊕ G) (Y ⊕ Unit)) (ord : G ≃ Fin active) (fits : active≤reserve) (input : X → Bool)
      (enum : Fin (Fintype.card (Cube D)) ≃ Cube D) (number : (Cube D → Deck (depth+1)) ≃ Fin cells)
      (cf : cells≤2^b) (p : Params) (_liveEq : (p.R+1)*p.sites = live) (vf : shape.sites≤2^w) (host width : Fin ports → ℕ)
      (name : ℕ → ℕ → ℕ) (hb : b≤w) (old : Fin originals → Fin shape.sites)
      (aux : Frame ((X ⊕ Fin reserve) ⊕ Y) (Fin shape.sites × Fin w))
      (read : RouteRows.Pins Move (Fintype.card (Cube D)) (depth+1) shape.sites shape.edges w → Y)
      (controls : Fin v → Fin (2^w)) (keep : Frame ((X ⊕ Fin reserve) ⊕ Y) HistoryPins) (T : Template EPin IPin Orig s pcells)
      (up : Frame ((Wires Move (Fintype.card (Cube D)) depth shape.sites shape.edges w b ⊕ Bool) ⊕ HistoryPins) (Base s k w EPin IPin))
      (anchors : Frame ((Wires Move (Fintype.card (Cube D)) depth shape.sites shape.edges w b ⊕ Bool) ⊕ HistoryPins) (Fin s × Fin a))
      (owner : Fin s → Fin pcells) (pin : Orig → T.Fields) (pad : s<2^a) (dest head : ℕ),
      1≤w → w≤60*logWidth r n → k≤L → a≤L →
      T.publicVolume+v ≤ A*rows*(logWidth r n)^degree →
      let shared := aux.size+keep.size+up.size+anchors.size
      ((hist.size+3*(reserve-active)+3+reserve+shared:ℕ):ℝ) ≤ H*r*(n:ℝ)^(92/100:ℝ) →
      let em := packetEmitter enum number cf p vf host width name hb old aux read controls keep T up anchors owner pin pad dest head
      let table := geometryTable hist ord fits em input
      let o := (shape.edges+p.slots)*3+
        (Packing.RoutingOutputs.count (shape.edges+p.slots) cells originals live+
          ((cells+(originals+cells))+(v+Total T.publicDepth T.chunkDepth)))
      ((ticks table.size reserve o w (60*logWidth r n)+GeometryAdviceRate.packetWords table.size reserve o w*(60*logWidth r n):ℕ):ℝ) <
        r*(n:ℝ)^(93/100:ℝ) := by
  let coeff := 360*Fintype.card (Cube D)+60
  obtain ⟨ω₁,hω₁,rate⟩ := eventually_terminal_program S scale (degree+3) 1
  obtain ⟨ω₂,hω₂,logSmall⟩ := exists_polylog_budget degree (by norm_num : (0:ℝ)<1)
  refine ⟨min ω₁ ω₂,lt_min hω₁ hω₂,fun H hH A => ?_⟩
  let B := (20000+250050*A)*(coeff+1)^3
  filter_upwards [rate H (B:ℝ) 60 hH (Nat.cast_nonneg _) (by norm_num),eventually_compiled_dimensions S scale,
    logSmall,eventually_ge_atTop 1,eventually_ge_atTop (4*A)] with n clock dims logs hn coefficient
  intro r hr bound start tiles epochsN depth shape cells live originals rows L X G Y Move EPin IPin Orig HistoryPins _ _ _ _ _ _ _
    reserve active b w ports v s k a pcells hist ord fits input enum number cf p liveEq vf host width name hb old aux read controls keep
    T up anchors owner pin pad dest head positive words wk wa mass shared sharedBound em table o
  obtain ⟨cfit,_,rowCap,key,sixty,logR,_⟩ := dims r hr
  have narrow (v : ℝ) (hv : min ω₁ ω₂ ≤ v) : (r:ℝ) ≤ 2^((n:ℝ)^v) :=
    bound.trans (Real.rpow_le_rpow_of_exponent_le (by norm_num)
      (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) hv))
  have logN : (logWidth r n)^degree ≤ n := by
    have logR := logs r hr (narrow ω₂ (min_le_right ..))
    rw [Real.rpow_one] at logR
    exact_mod_cast logR
  have nle : n≤r*n := Nat.le_mul_of_pos_left _ hr
  have polynomial := Nat.mul_le_mul (Nat.mul_le_mul (coefficient.trans nle) rowCap) (logN.trans nle)
  have limit : 4*T.publicVolume ≤ (r*n)^3 := by
    calc
      _ ≤ 4*(A*rows*(logWidth r n)^degree) := Nat.mul_le_mul_left _ ((Nat.le_add_right _ _).trans mass)
      _ = ((4*A)*rows)*(logWidth r n)^degree := by ring
      _ ≤ (r*n)*(r*n)*(r*n) := polynomial
      _ = _ := by ring
  have baseRoom : r*n≤2^(logWidth r n) := by
    rw [public_logWidth]
    exact (show r*n≤2*n*r by nlinarith only [Nat.zero_le (n*r)]).trans (Nat.le_pow_clog (by decide) _)
  have paddedRoom : 4*T.publicVolume ≤ 2^L := by
    have h₃ : (2^(logWidth r n))^3 = 2^(3*logWidth r n) := by rw [← pow_mul,Nat.mul_comm]
    exact limit.trans ((Nat.pow_le_pow_left baseRoom 3).trans (h₃.le.trans
      (Nat.pow_le_pow_right (by decide) (show 3*logWidth r n ≤ L by omega))))
  obtain ⟨wp,wd,wb,wh⟩ := packet_depths T paddedRoom
  have wr : w≤L := words.trans sixty
  have allocation : 1+Packing.CellAddressCircuit.count shape.sites (shape.edges+p.slots) ((p.R+1)*p.sites) cells+
      originals+(p.R+1)*p.sites ≤ rows := by
    have slot : p.slots = 4*live := by unfold Params.slots; rw [←liveEq]; ring
    rw [slot,liveEq]; rfl
  have actual := packetEmitter_size enum number cf p vf host width name hb old aux read controls keep T up anchors owner pin
    pad dest head allocation key ⟨hb.trans wr,wr,logR⟩ wk wa wp wd wb wh
  have charge := packet_cost_polynomial (GeometryAdviceRate.indexWidths hr hn).1
    (le_rfl : L≤coeff*logWidth r n) mass
  have total := actual.trans (Nat.add_le_add_left charge _)
  have boundEm : ((em.size+o*w:ℕ):ℝ) ≤ shared+(B:ℝ)*rows*(logWidth r n:ℝ)^(degree+3) := by
    have numerals : em.size+o*w ≤ shared+B*rows*(logWidth r n)^(degree+3) := by
      dsimp only [o]
      rw [←liveEq]
      exact total
    exact_mod_cast numerals
  have program := clock r hr (narrow ω₁ (min_le_left ..)) cells cfit (60*logWidth r n) shared hist ord fits em input positive
    (by norm_num) sharedBound
  specialize program (by
    simpa only [o,liveEq] using boundEm)
  simpa only [o,liveEq] using program

end PackedHistoryCircuit.Normalized.SelectedSchedule

end BorderVNP
end Computability
end OAI
