import OAI.Hierarchy.ProbeStripMenu
import OAI.Hierarchy.ProbePacketRate
import OAI.Hierarchy.ProbeQuotePrecision
import OAI.Hierarchy.ProtocolRAMActiveRate

namespace OAI
/-! # Joint read-only rates of the payload and bought finite packet menus -/

namespace Hierarchy.ProtocolRAM
open LinearAlgebra.SpectralBooks.ChordGraph AdaptiveProbe
open scoped BigOperators Classical
noncomputable section
universe u

/-- Numerical data read from the actual finite packet catalogue, before choosing
an input, a native time, a width, or a failed local site. -/
structure PacketWidths (J : Type*) where
  width : J→ℕ
  selector : J→ℕ
  entries : J→ℕ
  ports : ℕ
  demands : ℕ
  rate : J→ℕ
  margin : ℝ
  margin_pos : 0 < margin

namespace PacketWidths
variable {J K : Type*} [Fintype J] [Fintype K]

def ofMenu {F E A : Type*} [Field F] [Fintype E] [Nonempty E] [Fintype A]
    {s : ℕ} [Nonempty (Fin s)] {edge : E→Chord s} {req : A→E}
    {box : Set (E→ℝ)} {ε tree : ℝ} {minimum : ℕ} (m : Probe.FixedMenu F edge req box ε tree minimum) :
    PacketWidths m.index where
  width j := (m.packet j).width
  selector j := (m.packet j).terms
  entries j := (Finset.univ.sup fun v : Fin (m.packet j).terms × E=>(m.packet j).count v.1 v.2) +
    (m.packet j).width*Fintype.card A
  ports := Fintype.card E
  demands := Fintype.card A
  rate j := packetRate (m.packet j)
  margin := m.margin
  margin_pos := m.positive

/-- The common native row width and common cash margin cover both the payload
and purchased formats, despite their different request types and alphabet sizes. -/
def either (payload : PacketWidths J) (purchase : PacketWidths K) : PacketWidths (J⊕K) where
  width := Sum.elim payload.width purchase.width
  selector := Sum.elim payload.selector purchase.selector
  entries := Sum.elim payload.entries purchase.entries
  ports := max payload.ports purchase.ports
  demands := max payload.demands purchase.demands
  rate := Sum.elim payload.rate purchase.rate
  margin := min payload.margin purchase.margin
  margin_pos := lt_min payload.margin_pos purchase.margin_pos

/-- All constants precede the actual coordinate index, its cardinality, the input
length and the physical inventory tape. The outputs pay positive-demand stock,
all quote rounding and the signed quadratic remainder on the same copied batch. -/
theorem native_rates (menu : PacketWidths J) (lanes : ℕ) {a s₀ ρ ε L : ℝ}
    (ha : 0<a) (hs : 0<s₀) (hρ : 0<ρ) (hε : 0<ε) (hL : 0≤L) :
    ∃ Q K₀ : ℕ, 0<Q ∧ 8*lanes≤Q ∧ 1/(Q:ℝ)+1/(Q:ℝ)≤ε ∧
      (∀j, 0 < menu.width j → (menu.ports : ℝ) * ((Finset.univ.sup menu.entries : ℕ) : ℝ) * (1/(Q:ℝ)) ≤ (menu.width j : ℝ)*menu.margin/2) ∧ 0<K₀ ∧ ∀K≥K₀,∀ time≥s₀,
      (menu.demands:ℝ)/K≤time*a*menu.margin ∧
      ∀ (I : Type u) [Fintype I] (rows edges n bits : ℕ) (T : SelectedRows.Tape rows edges I),
        0<bits → (Fintype.card I:ℝ)≤L*n →
        (∀ i,(Finset.univ.filter fun e=>T.activeKind e=some i).card≤1) →
        (∀ e,∃ j: J,K*(T.put (T.use e)+T.take (T.use e))≤bits*menu.rate j) →
        (∑i,(stockChange T.kind (netUnits bits T.put T.take) i)^2/(4*time*a)) ≤
          (n:ℝ)*ρ*menu.margin/(8*(K*commonWidth menu.width:ℕ)) := by
  let rate := Finset.univ.sup menu.rate
  let entries := Finset.univ.sup menu.entries
  obtain ⟨Q,positive,lanesFit,accurate,coins⟩ := quote_precision menu.ports entries lanes hε menu.margin_pos
  obtain ⟨K₀,Kpos,all⟩ := uniform_packet_rate (B:=commonWidth menu.width) (multiplicity:=menu.demands)
    (C:=(rate:ℝ)) ha hs hρ menu.margin_pos (Nat.cast_nonneg _) hL (by unfold commonWidth; omega)
  refine ⟨Q,K₀,positive,lanesFit,accurate,?_,Kpos,?_⟩
  · intro j pos
    exact coins menu.ports entries (menu.width j) le_rfl le_rfl pos
  · intro K large time hot
    obtain ⟨stock,cost⟩ := all K large time hot
    refine ⟨stock,?_⟩
    intro I _ rows edges n bits T hw size deg localRate
    apply cost I n _ size
    intro i
    have limited (e) : K*(T.put (T.use e)+T.take (T.use e))≤bits*rate := by
      obtain ⟨j,bound⟩ := localRate e
      exact bound.trans (Nat.mul_le_mul_left _ (Finset.le_sup (Finset.mem_univ j)))
    simpa using T.abs_delta K bits rate 1 (Kpos.trans_le large) hw deg limited i

end PacketWidths
end
end Hierarchy.ProtocolRAM

end OAI
