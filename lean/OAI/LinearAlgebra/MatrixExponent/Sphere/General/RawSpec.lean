import OAI.LinearAlgebra.MatrixExponent.Sphere.General.Weight
import OAI.LinearAlgebra.MatrixExponent.Sphere.Proof.ControllerSize
import OAI.LinearAlgebra.MatrixExponent.Sphere.Copy.Overlay
import OAI.LinearAlgebra.MatrixExponent.Sphere.Price.Allowance
import OAI.LinearAlgebra.MatrixExponent.Sphere.General.Scales
import OAI.LinearAlgebra.MatrixExponent.Sphere.Surface.Cardinality
import OAI.LinearAlgebra.MatrixExponent.Sphere.Verifier.Caps
import OAI.LinearAlgebra.MatrixExponent.Sphere.General.Ballot

/-!
# Uniform bounds for an ordered input over a polynomial-size field

The field-size lower bound is fixed first. The controller constants
can depend on the exponent in the upper bound on the field order.
They do not depend on the number of cells or the input label length.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Input
open Assembly Coloring Routing.Private Sphere SphereScale Surface Surface.Local
open scoped Classical

theorem binaryDigits (T c : ℕ) :
    let f := (c + 1) * Nat.clog 2 (T + 1)
    T ≤ 2 ^ f ∧ (T + 1) ^ c ≤ 2 ^ f := by
  have h := Nat.le_pow_clog (by decide : 1 < 2) (T + 1)
  have hg : (T + 1) ^ (c + 1) ≤ 2 ^ ((c + 1) * Nat.clog 2 (T + 1)) := by
    rw [pow_mul']
    exact Nat.pow_le_pow_left h _
  exact ⟨(Nat.le_succ T).trans ((Nat.le_self_pow (by omega) _).trans hg),
    (Nat.pow_le_pow_right (by omega) (by omega)).trans hg⟩

theorem labelWidths (J R c a N v : ℕ) (hv : v ≤ R * (1 + a + N)) :
    let B := 2 * (J + 1) * (R + c + 2)
    J * (1 + (c + 1) * N) ≤ B * (1 + N) ∧ 2 * J * (1 + v + (c + 1) * N) ≤ B * (1 + a + N) := by
  have h₁ : 1 + (c + 1) * N ≤ (R + c + 2) * (1 + N) := by ring_nf; omega
  have h₂ : 1 + v + (c + 1) * N ≤ (R + c + 2) * (1 + a + N) := by ring_nf at hv ⊢; omega
  have h₃ : J ≤ 2 * (J + 1) := by omega
  have h₄ : 2 * J ≤ 2 * (J + 1) := by omega
  exact ⟨(Nat.mul_le_mul h₃ h₁).trans_eq (mul_assoc ..).symm, (Nat.mul_le_mul h₄ h₂).trans_eq (mul_assoc ..).symm⟩

theorem bounded_parameters (g ℓ D n p l b : ℕ) (hD : 2 * budget g ≤ D) (hd : D = 2 ^ n) :
    ∃ K₀ : ℕ, ∀ c : ℕ, ∃ J B : ℕ, 0 < B ∧ J ≤ B ∧
      ∀ {T d : ℕ}, Scales g ℓ D T (p ^ l) b d →
      ∀ (F K : Type) [Field F] [Fintype F] [Field K] [Algebra K F] [ExpChar F p],
      (ready : Ready K ℓ D g (p ^ l) b d) →
      K₀ * (1 + T) ^ K₀ ≤ Fintype.card F → Fintype.card F ≤ (T + 1) ^ c →
      D ^ (terminalExponent g ℓ) ≤ T →
      ∀ {a e : ℕ} (m h : ℕ) (read : BundleReader F a e), e ≤ inputBits g D →
        let S := bundleScheme read m h g D T
        let k := selectorBits K₀ D (room ℓ D g) T (Nat.card F)
        let u := T / D ^ (terminalExponent g ℓ)
        let f := (c + 1) * Nat.clog 2 (T + 1)
        ∃ (hF : room ℓ D g * (2 * depth ℓ D g (p ^ l) (d * b) + 1) < Fintype.card F)
          (r t : ℕ) (U : LocalPrinter S g ℓ D b d p l k r t n u f),
          ControllerBounds S U T J ∧
          J * (1 + f) ≤ B * (1 + Nat.clog 2 (T + 1)) ∧
          2 * J * (1 + S.ℓ + f) ≤ B * (1 + a + Nat.clog 2 (T + 1)) ∧
          ∀ {x y : Wire} {W : ℝ} (P : Input F x y h D T (d * b) g W)
            (v : P.Seating m) (o : BundleOrder P.diagram read), Nonempty P.V →
              (v.ordered o).ReadyPanel (v.next o) ready hF (mobility a e g D T) k U v.tape.2 (v.pres o) ∧
                ReadyPanel.NoExtras (S := S) (v.next o) v.tape.2 := by
  obtain ⟨K₀, go⟩ := ordered_parameters g ℓ D p l b hD
  refine ⟨K₀, fun c => ?_⟩
  let J := controllerBound g ℓ D n K₀ (channelBits g) (stationBits D)
  let B := 2 * (J + 1) * (rowFactor g D + c + 2)
  refine ⟨J, B, by unfold B; positivity, ?_, ?_⟩
  · exact (show J ≤ 2 * (J + 1) by omega).trans (Nat.le_mul_of_pos_right _ (by positivity))
  intro T d sc F K _ _ _ _ _ ready low high ht a e m h read he S k u f
  obtain ⟨ha, hb⟩ := binaryDigits T c
  obtain ⟨hf, r, t, U, hc, hr⟩ := go sc F K ready low (high.trans hb) hd ht m h read
  have hk := selector_width K₀ D (room ℓ D g) T (Nat.card F) f ha
    (Nat.card_eq_fintype_card.trans_le (high.trans hb))
  obtain ⟨h₁, h₂⟩ := labelWidths J (rowFactor g D) c a _ _ (bundleBits read m h g D T he)
  exact ⟨hf, r, t, U, controller_bounds S U hc hk ha, h₁, h₂,
    fun P v o alive => ⟨hr P v o alive, v.moving⟩⟩

end OAI.LinearAlgebra.MatrixExponent.Rounds.Input
end

/-!
# Ordered local concentration

For a fixed input dictionary the output printer is chosen before
the diagram, its exterior wire types, host placement, or any of
the local selectors. All contributions are exact field elements.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Input
open Assembly Filter Coloring Routing.Private Sphere SphereScale Surface Surface.Local
open scoped Classical

section

variable {F K : Type} [Field F] [Fintype F] [Field K] [Algebra K F]
    {x y : Wire} {g ℓ D T b d p l k r t n u f : ℕ} [ExpChar F p] {W : ℝ}
    {S : Scheme F} {P : Input F x y S.h D T (d * b) g W} {z : S.format.obj}
    {A : P.HostChart S z} {hK : Ready K ℓ D g (p ^ l) b d}
    {hF : room ℓ D g * (2 * depth ℓ D g (p ^ l) (d * b) + 1) < Fintype.card F}
    {mobility : B S.ℓ → B S.k → Bool} {U : LocalPrinter S g ℓ D b d p l k r t n u f}
    {status : (Print.Children.Header S.m S.d).obj} {pres : S.Presentation z P.diagram}

variable (hr : P.ReadyPanel A hK hF mobility k U status pres) (sc : Scales g ℓ D T (p ^ l) b d)

variable {D' T' R' : ℕ} {W' : ℝ}

def ReadyPanel.Represents (Q : Input F x y S.h D' T' R' g W') (C ℓ' : ℕ) : Prop :=
  (∀ i j, Q.diagram.eval i j = ∑ c : hr.Paths sc, (hr.summand sc c).diagram.eval i j) ∧
  ∀ c : hr.Paths sc, Concentrated Q (hr.summand sc c) C n ℓ'

theorem ReadyPanel.represents {Q : Input F x y S.h D' T' R' g W'} {C ℓ' : ℕ}
    (he : P.diagram.eval = Q.diagram.eval)
    (hc : ∀ X : LocalTerm F x y S.h u, Concentrated P X (ReadyPanel.exponent g ℓ) n ℓ →
      Concentrated Q X C n ℓ') :
    hr.Represents sc Q C ℓ' :=
  ⟨fun i j => (congrFun (congrFun he.symm i) j).trans (hr.exact_sum sc i j),
    fun t => hc _ (hr.bounded sc t)⟩

end

variable {K F : Type} [Field K] [Field F] [Algebra K F] [Fintype F]
  {g ℓ D T p l b d : ℕ} [ExpChar F p]

/-- The printer supplies one dictionary for all diagrams using
these dimensions and the given table decoder. -/
def OrderedFamily (sc : Scales g ℓ D T (p ^ l) b d) (hc : Ready K ℓ D g (p ^ l) b d)
    (n K₀ c B : ℕ) : Prop :=
  ∀ {a e : ℕ} (m h : ℕ) (read : BundleReader F a e), e ≤ inputBits g D →
    let S := bundleScheme read m h g D T
    let k := selectorBits K₀ D (room ℓ D g) T (Nat.card F)
    let u := T / D ^ (terminalExponent g ℓ)
    let f := (c + 1) * Nat.clog 2 (T + 1)
    ∃ (hF : room ℓ D g * (2 * depth ℓ D g (p ^ l) (d * b) + 1) < Fintype.card F)
      (r t : ℕ) (U : LocalPrinter S g ℓ D b d p l k r t n u f),
      ∀ {x y : Wire} {W : ℝ} (P : Input F x y h D T (d * b) g W) (o : BundleOrder P.diagram read),
        Fintype.card P.V ≤ 2 ^ m →
        (IsEmpty P.V ∧ LocalExpansion P u (ReadyPanel.exponent g ℓ) n ℓ B) ∨
        ∃ (v : P.Seating m) (hr : (v.ordered o).ReadyPanel (v.next o) hc hF (mobility a e g D T) k U
          v.tape.2 (v.pres o)),
          hr.Bookkeeping sc B a ∧ hr.Represents sc P (ReadyPanel.exponent g ℓ) ℓ

private theorem allHosts (g ℓ D n p l b : ℕ) (large : 2 * budget g ≤ D) (dyad : D = 2 ^ n) :
    ∃ K₀ : ℕ, ∀ c : ℕ, ∃ B : ℕ, 0 < B ∧
      ∀ {T d : ℕ} (sc : Scales g ℓ D T (p ^ l) b d)
        (F K : Type) [Field F] [Fintype F] [Field K] [Algebra K F] [ExpChar F p]
        (hc : Ready K ℓ D g (p ^ l) b d),
        K₀ * (1 + T) ^ K₀ ≤ Fintype.card F → Fintype.card F ≤ (T + 1) ^ c →
        D ^ (terminalExponent g ℓ) ≤ T → OrderedFamily (F := F) sc hc n K₀ c B := by
  obtain ⟨K₀, h₀⟩ := bounded_parameters g ℓ D n p l b large dyad
  refine ⟨K₀, fun c => ?_⟩
  obtain ⟨J, B, hB, hJ, hp⟩ := h₀ c
  refine ⟨B, hB, ?_⟩
  intro T d sc F K _ _ _ _ _ hc low high hT a e m h read he S j u f
  obtain ⟨hf, r, t, U, limits, hw, hl, hr⟩ := hp sc F K hc low high hT m h read he
  refine ⟨hf, r, t, U, ?_⟩
  intro x y W P o bound
  cases isEmpty_or_nonempty P.V with
  | inl h =>
    let _ := h
    exact .inl ⟨h, P.emptyExpansion ..⟩
  | inr h =>
    obtain ⟨v⟩ := P.seating bound
    obtain ⟨hv, hx⟩ := hr P v o h
    exact .inr ⟨v, hv, hv.complete sc hx limits hJ hw hl,
      hv.represents sc (v.eval o) (fun _ h => v.return_concentrated o h)⟩

theorem ordered_bookkeeping (k : Type) [Field k] [Finite k] (sync : Prices.SharedPrice (AlgebraicClosure k))
    (g ℓ D n : ℕ) (large : 2 * budget g ≤ D) (dyad : D = 2 ^ n) :
    ∃ (K : Type) (_ : Field K) (_ : Fintype K) (_ : Algebra k K)
      (p l b : ℕ) (_ : CharP K p) (_ : Fact p.Prime) (K₀ : ℕ),
      ∀ c : ℕ, ∃ B : ℕ, 0 < B ∧ ∀ᶠ T : ℕ in atTop,
        ∃ (d : ℕ) (sc : Scales g ℓ D T (p ^ l) b d) (hc : Ready K ℓ D g (p ^ l) b d),
          D ^ terminalExponent g ℓ ≤ T ∧
          ∀ (F : Type) [Field F] [Fintype F] [Algebra K F],
            K₀ * (1 + T) ^ K₀ ≤ Fintype.card F → Fintype.card F ≤ (T + 1) ^ c →
            ∃ _ : ExpChar F p, OrderedFamily (F := F) sc hc n K₀ c B := by
  obtain ⟨K, _, _, _, p, l, b, _, _, go⟩ := SphereScale.choose (ℓ := ℓ) k sync large
  obtain ⟨K₀, h₀⟩ := allHosts g ℓ D n p l b large dyad
  refine ⟨K, inferInstance, inferInstance, inferInstance, p, l, b, inferInstance, inferInstance, K₀, ?_⟩
  intro c
  obtain ⟨B, hB, hp⟩ := h₀ c
  refine ⟨B, hB, ?_⟩
  filter_upwards [go, eventually_ge_atTop (D ^ terminalExponent g ℓ)] with T hh hT
  obtain ⟨d, sc, hc⟩ := hh
  refine ⟨d, sc, hc, hT, ?_⟩
  intro F _ _ _ low high
  have : CharP F p := charP_of_injective_algebraMap' K p
  exact ⟨inferInstance, hp sc F K hc low high hT⟩

end OAI.LinearAlgebra.MatrixExponent.Rounds.Input
end

/-! # Accounting for preparation and the doubled scale -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Input.ReadyPanel
open Assembly Coloring Sphere SphereScale Surface Surface.Local Geometry
open scoped Classical

variable {F K : Type} [Field F] [Fintype F] [Field K] [Algebra K F]
    {x y : Wire} {g ℓ D T b d p l k r t n u f : ℕ} [ExpChar F p] {W : ℝ}
    {S : Scheme F} {P : Input F x y S.h D T (d * b) g W} {z : S.format.obj}
    {A : P.HostChart S z} {hK : Ready K ℓ D g (p ^ l) b d}
    {hF : room ℓ D g * (2 * depth ℓ D g (p ^ l) (d * b) + 1) < Fintype.card F}
    {mobility : B S.ℓ → B S.k → Bool} {U : LocalPrinter S g ℓ D b d p l k r t n u f}
    {status : (Print.Children.Header S.m S.d).obj} {pres : S.Presentation z P.diagram}

local notation "Cfg" => design S g ℓ D b d p l
variable {h : P.ReadyPanel A hK hF mobility k U status pres} {sc : Scales g ℓ D T (p ^ l) b d}

/-- The cost of computing the two initial caps from local packet
counts and immobility bits is independent of the label and scale. -/
def extra (g ℓ D deg : ℕ) :=
  let waves := Neighborhood.paletteSize deg (2 * D ^ 5 + 2) * room ℓ D g
  capCost g ℓ D waves + Fintype.card (CapPins ℓ D) + indexWidth (Credits.Caps g ℓ D waves)

theorem Bookkeeping.prepare {B a : ℕ} (books : h.Bookkeeping sc B a) :
    ∃ f : Fin (indexWidth (Credits.Caps g ℓ D (Cfg).waves)) → BitFormula (CapPins ℓ D),
      controllerWork S U (wordWidth D T) + (∑ i, (f i).cost) + Fintype.card (CapPins ℓ D)
        + indexWidth (Credits.Caps g ℓ D (Cfg).waves) ≤ (B + extra g ℓ D S.d) * (1 + a + Nat.clog 2 (T + 1)) ∧
      ∀ v i, (f i).eval (capCode (P.capData sc v)) =
        labelCode _ (Credits.caps g ℓ D (Cfg).waves (P.initialEnergyTokens ℓ (p ^ l) (Cfg).waves v)
          (P.initialTimeTokens v)) i := by
  obtain ⟨q, hq, he⟩ := P.local_caps sc (Cfg).waves
  refine ⟨q, ?_, he⟩
  let w := 1 + a + Nat.clog 2 (T + 1)
  have hi : (∑ i, (q i).cost) + Fintype.card (CapPins ℓ D) +
      indexWidth (Credits.Caps g ℓ D (Cfg).waves) ≤ extra g ℓ D S.d :=
    Nat.add_le_add_right (Nat.add_le_add_right hq _) _
  have hw : 0 < w := by unfold w; omega
  have hw' := Nat.add_le_add books.work (hi.trans (Nat.le_mul_of_pos_right _ hw))
  simpa only [w, add_mul, add_assoc] using hw'

end OAI.LinearAlgebra.MatrixExponent.Rounds.Input.ReadyPanel
end

/-!
# Bookkeeping at arbitrary scales

Rounding the subdivision up and padding the wires preserve the
labels. The doubled scale pays for the additional wires. Raising
the working accuracy by one recovers the original core cutoff.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Input
open Assembly Filter Coloring Sphere SphereScale
open scoped Classical
variable {K F : Type} [Field K] [Field F] [Algebra K F] [Fintype F]
  {g ℓ D T p l b d : ℕ} [ExpChar F p]

local notation "Dyad" d => 2 ^ Nat.clog 2 d

def packetExponent (g ℓ : ℕ) := 2 * (202 * ReadyPanel.exponent g (ℓ + 1))

abbrev PacketScales (g ℓ D T p l b d : ℕ) :=
  Scales g (ℓ + 1) (Dyad D) (2 * T) (p ^ l) b d

attribute [local irreducible] Print.indexBits Nat.clog

def PaddedFamily (sc : PacketScales g ℓ D T p l b d) (ready : Ready K (ℓ + 1) (Dyad D) g (p ^ l) b d)
    (hD : threshold g ≤ D) (K₀ c B : ℕ) : Prop :=
  ∀ {a e : ℕ} (m h : ℕ) (read : BundleReader F a e), e ≤ inputBits g D →
    let S := (bundleScheme read m h g (Dyad D) T).padded (d * b)
    let k := selectorBits K₀ (Dyad D) (room (ℓ + 1) (Dyad D) g) (2 * T) (Nat.card F)
    let u := unitSize g ℓ D T
    let f := (c + 1) * Nat.clog 2 (2 * T + 1)
    ∃ (hF : room (ℓ + 1) (Dyad D) g * (2 * depth (ℓ + 1) (Dyad D) g (p ^ l) (d * b) + 1) < Fintype.card F)
      (r t : ℕ) (U : LocalPrinter S g (ℓ + 1) (Dyad D) b d p l k r t (Nat.clog 2 D) u f),
      ∀ {x y : Wire} {R : ℕ} {W : ℝ} (P : Input F x y h D T R g W) (o : BundleOrder P.diagram read),
        Fintype.card P.V ≤ 2 ^ m →
        (IsEmpty P.V ∧ LocalExpansion P u (packetExponent g ℓ) (Nat.clog 2 D) ℓ B) ∨
        let Q := P.round_up (lt_of_lt_of_le Nat.zero_lt_two (threshold_large hD))
        let hp := threshold_packet hD
        ∃ (v : Q.Seating m)
          (hr : (v.packetOrdered o (d * b) sc.Rpos hp sc.smallR).ReadyPanel (S := S)
            (v.packetChart o (d * b) sc.Rpos hp sc.smallR) ready hF (mobility a e g (Dyad D) T)
            k U v.tape.2 (v.packetPres o (d * b) sc.Rpos hp sc.smallR)),
          hr.Bookkeeping (S := S) sc B a ∧ hr.Represents (S := S) sc P (packetExponent g ℓ) ℓ

/-- No packet-divisibility or power-of-two requirement is imposed
on the input. The polynomial lower field bound precedes the choice
of exponent for the polynomial upper bound. -/
theorem padded_bookkeeping (k : Type) [Field k] [Finite k] (sync : Prices.SharedPrice (AlgebraicClosure k))
    (g ℓ D : ℕ) (hD : threshold g ≤ D) :
    ∃ (K : Type) (_ : Field K) (_ : Fintype K) (_ : Algebra k K)
      (p l b : ℕ) (_ : CharP K p) (_ : Fact p.Prime) (K₀ : ℕ),
      ∀ c : ℕ, ∃ B : ℕ, 0 < B ∧ ∀ᶠ T : ℕ in atTop,
        ∃ (d : ℕ) (sc : PacketScales g ℓ D T p l b d) (hc : Ready K (ℓ + 1) (Dyad D) g (p ^ l) b d),
          0 < unitSize g ℓ D T ∧ T ≤ unitSize g ℓ D T * D ^ (2 * terminalExponent g (ℓ + 1)) ∧
          ∀ (F : Type) [Field F] [Fintype F] [Algebra K F],
            K₀ * (1 + 2 * T) ^ K₀ ≤ Fintype.card F → Fintype.card F ≤ (T + 1) ^ c →
            ∃ _ : ExpChar F p, PaddedFamily (F := F) sc hc hD K₀ c B := by
  let N := Dyad D
  let n := Nat.clog 2 D
  have large := threshold_scales hD
  obtain ⟨K, _, _, _, p, l, b, _, _, go⟩ := SphereScale.choose (ℓ := ℓ + 1) k sync large
  obtain ⟨K₀, h₀⟩ := layoutParameters g (ℓ + 1) N p l b
  refine ⟨K, inferInstance, inferInstance, inferInstance, p, l, b, inferInstance, inferInstance, K₀, ?_⟩
  intro c
  let J := controllerBound g (ℓ + 1) N n K₀ (channelBits g) (stationBits N)
  let B := 2 * (J + 1) * (rowFactor g N + c + 2)
  have hJ : J ≤ B := (show J ≤ 2 * (J + 1) by omega).trans (Nat.le_mul_of_pos_right _ (by omega))
  refine ⟨B, by unfold B; positivity, ?_⟩
  have twice : Tendsto (fun T : ℕ => 2 * T) atTop atTop := by
    apply tendsto_atTop.2
    intro a
    filter_upwards [eventually_ge_atTop a] with T ht
    omega
  filter_upwards [twice.eventually go, twice.eventually (eventually_ge_atTop (N ^ terminalExponent g (ℓ + 1)))] with T hh hT
  obtain ⟨d, sc, hc⟩ := hh
  obtain ⟨hu, hunit⟩ := packet_unit (threshold_large hD) hT
  refine ⟨d, sc, hc, hu, hunit, ?_⟩
  intro F _ _ _ lo hi
  have : CharP F p := charP_of_injective_algebraMap' K p
  refine ⟨inferInstance, ?_⟩
  intro a e m h read he S j u f
  obtain ⟨ht, hf⟩ := binaryDigits (2 * T) c
  have order : Fintype.card F ≤ 2 ^ f := hi.trans ((Nat.pow_le_pow_left (by omega) c).trans hf)
  obtain ⟨field, r, t, U, cap, run⟩ := h₀ sc F K hc lo order rfl hT S (mobility a e g N T) (channel_cap large)
  have hj := selector_width K₀ N (room (ℓ + 1) N g) (2 * T) (Nat.card F) f ht (Nat.card_eq_fintype_card.trans_le order)
  have lim : ControllerBounds S U (2 * T) J := controller_bounds S U cap hj ht
  have hw : S.ℓ ≤ rowFactor g N * (1 + a + Nat.clog 2 (2 * T + 1)) := by
    refine (bundleBits read m h g N T (he.trans (inputBits_round g D))).trans ?_
    gcongr
    omega
  obtain ⟨hw, hl⟩ := labelWidths J (rowFactor g N) c a _ _ hw
  refine ⟨field, r, t, U, ?_⟩
  intro x y R W P o size
  cases isEmpty_or_nonempty P.V with
  | inl hp =>
    let _ := hp
    exact .inl ⟨hp, P.emptyExpansion ..⟩
  | inr hp =>
    let Q := P.round_up (lt_of_lt_of_le Nat.zero_lt_two (threshold_large hD))
    let o' : BundleOrder Q.diagram read := o
    let a' := threshold_packet hD
    obtain ⟨v⟩ := Q.seating size
    have hv := run (v.packetOrdered o' (d * b) sc.Rpos a' sc.smallR)
      (v.packetChart o' (d * b) sc.Rpos a' sc.smallR) v.tape.2 (v.packetPres o' (d * b) sc.Rpos a' sc.smallR)
      (v.packetPlaced o' (d * b) sc.Rpos a' sc.smallR) (v.packetDirected o' (d * b) sc.Rpos a' sc.smallR)
      (v.packetRanks o' (d * b) sc.Rpos a' sc.smallR) (v.packetLocation o' (d * b) sc.Rpos a' sc.smallR)
      (v.packetParents o' (d * b) sc.Rpos a' sc.smallR) hp
    refine .inr ⟨v, hv, hv.complete sc (v.packetMoving o' (d * b) sc.Rpos a' sc.smallR) lim hJ hw hl, ?_⟩
    exact hv.represents sc (v.packetEval o' (d * b) sc.Rpos a' sc.smallR)
      (fun _ h => Concentrated.of_round_up P (threshold_large hD) (v.packetBounds o' (d * b) sc.Rpos a' sc.smallR h))

end OAI.LinearAlgebra.MatrixExponent.Rounds.Input
end

/-! # Common dictionaries for raw, ordered station diagrams -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Raw
open Assembly Coloring Input Sphere SphereScale
open scoped Classical
variable {K F : Type} [Field K] [Field F] [Algebra K F] [Fintype F]
  {g ℓ D T p l b d : ℕ} [ExpChar F p]

local notation "Dyad" d => 2 ^ Nat.clog 2 d
section
open Surface Surface.Local
variable {F K : Type} [Field F] [Fintype F] [Field K] [Algebra K F]
    {x y : Wire} {g ℓ D T b d p l k r t n u f : ℕ} [ExpChar F p] {W : ℝ}
    {S : Scheme F} {P : Input F x y S.h D T (d * b) g W} {z : S.format.obj}
    {A : P.HostChart S z} {hK : Ready K ℓ D g (p ^ l) b d}
    {hF : room ℓ D g * (2 * depth ℓ D g (p ^ l) (d * b) + 1) < Fintype.card F}
    {mobility : B S.ℓ → B S.k → Bool} {U : LocalPrinter S g ℓ D b d p l k r t n u f}
    {status : (Print.Children.Header S.m S.d).obj} {pres : S.Presentation z P.diagram}

variable (hr : P.ReadyPanel A hK hF mobility k U status pres) (sc : Scales g ℓ D T (p ^ l) b d)

variable {D' T' : ℕ} {W' : ℝ}

/-- The scalar may vanish and is retained even then. -/
def Weighted (Q : Raw F x y S.h D' T' g W') : Prop :=
  ∀ i j, Q.diagram.eval i j = ∑ v : hr.Paths sc, Q.coeff * (hr.summand sc v).diagram.eval i j

/-- Original holder identities and cells are preserved in every branch. -/
def Keeps (Q : Raw F x y S.h D' T' g W') (parent : P.V → Q.V) : Prop :=
  ∀ v : hr.Paths sc, Q.Holders (hr.summand sc v) (parent ∘ hr.scalarParent sc v)

end

attribute [local irreducible] Print.indexBits Nat.clog

/-- The working field, controller and table dictionary are shared across
diagrams. The withdrawn scalar is the same for every term of a diagram.
The final bounds use the original arity scale and label length. -/
def Family (sc : PacketScales g ℓ D T p l b d) (ready : Ready K (ℓ + 1) (Dyad D) g (p ^ l) b d)
    (hD : threshold g ≤ D) (K₀ c B : ℕ) : Prop :=
  ∀ {a e : ℕ} (m h : ℕ) (read : BundleReader F a e), e ≤ inputBits g D →
    labelSize D T a e ≤ a + B * (1 + Nat.clog 2 (T + 1)) ∧
    let S := (bundleScheme (reader D T read) m h g (Dyad D) T).padded (d * b)
    let k := selectorBits K₀ (Dyad D) (room (ℓ + 1) (Dyad D) g) (2 * T) (Nat.card F)
    let u := unitSize g ℓ D T
    let f := (c + 1) * Nat.clog 2 (2 * T + 1)
    ∃ (hF : room (ℓ + 1) (Dyad D) g * (2 * depth (ℓ + 1) (Dyad D) g (p ^ l) (d * b) + 1) < Fintype.card F)
      (r t : ℕ) (U : LocalPrinter S g (ℓ + 1) (Dyad D) b d p l k r t (Nat.clog 2 D) u f),
      ∀ {x y : Wire} {W : ℝ} (P : Raw F x y h D T g W) (o : BundleOrder P.diagram read),
        Fintype.card P.V ≤ 2 ^ m →
        (P.coeff = ∏ v : {v // ¬0 < P.diagram.removeLoops.arity v},
          reader D T read (o.traceLabel (weightBits D T) v.val)
            (fun _ => 0) (fun t => o.dir (v.val, t)) (fun _ _ => false)) ∧
        (∀ i j, P.coeff * P.reduced.diagram.eval i j = P.diagram.eval i j) ∧
        ((IsEmpty P.V ∧ LocalExpansion P.reduced u (packetExponent g ℓ) (Nat.clog 2 D) ℓ B) ∨
        let Q := P.reduced.round_up (lt_of_lt_of_le Nat.zero_lt_two (threshold_large hD))
        let hp := threshold_packet hD
        let ord := P.order o
        ∃ (v : Q.Seating m)
          (hr : (v.packetOrdered ord (d * b) sc.Rpos hp sc.smallR).ReadyPanel (S := S)
            (v.packetChart ord (d * b) sc.Rpos hp sc.smallR) ready hF
            (mobility (labelSize D T a e) e g (Dyad D) T) k U v.tape.2
            (v.packetPres ord (d * b) sc.Rpos hp sc.smallR)),
          hr.Bookkeeping (S := S) sc B a ∧
          hr.Represents (S := S) sc P.reduced (packetExponent g ℓ) ℓ ∧
          Weighted (S := S) hr sc P ∧
          Keeps (S := S) hr sc P id)

end OAI.LinearAlgebra.MatrixExponent.Rounds.Raw
end
