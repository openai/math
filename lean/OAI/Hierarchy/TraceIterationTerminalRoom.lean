import OAI.Hierarchy.TraceIterationPlacement
import OAI.ThreeFlat.Diagonal.NavigationTerminalWindow
import OAI.ThreeFlat.Diagonal.TraceTerminalEdges

namespace OAI
/-! # The native terminal padding pass fits in the actual selector and archive banks -/
namespace Hierarchy.TraceAdmission
open Filter TraceDistribution ThreeFlat Diagonal PhysicalStage NavigationPass
open NavigationDirectory Computability.VPVNP.BurstRAM
variable {F : Type} [Field F] (B : Block F)

theorem terminal_edges {u s : ℕ→ℕ} (scale : Scale u s) :
    ∀ᶠ w : ℕ in atTop, ∀ k, k=u w+1-w/2 → B.blockCharge*s w≤k →
      let P:=B.repeat (s w)
      P.finalEdges (k-P.charge) k≤2^(3*w/5) := by
  filter_upwards [record_room scale (2^B.exponent 0)] with w bulk
  intro k axes fits P
  rw [←axes] at bulk
  let rem:=k-P.charge
  let edges:=P.finalEdges rem k
  let limit:=2^(3*w/5)
  have split : P.charge+rem=k := by dsimp [P,rem];rw [B.charge_repeat];omega
  have smallE : edges≤limit := calc
    _ ≤ 2^P.terminalExponent*(k*2^(P.charge+rem)) := P.finalEdges_le rem k
    _ = 2^B.exponent 0*(k*2^k) := by rw [split,B.terminalExponent_repeat]
    _ ≤ 2^B.exponent 0*(s w+1)*(1+k*2^k)*(64*w+1) := by
      calc
        _ ≤ (2^B.exponent 0)*(1+k*2^k) := Nat.mul_le_mul_left _ (by omega)
        _ ≤ (2^B.exponent 0*(s w+1))*(1+k*2^k) :=
          Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_right _ (by omega))
        _ ≤ _ := Nat.le_mul_of_pos_right _ (by omega)
    _ ≤ _ := bulk
  exact smallE

theorem eventual_terminal_room_at {u s : ℕ→ℕ} (scale : Scale u s) :
    ∀ᶠ w : ℕ in atTop, ∀ (_fits : B.blockCharge*s w≤u w+1-w/2) (a : Archive) (β : ℕ),
      let k:=u w+1-w/2
      let P:=B.repeat (s w)
      let rem:=k-P.charge
      let ss:=P.directory rem k
      let edges:=P.finalEdges rem k
      ArchivePlacement a β w → a.K=B.alphabetCap →
      β+8*(2^w)^4<2^(64*w) → a.phase≤β → a.oldHistory+a.pairCapacity≤β → a.newHistory+a.pairCapacity≤β →
      a.seed+(a.directory ss edges (64*w)).length<2^(64*w) ∧ a.TerminalRoom ss edges (64*w) := by
  filter_upwards [terminal_edges B scale,eventual_stage_heap B scale,
    eventual_stage_headers B scale,eventual_record_length B scale,eventually_ge_atTop 7]
    with w edgeb heap headers records hw
  intro fits a β k P rem ss edges placed alph powRoom phase old fresh
  let stride:=(2^w)^4
  let limit:=2^(3*w/5)
  let c:=finish a.K ss a.cursor
  change β+8*stride<2^(64*w) at powRoom
  have margin : limit+limit+1 < stride := by
    have one : 1≤limit := Nat.one_le_two_pow
    have big : 4*limit ≤ stride := calc
      _ = 2^(2+3*w/5) := (pow_add ..).symm
      _ ≤ 2^(w*4) := Nat.pow_le_pow_right (by decide) (by omega)
      _ = _ := by rw [pow_mul]
    omega
  have smallE : edges≤limit := edgeb k rfl fits
  have sumH : (ss.map Stage.heapWords).sum≤limit := heap fits
  have tape : (a.directory ss edges (64*w)).length≤limit := by
    rw [Archive.directory_length]
    exact headers rem k
  have raw : 64*w*a.histWords ss≤limit := by
    simpa only [Archive.histWords,alph,ss,k,P,rem,stageCounts,limit,Nat.mul_assoc,Nat.mul_comm,
      Nat.mul_left_comm] using records fits
  have seed:=placed.seed
  have addr:=placed.control
  have upper : c.heap≤β+5*stride+limit := by dsimp [c];rw [heap_finish,placed.heap];omega
  have lower : β+5*stride≤c.heap := by dsimp [c];rw [heap_finish,placed.heap];omega
  have hh : c.header<c.heap := by
    have address : c.header = β+64+64*ss.length := by
      change (finish a.K ss a.cursor).header = _
      rw [header_finish,placed.header]
    rw [Archive.directory_length] at tape
    omega
  have ww : c.width≤c.heap :=
    width_before_heap a.K ss a.cursor (by rw [placed.width,placed.heap];omega)
  have seedHeap : a.seed≤c.heap := by rw [seed]; omega
  refine ⟨by omega,⟨?_,hh,?_,seedHeap⟩⟩
  · change RAM.TerminalWireArchive.Bounds
      ⟨a.control,a.phase,a.oldHistory+64*w*a.histWords ss,a.newHistory+64*w*a.histWords ss,
        a.pairCapacity-64*w*a.histWords ss,c.width,edges,c.heap⟩ (64*w)
    constructor <;> dsimp only <;> omega
  · change c.heap+edges<a.control
    omega

theorem eventual_terminal_room {u s : ℕ→ℕ} (scale : Scale u s) :
    ∀ᶠ w : ℕ in atTop, ∀ (_fits : B.blockCharge*s w≤u w+1-w/2) (a : Archive),
      let k:=u w+1-w/2
      let J:=2^(32*w)
      let P:=B.repeat (s w)
      let rem:=k-P.charge
      let ss:=P.directory rem k
      let edges:=P.finalEdges rem k
      ArchivePlacement a (16*J) w → a.K=B.alphabetCap →
      a.phase=12*J → a.oldHistory=12*J+1 → a.newHistory=12*J+1 → a.pairCapacity≤J →
      a.seed+(a.directory ss edges (64*w)).length<2^(64*w) ∧ a.TerminalRoom ss edges (64*w) := by
  filter_upwards [eventual_terminal_room_at B scale,eventually_ge_atTop 1] with w enough hw
  intro fit a k J P rem ss edges placed alph phase old fresh cap
  have one : 1≤J := Nat.one_le_two_pow
  exact enough fit a (16*J) placed alph (sector_placement_room hw).2 (by omega) (by omega) (by omega)

end Hierarchy.TraceAdmission

end OAI
