import OAI.Computability.BorderVNP.RoutingISAScheduleClockTally
import OAI.Computability.BorderVNP.CellTeamSignedScales
import OAI.Computability.BorderVNP.PackedBundleDirectoryRun
import OAI.Computability.BorderVNP.PackedDirectoryNative
import OAI.Computability.BorderVNP.PrivatePlacementProof

/-! # Combined rounded team clock for the signed evaluator

The sparse public preparations are charged by the original tile rectangle
and the physical geometry output. The local preparations use the emitted
descriptors and each team's true incidence and power slots. The dense
residue work uses the chart's separate batch allowance.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator.ScheduleClock

open BorderVNP.Cube TeamScales Filter VPVNP CellPacketGeometry

/-- Exact ordinary allowances for private placement, demand generation,
six-word bottom bundle publication and the two owned task directory scans. -/
def directoryWork (R V entries cells bundles : ℕ) :=
  PrivatePlacement.setup.slots+entries*15+1+
    (Packing.Directory.ISA.setup.slots+(Packing.Directory.ISA.candidate.slots+19)*(8*(R*V))+8)+
    (Packing.BundleDirectory.setup.slots+16*cells+30*bundles+1)+
    (CellControlRows.setup.slots+cells*(CellControlRows.body.slots+1)+1+CellControlRows.finish.slots+
      (TypedTaskBuilder.setup.slots+cells*(TypedTaskBuilder.body.slots+1)+2))

/-- Only the reserved site/team rectangle and the actual geometry outputs
are scanned, including empty cells. -/
theorem directoryWork_le {R V entries cells bundles output : ℕ} (privateRows : entries ≤ R*V)
    (cellFit : cells ≤ output) (bundleFit : bundles ≤ output) :
    directoryWork R V entries cells bundles ≤ 1024*(R*V+output+1) := by
  have task := DiagonalTallyCellReports.header_task_charge cells
  unfold directoryWork
  change 37+entries*15+1+(67+(69+19)*(8*(R*V))+8)+(32+16*cells+30*bundles+1)+_ ≤ _
  omega

/-- The typed source rectangle and the bottom-bundle outputs are subarrays
of the true joint geometry emission. These charges come directly from its
stripe-read loop, regardless of the later contents of the words. -/
theorem geometrySubarrays_le {p d k u o b w : ℕ} (hw : 1 ≤ w) (hb : 1 ≤ b)
    (cells : Total p d ≤ o) :
    (w+1)*(2^p+2^d) ≤ GeometryAdviceRate.ticks k u o b w ∧ o ≤ GeometryAdviceRate.ticks k u o b w := by
  let words := GeometryAdviceRate.packetWords k u o b
  have out : o ≤ words := (Nat.le_mul_of_pos_right o hb).trans (by dsimp [words,GeometryAdviceRate.packetWords]; omega)
  have stripe : words*w ≤ GeometryAdviceRate.ticks k u o b w := by
    unfold GeometryAdviceRate.ticks
    change words*w ≤ GeometryAdvice.beginStripe.slots+words*w*(GeometryAdvice.copyStripeBit.slots+1)+1+_+_
    have factor : words*w ≤ words*w*(GeometryAdvice.copyStripeBit.slots+1) := Nat.le_mul_of_pos_right _ (by omega)
    omega
  have rect : 2*(2^p+2^d) ≤ o := by
    have shape : Total p d=2*(2^p+2^d) := by dsimp [Total]; ring
    rwa [←shape]
  have rw := Nat.mul_le_mul_right w (rect.trans out)
  have rpos := Nat.le_mul_of_pos_right (2^p+2^d) hw
  have left : (w+1)*(2^p+2^d) ≤ 2*(2^p+2^d)*w := by nlinarith only [rpos]
  exact ⟨left.trans (rw.trans stripe),out.trans ((Nat.le_mul_of_pos_right _ hw).trans stripe)⟩

/-- A returning evaluation is charged by the real core, public group
allowances, source and task directories, team-local cube work, true sparse
cell preparations, and aligned subtotal/reader work. The fixed code size
covers the four literal cube tables. -/
def completeAllowance (core geometry fixed R V entries cells bundles desc decl cables
    cubeUnits formatCoefficient vertexCoefficient w publicWords powerSlots exterior dense : ℕ) :=
  core + geometry + fixed + directoryWork R V entries cells bundles + desc+decl + 32*desc +
    (82*cables+formatCoefficient*cubeUnits) +
    (5000*((w+1)*publicWords)+700000000*((w+1)*exterior)+500*powerSlots) +
    (64*(publicWords+powerSlots+vertexCoefficient*cubeUnits)+dense)

/-- Passing from the two measured work scales to the rounded native clock
also works for arbitrary interleavings of public and local instructions. -/
theorem eventually_mixedClock (a D : ℕ) (ha : 1 ≤ a) {α ξ : ℝ} (hα : 0 ≤ α)
    (small : α*a < 1/10^6) (hξ : 0 < ξ) (hξ' : ξ<1/25) :
    ∃ ω : ℝ, 0 < ω ∧ ∀ A B : ℝ, 0 ≤ A → 0 ≤ B → ∀ᶠ n : ℕ in atTop, ∀ r R N core total : ℕ,
      1 ≤ r → 1 ≤ R → (r:ℝ) ≤ 2^((n:ℝ)^ω) → (R:ℝ) ≤ (n:ℝ)^(2*α) →
      core ≤ 2048*(exterior ξ r n+(R+1)^3+N+r+1) → (N:ℝ) ≤ A*publicWork a α r n R →
      (total:ℝ) ≤ core+B*(publicWork a α r n R+localWork a D α ξ r n R) → total ≤ ticks ξ r n := by
  obtain ⟨ω,positive,h⟩ := eventually_eval_clock a D ha hα small hξ hξ'
  refine ⟨ω,positive,?_⟩
  intro A B hA hB
  filter_upwards [h A (B+1) hA (by linarith),eventually_ge_atTop 1] with n bound hn
  intro r R N core total hr hR batch teams cCap rowCap cost
  let P := publicWork a α r n R
  let L := localWork a D α ξ r n R
  have rp : 1 ≤ (r:ℝ) := by exact_mod_cast hr
  have nz : 1 ≤ (n:ℝ) := by exact_mod_cast hn
  have base : 1 ≤ (r:ℝ)*(n:ℝ)^(19/20:ℝ) := one_le_mul_of_one_le_of_one_le rp (Real.one_le_rpow nz (by norm_num))
  have pp : 1 ≤ P := by dsimp [P,publicWork]; linarith [show 0 ≤ ((Routing.labelCount a α n:ℝ)+R)^10 by positivity]
  have Rpos : 1 ≤ (R:ℝ) := by exact_mod_cast hR
  have table : 1 ≤ ((Routing.labelCount a α n:ℝ)+R)^10 := one_le_pow₀ (by linarith [Nat.cast_nonneg (α:=ℝ) (Routing.labelCount a α n)])
  have lp : 1 ≤ L := by
    apply one_le_mul_of_one_le_of_one_le (by linarith [Nat.cast_nonneg (α:=ℝ) (exterior ξ r n)])
      (one_le_pow₀ (by exact_mod_cast (GeometryAdviceRate.indexWidths hr hn).1))
  have ceil (x : ℝ) (hx : 1 ≤ x) : (⌈B*x⌉₊:ℝ) ≤ (B+1)*x := by
    have h0 := Nat.ceil_lt_add_one (mul_nonneg hB (zero_le_one.trans hx))
    linarith
  have c := bound r R N core ⌈B*P⌉₊ ⌈B*L⌉₊ hr hR batch teams cCap rowCap (ceil P pp) (ceil L lp)
  apply le_trans _ c
  have u := Nat.le_ceil (B*P)
  have v := Nat.le_ceil (B*L)
  change (total:ℝ) ≤ core+B*(P+L) at cost
  exact_mod_cast (show (total:ℝ) ≤ (core:ℝ)+(⌈B*P⌉₊:ℝ)+(⌈B*L⌉₊:ℝ) by linarith only [cost,u,v])

/-- Native allowances summed above fit the physical tick limit. The bound
on the geometry input counts concerns its gate/bit size; the time for the
physical interpreter is derived here. The dense count is bounded by
`eventually_readerRectangle` on the stretched §11 chart. -/
theorem eventually_completeAllowance (a D e bits B C fixed F H : ℕ) (ha : 1 ≤ a) (hD : 1 ≤ D)
    {α ξ τ : ℝ} (hα : 0 < α) (hτ : 0 ≤ τ) (small : α*a < 1/10^6) (alphaCap : α ≤ 1/1000)
    (hξ : 0 < ξ) (hξ' : ξ < 1/25) (G K : ℕ) (hG : 1 ≤ G) (hK : 1 ≤ K)
    (growth : τ*Real.logb 2 G ≤ α/10) (fan : τ*Real.logb 2 K ≤ α) :
    ∃ ω : ℝ, 0 < ω ∧ ∀ A : ℝ, 0 ≤ A → ∀ᶠ n : ℕ in atTop,
      ∀ (r R V z w g k u o b p d entries cells bundles core dense powers : ℕ)
        (l : LabelIndex.Layout) (mem : ℕ → ℕ) (groups : GroupWeights.Layout) (t : TeamNative.Layout) (header : HeaderDecode.Layout),
      let M := max (G^epochs τ n) (teams α τ K n)
      let Z := Routing.labelCount a α n
      let X := exterior ξ r n
      1 ≤ r → 1 ≤ R → (r:ℝ) ≤ 2^((n:ℝ)^ω) → (R:ℝ) ≤ (n:ℝ)^(2*α) → R ≤ M →
      (V:ℝ) ≤ C*r*(n:ℝ)^(9/10:ℝ) → 1+l.cells+l.cableCount+l.deliveryCount ≤ B*(V+1)*(M+1) →
      l.labels=Z → l.labels=z+1 → groups.cells=l.cells → t.groups=groups.groups →
      t.r+1 ≤ groups.groups → groups.groups ≤ l.labels → header.d=groups.groups → header.a=a →
      header.cw ≤ w → header.rw ≤ w → 1 ≤ w → w ≤ logWidth r n^D →
      1 ≤ b → k ≤ 4*g → ((g+u+o*b:ℕ):ℝ) ≤ A*r*(n:ℝ)^(93/100:ℝ)*(logWidth r n:ℝ)^e →
      Total p d ≤ o → entries ≤ R*V → cells ≤ o → bundles ≤ o → powers ≤ r*logWidth r n → dense ≤ r →
      core ≤ 2048*(X+(R+1)^3+(l.deliveryCount+groups.groups.choose 2)+r+1) →
      completeAllowance core (GeometryAdviceRate.ticks k u o b w) fixed R V entries cells bundles
        (descriptorTicks l mem z a groups t) (declarationTicks header (a-1) bits) l.cableCount
        (Z^2+X+1) F H w (2^p+2^d) powers X dense ≤ ticks ξ r n := by
  obtain ⟨ω,hω,clock⟩ := eventually_mixedClock a D ha hα.le small hξ hξ'
  obtain ⟨δ,hδ,geo⟩ := GeometryAdviceRate.eventually_fits e D (α:=α) (by linarith)
  refine ⟨min ω δ,lt_min hω hδ,?_⟩
  intro A hA
  let C₀ : ℝ := 2000000000+fixed+512*(a+bits+1)+2*(F+64*H)
  have pos : 0 ≤ C₀ := by dsimp [C₀]; positivity
  filter_upwards [clock 2 C₀ (by norm_num) pos,geo A 1 hA zero_le_one UniversalMachine.emptyProgram 0 0,
    eventually_scheduleTicks (ξ:=ξ) hα a bits B C D small,MeanChoice.eventually_scanEnvelope hα a small 1 C,
    eventually_ge_atTop 1] with n rounded geometry schedule rectangle hn
  intro r R V z w g k u o b p d entries cells bundles core dense powers l mem groups t header M Z X hr hR batch teamGrowth RM
    Vcap rows ZZ hz gc tg rg gz gd ga cw rw hw word bw gates graph output privateRows cellFit bundleFit source entry coreCap
  have npos : 1 ≤ (n:ℝ) := by exact_mod_cast hn
  have rpos : 1 ≤ (r:ℝ) := by exact_mod_cast hr
  have Rpos : 1 ≤ (R:ℝ) := by exact_mod_cast hR
  have smaller (v : ℝ) (ok : min ω δ ≤ v) : (r:ℝ) ≤ 2^((n:ℝ)^v) :=
    batch.trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) (Real.rpow_le_rpow_of_exponent_le npos ok))
  let P := publicWork a α r n R
  let L := localWork a D α ξ r n R
  let geoT := GeometryAdviceRate.ticks k u o b w
  let desc := descriptorTicks l mem z a groups t
  let decl := declarationTicks header (a-1) bits
  let U := Z^2+X+1
  let Q := logWidth r n^D
  have MCap := LabelIndex.multiplicity_le hn hτ alphaCap hG hK growth fan
  obtain ⟨cd,ch⟩ := schedule r R V M z w l mem groups t header hr hR Vcap MCap rows ZZ hz gc tg rg gz gd ga cw rw word
  change (desc:ℝ) ≤ P at cd
  change (decl:ℝ) ≤ ((512*(a+bits+1):ℕ):ℝ)*L at ch
  have scalar : (w:ℝ) ≤ 1*(logWidth r n:ℝ)^D := by simpa using (Nat.cast_le (α:=ℝ)).mpr word
  have geot := (geometry r g k u o b w hr (smaller δ (min_le_right ..)) bw gates graph scalar).1
  have geomN : geoT ≤ r*width n (95/100:ℝ) := (Nat.le_add_right ..).trans geot
  have rp : (r:ℝ) ≤ r*(n:ℝ)^(19/20:ℝ) := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (Real.one_le_rpow npos (by norm_num : 0≤(19/20:ℝ))) (zero_le_one.trans rpos)
  have pubBase : (r:ℝ)*(n:ℝ)^(19/20:ℝ) ≤ P := by dsimp [P,publicWork]; linarith [show 0 ≤ ((Routing.labelCount a α n:ℝ)+R)^10 by positivity]
  have oneP := rpos.trans (rp.trans pubBase)
  have geomP : (geoT:ℝ) ≤ P := by
    have floor : (width n (95/100:ℝ):ℝ) ≤ (n:ℝ)^(19/20:ℝ) := by
      rw [show (95/100:ℝ)=19/20 by norm_num]; exact Nat.floor_le (by positivity)
    have gN := (Nat.cast_le (α:=ℝ)).mpr geomN
    rw [Nat.cast_mul] at gN
    exact gN.trans ((mul_le_mul_of_nonneg_left floor (Nat.cast_nonneg _)).trans pubBase)
  obtain ⟨geomSlots,out⟩ := geometrySubarrays_le (k:=k) (u:=u) hw bw output
  have slotsP : (((w+1)*(2^p+2^d):ℕ):ℝ) ≤ P := ((Nat.cast_le (α:=ℝ)).mpr geomSlots).trans geomP
  have outP := ((Nat.cast_le (α:=ℝ)).mpr out).trans geomP
  have rv : (R*V:ℕ) ≤ MeanChoice.scanEnvelope 1 V M (Routing.labelCount a α n) := by
    have fit := Nat.mul_le_mul (RM.trans (Nat.le_succ _)) (Nat.le_succ V)
    have pos₁ : 1 ≤ (Routing.labelCount a α n+1)^6 := pow_pos (Nat.zero_lt_succ _) _
    simp only [MeanChoice.scanEnvelope,one_mul]
    rw [Nat.mul_comm (V+1)]
    exact fit.trans (Nat.le_mul_of_pos_right _ pos₁)
  have prodP : ((R*V:ℕ):ℝ) ≤ P := ((Nat.cast_le (α:=ℝ)).mpr rv).trans ((rectangle r V M hr Vcap MCap).le.trans (by
    norm_num1; exact pubBase))
  have dirs := (Nat.cast_le (α:=ℝ)).mpr (directoryWork_le privateRows cellFit bundleFit)
  have cables := (Nat.cast_le (α:=ℝ)).mpr (cableSweep_le l mem z a groups t)
  have Ucap : (U:ℝ) ≤ 2*L := by simpa [U,Z,X,L] using cubeUnits_le_localWork (a:=a) (D:=D) (α:=α) (ξ:=ξ) hn hr hR
  have wp : 1 ≤ Q := Nat.one_le_pow _ _ (GeometryAdviceRate.indexWidths hr hn).1
  have widthBound : w+1 ≤ 2*Q := by change w≤Q at word; omega
  have xL : ((X*Q:ℕ):ℝ) ≤ L := by
    dsimp [Q,L,localWork,X]
    push_cast
    gcongr
    exact le_add_of_nonneg_right (by positivity)
  have rX : r ≤ X := Nat.le_mul_of_pos_right r (Nat.le_floor (by simpa using Real.one_le_rpow npos (show 0≤1-ξ by linarith)))
  have powerL : (powers:ℝ) ≤ L := by
    have logQ := Nat.pow_le_pow_right (GeometryAdviceRate.indexWidths hr hn).1 hD
    rw [pow_one] at logQ
    exact ((Nat.cast_le (α:=ℝ)).mpr (source.trans (Nat.mul_le_mul rX logQ))).trans xL
  have wordX : (((w+1)*X:ℕ):ℝ) ≤ 2*L := by
    have bound : (w+1)*X ≤ 2*(X*Q) := by
      simpa [Nat.mul_assoc,Nat.mul_comm X Q] using Nat.mul_le_mul_right X widthBound
    calc
      _ ≤ 2*((X*Q:ℕ):ℝ) := by exact_mod_cast bound
      _ ≤ _ := mul_le_mul_of_nonneg_left xL (by norm_num)
  have denseP := ((Nat.cast_le (α:=ℝ)).mpr entry).trans (rp.trans pubBase)
  have pp := (Nat.cast_le (α:=ℝ)).mpr (Nat.le_mul_of_pos_left (2^p+2^d) (Nat.zero_lt_succ w))
  have pcap := pp.trans slotsP
  have hfix : (fixed:ℝ) ≤ fixed*P := by simpa using mul_le_mul_of_nonneg_left oneP (Nat.cast_nonneg fixed)
  have ncap : ((l.deliveryCount+groups.groups.choose 2:ℕ):ℝ) ≤ 2*P := by
    have data : l.deliveryCount ≤ desc := by dsimp [desc,descriptorTicks]; change _ ≤ _+(41+l.deliveryCount*43+5)+_; omega
    have sq : groups.groups.choose 2 ≤ l.labels^2 := by
      rw [Nat.choose_two_right,pow_two]
      exact (Nat.div_le_self ..).trans (Nat.mul_le_mul gz ((Nat.sub_le ..).trans gz))
    have sqP : (l.labels:ℝ)^2 ≤ P := by
      have zR : (l.labels:ℝ) ≤ (Z:ℝ)+R := by rw [ZZ]; exact le_add_of_nonneg_right (Nat.cast_nonneg _)
      have top := (pow_le_pow_left₀ (Nat.cast_nonneg _) zR 2).trans (pow_le_pow_right₀
        (show 1≤(Z:ℝ)+R by linarith [Nat.cast_nonneg (α:=ℝ) Z]) (by decide : 2≤10))
      exact top.trans (by dsimp [P,publicWork,Z]; linarith [show 0 ≤ (r:ℝ)*(n:ℝ)^(19/20:ℝ) by positivity])
    have d' := ((Nat.cast_le (α:=ℝ)).mpr data).trans cd
    have s' := (Nat.cast_le (α:=ℝ)).mpr sq
    push_cast at s' ⊢
    linarith
  apply rounded r R _ core _ hr hR (smaller ω (min_le_left ..)) teamGrowth coreCap ncap
  change (completeAllowance core geoT fixed R V entries cells bundles desc decl l.cableCount U F H w (2^p+2^d) powers X dense:ℝ) ≤
    core+C₀*(P+L)
  unfold completeAllowance
  have lx : 0 ≤ L := by dsimp [L,localWork]; positivity
  have px : 0 ≤ P := zero_le_one.trans oneP
  have scaled f := mul_le_mul_of_nonneg_left Ucap (Nat.cast_nonneg f)
  have addP : 0 ≤ ((F:ℝ)+64*H+512*(a+bits+1))*P := by positivity
  have addL : 0 ≤ (fixed:ℝ)*L := by positivity
  have fU := scaled F
  have hU := scaled H
  dsimp only [C₀]
  push_cast at dirs cables wordX slotsP ch prodP pcap ⊢
  nlinarith only [dirs,cables,wordX,slotsP,ch,prodP,pcap,outP,cd,geomP,denseP,powerL,fU,hU,hfix,oneP,px,lx,addP,addL,
    show 0 ≤ ((F:ℝ)+64*H)*P by positivity]

end RoutingISA.Evaluator.ScheduleClock

end BorderVNP
end Computability
end OAI
