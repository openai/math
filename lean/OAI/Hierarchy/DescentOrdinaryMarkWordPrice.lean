import OAI.Hierarchy.DescentMaterialTariffNumbers
import OAI.Hierarchy.DescentDatedOrdinaryMark
import OAI.ThreeFlat.Routing.CallBatches

namespace OAI
/-! The word price of reading each genuine source bit at the two physical SIMD pitches. -/
namespace Hierarchy.DescentOrdinaryMarkProject.Shape
open DescentSIMDLookup DescentDyadicSpan
open ThreeFlat.Routing
noncomputable section

def tariff (s : Shape) :=
  4+10*s.portWords+7*(15*(s.portWords+1))+
    bill s.paths s.slots s.oldHosts s.hosts s.groups s.blocks s.degree s.cap s.oldLanes s.lanes

def scale (s : Shape) := 131072*(s.paths+2)*(s.slots+1)*(s.blocks+1)
def population (s : Shape) :=
  s.oldHosts+s.hosts+s.sourceRows+s.oldHosts*chunks s.groups s.lanes+s.hosts*chunks s.groups s.lanes

private theorem joined_chunks (G X M : ℕ) (hx : 0<X) (hm : 0<M) :
    chunks (G*X) (M*X)≤chunks G M := by
  change (G*X) ⌈/⌉ (M*X)≤chunks G M
  apply (ceilDiv_le_iff_le_mul (Nat.mul_pos hm hx)).2
  calc G*X≤(M*chunks G M)*X := Nat.mul_le_mul_right _ (CallPool.count_le_batches_mul G M hm)
       _=M*X*chunks G M := by ring

theorem tariff_le (s : Shape) (h : ℕ) (ha : 0<s.oldLanes) (hm : 0<s.lanes) (hx : 0<s.blocks)
    (handles : DescentSignedCableCodec.width s.degree s.cap*s.oldLanes≤h/2)
    (input : s.oldLanes≤h/2) (output : s.blocks*s.lanes≤h/2) :
    s.tariff≤ s.scale*(s.population+shared h) := by
  let n:=s.paths*s.slots
  let E:=s.population+shared h
  let N:=s.oldHosts
  let H:=s.hosts
  let G:=s.groups
  let X:=s.blocks
  let A:=s.oldLanes
  let M:=s.lanes
  have e₁ : 1≤E :=by change 0 < E; dsimp [E,shared]; positivity
  have slab : (h+2)^2*2^(h/2)≤E :=Nat.le_add_left ..
  have page : 2^(h/2)≤E :=
    (Nat.le_mul_of_pos_left _ (by positivity : 0<(h+2)^2)).trans slab
  have hA : A≤h := input.trans (Nat.div_le_self ..)
  have hMX : M*X≤h := by simpa only [Nat.mul_comm M X] using output.trans (Nat.div_le_self ..)
  have pieces : Overlap.pieces (G*X) A (M*X)+1≤h+2 :=by
    have cap : chunks (M*X) A≤M*X :=by
      change (M*X) ⌈/⌉ A≤M*X
      apply (ceilDiv_le_iff_le_mul ha).2
      exact Nat.le_mul_of_pos_left _ ha
    have:=min_le_right (chunks (G*X) A) (chunks (M*X) A+1)
    change min _ _+1≤_
    omega
  have overlap : (Overlap.pieces (G*X) A (M*X)+1)*(A+1)*2^(1*A)≤E :=by
    apply le_trans _ slab
    rw [pow_two, Nat.one_mul]
    exact Nat.mul_le_mul (Nat.mul_le_mul pieces (by omega)) (Nat.pow_le_pow_right (by decide) input)
  have hp : 2^DescentOrdinarySignedMeta.MarkGather.width s.degree s.cap A≤E :=
    (Nat.pow_le_pow_right (by decide) handles).trans page
  have proj : X*2^((1*X)*M)≤X*E :=
    Nat.mul_le_mul_left _ ((Nat.pow_le_pow_right (by decide) (by simpa only [Nat.one_mul] using output)).trans page)
  have sc : N*chunks (G*X) A≤E :=by dsimp [E,population,sourceRows,N,G,X,A];omega
  have nc : N*chunks G M≤E :=by dsimp [E,population,N,G,M];omega
  have hc : H*chunks G M≤E :=by dsimp [E,population,H,G,M];omega
  have n₀ : N≤E :=by dsimp [E,population,N];omega
  have old : (n*N)*chunks (G*X) A≤n*E :=by rw [Nat.mul_assoc];exact Nat.mul_le_mul_left _ sc
  have fresh : (n*N)*chunks (G*X) (M*X)≤n*E :=by
    rw [Nat.mul_assoc]
    exact Nat.mul_le_mul_left _ ((Nat.mul_le_mul_left _ (joined_chunks G X M hx hm)).trans nc)
  have fieldRows : n*DescentVectorBookReshape.rows N 1 G X M≤n*(X*E) :=by
    simp only [DescentVectorBookReshape.rows,Nat.mul_one];gcongr
  have nE := Nat.le_mul_of_pos_right n e₁
  have vol : DescentResetStemProject.volume n N G X 1 A M≤
      n*E+n*E+n*E+E+X*E+n*(X*E)+E+E := by
    dsimp only [DescentResetStemProject.volume,Overlap.rows,DescentVectorBookReshape.dictionaryWords]
    gcongr
  have span₀ := span_le (1+N+N*chunks (G*X) A)
  have pitch : s.pitch≤7*E :=by
    change span (1+N+N*chunks (G*X) A)≤_
    omega
  have port : s.portWords≤(s.paths+2)*(7*E) := Nat.mul_le_mul_left _ pitch
  have extra : n*(4+N*chunks (G*X) A*(2*57+4))≤n*(4*E+E*(2*57+4)) :=by
    gcongr
    exact Nat.le_mul_of_pos_right _ e₁
  change 4+10*s.portWords+7*(15*(s.portWords+1))+
    ((4+10*(4*2^DescentOrdinarySignedMeta.MarkGather.width s.degree s.cap A))+7*(15*(4*2^DescentOrdinarySignedMeta.MarkGather.width s.degree s.cap A+1))+
      (4096*DescentResetStemProject.volume n N G X 1 A M+(4+n*(4+N*chunks (G*X) A*(2*57+4)))+
       7*(15+n*(11+4*57)))+((4+10*(H*chunks G M))+7*(15*(H*chunks G M+1))))≤ s.scale*E
  calc
    _ ≤ 4*E+10*((s.paths+2)*(7*E))+7*(15*((s.paths+2)*(7*E)+E))+
      ((4*E+10*(4*E))+7*(15*(4*E+E))+
       (4096*(n*E+n*E+n*E+E+X*E+n*(X*E)+E+E)+(4*E+n*(4*E+E*(2*57+4)))+
         7*(15*E+(n*E)*(11+4*57)))+((4*E+10*E)+7*(15*(E+E)))) :=by
      gcongr <;> first | assumption | exact Nat.le_mul_of_pos_right _ e₁
    _ ≤ _ := by dsimp only [scale,n,X];ring_nf;omega

theorem word_tariff (s : Shape) (h w u₀ u₁ ratio : ℕ) (old : s.oldLanes=DescentSIMDLookup.lanes h u₀)
    (fresh : s.lanes=DescentSIMDLookup.lanes h u₁) (oldPos : 0<u₀) (newPos : 0<u₁) (oldWide : 2*u₀≤h)
    (newWide : 2*u₁≤h) (blocks : 0<s.blocks) (handleUnit : DescentSignedCableCodec.width s.degree s.cap≤u₀)
    (newUnit : s.blocks≤u₁) (machine : w≤ratio*h) :
    s.tariff*w ≤ (ratio*s.scale*(4*s.blocks+12))*
        ((s.oldHosts+s.hosts)*h+(s.oldHosts+s.hosts)*s.groups*(u₀+u₁))+
      (ratio*s.scale)*(shared h*h) := by
  have a := occupancy h u₀ oldPos oldWide
  have b := occupancy h u₁ newPos newWide
  have h₀ : u₀*s.oldLanes≤h/2 :=by rw [old,Nat.mul_comm];exact lanes_fit h u₀
  have h₁ : u₁*s.lanes≤h/2 :=by rw [fresh,Nat.mul_comm];exact lanes_fit h u₁
  have count:=s.tariff_le h (old ▸ a.1) (fresh ▸ b.1) blocks
    ((Nat.mul_le_mul_right _ handleUnit).trans h₀) ((Nat.le_mul_of_pos_left _ oldPos).trans h₀)
    ((Nat.mul_le_mul_right _ newUnit).trans h₁)
  have src:=volume s.oldHosts (s.groups*s.blocks) h u₀ oldPos oldWide
  have localRows:=volume s.oldHosts s.groups h u₁ newPos newWide
  have hostRows:=volume s.hosts s.groups h u₁ newPos newWide
  rw [←old] at src
  rw [←fresh] at localRows hostRows
  have total : s.population*h≤(4*s.blocks+12)*((s.oldHosts+s.hosts)*h+
      (s.oldHosts+s.hosts)*s.groups*(u₀+u₁)) :=by
    dsimp only [population,sourceRows];simp only [Nat.add_mul]
    calc
      _ ≤ s.oldHosts*h+s.hosts*h+(s.oldHosts*h+4*s.oldHosts*(s.groups*s.blocks)*u₀)+
          (s.oldHosts*h+4*s.oldHosts*s.groups*u₁)+(s.hosts*h+4*s.hosts*s.groups*u₁) :=by gcongr
      _ ≤ _ :=by ring_nf;omega
  calc
    _≤(s.scale*(s.population+shared h))*(ratio*h) :=Nat.mul_le_mul count machine
    _=(ratio*s.scale)*(s.population*h)+(ratio*s.scale)*(shared h*h) :=by ring
    _≤(ratio*s.scale)*((4*s.blocks+12)*((s.oldHosts+s.hosts)*h+(s.oldHosts+s.hosts)*s.groups*(u₀+u₁)))+
        (ratio*s.scale)*(shared h*h) := Nat.add_le_add_right (Nat.mul_le_mul_left _ total) _
    _=_ := by ring

end
end Hierarchy.DescentOrdinaryMarkProject.Shape

namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentDatedAddressBook DescentOrdinaryMarkProject DescentStaticWordColumn DescentPacking.PackedMatch.Local.Stage
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
variable {F P : Type} [Field F] (v : PhysicalOrdinary F P) (floor : ℕ) (input : Dated.Operands) {w : ℕ}

theorem mark_tariff (h : v.MarkRoom floor input w) (old : 0<v.markShape.oldLanes) :
    (v.mark floor input w).ticks+7*names (v.mark floor input w).program≤v.markShape.tariff :=by
  let s:=v.markShape
  let f:=v.peerTail floor
  have core:=v.mark_core_room floor input h
  have paid:=native_bill (s.portChart f (v.markVisited floor)) (v.markWire input) v.markBorn (s.markStart f)
    v.materialPitch core old
  change (4+10*s.portWords+_)+7*names ((DescentStaticWordColumn.program w f s.portWord s.portWords).seq _)≤_
  rw [names_seq,names_mount]
  change _≤4+10*s.portWords+7*(15*(s.portWords+1))+_
  let corePhase := native (s.portChart f (v.markVisited floor)) (v.markWire input) v.markBorn
    (s.markStart f) v.materialPitch core
  change ((4+10*s.portWords)+corePhase.ticks)+7*(_+names corePhase.program) ≤
    4+10*s.portWords+7*(15*(s.portWords+1))+
      bill s.paths s.slots s.oldHosts s.hosts s.groups s.blocks s.degree s.cap s.oldLanes s.lanes
  change corePhase.ticks+7*names corePhase.program ≤
    bill s.paths s.slots s.oldHosts s.hosts s.groups s.blocks s.degree s.cap s.oldLanes s.lanes at paid
  omega

/-- Word-price of the actual mark program on the two incoming and outgoing lane pitches. -/
theorem mark_word_bill (room : v.MarkRoom floor input w) (h u₀ u₁ ratio : ℕ)
    (old : v.markShape.oldLanes=DescentSIMDLookup.lanes h u₀)
    (fresh : v.markShape.lanes=DescentSIMDLookup.lanes h u₁)
    (oldPos : 0<u₀) (newPos : 0<u₁) (oldWide : 2*u₀≤h) (newWide : 2*u₁≤h)
    (handleUnit : DescentSignedCableCodec.width v.markShape.degree v.markShape.cap≤u₀)
    (newUnit : v.markShape.blocks≤u₁) (machine : w≤ratio*h) :
    let s:=v.markShape
    ((v.mark floor input w).ticks+7*names (v.mark floor input w).program)*w ≤
      (ratio*s.scale*(4*s.blocks+12))*((s.oldHosts+s.hosts)*h+(s.oldHosts+s.hosts)*s.groups*(u₀+u₁))+
        (ratio*s.scale)*(Shape.shared h*h) := by
  have earlier : 0<v.markShape.oldLanes := old ▸ (DescentSIMDLookup.occupancy h u₀ oldPos oldWide).1
  exact (Nat.mul_le_mul_right w (v.mark_tariff floor input room earlier)).trans
    (v.markShape.word_tariff h w u₀ u₁ ratio old fresh oldPos newPos oldWide newWide room.blocks handleUnit newUnit machine)

end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
