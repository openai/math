import OAI.Hierarchy.DescentPackedDonorSpace
import OAI.Hierarchy.DescentStaticWordColumn
import OAI.Hierarchy.DescentPackedFieldLanePrice

namespace OAI
/-! # Native installation of both shared lookups and the partial-donor masks -/

namespace Hierarchy.DescentPackedDonorTables
open ProtocolRAM DescentSIMDLookup Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.RAMSerialization
open ThreeFlat.RAM PhysicalProcedure
open scoped Fin.CommRing Classical
noncomputable section
variable {a b H J M w : ℕ}

def key (width j : ℕ) : Cell width:=⟨j%2^width,Nat.mod_lt _ (Nat.two_pow_pos _)⟩
@[simp] theorem key_val (x : Cell a) : key a x.val=x:=Fin.ext (Nat.mod_eq_of_lt x.isLt)

def literal (banks : Banks) (scoreBase H J M : ℕ) (f : Cell a→Cell (b*11)) (score : Cell b→ℕ)
    (j : ℕ) : ℕ :=
  let at₀:=banks.mask.base+j
  if scoreBase≤ at₀ then DescentPackedScore.chunkScore (M:=M*11) score (key (b*(M*11)) (at₀-scoreBase))
  else if banks.dictionary.base≤ at₀ then (table (M:=M) f (key (a*M) (at₀-banks.dictionary.base))).val
  else if inside : j< H*chunks J M then maskWord (b*11) M J ((row H J M).symm ⟨j,inside⟩).2.val
  else 0

/-- Everything between the first mask and the end of the score ROM is fresh.
The resolver will subsequently write the output area lying in this same interval. -/
def size (banks : Banks) (scoreBase b M : ℕ) := scoreBase+2^(b*(M*11))-banks.mask.base

def program (banks : Banks) (scoreBase H J M w : ℕ) (f : Cell a→Cell (b*11)) (score : Cell b→ℕ) :=
  DescentStaticWordColumn.program w banks.mask.base (literal banks scoreBase H J M f score) (size banks scoreBase b M)

def image (banks : Banks) (scoreBase H J M : ℕ) (f : Cell a→Cell (b*11)) (score : Cell b→ℕ) (m : Memory w) :=
  DescentStaticWordColumn.image banks.mask.base (literal banks scoreBase H J M f score) m (size banks scoreBase b M)

structure Room (banks : Banks) (scoreBase a b H J M w : ℕ) : Prop where
  input : banks.source.base+H*chunks J M≤ banks.mask.base
  masks : banks.mask.base+H*chunks J M≤ banks.dictionary.base
  dictionary : banks.dictionary.base+2^(a*M)≤ scoreBase
  endFit : scoreBase+2^(b*(M*11))< 2^w

theorem install (banks : Banks) (scoreBase : ℕ) (f : Cell a→Cell (b*11)) (score : Cell b→ℕ)
    (x : Fin H→Fin J→Cell a) (m : Memory w) (space : Room banks scoreBase a b H J M w)
    (pins : ∀p : Row H J M,m (banks.source.base+(row H J M p).val)=(data x p).val) :
    let last:=image banks scoreBase H J M f score m
    (program banks scoreBase H J M w f score).Exec m last (4+10*size banks scoreBase b M) ∧
      PinFrame (M:=M) banks f x last ∧
      (∀q : Cell (b*(M*11)),last (scoreBase+q.val)=(DescentPackedScore.chunkScore (M:=M*11) score q:Word w)) ∧
      ∀addr,addr< banks.mask.base→last addr=m addr := by
  dsimp only
  have inp:=space.input
  have masks:=space.masks
  have dict:=space.dictionary
  have fin:=space.endFit
  have maskLow : banks.mask.base≤ banks.dictionary.base := (Nat.le_add_right ..).trans masks
  have dictLow : banks.dictionary.base≤ scoreBase := (Nat.le_add_right ..).trans dict
  have tablePositive : 0< 2^(b*(M*11)) :=Nat.two_pow_pos _
  have count : banks.mask.base+size banks scoreBase b M=scoreBase+2^(b*(M*11)) := by
    unfold size
    omega
  have read (addr : ℕ) (lo : banks.mask.base≤ addr) (hi : addr< scoreBase+2^(b*(M*11))) :
      image banks scoreBase H J M f score m addr=(literal banks scoreBase H J M f score (addr-banks.mask.base):Word w) := by
    have k:=DescentStaticWordColumn.read banks.mask.base (size banks scoreBase b M)
      (literal banks scoreBase H J M f score) m (j:=addr-banks.mask.base) (by omega)
    simpa only [image,Nat.add_sub_of_le lo] using k
  have keep (addr : ℕ) (early : addr< banks.mask.base) : image banks scoreBase H J M f score m addr=m addr :=
    DescentStaticWordColumn.frame _ _ _ _ _ (.inl early)
  refine ⟨DescentStaticWordColumn.mount _ _ _ _ (by omega),⟨?_,?_⟩,?_,keep⟩
  · intro j bit
    rcases j with q|q
    · have hq : q.val< 2^(a*M):=q.isLt
      change wordBits w (image _ _ _ _ _ _ _ m (banks.dictionary.base+q.val)) bit=
        wordBits w ((table (M:=M) f q).val:Word w) bit
      apply congrArg (fun v : Word w=>wordBits w v bit)
      rw [read _ (by omega) (by omega)]
      simp only [literal,Nat.add_sub_of_le (show banks.mask.base≤ banks.dictionary.base+q.val by omega),
        ite_eq_right (show ¬scoreBase≤ banks.dictionary.base+q.val by omega),
        ite_eq_left (Nat.le_add_right _ _),Nat.add_sub_cancel_left,key_val]
    · have hq:=q.isLt
      change wordBits w (image _ _ _ _ _ _ _ m (banks.mask.base+q.val)) bit=
        wordBits w (maskWord (b*11) M J ((row H J M).symm q).2.val:Word w) bit
      apply congrArg (fun v : Word w=>wordBits w v bit)
      rw [read _ (by omega) (by omega)]
      simp only [literal,Nat.add_sub_cancel_left,ite_eq_right (show ¬scoreBase≤ banks.mask.base+q.val by omega),
        ite_eq_right (show ¬banks.dictionary.base≤ banks.mask.base+q.val by omega),dite_eq_left hq]
  · intro p
    exact (keep _ ((Nat.add_lt_add_left (row H J M p).isLt _).trans_le inp)).trans (pins p)
  · intro q
    have hq : q.val< 2^(b*(M*11)):=q.isLt
    rw [read _ (by omega) (by omega)]
    simp only [literal,Nat.add_sub_of_le (show banks.mask.base≤ scoreBase+q.val by omega),
      ite_eq_left (Nat.le_add_right _ _),Nat.add_sub_cancel_left,key_val]

/-- The concrete arena discharges every interval premise of the table installer. -/
theorem arena {base a b H J M w : ℕ} (fit : DescentPackedDonorSpace.endAt base H J M a b< 2^w) :
    Room (DescentPackedDonorSpace.banks base H J M a)
      (DescentPackedDonorSpace.layout base H J M a b).rom.base a b H J M w := by
  let s:=(DescentPackedPrivateSpace.source base H J M).size
  let t:=(DescentPackedPrivateSpace.source (DescentPackedDonorSpace.consumerBase base H J M a) H (J*11) (M*11)).size
  let middle:=base+1+s+s+2^(a*M)
  have less:H*chunks J M< s := (DescentPackedPrivateSpace.source_size base H J M).1
  change middle+1+t+2^(b*(M*11))+_+_+2+1< 2^w at fit
  refine ⟨?_,?_,?_,?_⟩
  · change base+1+H*chunks J M≤ base+1+s
    omega
  · change base+1+s+H*chunks J M≤ base+1+s+s
    omega
  · change middle≤ middle+1+t
    omega
  · change middle+1+t+2^(b*(M*11))< 2^w
    omega

/-- The installer skips the live donor source column. Between the lookup
tables it writes only the bounded tail of the mask and output windows. -/
theorem arena_size (base H J M a b : ℕ) (hm : 0< M) :
    size (DescentPackedDonorSpace.banks base H J M a)
      (DescentPackedDonorSpace.layout base H J M a b).rom.base b M≤
      4*(H*chunks J M)+2^(a*M)+2^(b*(M*11))+5 := by
  let s:=(DescentPackedPrivateSpace.source base H J M).size
  let t:=(DescentPackedPrivateSpace.source (DescentPackedDonorSpace.consumerBase base H J M a)
    H (J*11) (M*11)).size
  have hs:= (DescentPackedPrivateSpace.source_size base H J M).2
  have ht:= (DescentPackedPrivateSpace.source_size (DescentPackedDonorSpace.consumerBase base H J M a)
    H (J*11) (M*11)).2
  change s≤ 2*(H*chunks J M+1) at hs
  change t≤ 2*(H*chunks (J*11) (M*11)+1) at ht
  rw [chunks_group J M 11 hm (by decide)] at ht
  change base+1+s+s+2^(a*M)+1+t+2^(b*(M*11))-(base+1+s)≤_
  rw [show base+1+s+s+2^(a*M)+1+t+2^(b*(M*11))=
    (base+1+s)+(s+t+1+2^(a*M)+2^(b*(M*11))) by ring,Nat.add_sub_cancel_left]
  omega

/-- Includes the cost of creating the fixed tables from literal word instructions. -/
theorem complete_price (base w H J a b grain : ℕ) (C : DescentPackedPrivateAccumulator.Counters)
    (pos : 0< max a (b*11)) (wide : 2*max a (b*11)≤ w) :
    let full:=max a (b*11)
    let m:=lanes w full
    let pages:=size (DescentPackedDonorSpace.banks base H J m a)
      (DescentPackedDonorSpace.layout base H J m a b).rom.base b m
    ((4+10*pages)+((4+44*(H*chunks J m))+(DescentPackedPrivateSum.Layout.billed H (J*11) (m*11)+C.scaling.steps grain)))*w≤
      (131+4*ProtocolRAMPortScale.bitWidth grain)*w+124*(H*w+4*H*J*full)+20*2^(w/2)*w := by
  dsimp only
  let full:=max a (b*11)
  let m:=lanes w full
  have hm:0< m:=(occupancy w full pos wide).1
  have first:=rom_entries a (b*11) w
  obtain ⟨main,last⟩:=DescentSixParty.Chronology.donor_stage_tariff C w H J full b grain pos (Nat.le_max_right _ _) wide
  have count:=arena_size base H J m a b hm
  have vol:=volume H J w full pos wide
  let pages:=size (DescentPackedDonorSpace.banks base H J m a)
    (DescentPackedDonorSpace.layout base H J m a b).rom.base b m
  let rows:=H*chunks J m
  let V:=H*w+4*H*J*full
  let U:=2^(w/2)
  change pages≤4*rows+2^(a*m)+2^(b*(m*11))+5 at count
  change 2^(a*m)≤U at first
  change 2^(b*(m*11))≤U at last
  change rows*w≤V at vol
  have written : pages≤4*rows+U+U+5 := by omega
  have bound₀ : (4+10*pages)*w≤54*w+40*V+20*U*w := by
    calc
      _ ≤ (4+10*(4*rows+U+U+5))*w := Nat.mul_le_mul_right w (Nat.add_le_add_left (Nat.mul_le_mul_left 10 written) 4)
      _ = 54*w+40*(rows*w)+20*U*w :=by ring
      _ ≤ _ :=by gcongr
  let spend:=(4+44*rows)+(DescentPackedPrivateSum.Layout.billed H (J*11) (m*11)+C.scaling.steps grain)
  change spend*w≤(21+(56+4*ProtocolRAMPortScale.bitWidth grain))*w+84*V at main
  change ((4+10*pages)+spend)*w≤(131+4*ProtocolRAMPortScale.bitWidth grain)*w+124*V+20*U*w
  rw [Nat.add_mul]
  exact (Nat.add_le_add bound₀ main).trans_eq (by ring)

end
end Hierarchy.DescentPackedDonorTables

end OAI
