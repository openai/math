import OAI.Hierarchy.DescentResetPreparedSplits

namespace OAI
/-! # Numeric address bounds of every operand used by the reset stencil -/
namespace Hierarchy.DescentPlainTerminal.Suffix.StencilBook
open DescentSixParty.PackedFlow DescentGL DescentGLPacked.BankImage DescentColonies DescentPackedColony
open DescentSIMDLookup DescentIssuedFallbackPanel DescentPackedColony.Phase ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable (S : StencilBook) {w : ℕ}

/-- These are the original scalar count, selected depths, real hub flags and measured spectrum. -/
structure Sources where
  count : Expr
  levels : Bank
  hubs : Bank
  spectrum : Bank
  roster : Bank
  precision : ℕ

def Sources.head (X : Sources) : Padded.Heads := ⟨X.count,X.levels,X.hubs⟩
def Sources.paid (X : Sources) (base out : ℕ) : Padded.Paid S.degree :=
  ⟨X.levels,X.spectrum,(S.chosen base out X.roster).ports,X.precision,S.levels,S.total⟩

def inputs (X : Sources) (base out g : ℕ) : Stencil.Inputs S.m S.c (S.degree+S.degree) :=
  let C:=S.readers base
  { header:=X.head.field (S.header base) g S.c
    portHeader:=(Sources.paid S X base out).field (S.header base) S.c
    weights:=.lookup (S.weightBank out) .row
    flows:=fun j=>.lookup (S.bankAt out (Channels.flowIndex S.m (Padded.side j))) .row
    splits:=.lookup ((S.chosen base out X.roster).source S.r) .row
    planes:=fun d=>PackedOrder.projected (S.narrow base) (.lookup (S.bankAt out (Channels.planeIndex S.degree d)) .row)
    broadcastBank:=C.column (.inl ())
    mask:=C.mask
    amount:=fun x=>C.column (.inr (.inl (.inl x)))
    vote:=fun i x=>C.column (.inr (.inl (.inr (i,x))))
    planeTables:=StencilTables.tabs C.planeBase (2^C.r) C.m C.M
    compare:=fun i x=>C.column (.inr (.inr (i,x))) }

/-- The final read of two remixed low corners compares their original indices. -/
def orderExpr (X : Sources) (base out g i x : ℕ) : Expr :=
  let row (z : ℕ) : Block S.r:=⟨z%2^S.r,Nat.mod_lt _ (Nat.two_pow_pos _)⟩
  ((S.readers base).inputs (S.inputs X base out g)).field (.inr (.inr (.inl (row i,row x))))

structure OldOrder (X : Sources) (base out g c : ℕ) {m : ℕ} (basis : DescentGL.Layout m) (mem : Memory w) : Prop where
  fits (i x : Block (m-c)) : (S.orderExpr X base out g i.val x.val).Fits w (S.endAddress base)
  read : ∀(small : c≤ m) (i x : Block (m-c)), DescentPackedZip.Source (S.orderExpr X base out g i.val x.val)
    (fun (_:Fin S.hosts) (hi:Block c)=>if (rearrange basis).symm (join small hi i)<(rearrange basis).symm (join small hi x)
      then (1:Cell S.n) else 0) S.M mem

  accessible : let L:=S.chosen base out X.roster
    Accessible L.ports (L.source S.r) S.hosts (2^S.c) S.M w (S.afterHeader base)
  mounted (rs : Fin S.hosts→Fin S.degree→Option (Fin S.hosts))
    (original : ∀v j,mem (X.roster.base+(v.val*S.degree+j.val))=(target (rs v j):Word w)) :
    Mounted (S.chosen base out X.roster).ports rs mem (2^S.c) S.M
  /-- The scalar address tables mounted by `scalar_issue` survive the final two stencil scans. -/
  resident : (S.header base).chart.Resident mem

structure Sources.Before (X : Sources) (w base : ℕ) : Prop where
  count : X.count.Fits w base
  levels : X.levels.Fits w base
  hubs : X.hubs.Fits w base
  spectrum : X.spectrum.Fits w base
  roster : X.roster.Fits w base

theorem result_bank (A : Frame.Chart) (k s b Δ M : ℕ) :
    let B:=(A.issued Δ k b M).source s
    B.size=A.page ∧ B.base+B.size≤A.fresh Δ k+s*A.page := by
  cases s with
  | zero=>
    refine ⟨rfl,?_⟩
    change (A.atSlot (.initial : Frame.Slot Δ k)).base+A.page ≤ A.fresh Δ k+0*A.page
    rw [Nat.zero_mul,Nat.add_zero]
    exact Frame.slot_before A (.initial : Frame.Slot Δ k)
  | succ s=>exact ⟨rfl,by change A.fresh Δ k+s*A.page+A.page≤A.fresh Δ k+(s+1)*A.page;
                          rw [Nat.succ_mul,Nat.add_assoc]⟩

structure Geometry (X : Sources) (base out w : ℕ) : Prop where
  old : X.Before w base
  ports : S.hosts*S.degree≤X.roster.size
  small : out+((1+S.maxPorts)+S.m)*S.rows≤base
  safe : S.afterHeader base<2^w

theorem banks (X : Sources) (base out : ℕ) (B : Geometry S X base out w) :
    let H:=S.header base
    let L:=S.chosen base out X.roster
    let last:=L.source S.r
    let floor:=S.afterHeader base
    H.pos.Fits w floor ∧ H.depth.Fits w floor ∧ H.lead.Fits w floor ∧
    (Cutoff.levelBank H.stop S.levels).Fits w floor ∧ (Cutoff.tableBank H.stop S.levels S.total).Fits w floor ∧
    (S.narrow base).Fits w floor ∧
    Accessible L.ports last S.hosts (2^S.c) S.M w floor ∧
    (∀i : Channels.Index S.degree S.m,(S.bankAt out i).Fits w floor) ∧ base≤floor := by
  let H:=S.header base
  let A:=S.layer base out X.roster
  let L:=S.chosen base out X.roster
  let N:=S.narrow base
  let floor:=S.afterHeader base
  have dim:H.origin≤H.stop:=by dsimp [PortLevels.AddressBook.stop,PortLevels.AddressBook.lead,PortLevels.AddressBook.depth,
    PortLevels.AddressBook.pos];omega
  have stop:H.stop≤N.base:=(Nat.le_add_right H.stop _).trans (Nat.le_add_right ..)
  have last:N.base≤floor:=Nat.le_add_right ..
  have prev:=dim.trans (stop.trans last)
  have beginAt:base≤A.origin:=Nat.le_add_right ..
  have age:A.origin≤A.fresh S.degree S.r:=Nat.le_add_right ..
  have land:=S.split_end base X.roster (S.weightBank out)
  change A.fresh S.degree S.r+(S.r+1)*A.page=H.origin at land
  have before:A.origin≤H.origin:=by omega
  have upper:=B.safe
  have old:=B.old.roster
  have initial : X.roster.Fits w A.origin:=⟨old.1,old.2.1,old.2.2.trans beginAt⟩
  have room:=S.layer_room base out X.roster (by simpa only [rows,Nat.mul_assoc] using B.small) initial B.ports (prev.trans_lt upper)
  have low:=Frame.low A room
  have ready (b : Bank) (endAt:b.base+b.size≤floor) : b.Fits w floor:=
    ⟨Nat.two_pow_pos _,by omega,endAt⟩
  have geometry:H.pos.base+H.pos.size≤H.stop ∧ H.depth.base+H.depth.size≤H.stop ∧ H.lead.base+H.lead.size≤H.stop:=by
    dsimp [PortLevels.AddressBook.stop,PortLevels.AddressBook.lead,PortLevels.AddressBook.depth,PortLevels.AddressBook.pos]
    omega
  have ends:=result_bank A S.r S.r S.b S.degree S.M
  have stopAt:L.fresh≤floor:=by change A.fresh S.degree S.r≤_;omega
  have first(s : Frame.Slot S.degree S.r) : (A.atSlot s).Fits w floor:=
    ready _ ((Frame.slot_before A s).trans stopAt)
  have previous:(L.source S.r).Fits w floor:=ready _ (by
    rw [Nat.succ_mul] at land;exact ends.2.trans (by omega))
  refine ⟨ready _ (geometry.1.trans (stop.trans last)),ready _ (geometry.2.1.trans (stop.trans last)),
    ready _ (geometry.2.2.trans (stop.trans last)),ready _ ?_,ready _ ?_,ready _ le_rfl,
    ⟨fun i=>first (.id i),fun _=>room.cells,ready _ (old.2.2.trans ((beginAt.trans before).trans prev)),
      B.ports,first .offsets,room.sites,first .chunks,room.cells,previous,by
        change S.rows ≤ ((A.issued S.degree S.r S.b S.M).source S.r).size
        rw [ends.1]
        exact room.cells⟩,?_,
    (beginAt.trans before).trans prev⟩
  · change H.stop+2^S.levels≤floor
    exact (Nat.le_add_right (H.stop+2^S.levels) _).trans last
  · exact last
  · intro i
    apply Channels.short_fits
    · have c:=Nat.add_le_add_right B.small (2^(Nat.clog 2 S.rows))
      exact (by simpa only [start,rows,Nat.mul_assoc] using c : out+_+_≤S.start base).trans (before.trans prev)
    · exact upper

theorem fit (X : Sources) (base out g : ℕ) (B : Geometry S X base out w) :
    Stencil.Operands (S.readers base) (S.inputs X base out g) w := by
  let H:=S.header base
  let P:=S.inputs X base out g
  let L:=S.chosen base out X.roster
  obtain ⟨pos,levels,leads,lowCut,cut,narrow,ports,bank,before⟩:=S.banks X base out B
  have lift {T:Bank} (h:T.Fits w base) : T.Fits w (S.afterHeader base):=⟨h.1,h.2.1,h.2.2.trans before⟩
  have floor:=S.afterHeader base
  have host : H.host.Fits w (S.afterHeader base):=⟨pos,trivial⟩
  have d (e:Expr) (ok:e.Fits w (S.afterHeader base)) : (H.levelAt X.levels e).Fits w (S.afterHeader base):=
    ⟨lift B.old.levels,levels,ok⟩
  constructor
  · intro j
    change (X.head.field H g S.c j).Fits w (S.afterHeader base)
    unfold Padded.Heads.field
    split_ifs <;> exact ⟨host,ProtocolRAMGeneratedWrite.fits_mono _ before B.old.count,
      by first | exact ⟨d _ host,trivial⟩ | exact trivial | exact ⟨lift B.old.hubs,host⟩,trivial⟩
  · intro j s
    let i:=Padded.side j
    change ((Sources.paid S X base out).field H S.c j s).Fits w (S.afterHeader base)
    have u : (neighborID L.ports i).Fits w (S.afterHeader base):=⟨ports.roster,ports.ids i,trivial⟩
    have a:=d _ host
    have b:=d _ u
    have dep:(Cutoff.level (H.levelAt X.levels H.host) (H.levelAt X.levels (neighborID L.ports i))).Fits w (S.afterHeader base):=
      ⟨a,b,b,a⟩
    unfold Padded.Paid.field
    split_ifs <;> exact ⟨u,trivial,trivial,by first | exact ⟨dep,trivial⟩ |
      exact ⟨cut,⟨lowCut,dep⟩,⟨⟨lift B.old.spectrum,⟨⟨leads,host⟩,trivial⟩⟩,trivial⟩⟩⟩
  · exact ⟨bank _,trivial⟩
  · intro j;exact ⟨bank _,trivial⟩
  · exact ⟨ports.source,trivial⟩
  · intro j;exact ⟨narrow,bank _,trivial⟩

end
end Hierarchy.DescentPlainTerminal.Suffix.StencilBook

end OAI
