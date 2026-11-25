import OAI.Hierarchy.DescentIssuedOwnerBoard
import OAI.Hierarchy.DescentOrdinaryDonorHeaders
import OAI.Hierarchy.DescentPrivateNativePhase
import OAI.Hierarchy.DescentStaticWordCheap

namespace OAI
/-! # Uniform owner, rank and hub publication on all native states -/
namespace Hierarchy.DescentRawCablePanel.DepotRAM.Resident.Dynamic
open DescentPacking.PackedMatch.Local DescentSIMDLookup ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open DescentHaloWalkRAM DescentSixParty.Chronology
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section

structure Layout where
  ownerBase : ℕ
  walks : DescentHaloWalkRAM.Banks
  ranks : Ranks.Columns
  hub : Bank
  rankOut : ℕ
  hubOut : ℕ
  literal : ℕ

variable (L : Layout) (r D p d cap profile H G M w : ℕ) (e : Expr)
local notation "P" => breadth D
local notation "rows" => H*chunks G M
local notation "a" => Owners.inputBits r D p d
local notation "b" => (Owners.digits r D d*3)*r
local notation "base" => L.ownerBase
local notation "render_" => Owners.render r D p d cap profile
local notation "out" => Owners.Board.venue a M base rows
local notation "publish" => Owners.Board.issue cap profile base e H G M w r D p d
local notation "first" m => Owners.Board.issued cap profile base e H G M r D p d m
local notation "books" => DonorChartBook.install H G M P L.literal w
local notation "second" mem => DonorHeaders.after L.walks L.ranks L.hub L.rankOut L.hubOut H D mem

def phase : NativePhase w where
  program := publish |>.seq ((DonorHeaders.schedule L.walks L.ranks L.hub L.rankOut L.hubOut H D w).seq books)
  ticks := Owners.Board.ticks a H G M e+
    (DonorHeaders.clocks L.walks L.ranks L.hub H D+(4+10*DonorChartBook.words H G M P))
  image m := DonorChartBook.image H G M P L.literal (second (first m))
  cheap := cheap_seq (cheap_seq (cheap_seq (@scan_cheap _ _ _ _) (@DescentStaticWordColumn.cheap _ _ _ _)) (@scan_cheap _ _ _ _))
    (cheap_seq (cheap_seq (cheap_seq (@scan_cheap _ _ _ _) (@scan_cheap _ _ _ _)) (@scan_cheap _ _ _ _)) (@DescentStaticWordColumn.cheap _ _ _ _))

structure Room : Prop where
  operand : e.Fits w base
  packed : M*max a b≤w/2
  owner_end : out+rows≤L.ranks.endpoints.base
  walk : DescentHaloWalkRAM.Fits L.walks L.ranks.endpoints.base H D w
  order : Ranks.Fits L.ranks L.rankOut H P w
  separated : L.rankOut+H*P≤L.hubOut
  table : L.hubOut+H*P≤L.literal
  ceiling : L.literal+DonorChartBook.words H G M P<2^w
  flag : L.hub.Fits w L.ranks.endpoints.base

theorem any_frame (room : Room L r D p d H G M w e) (m : Memory w) :
    (phase L r D p d cap profile H G M w e).Runs m ∧
      ∀i,i<base ∨ L.literal+DonorChartBook.words H G M P≤ i→(phase L r D p d cap profile H G M w e).image m i=m i := by
  let shadow:=image base rows e m
  let api:=Book.banks (Owners.Board.rom base rows) a H G M (Owners.Board.bank base rows)
  let fixed:=Book.image render_ H G M (Owners.Board.rom base rows) shadow
  let pkt:=first m
  let paths:=image L.ranks.endpoints.base (H*P) (body L.walks H D 4) pkt
  let numbered:=image L.rankOut (H*P) (Ranks.body L.ranks P) paths
  let marked:=second pkt
  have occupied : rows≤(Owners.Board.bank base rows).size:=Nat.le_pow_clog (by decide) _
  have firstGap : base+rows≤Owners.Board.rom base rows:=Nat.add_le_add_left occupied _
  have secondGap : Owners.Board.rom base rows+Book.words a H G M≤out:=by dsimp [Owners.Board.venue,Book.words];omega
  have right:=room.owner_end
  have names:=room.order
  have ends : L.ranks.endpoints.base+H*P≤L.rankOut:=(Nat.add_le_add_left names.sizeEnd _).trans names.endpoints.2.2
  have br:=room.separated
  have more:=room.table
  have upper:=room.ceiling
  have bound : out+rows<2^w:=by omega
  have fitsBank (B : Bank) (ok : B.base+B.size≤out) : B.Fits w out:=
    ⟨Nat.two_pow_pos _,(Nat.le_add_left ..).trans_lt (by omega : B.base+B.size<2^w),ok⟩
  have f : DescentSIMDLookup.Fits api a b M H G w out := by
    refine ⟨fitsBank _ (by change Owners.Board.rom base rows≤out;omega),fitsBank _ ?_,fitsBank _ le_rfl,
      occupied,rfl,occupied,bound,room.packed⟩
    change Owners.Board.rom base rows + 2^(a*M) ≤
      (Owners.Board.rom base rows + 2^(a*M)) + (Owners.Board.bank base rows).size
    exact Nat.le_add_right _ _
  have narrow (B : Bank) (fit : B.Fits w L.ranks.endpoints.base) : B.Fits w L.hubOut:=
    ⟨fit.1,fit.2.1,by have:=fit.2.2;omega⟩
  have far : L.ranks.endpoints.Fits w L.hubOut:=⟨names.endpoints.1,names.endpoints.2.1,by have:=names.endpoints.2.2;omega⟩
  have hfit : (DonorHeaders.hubExpr L.ranks.endpoints L.hub H).Fits w L.hubOut:=by
    simp [DonorHeaders.hubExpr,Expr.Fits,far,narrow _ room.flag]
  have old : (scan w base rows e).Exec m shadow (4+rows*(2*e.work+4)) :=
    scan_exec base rows e m room.operand (by omega)
  have literals : (Book.install render_ H G M w (Owners.Board.rom base rows)).Exec shadow fixed (4+10*Book.words a H G M) :=
    DescentStaticWordColumn.mount (Owners.Board.rom base rows) (Book.words a H G M) (Book.literal render_ H G M) shadow (by omega)
  have lookupTicks : 4+rows*(2*(lookup api).work+4) = 4+44*rows := by
    rw [lookup_work, show 2*20+4=44 by decide, Nat.mul_comm rows 44]
  have printed : (program api out H G M w).Exec fixed pkt (4+44*rows):=by
    rw [← lookupTicks]
    exact scan_exec out rows (lookup api) fixed
      (by simp [lookup,Expr.Fits,f.source,f.mask,f.dictionary]) bound
  have walkRun : (scan w L.ranks.endpoints.base (H*P) (body L.walks H D 4)).Exec pkt paths
      (4+H*P*(2*(body L.walks H D 4).work+4)) :=
    scan_exec _ _ _ pkt (body_fits L.walks _ room.walk 4) (by omega)
  have nums : (scan w L.rankOut (H*P) (Ranks.body L.ranks P)).Exec paths numbered
      (4+H*P*(2*(Ranks.body L.ranks P).work+4)) :=
    scan_exec _ _ _ paths (Ranks.body_fits L.ranks _ names) names.output
  have flags : (scan w L.hubOut (H*P) (DonorHeaders.hubExpr L.ranks.endpoints L.hub H)).Exec numbered marked
      (4+H*P*(2*(DonorHeaders.hubExpr L.ranks.endpoints L.hub H).work+4)) :=
    scan_exec _ _ _ numbered hfit (by omega)
  have booksRun : (DonorChartBook.install H G M P L.literal w).Exec marked
      (DonorChartBook.image H G M P L.literal marked) (4+10*DonorChartBook.words H G M P) :=
    DescentStaticWordColumn.mount L.literal (DonorChartBook.words H G M P) (DonorChartBook.data H G M P) marked upper
  constructor
  · intro pReg rReg kReg machine pc reg pub exit installed advice cfg mem enter same
    exact Procedure.Exec.then (Procedure.Exec.then (Procedure.Exec.then old literals) printed)
      (Procedure.Exec.then (Procedure.Exec.then (Procedure.Exec.then walkRun nums) flags) booksRun)
      machine pc reg pub exit installed advice cfg mem enter same
  · intro i hi
    have away (start len : ℕ) (lo : base ≤ start) (top : start+len ≤ L.literal+DonorChartBook.words H G M P) :
        i < start ∨ start+len ≤ i := hi.imp (fun h => h.trans_le lo) (fun h => top.trans h)
    exact (DescentStaticWordColumn.frame L.literal (DonorChartBook.words H G M P) (DonorChartBook.data H G M P)
        marked i (away _ _ (by omega) le_rfl)).trans
      ((ProtocolRAMGeneratedWrite.frame_image L.hubOut (H*P) (DonorHeaders.hubExpr L.ranks.endpoints L.hub H)
        numbered i (away _ _ (by omega) (by omega))).trans
      ((ProtocolRAMGeneratedWrite.frame_image L.rankOut (H*P) (Ranks.body L.ranks P) paths i (away _ _ (by omega) (by omega))).trans
      ((ProtocolRAMGeneratedWrite.frame_image L.ranks.endpoints.base (H*P) (body L.walks H D 4) pkt i (away _ _ (by omega) (by omega))).trans
      ((ProtocolRAMGeneratedWrite.frame_image out rows (lookup api) fixed i (away _ _ (by omega) (by omega))).trans
      ((DescentStaticWordColumn.frame (Owners.Board.rom base rows) (Book.words a H G M) (Book.literal render_ H G M)
        shadow i (away _ _ (by omega) (by omega))).trans
      (ProtocolRAMGeneratedWrite.frame_image base rows e m i (away _ _ le_rfl (by omega))))))))

theorem any (room : Room L r D p d H G M w e) (m : Memory w) :
    (phase L r D p d cap profile H G M w e).Runs m ∧
      ∀i,i<base→(phase L r D p d cap profile H G M w e).image m i=m i := by
  obtain ⟨run,fr⟩:=any_frame L r D p d cap profile H G M w e room m
  exact ⟨run,fun i hi=>fr i (.inl hi)⟩

end
end Hierarchy.DescentRawCablePanel.DepotRAM.Resident.Dynamic

end OAI
