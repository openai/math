import OAI.Hierarchy.DescentResetHeadReaders
import OAI.Hierarchy.DescentResetPortTotal

namespace OAI
/-! # Executing the cut and depth reader on every real or missing signed slot -/
namespace Hierarchy.DescentSixParty.PackedFlow.Padded
open DescentGL DescentColonies DescentSIMDLookup DescentPackedZip DescentIssuedFallbackPanel DescentPackedColony
open DescentPlainTerminal.Suffix DescentPackedFlowPair.Padded DescentPackedFlowReturn DescentPackedWalsh
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM ProtocolRAM
open scoped Classical BigOperators Fin.CommRing
noncomputable section
variable {F P J V : Type} [Field F] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
    {d k H n w : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F} {q ε : ℝ}
    (A : GroupStage W G q ε J V k) (name : V≃Fin H) (L : PortLevels.AddressBook)

structure Paid (D : ℕ) where
  levels : Bank
  spectrum : Bank
  ports : Ports D
  precision : ℕ
  depthBits : ℕ
  totalBits : ℕ

def Paid.field {D} (C : Paid D) (L : PortLevels.AddressBook) (c : ℕ) (p : Fin (D+D)) (s : Fin 2) :=
  let j:=side p
  let u:=neighborID C.ports j
  let v:=L.host
  let left:=L.levelAt C.levels v
  let right:=L.levelAt C.levels u
  let sum:=firstTotal C.spectrum (L.zeroAt v j.val) C.precision
  let term:=if s.val=0 then PortLevels.relative c (Cutoff.level left right)
            else Cutoff.term L.stop C.depthBits C.totalBits left right sum
  PortLevels.protect C.ports L.hosts j term

theorem projected_target (ph : H≤L.hosts) (v : Fin L.hosts) (j : Fin A.degree) :
    roster (D:=A.degree) A name ph v j=(project H v).bind (fun h=>
      (portAt A name (name.symm h) j).map (fun u=>(name u).castLE ph)) := by
  cases hit:project H v with
  | none=>simp [roster,DescentPackedFlowPair.Padded.next,hit]
  | some h=>
    have eqn:=project_some hit ph
    subst v
    simpa [hit,Function.Embedding.trans_apply,Function.comp_def] using socket_padded A name ph (name.symm h) j

theorem Paid.at_port (C : Paid A.degree) (ph : H≤L.hosts) (c f B K cap : ℕ) (depth : V→ℕ)
    (digits : Block L.dimension≃J×Block k) (prior : Bank) (out : ℕ) (mem : Memory w)
    (static : L.chart.Resident mem) (rows : L.pos.Fits w out) (slot : L.depth.Fits w out)
    (leads : L.lead.Fits w out) (level : C.levels.Fits w out) (spec : C.spectrum.Fits w out)
    (usable : Accessible C.ports prior L.hosts L.groups L.batch w out)
    (mounted : Mounted C.ports (roster A name ph) mem L.groups L.batch)
    (levelsFit : L.hosts*(L.dimension+1)≤C.levels.size)
    (spectrumFit : L.hosts*(L.dimension+1+L.degree)*2^L.high≤C.spectrum.size)
    (portsFit : A.degree≤L.degree) (large : L.hosts<2^w) (ns : L.dimension-c<2^n)
    (width : C.precision≤w) (pairBits : C.depthBits+C.totalBits≤w)
    (depthBits : L.dimension<2^C.depthBits) (boundBits : 2^(L.dimension-c)*cap<2^n)
    (lower : ∀v,c≤depth v ∧ depth v≤L.dimension)
    (totalFit : ∀v u,(∑x,A.resetFlow digits v u x)<2^C.totalBits)
    (smoothed : ∀v,mem (C.levels.base+(name v).val*(L.dimension+1))=(depth v:Word w))
    (paid : ∀v u (j : Fin A.degree),portAt A name v j=some u→
      (mem (C.spectrum.base+(L.hosts*(L.dimension+1)+(name v).val*L.degree+j.val)*2^L.high)).val%2^C.precision=
        ∑x,A.resetFlow digits v u x)
    (thresholds : Cutoff.Resident L.stop C.depthBits C.totalBits K (2^f*B) (2^(L.dimension-c)*cap) mem)
    (j : Fin (A.degree+A.degree)) (s : Fin 2) (p : Row L.hosts L.groups L.batch) :
    (C.field L c j s).eval mem ((DescentSIMDLookup.row _ _ _ p).val:Word w)=
      ((portHeader (c:=c) (n:=n) A name digits depth f B K cap p.1 j s).val:Word w) := by
  let tick:Word w:=(DescentSIMDLookup.row _ _ _ p).val
  let i:=side j
  let nb:=neighborID C.ports i
  let op := if s.val=0 then PortLevels.relative c (Cutoff.level (L.levelAt C.levels L.host) (L.levelAt C.levels nb))
            else Cutoff.term L.stop C.depthBits C.totalBits (L.levelAt C.levels L.host) (L.levelAt C.levels nb)
              (firstTotal C.spectrum (L.zeroAt L.host i.val) C.precision)
  let rs:=roster (D:=A.degree) A name ph
  have host:L.host.eval mem tick=(p.1.val:Word w):=L.host_word mem out static rows p
  have targetWord:nb.eval mem tick=(target (rs p.1 i):Word w):=
    PortLevels.peer_id C.ports prior out rs mem usable mounted i p
  have selected:=projected_target A name L ph p.1 i
  have levelRead (v : V) (z : Fin L.hosts) (slotId : z.val=(name v).val) (source : Expr)
      (reads:source.eval mem tick=(z.val:Word w)) :
      (L.levelAt C.levels source).eval mem tick=(depth v:Word w) := by
    have fit:=Nat.mul_le_mul_right (L.dimension+1) z.isLt
    rw [Nat.succ_mul] at fit
    exact (L.level_at C.levels source mem tick out z static slot level (by omega) reads).trans (by rw [slotId,smoothed])
  generalize hp : project H p.1=real at selected ⊢
  cases real with
  | none=>
    have missing:rs p.1 i=none:=by simpa using selected
    have result:=PortLevels.protect_word C.ports i op mem tick (none:Option (Fin L.hosts)) (fun _=>0) large
      (by simpa [missing] using targetWord) (by intro v h;cases h)
    simpa only [Paid.field,op,nb,i,tick,portHeader,hp,Option.elim_none,Nat.cast_zero,Fin.val_zero] using result
  | some h=>
    let v:=name.symm h
    have ord:p.1.val=(name v).val:=by rw [project_some hp ph];simp [v]
    have lv:=levelRead v p.1 ord L.host host
    cases hit:portAt A name v i with
    | none=>
      have hit' : portAt A name (name.symm h) (side j)=none := hit
      have missing:rs p.1 i=none:=by simpa [v,hit] using selected
      have result:=PortLevels.protect_word C.ports i op mem tick (none:Option (Fin L.hosts)) (fun _=>0) large
        (by simpa [missing] using targetWord) (by intro v h;cases h)
      simpa only [Paid.field,op,nb,i,tick,portHeader,hp,Option.elim_some,hit',Option.elim_none,Nat.cast_zero,Fin.val_zero] using result
    | some u=>
      have hit' : portAt A name (name.symm h) (side j)=some u := hit
      let dst:Fin L.hosts:=(name u).castLE ph
      have found:rs p.1 i=some dst:=by simpa [v,hit,dst] using selected
      have nv:nb.eval mem tick=(dst.val:Word w):=by simpa [found,target] using targetWord
      have rv:=levelRead u dst rfl nb nv
      let dep:=max (depth v) (depth u)
      let total:=∑x,A.resetFlow digits v u x
      let cut:=threshold K (2^f*B) dep total (2^(L.dimension-c)*cap)
      let ix:=(L.hosts*(L.dimension+1)+(name v).val*L.degree+i.val)*2^L.high
      have ixFit:ix<C.spectrum.size:=by
        have exactRow:=Nat.mul_le_mul_right L.degree p.1.isLt
        rw [Nat.succ_mul,ord] at exactRow
        have ip:=i.isLt.trans_le portsFit
        have sum:L.hosts*(L.dimension+1)+(name v).val*L.degree+i.val<L.hosts*(L.dimension+1+L.degree):=by
          rw [Nat.mul_add L.hosts (L.dimension+1) L.degree]; omega
        exact (Nat.mul_lt_mul_of_pos_right sum (Nat.two_pow_pos _)).trans_le spectrumFit
      have idx:(L.zeroAt L.host i.val).eval mem tick=(ix:Word w):=by
        simpa [ix,ord] using L.zero_at L.host i.val mem tick out p.1 static leads host
      have zero:=first_value C.spectrum (L.zeroAt L.host i.val) mem tick ix total spec ixFit width idx (paid v u i hit)
      have dv:dep≤L.dimension:=max_le (lower v).2 (lower u).2
      have depthRoom:dep<2^C.depthBits:=dv.trans_lt depthBits
      have depWord:dep<2^w:=depthRoom.trans_le (Nat.pow_le_pow_right (by decide) (by omega))
      have maxRead : (Cutoff.level (L.levelAt C.levels L.host) (L.levelAt C.levels nb)).eval mem tick=(dep:Word w) := by
        rw [PortLevels.read_level _ _ mem tick _ _ lv rv depWord]
        have low := (le_max_left (depth v) (depth u)).trans_lt depWord
        have high := (le_max_right (depth v) (depth u)).trans_lt depWord
        rcases le_total (depth v) (depth u) with le | le
        · have words : (depth v : Word w) ≤ (depth u : Word w) := by
            simpa only [Fin.le_def,Fin.val_cast_of_lt low,Fin.val_cast_of_lt high] using le
          simp only [dep,max_eq_right le,max_eq_right words]
        · have words : (depth u : Word w) ≤ (depth v : Word w) := by
            simpa only [Fin.le_def,Fin.val_cast_of_lt low,Fin.val_cast_of_lt high] using le
          simp only [dep,max_eq_left le,max_eq_left words]
      have cutRead:=Cutoff.read L.stop C.depthBits C.totalBits K (2^f*B) (2^(L.dimension-c)*cap) _ _ _ mem tick
        (depth v) (depth u) total lv rv zero depthRoom (totalFit v u) pairBits thresholds
      have dec : (if s.val=0 then PortLevels.relative c (Cutoff.level (L.levelAt C.levels L.host) (L.levelAt C.levels nb))
          else Cutoff.term L.stop C.depthBits C.totalBits (L.levelAt C.levels L.host) (L.levelAt C.levels nb)
            (firstTotal C.spectrum (L.zeroAt L.host i.val) C.precision)).eval mem tick=
          ((if s.val=0 then dep-c else cut:ℕ):Word w) := by
        split_ifs
        · exact PortLevels.read_relative c dep _ mem tick ((lower v).1.trans (le_max_left ..)) maxRead
        · exact cutRead
      have result:=PortLevels.protect_word C.ports i _ mem tick (some dst)
        (fun _=>if s.val=0 then dep-c else cut) large (by simpa [found] using targetWord) (fun _ _=>dec)
      have wordFit:(if s.val=0 then dep-c else cut)<2^n:=by
        split_ifs
        · exact (Nat.sub_le_sub_right dv c).trans_lt ns
        · exact (min_le_left ..).trans_lt boundBits
      simp only [portHeader,hp,Option.elim_some,hit']
      change _ = (((((if s.val=0 then dep-c else cut) : ℕ) : Cell n).val) : Word w)
      rw [Fin.val_cast_of_lt wordFit]
      exact result

end
end Hierarchy.DescentSixParty.PackedFlow.Padded

end OAI
