import OAI.Hierarchy.DescentWinningRows
import OAI.Hierarchy.DescentRosterSearch
import OAI.Hierarchy.DescentColonySlabHardware
import OAI.Hierarchy.DescentAffineColorRAM

namespace OAI
/-! # One physical program for all stored host rosters and both ordinary-stage choices -/

namespace Hierarchy.DescentAffineColors.RosterPaint
open DescentColonies DescentGL DescentBinaryField ProtocolRAM
open WinningSlabs Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM.PhysicalProcedure
open scoped Fin.CommRing BigOperators Classical
noncomputable section
variable {G H ℓ Δ w k : ℕ}

def program (w ℓ Δ adj base D cap : ℕ) (a : Bits k) (wp raw : Fin G→Fin (2^ℓ)→ℕ) :=
  let s := RosterSearch.search w ℓ Δ adj base D cap a wp
  let slabs := Selected.program w base raw a
  let z := Selected.endAt G (2^ℓ) k base
  let cols := Selected.dest (G:=G) (H:=2^ℓ) (k:=k) base
  ((s.1.seq slabs.text).seq (RAM.run w k z cols),s.2+slabs.ticks+RAM.ticks k z cols)

private theorem winner_before (G H k base : ℕ) :
    WinningColumns.winnerPtr G H k base<Materialized.first G H k base := by
  unfold WinningColumns.winnerPtr Materialized.first
  have := Nat.two_pow_pos k
  omega

/-- Materializing the chosen columns and all their slabs preserves the native
word from which they read the winning multiplier. -/
theorem read_multiplier (base : ℕ) (raw : Fin G→Fin H→ℕ) (a : Bits k) (m : Memory w) :
    let i := WinningColumns.winnerPtr G H k base
    (Selected.program w base raw a).after m i=m i := by
  let i := WinningColumns.winnerPtr G H k base
  have before : i<Materialized.first G H k base := winner_before ..
  have slab : i<Selected.slabBase G H k base := before.trans_le (Nat.le_add_right ..)
  have columns := Materialized.below base raw a m i before
  exact (world_below k (Selected.slabBase G H k base) (Selected.flags (G:=G) (H:=H) base)
    (Selected.amounts k base) ((Materialized.program w base raw a).after m) slab).trans columns

/-- The neighbor IDs, the two original measurement columns, and all table
contents can vary. The instruction stream and exact clock in the conclusion
use only the public extents and addresses. -/
theorem execute (ℓ Δ adj base D cap : ℕ) (hk : 0<k) (wp raw : Fin G→Fin (2^ℓ)→ℕ)
    (rs : DynamicSplit.Roster ℓ Δ) (m : Memory w) (data : DynamicSplit.Stored adj rs m)
    (weight amount : Fin G→Fin (2^ℓ)→Block k→ℕ) (B : ℕ)
    (prior : adj+2^ℓ*Δ≤base) (old : ∀g v,wp g v+2^k≤base) (oldRaw : ∀g v,raw g v+2^k≤base)
    (room : RAM.paint k (Selected.endAt G (2^ℓ) k base)+2^k<2^w) (wide : 2^(ℓ+k)<2^w)
    (cf : cap<2^w) (counts : G*(2^ℓ*2^k)<2^w) (small : ∀g v x,weight g v x≤B)
    (reserve : 2^k*B<2^w) (amountRoom : ∑g,∑v,∑x,amount g v x<2^w)
    (weights : ∀g v (x : Block k),m (wp g v+x.val)=(weight g v x:Word w))
    (amounts : ∀g v (x : Block k),m (raw g v+x.val)=(amount g v x:Word w)) :
    let a := modulus hk
    let income := DynamicSplit.incoming rs
    let Q := uniformColonyScore income weight D cap a
    let z := Selected.endAt G (2^ℓ) k base
    let P := program w ℓ Δ adj base D cap a wp raw
    ∃ out : Memory w,∃ μ : Nonzero k,∃ j : Candidate k,
      let A := worldValue (Selected.winningRows income weight D cap a μ) (Selected.winningAmounts amount a μ)
      P.1.Exec m out P.2 ∧
      (scanMinimum Q (nonzeroWords k)).1=some (μ,Q μ) ∧
      (scanMinimum (scoreAt A) (List.range (2^(k+1)))).1=some (j.val,score A j) ∧
      out (WinningColumns.winnerPtr G (2^ℓ) k base)=(MultiplierMinimumRAM.key μ:Word w) ∧
      out (RAM.chosen k z)=(j.val:Word w) ∧
      (∀x : Block k,out (RAM.paint k z+x.val)=((thick j x).toNat:Word w)) ∧
      (∀t<base,out t=m t) ∧
      ∀ g v (d : Fin k) (x : Block k), out (Materialized.dest base ((g,v),some d)+x.val)=
        ((Scan.lookup (Selected.winningRows income weight D cap a μ g) d.val v x).toNat:Word w) := by
  let a := modulus hk
  let income := DynamicSplit.incoming rs
  let z := Selected.endAt G (2^ℓ) k base
  let mid := AllSeedsRAM.afterSearch base D cap a income wp m
  let slabs := Selected.program w base raw a
  let cols := Selected.dest (G:=G) (H:=2^ℓ) (k:=k) base
  have nz : z<2^w := by
    have first : z≤RAM.choices k z := Nat.le_add_right ..
    have second : RAM.choices k z≤RAM.paint k z := Nat.le_add_right ..
    exact (first.trans (second.trans (Nat.le_add_right ..))).trans_lt room
  have zbase : base≤z := by
    calc
      base ≤ AllSeedsRAM.gatherBase G (2^ℓ) k base := Nat.le_add_right ..
      _ ≤ AllSeedsRAM.winningBase G (2^ℓ) k base := Nat.le_add_right ..
      _ ≤ Materialized.first G (2^ℓ) k base := Nat.le_add_right ..
      _ ≤ Selected.slabBase G (2^ℓ) k base := Nat.le_add_right ..
      _ ≤ z := Nat.le_add_right ..
  have winRoom : AllSeedsRAM.winningBase G (2^ℓ) k base+(2^k-1)<2^w := by
    have row : AllSeedsRAM.winningBase G (2^ℓ) k base+(2^k-1)≤Materialized.first G (2^ℓ) k base :=
      Nat.add_le_add_left (Nat.sub_le _ _) _
    have slabs : Materialized.first G (2^ℓ) k base≤Selected.slabBase G (2^ℓ) k base := Nat.le_add_right ..
    exact (row.trans (slabs.trans (Nat.le_add_right ..))).trans_lt nz
  let search := RosterSearch.search w ℓ Δ adj base D cap a wp
  have reach : search.1.Exec m mid search.2 :=
    RosterSearch.exec_eq w ℓ Δ adj base D cap a wp rs m data prior old winRoom wide
  obtain ⟨μ,_,found,_,read,_,frame⟩ := Selected.from_inputs base D cap a income wp raw m weight amount hk old oldRaw nz
    cf counts B reserve small weights amounts
  let A := worldValue (Selected.winningRows income weight D cap a μ) (Selected.winningAmounts amount a μ)
  have capA : ∑c,∑x,A c x<2^w := by
    dsimp only [A]
    rw [mass]
    have perm (g : Fin G) (v : Fin (2^ℓ)) :
        (∑x,Selected.winningAmounts amount a μ g v x)=∑x,amount g v x := by
      unfold Selected.winningAmounts
      rw [multiplierLoad_eq _ _ _ _ (multiplier_native hk μ)]
      exact Equiv.sum_comp (rearrange (multiplier hk μ)).symm (amount g v)
    simpa only [perm] using amountRoom
  obtain ⟨out,j,colored,tie,_,atKey,painted,lower⟩ :=
    RAM.execution z cols (slabs.after mid) A (Selected.dest_end base) room capA read
  obtain ⟨ν,_,first,_,atWinner,_⟩ := AllSeedsRAM.selection base D cap a income wp m weight hk old winRoom
    cf counts B reserve small weights
  have which : ν=μ := congrArg Prod.fst (Option.some.inj (first.symm.trans found))
  subst ν
  let i := WinningColumns.winnerPtr G (2^ℓ) k base
  have belowSlabs : i<Selected.slabBase G (2^ℓ) k base := (winner_before G (2^ℓ) k base).trans_le
    (Nat.le_add_right ..)
  have beforePaint : i<z := belowSlabs.trans_le (Nat.le_add_right ..)
  have kept : out i=(MultiplierMinimumRAM.key μ:Word w) :=
    (lower i beforePaint).trans ((read_multiplier base raw a mid).trans atWinner)
  have slabStart : Selected.slabBase G (2^ℓ) k base≤z := Nat.le_add_right ..
  have retained := Materialized.published base D cap a income wp raw m weight amount old oldRaw
    (slabStart.trans_lt nz) cf weights amounts
    (fun ν g d _ v x=>CandidateRAM.interval_room weight a ν B small reserve g d v x) μ atWinner
  have gathered : (search.1.seq slabs.text).Exec m (slabs.after mid) (search.2+slabs.ticks) := by
    intro labels registers slots machine
    exact Procedure.Exec.then reach (Selected.run base raw a mid oldRaw nz) machine
  refine ⟨out,μ,j,?_,
    found,tie,kept,atKey,painted,fun x hx=>(lower x (hx.trans_le zbase)).trans (frame x hx),?_⟩
  · intro labels registers slots machine
    exact Procedure.Exec.then gathered colored machine
  intro g v d x
  let s : Materialized.Slot G (2^ℓ) k := ((g,v),some d)
  have early : Materialized.dest base s+x.val<Selected.slabBase G (2^ℓ) k base :=
    (Nat.add_lt_add_left x.isLt _).trans_le (Materialized.dest_end base s)
  have copy := world_below k (Selected.slabBase G (2^ℓ) k base) (Selected.flags (G:=G) (H:=2^ℓ) base)
    (Selected.amounts k base) ((Materialized.program w base raw a).after mid) early
  exact (lower _ (early.trans_le slabStart)).trans (copy.trans (retained s x))

/-- Host padding is charged linearly. Both scans depend polynomially on the
local block alphabet, independently of the stored adjacency and graph. -/
theorem time_le (w ℓ Δ adj base D cap : ℕ) (a : Bits k) (wp raw : Fin G→Fin (2^ℓ)→ℕ) :
    (program w ℓ Δ adj base D cap a wp raw).2 ≤
      10000*(G+1)*(2^ℓ+1)*(k+1)*(Δ+1)*(2^k+1)^5 := by
  let H := 2^ℓ
  let r := 2^k
  let z := Selected.endAt G H k base
  let cols := Selected.dest (G:=G) (H:=H) (k:=k) base
  have seed := RosterSearch.cost_le w ℓ Δ adj base D cap a wp
  have slabs := Selected.ticks_bound (w:=w) base raw a
  have colors := RAM.ticks_le k z cols
  have len : (keys k).length≤2*r := by have h := keys_count k;dsimp only [r];omega
  apply (Nat.add_le_add (Nat.add_le_add seed slabs) colors).trans
  change (2000*(G+1)*(H+1)*(k+1)*(Δ+1)*(r+1)^5)+
    ((4+G*H*(k+1)*(4+r*(2*(1+(r-1)*(10*r+18))+4)))+
     (4+G*H*(keys k).length*(4+r*(2*(21+10*k)+4))))+
    1000*(G*H*(keys k).length+1)*(r+1)^4 ≤ _
  calc
    _ ≤ 2000*(G+1)*(H+1)*(k+1)*(Δ+1)*(r+1)^5+
        ((4+G*H*(k+1)*(4+r*(2*(1+r*(10*r+18))+4)))+
         (4+G*H*(2*r)*(4+r*(2*(21+10*k)+4))))+
        1000*(G*H*(2*r)+1)*(r+1)^4 := by gcongr; omega
    _ ≤ 10000*(G+1)*(H+1)*(k+1)*(Δ+1)*(r+1)^5 := by
      zify
      apply sub_nonneg.mp
      ring_nf
      positivity

theorem bounded (w ℓ Δ adj base D cap : ℕ) (a : Bits k) (wp raw : Fin G→Fin (2^ℓ)→ℕ) :
    let P := program w ℓ Δ adj base D cap a wp raw
    CandidateRAM.Bounded P.1 P.2 := by
  apply CandidateRAM.seq_bound (CandidateRAM.seq_bound (RosterSearch.bounded ..) (Selected.program_bounded ..))
  exact CandidateRAM.seq_bound
    (CandidateRAM.seq_bound (CandidateRAM.scan_bound _ _ _ _ (Nat.two_pow_pos _)) (DescentFirstMinimumRAM.code_bound ..))
    (CandidateRAM.scan_bound _ _ _ _ (Nat.two_pow_pos _))

end
end Hierarchy.DescentAffineColors.RosterPaint

end OAI
