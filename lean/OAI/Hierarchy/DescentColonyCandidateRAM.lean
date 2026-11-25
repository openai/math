import OAI.Hierarchy.DescentColonySiteRAM

namespace OAI
/-! # The native score of one nonzero multiplier on every load group -/

noncomputable section
namespace Hierarchy.DescentColonies.CandidateRAM
open ProtocolRAM Computability.VPVNP.BurstRAM Computability.VPVNP.BurstRAM.PrivateRAM
open ThreeFlat.RAM PhysicalProcedure DescriptorExpr
open NativeBatch
open DescentGL (Bits Nonzero)
open scoped Classical BigOperators Fin.CommRing

variable {G H k w : ℕ}

def stride (H k : ℕ) := (k+1)*H*2^k+1

def output (G H k base : ℕ) := base+G*stride H k

theorem start (g H k base : ℕ) : base≤output g H k base := Nat.le_add_right _ _

theorem mono (H k base : ℕ) {i j : ℕ} (h : i≤j) : output i H k base≤output j H k base :=
  Nat.add_le_add_left (Nat.mul_le_mul_right _ h) _

theorem next (g H k base : ℕ) :
    SiteRAM.scoreAt H k (output g H k base)+1=output (g+1) H k base := by
  unfold SiteRAM.scoreAt SiteRAM.bank PhysicalCensus.output output stride
  ring

def steps (w base : ℕ) (incoming : Fin H→List (Fin H)) (ptr : Fin G→Fin H→ℕ)
    (D cap : ℕ) (a : Bits k) (μ : Nonzero k) (g : Fin G) :=
  SiteRAM.groupCode w k (output g.val H k base) incoming (ptr g) D cap a μ.val

def receipt (H k base : ℕ) (g : Fin G) := SiteRAM.scoreAt H k (output g.val H k base)

theorem live (H k base : ℕ) (g : Fin G) : receipt H k base g<output G H k base :=
  ((next g.val H k base).le.trans (mono _ _ _ g.isLt))

def tally : (n : ℕ) → (Fin n→ℕ) → Expr
  | 0,_ => .lit 0
  | n+1,p => .op .add (.lookup ⟨p 0,0⟩ (.lit 0)) (tally n (fun j=>p j.succ))

private theorem tally_eval (n : ℕ) (p : Fin n→ℕ) (m : Memory w) (r : Word w) :
    (tally n p).eval m r=∑i,m (p i) := by
  induction n with
  | zero => simp [tally,Expr.eval]
  | succ n ih =>
    rw [Fin.sum_univ_succ]
    simp [tally,Expr.eval,RowOp.opcode,BinaryOp.eval,Bank.read,Bank.size,ih]

theorem tally_fits (n : ℕ) (p : Fin n→ℕ) (out : ℕ) (wide : 1<2^w) (old : ∀i,p i<out) :
    (tally n p).Fits w out := by
  induction n with
  | zero => trivial
  | succ n ih => exact ⟨⟨⟨Nat.two_pow_pos _,wide,Nat.succ_le_of_lt (old 0)⟩,trivial⟩,
      ih _ (fun j=>old j.succ)⟩

theorem tally_work (n : ℕ) (p : Fin n→ℕ) : (tally n p).work=1+7*n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [tally,Expr.work,ih,Nat.mul_succ]; omega

def summary (w G H k base : ℕ) : Code w :=
  let b := output G H k base
  let e := tally G (receipt H k base)
  ⟨scan w b 1 e,image b 1 e,4+1*(2*e.work+4)⟩

def code (w base : ℕ) (incoming : Fin H→List (Fin H)) (ptr : Fin G→Fin H→ℕ) (D cap : ℕ)
    (a : Bits k) (μ : Nonzero k) :=
  (Code.seq (steps w base incoming ptr D cap a μ) G le_rfl).thenDo (summary w G H k base)

def program (w base : ℕ) (incoming : Fin H→List (Fin H)) (ptr : Fin G→Fin H→ℕ) (D cap : ℕ)
    (a : Bits k) (μ : Nonzero k) := (code w base incoming ptr D cap a μ).text

def after (base : ℕ) (incoming : Fin H→List (Fin H)) (ptr : Fin G→Fin H→ℕ) (D cap : ℕ)
    (a : Bits k) (μ : Nonzero k) (m : Memory w) := (code w base incoming ptr D cap a μ).after m

def ticks (w base : ℕ) (incoming : Fin H→List (Fin H)) (ptr : Fin G→Fin H→ℕ) (D cap : ℕ)
    (a : Bits k) (μ : Nonzero k) := (code w base incoming ptr D cap a μ).ticks

theorem run (base : ℕ) (incoming : Fin H→List (Fin H)) (ptr : Fin G→Fin H→ℕ) (D cap : ℕ)
    (a : Bits k) (μ : Nonzero k) (m : Memory w) (old : ∀g i,ptr g i+2^k≤base)
    (room : output G H k base+1<2^w) :
    (program w base incoming ptr D cap a μ).Exec m (after base incoming ptr D cap a μ m)
      (ticks w base incoming ptr D cap a μ) := by
  let perGroup := steps w base incoming ptr D cap a μ
  have runGroups : (Code.seq perGroup G le_rfl).exec := by
    apply Code.exec_seqAll
    intro g
    apply SiteRAM.run (output g.val H k base) incoming (ptr g) D cap a μ.val
    · exact fun i => (old g i).trans (start g.val H k base)
    · rw [next]
      exact (mono H k base g.isLt).trans_lt (by omega)
  have runSummary : (summary w G H k base).exec := by
    intro M labels registers slots machine
    exact scan_exec (output G H k base) 1 (tally G (receipt H k base)) M
      (tally_fits G (receipt H k base) _ (by omega) (live H k base)) room machine
  intro labels registers slots machine
  exact Code.exec_seq runGroups runSummary m machine

theorem below (base : ℕ) (incoming : Fin H→List (Fin H)) (ptr : Fin G→Fin H→ℕ) (D cap : ℕ)
    (a : Bits k) (μ : Nonzero k) (m : Memory w) (z : ℕ) (prior : z<base) :
    after base incoming ptr D cap a μ m z=m z := by
  let step := steps w base incoming ptr D cap a μ
  let M := (Code.seq step G le_rfl).after m
  change image (output G H k base) 1 (tally G (receipt H k base)) M z=m z
  refine (ProtocolRAMGeneratedWrite.frame_image _ _ _ M z
    (Or.inl (prior.trans_le (start G H k base)))).trans ?_
  exact Code.frame_seq step z (fun g tape => SiteRAM.below (output g.val H k base)
    incoming (ptr g) D cap a μ.val tape z (prior.trans_le (start g.val H k base))) m G le_rfl

theorem published (base : ℕ) (incoming : Fin H→List (Fin H)) (ptr : Fin G→Fin H→ℕ) (D cap : ℕ)
    (a : Bits k) (μ : Nonzero k) (m : Memory w) (weight : Fin G→Fin H→Block k→ℕ)
    (old : ∀g i,ptr g i+2^k≤base) (room : output G H k base+1<2^w) (bits : 2^k≤2^w) (cf : cap<2^w)
    (loads : ∀g i (x : Block k),m (ptr g i+x.val)=(weight g i x:Word w))
    (sumRoom : ∀g d,d<k→∀v x,(Scan.readWeights (multiplierLoad (weight g) a μ.val) d v x).sum<2^w) :
    after base incoming ptr D cap a μ m (output G H k base)=(uniformColonyScore incoming weight D cap a μ:Word w) := by
  let step := steps w base incoming ptr D cap a μ
  let Init := fun M : Memory w => ∀g i (x : Block k),M (ptr g i+x.val)=(weight g i x:Word w)
  let cost := fun g=>Scan.leafScore incoming (multiplierLoad (weight g) a μ.val) D cap
  let Claim := fun g:Fin G=>fun M : Memory w=> M (receipt H k base g)=(cost g:Word w)
  have stable (j : Fin G) (M : Memory w) (ok : Init M) : Init ((step j).after M) := by
    intro g i x
    apply Eq.trans (SiteRAM.below (output j.val H k base) incoming (ptr j) D cap
      a μ.val M (ptr g i+x.val) ?_) (ok g i x)
    exact ((Nat.add_lt_add_left x.isLt _).trans_le (old g i)).trans_le (start j.val H k base)
  have now (g : Fin G) (M : Memory w) (ok : Init M) : Claim g ((step g).after M) := by
    refine SiteRAM.published (output g.val H k base) incoming (ptr g) D cap a μ.val M (weight g)
      (fun i => (old g i).trans (start g.val H k base)) ?_ bits cf (ok g) (sumRoom g)
    rw [next]
    exact (mono H k base g.isLt).trans_lt (by omega)
  have keep (i j : Fin G) (lt : i<j) (M : Memory w) (ok : Claim i M) : Claim i ((step j).after M) := by
    refine (SiteRAM.below (output j.val H k base) incoming (ptr j) D cap a μ.val M
      (receipt H k base i) ?_).trans ok
    exact (next i.val H k base).le.trans (mono H k base lt)
  let M := (Code.seq step G le_rfl).after m
  have all := (Code.read_seq step Init stable Claim now keep m loads G le_rfl).2
  have read := ProtocolRAMGeneratedWrite.read_image (output G H k base) 1
    (tally G (receipt H k base)) M (0:Fin 1)
  have total : (tally G (receipt H k base)).eval M (0:Word w) =
      (uniformColonyScore incoming weight D cap a μ : Word w) := by
    rw [tally_eval]
    change (∑ g : Fin G,M (receipt H k base g)) = ((∑ g : Fin G,cost g : ℕ) : Word w)
    rw [Nat.cast_sum]
    exact Finset.sum_congr rfl fun g _ => all g g.isLt
  change image (output G H k base) 1 (tally G (receipt H k base)) M (output G H k base) = _
  exact (show _ = (tally G (receipt H k base)).eval M (0:Word w) by
    simpa only [Fin.val_zero,Nat.cast_zero,Nat.add_zero] using read).trans total

/-- A single old-word upper bound gives sufficient arithmetic room for every
permuted dyadic interval and every candidate in the seed sweep. -/
theorem interval_room (weight : Fin G→Fin H→Block k→ℕ) (a : Bits k) (μ : Nonzero k) (B : ℕ)
    (limit : ∀g v x,weight g v x≤B) (fits : 2^k*B<2^w) (g : Fin G) (d : ℕ) (v : Fin H) (x : Block k) :
    (Scan.readWeights (multiplierLoad (weight g) a μ.val) d v x).sum<2^w := by
  rw [Scan.readWeights,List.sum_ofFn]
  apply lt_of_le_of_lt _ fits
  calc
    _ ≤ ∑ _ : Block k,B := Finset.sum_le_sum fun y _=>by
      split
      · unfold multiplierLoad
        split
        · exact Nat.zero_le _
        · exact limit _ _ _
      · exact Nat.zero_le _
    _ = _ := by simp [Block]

theorem published_nat (base : ℕ) (incoming : Fin H→List (Fin H)) (ptr : Fin G→Fin H→ℕ) (D cap : ℕ)
    (a : Bits k) (μ : Nonzero k) (m : Memory w) (weight : Fin G→Fin H→Block k→ℕ)
    (old : ∀g i,ptr g i+2^k≤base) (room : output G H k base+1<2^w) (bits : 2^k≤2^w) (cf : cap<2^w)
    (bill : G*(H*2^k)<2^w) (loads : ∀g i (x : Block k),m (ptr g i+x.val)=(weight g i x:Word w))
    (sumRoom : ∀g d,d<k→∀v x,(Scan.readWeights (multiplierLoad (weight g) a μ.val) d v x).sum<2^w) :
    (after base incoming ptr D cap a μ m (output G H k base)).val=uniformColonyScore incoming weight D cap a μ := by
  rw [published base incoming ptr D cap a μ m weight old room bits cf loads sumRoom,Fin.val_cast_of_lt]
  apply lt_of_le_of_lt _ bill
  unfold uniformColonyScore
  calc
    _ ≤ ∑ _ : Fin G,H*2^k := Finset.sum_le_sum fun i _=>by
      rw [←Scan.FinRows.score_eq_leafScore]
      exact PhysicalCensus.score_le ..
    _ = _ := by simp

theorem ticks_le (base : ℕ) (incoming : Fin H→List (Fin H)) (ptr : Fin G→Fin H→ℕ) (D cap deg : ℕ)
    (a : Bits k) (μ : Nonzero k) (bound : ∀i,(incoming i).length≤deg) :
    ticks w base incoming ptr D cap a μ≤(4+G*SiteRAM.stepBound H k deg)+(4+1*(2*(1+7*G)+4)) := by
  change (Code.seq _ G le_rfl).ticks+(4+1*(2*(tally G _).work+4))≤_
  rw [tally_work]
  apply Nat.add_le_add_right
  exact Code.clock_seq (steps w base incoming ptr D cap a μ) (SiteRAM.stepBound H k deg)
    (fun g => SiteRAM.ticks_le (w:=w) (output g.val H k base) incoming (ptr g)
      D cap deg a μ.val bound) G le_rfl

/-- The cubic cost in the number of block words is linear in the number of
groups, sites, depths and incoming ports after adding one to each extent. -/
theorem ticks_cubic (base : ℕ) (incoming : Fin H→List (Fin H)) (ptr : Fin G→Fin H→ℕ) (D cap deg : ℕ)
    (a : Bits k) (μ : Nonzero k) (bound : ∀i,(incoming i).length≤deg) :
    ticks w base incoming ptr D cap a μ ≤ 256*(G+1)*(H+1)*(k+1)*(deg+1)*(2^k+1)^3 := by
  apply (ticks_le base incoming ptr D cap deg a μ bound).trans
  unfold SiteRAM.stepBound CensusRAM.workBound SplitRAM.workBound
  generalize 2^k=n
  zify
  apply sub_nonneg.mp
  ring_nf
  positivity

end Hierarchy.DescentColonies.CandidateRAM

end
end OAI
