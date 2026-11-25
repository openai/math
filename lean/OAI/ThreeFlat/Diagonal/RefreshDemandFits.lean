import OAI.ThreeFlat.Diagonal.RefreshDemandRows

namespace OAI
/-! # Word and memory bounds for physical refresh demand lookup -/

namespace ThreeFlat.Diagonal.RefreshDemandRows

open Computability.VPVNP.BurstRAM Computability.VPVNP.Compression RAM.PhysicalPinsExpr CompressorPacking.Native RefreshTies
open scoped Classical
noncomputable section

private theorem productRow_lt {i j n m : ℕ} (hi : i<n) (hj : j<m) : i*m+j < n*m := by
  calc
    i*m+j < i*m+m := Nat.add_lt_add_left hj _
    _ = (i+1)*m := by ring
    _ ≤ n*m := Nat.mul_le_mul_right _ hi

theorem ordinal_lt {m lanes bases v s j l : ℕ} (hv : v<bases) (hs : s<m) (hj : j<m) (hl : l<lanes) :
    ordinal m lanes v s j l < (bases*m)*(m*lanes) := by
  apply productRow_lt (productRow_lt hv hs)
  simpa only [Nat.add_comm j, Nat.mul_comm m] using productRow_lt hl hj

theorem index_lt {v a t : ℕ} (e : Address' v a t) :
    index e < (v*mPort a)*(mPort a*2^t) :=
  ordinal_lt e.1.1.isLt e.2.2.isLt e.2.1.isLt (tagOrdinal t e.1.2).isLt

variable {W n : ℕ} (data : Param → ℕ) (mem : ℕ → ℕ) (vs : Fin n → ℕ)
local notation "V" => Formula.natural W data mem vs
local notation "Fit" => Formula.Fits W data mem vs

private theorem wordAddress_fit (m : ℕ) {l b s i x : Formula n}
    (hl : Fit l) (hb : Fit b) (hs : Fit s) (hi : Fit i) (hx : Fit x) :
    Fit (wordAddress m l b s i x) := by
  simp [wordAddress,Formula.Fits,opFits,hl,hb,hs,hi,hx]

private theorem load_fit {a p : Formula n} (ha : Fit a) (hp : Fit p) (bound : V a + V p < 2^W) :
    Fit (readColumn a p) := ⟨⟨ha,hp,trivial⟩,bound⟩

/-- Actual region ends and the two fixed radices suffice for faithful native
width reads. Every incoming XOR operand is bounded by its own lane radix. -/
theorem demand_fits {a t v : ℕ} (G : LiftedSlots (Fin v) (mPort a) (BitWord a × BitWord t))
    (C : Columns (Formula n)) (remaining block : Formula n) (z : Block v t) (dir : Bool)
    (i s : Fin (mPort a)) (w : Address' v a t → ℕ) (stored : Stored G (C.map V) mem w)
    (hrem : V remaining = 2^t) (hblock : V block = blockId z)
    (hbr : Fit block) (hrr : Fit remaining) (hbc : V block < 2^W)
    (hpc : mPort a ≤ 2^W) (hrc : 2^t < 2^W)
    (hf : Fit C.widths ∧ Fit C.sourceBase ∧ Fit C.sourceSlot ∧ Fit C.portShift ∧ Fit C.laneShift)
    (hw : V C.widths+(v*mPort a)*(mPort a*2^t) ≤ 2^W)
    (hc : ∀ c ∈ [C.sourceBase,C.sourceSlot,C.portShift,C.laneShift], V c + v*mPort a ≤ 2^W) :
    Fit (demand (mPort a) C remaining block dir i.val s.val) := by
  obtain ⟨fw,fb,fs,fp,fl⟩ := hf
  let m := mPort a
  let b := Formula.op .div block remaining
  let l := Formula.op .mod block remaining
  let p := Formula.op .add (.op .mul b (.lit m)) (.lit s.val)
  have fr : V remaining < 2^W := hrem ▸ hrc
  have fdb : Fit b := ⟨hbr,hrr,hbc,fr⟩
  have fdl : Fit l := ⟨hbr,hrr,hbc,fr⟩
  have fdp : Fit p := ⟨⟨fdb,trivial,trivial⟩,trivial,trivial⟩
  have division : V b = z.1.val := by
    change V block/V remaining = _
    rw [hrem,hblock]
    simp only [blockId,Nat.mul_comm z.1.val (2^t),Nat.mul_add_div (by positivity : 0<2^t),Nat.div_eq_of_lt (tagOrdinal t z.2).isLt,Nat.add_zero]
  have row : V p = z.1.val*m+s.val := by
    change V b*m+s.val = _
    rw [division]
  have modBound : V l < 2^t := by
    change V block % V remaining < _
    rw [hrem]
    exact Nat.mod_lt _ (by positivity)
  have fld (c : Formula n) (fc : Fit c) (h : c ∈ [C.sourceBase,C.sourceSlot,C.portShift,C.laneShift]) :
      Fit (readColumn c p) := by
    apply load_fit data mem vs fc fdp
    rw [row]
    exact (Nat.add_lt_add_left (productRow_lt z.1.isLt s.isLt) _).trans_le (hc c h)
  have getP : V (readColumn C.portShift p) < m := by
    change mem (V C.portShift+ V p) < _
    rw [row]
    exact (stored.consumed z.1 s).le.trans_lt (tagOrdinal a _).isLt
  have getL : V (readColumn C.laneShift p) < 2^t := by
    change mem (V C.laneShift+ V p) < _
    rw [row]
    exact (stored.remaining z.1 s).le.trans_lt (tagOrdinal t _).isLt
  have fxor : Fit (.op .bitXor (.lit i.val) (readColumn C.portShift p)) :=
    ⟨trivial,fld _ fp (by simp),i.isLt.trans_le hpc,getP.trans_le hpc⟩
  have flxor : Fit (.op .bitXor l (readColumn C.laneShift p)) :=
    ⟨fdl,fld _ fl (by simp),modBound.trans hrc,getL.trans hrc⟩
  have addrFit : absAddress m (C.map V) mem (V remaining) (V block) dir i.val s.val < 2^W := by
    rw [hrem,hblock,demand_address G stored]
    exact (Nat.add_lt_add_left (index_lt _) _).trans_le hw
  cases dir with
  | false =>
    exact load_fit data mem vs fw (wordAddress_fit data mem vs m hrr fdb trivial trivial fdl) addrFit
  | true =>
    exact load_fit data mem vs fw
      (wordAddress_fit data mem vs m hrr (fld _ fb (by simp)) (fld _ fs (by simp)) fxor flxor) addrFit

end
end ThreeFlat.Diagonal.RefreshDemandRows

end OAI
