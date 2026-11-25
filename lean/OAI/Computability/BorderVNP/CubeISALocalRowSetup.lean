import OAI.Computability.BorderVNP.CubeISALocalRowAddress

/-! # Complete physical setup for verifying one owned cube declaration row -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.LocalRow

open VPVNP.BurstRAM BorderVNP.Cube BorderVNP.Cube.Physical.Owned BorderVNP.Cube.Tally OwnedRowSetup

/-- Shape registers, real temporary descriptor and addressed declaration produced
by local setup. The strict iterator is available precisely for distinct endpoints. -/
structure Ready (l : Layout) {n : ℕ} (b h K s actual claim vertex : ℕ) (i : Fin (n+1))
    (lo hi : Fin l.d) (z : NatState) : Prop where
  cfg : SingleTally.Config i lo hi actual (l.blocks*l.bc) z
  packet : ∀ eqn : lo < hi, Owned.packetReady (blocks := l.blocks) i ⟨(lo,hi),eqn⟩ (bankWidth n b h K s) l.bank 0 z
  descriptor : z.reg 8 = head l n b h K s
  header : PacketTally.Header z.mem (head l n b h K s) n K h actual (head l n b h K s+8) s
  zero : z.reg 56 = 0
  dim : z.reg 57 = n+1
  base : z.reg 58 = actual
  declared : z.reg 59 = claim
  saved : z.reg 61 = vertex

/-- The native setup produces the full addressed input for tallying and leaves
every other memory word, including all claims and packet bits, unchanged. -/
theorem setup_run {w n : ℕ} (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
    (r : Bank w) (m : Memory w) (l : Layout) (i : Fin (n+1)) (lo hi : Fin l.d)
    (b h K s actual claimed : ℕ)
    (loaded : l.Loaded n (readings pub) (readings m)) (A : readings m l.header = actual)
    (D : readings m (l.header+1) = claimed) (space : Space l w n b h K s (readings pub 0) actual claimed)
    (h0 : readings r 0 = 0) (h1 : readings r 1 = 1) (axis : readings r 4 = i.val)
    (left : readings r 14 = lo.val) (right : readings r 15 = hi.val) :
    let hd := head l n b h K s
    let claim := atPair claimed l.d n lo.val hi.val
    BoundedRun pub mac (setup n b h K s) r m (setup n b h K s).slots (fun z =>
      Ready l b h K s actual claim (readings r 7) i lo hi z ∧
      ∀ x, x < hd ∨ hd+8 ≤ x → z.mem x = readings m x) := by
  intro hd claim
  have bank := bank_le_head l n b h K s
  have fr := space.beforeHeader
  have hA := space.beforeActual
  have hD := space.beforeClaim
  have hB := space.beforeBank
  have small := space.endRoom
  have H : l.header+8 < hd := by dsimp only [hd]; omega
  have F : (pub 0).val+63 < hd := by change readings pub 0+63 < hd; omega
  have lim := row_before_bank space lo hi
  have stride := space.positive
  have prod : packetTrials n l.d l.blocks*(l.d*l.d) < 2^w := by
    let k := packetTrials n l.d l.blocks*(l.d*l.d)
    have hk : k ≤ k * bankWidth n b h K s := by simpa only [Nat.mul_one] using Nat.mul_le_mul_left k stride
    change l.bank + k*bankWidth n b h K s + 8 + h < 2^w at small
    change k < 2^w
    omega
  apply (prime_run pub mac r m l i lo hi b h K s loaded space.frameFit space.trials space.width
    space.count space.stride h0 h1 axis left right).seq
  rintro u mu ⟨pr,pm⟩
  change readings mu = readings m at pm
  have pH : readings mu ((pub 0).val+63) = l.header := by rw [pm]; exact loaded.header
  have aH : readings mu l.header = actual := by rw [pm,A]
  apply (metadata_run pub mac u mu n K h s l.bank (packetTrials n l.d l.blocks) (l.d*l.d)
    (bankWidth n b h K s) l.header actual pr.one pr.dim pr.width pr.count pr.square pr.stride
    pr.bank pr.trials pr.literalOne pH aH F (by omega : l.header < hd) prod space.endRoom
    space.edges space.dimension space.edgeWidth).seq
  rintro v mv ⟨vr8,vr9,desc,mem,regs⟩
  have pH' : frameField (readings pub) (readings mv) 63 = l.header :=
    (mem ((pub 0).val+63) (.inl F)).trans pH
  have dH' : readings mv (l.header+1) = claimed :=
    (mem _ (.inl (by omega : l.header+1 < hd))).trans ((congrFun pm _).trans D)
  have value (j : Reg) (hj : j ∉ ([8,9,50,51,53,58,62,63] : List Reg)) : readings v j = readings u j :=
    regs j hj
  apply (rowAddress_run pub mac v mv l.d actual claimed l.header lo hi
    ((value 0 (by decide)).trans pr.zero) ((value 1 (by decide)).trans pr.one) ((value 5 (by decide)).trans pr.dim)
    vr9 ((value 10 (by decide)).trans pr.radix) ((value 14 (by decide)).trans pr.left)
    ((value 15 (by decide)).trans pr.right) pH' dH' space.frameFit.primary (by have := space.frameFit.header; omega)
    space.dimension (by omega)).mono le_rfl
  rintro z ⟨start,dim,base,declared,zm,keep⟩
  have preserved (j : Reg) (hj : rowAddress.keeps j = true)
      (j' : j ∉ ([8,9,50,51,53,58,62,63] : List Reg)) : z.reg j = readings u j := (keep j hj).trans (value j j')
  refine ⟨⟨?_,?_,(keep 8 (by decide)).trans vr8,zm ▸ desc,start,dim,base,declared,
    (preserved 61 (by decide) (by decide)).trans pr.saved⟩,fun x hx => (congrFun zm x).trans
    ((mem x hx).trans (congrFun pm x))⟩
  · constructor
    all_goals first | exact (keep 9 (by decide)).trans vr9 | apply (preserved _ (by decide) (by decide)).trans
    all_goals first | exact pr.zero | exact pr.one | exact pr.dim | exact pr.tail | exact pr.place | exact pr.radix
                    | exact pr.left | exact pr.right | exact pr.bits
  · intro good
    refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
    all_goals apply (preserved _ (by decide) (by decide)).trans
    all_goals first | exact pr.zero | exact pr.one | exact pr.two | exact pr.radix | exact pr.square
                    | exact pr.squarePlace | exact pr.blocks | exact pr.left | exact pr.right
                    | exact pr.stride | exact pr.bank | exact pr.cursor | exact pr.trials

end RoutingISA.LocalRow

end BorderVNP
end Computability
end OAI
