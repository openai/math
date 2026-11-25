import OAI.Computability.BorderVNP.CubeScatterPaddingOperands

/-! # Recovering the native padding layout from the literal and computed frame words -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Padding

open RoutingISA RoutingISA.CubeHeaderInstall VPVNP.BurstRAM Tally

/-- Inputs of the geometry allocation used by the genuine joint extension. -/
structure Bootstrap (w : ℕ) where
  /-- Base of the geometry allocation. -/
  fresh : ℕ
  /-- Encoded profile length. -/
  profile : ℕ
  /-- Number of emitted geometry gates. -/
  gates : ℕ
  /-- Number of gathered geometry outputs. -/
  outputs : ℕ
  /-- Encoding width of a geometry word. -/
  width : ℕ
  /-- Geometry stream offset and length. -/
  off : ℕ
  /-- Length of the geometry stream. -/
  ell : ℕ
  /-- Caller-supplied extension before the geometry and cube scalar overlays. -/
  old : Fin 81 → Word w

variable {w n d blocks b h K s : ℕ}

/-- The actual secondary header allocated by the geometry program. -/
def Bootstrap.stat (B : Bootstrap w) (d n blocks b h s : ℕ) :=
  geometryInputs B.fresh B.profile B.gates B.outputs B.width w d n blocks b h s

/-- The actual literal array decoded by the primary extension routine. -/
def Bootstrap.extension (B : Bootstrap w) (d n blocks b h s : ℕ) :=
  jointFields B.old B.fresh B.profile B.gates B.outputs B.width B.off B.ell d n blocks b h s

/-- Native table and bank layout in terms of the scalar geometry and placed allocations. -/
def Pointers.layout (P : Pointers) (frame team packet : ℕ) (axis : Fin (n+1)) (d blocks b h K s : ℕ) : Layout :=
  ⟨frame,d,d^(n+1),d^axis.val,P.owners,P.widths,P.triples,P.singles,packet,blocks,h*b,
    bankWidth n b h K s,selectorWidth n K h,team⟩

/-- Primary extension slots read by the padding routine. -/
def fixedFields : List ℕ := [56,57,59,61,62,63,77,88,91,93,94]

/-- Concrete readouts of the ordinary boot, joint literal array, decoded declaration and power install.
They may be transported to a later memory by agreement at their displayed addresses. -/
structure Published (P : Pointers) (B : Bootstrap w) (pub : Arg → Word w) (m : Memory w)
    (team : ℕ) (axis : Fin (n+1)) (d blocks b h K s : ℕ) : Prop where
  /-- The team number at primary word zero. -/
  core : readings m (readings pub 0) = team
  /-- The eleven literal words read by the verifier survive to its entry. -/
  extended : ∀ j : Fin 81, 31+j.val ∈ fixedFields → m ((pub 0).val+31+j.val) = B.extension d n blocks b h s j
  /-- The eight designated literal words in the caller's physical arena extension. -/
  literal : ∀ j : Fin 81, ∀ v, P.operand n d b h K s (31+j.val) = some v → (B.old j).val = v
  /-- Actual chosen coordinate in the returned dynamic declaration. -/
  axisWord : readings m ((B.stat d n blocks b h s).header+5) = axis.val
  /-- The two secondary words in the image returned by `prepare_after_geometry`. -/
  secondary : ∃ broadcast old, ∀ j ∈ [7,8],
    let stat := B.stat d n blocks b h s
    readings m (stat.header+j) = (stat.decoder broadcast).finalImage (stat.image n (selectorWidth n K h) old) (stat.header+j)
  /-- The selected power-table word from the complete native powers install. -/
  power : ∃ old, readings m (P.powers+axis.val) = CubePowers.image d P.powers (n+1) old (P.powers+axis.val)

/-- The numeric room supplied by the two genuine startup passes, including both loop bounds. -/
structure Bootstrap.Room (B : Bootstrap w) (P : Pointers) (pub : Arg → Word w) (d n blocks b h K s : ℕ) : Prop where
  /-- Verified secondary header allocation and primary frame extent. -/
  install : (B.stat d n blocks b h s).Fits w n (selectorWidth n K h) (readings pub 0)
  /-- Word for the geometry profile length. -/
  profile : B.profile < 2^w
  /-- Word for the actual block width. -/
  block : h*b < 2^w
  /-- Extent of the powers installation. -/
  powers : P.powers+(n+1) ≤ 2^w
  /-- The runtime pair counter including its last value. -/
  square : d^(n+1)*d^(n+1) < 2^w

/-- Reading the actual prepared frame gives precisely the physical layout, and all
addresses used by the fixed setup are representable. -/
theorem Published.decode {P : Pointers} {B : Bootstrap w} {pub : Arg → Word w} {m : Memory w}
    {team : ℕ} {axis : Fin (n+1)} (words : Published P B pub m team axis d blocks b h K s)
    (room : B.Room P pub d n blocks b h K s) :
    let stat := B.stat d n blocks b h s
    Layout.fromFrame (readings pub 0) (readings m) =
      P.layout (readings pub 0) team stat.packetBase axis d blocks b h K s ∧
    HeaderFits w (readings pub 0) (readings m) := by
  intro stat
  have take (f v : ℕ) (hh : P.operand n d b h K s f = some v) :=
    P.resident_at pub m B.old B.fresh B.profile B.gates B.outputs B.width B.off B.ell d n blocks b h K s
      (fun j eq => words.extended j (by rw [eq]; unfold Pointers.operand at hh; split at hh <;> simp_all [fixedFields]))
      words.literal hh
  have z := take 56 _ rfl
  have wi := take 57 _ rfl
  have po := take 62 _ rfl
  have ow := take 77 _ rfl
  have si := take 88 _ rfl
  have tr := take 91 _ rfl
  have bw := take 93 _ rfl
  have sw := take 94 _ rfl
  have scalar (k v : ℕ) (hk : k ∈ fixedFields)
      (chosen : CubeHeaderInstall.operand stat.header d (n+1) (h*b) blocks B.profile
        (Physical.declarationCap n d blocks b h s) k = some v) (fit : v < 2^w) :
      readings m ((pub 0).val+k) = v :=
    resident_operand_at pub m B.old B.fresh B.profile B.gates B.outputs B.width B.off B.ell d n blocks b h s
      (fun j eq => words.extended j (eq ▸ hk)) chosen fit
  have hd : readings m (readings pub 0+59) = d := by
    apply scalar 59 d (by decide) rfl
    have hs : d*d < 2^w := room.install.square
    by_cases zero : d=0
    · simp [zero]
    · exact (Nat.le_mul_of_pos_right d (Nat.pos_of_ne_zero zero)).trans_lt hs
  have head : readings m (readings pub 0+63) = stat.header := by
    apply scalar 63 stat.header (by decide) rfl
    have room' : stat.header+13+2*stat.entries+stat.a < 2^w := room.install.bank
    omega
  have block := scalar 61 (h*b) (by decide) rfl room.block
  obtain ⟨origin,old,store⟩ := words.secondary
  obtain ⟨hb,hp⟩ := secondary_banks stat n (selectorWidth n K h) origin old
  have blocksAt : readings m (stat.header+7) = blocks := (store 7 (by simp)).trans hb
  have packetAt : readings m (stat.header+8) = stat.packetBase := (store 8 (by simp)).trans hp
  obtain ⟨initial,pe⟩ := words.power
  have power : readings m (P.powers+axis.val) = d^axis.val := pe.trans (installed_power initial axis)
  change readings m (readings pub 0+61) = h*b at block
  have zz : readings m (readings pub 0+56) = d^(n+1) := z
  have pw : readings m (readings pub 0+62) = P.powers := po
  refine ⟨?_,?_⟩
  · dsimp only [Layout.fromFrame,Pointers.layout]
    rw [hd,zz,head,words.axisWord,pw,power,show readings m (readings pub 0+77)=P.owners from ow,
      show readings m (readings pub 0+57)=P.widths from wi,show readings m (readings pub 0+91)=P.triples from tr,
      show readings m (readings pub 0+88)=P.singles from si,blocksAt,packetAt,block,
      show readings m (readings pub 0+93)=bankWidth n b h K s from bw,
      show readings m (readings pub 0+94)=selectorWidth n K h from sw,words.core]
  · refine ⟨by have := room.install.primary; omega,?_,?_,by rw [zz]; exact room.square⟩
    · rw [head]; have bound := room.install.bank
      change stat.header+13+2*stat.entries+stat.a < 2^w at bound
      omega
    · rw [pw,head,words.axisWord]; exact (Nat.add_lt_add_left axis.isLt _).trans_le room.powers

end Cube.Padding

end BorderVNP
end Computability
end OAI
