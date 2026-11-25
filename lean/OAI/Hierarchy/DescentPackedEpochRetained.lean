import OAI.Hierarchy.DescentPackedEpochBill

namespace OAI
/-! # Use immutable original epoch shelves after genuine mutable stage executions -/
namespace Hierarchy.DescentPackedEpochShelves
open DescentTerminalEpochChart DescentPackedProfileTape DescentPackedProfileValidity DescentPackedProfileInstall DescentPackedEpochFold
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical
noncomputable section
variable {A : Type} {w : ℕ}

theorem held_reads (s : Stage A) (low high : ℕ) (z : A→ Bool) (org m : Memory w)
    (space : Paid w high s) (base : ∀b∈[s.banks.source,s.banks.starts,s.banks.shifts,s.banks.dictionary],low ≤ b.base)
    (static_ : ∀a,low ≤ a→ a < high→ m a=org a) (original : Reads s.banks org s.source.pin z s.grain) :
    Reads s.banks m s.source.pin z s.grain := by
  have at_ (b : Bank) (mem : b∈[s.banks.source,s.banks.starts,s.banks.shifts,s.banks.dictionary])
      (i : ℕ) (small : i < b.size) : m (b.base+i)=org (b.base+i) := by
    have lo:=base b mem
    have hi:=space.retained b (by simpa using List.mem_append_left [s.banks.count] mem)
    exact static_ _ (by omega) (by omega)
  refine ⟨fun i=>(at_ _ (by simp) _ (i.isLt.trans_le space.space.sourceSize)).trans (original.source i),
    fun i=>(at_ _ (by simp) _ (i.isLt.trans_le space.space.startsSize)).trans (original.starts i),
    fun i h=>(at_ _ (by simp) _ (Nat.lt_of_lt_of_le (by omega) space.space.shiftsSize)).trans (original.shifts i h),
    ?_⟩
  intro i hi key
  let K:=2^(DescentTerminalEpochBits.width s.source.C*s.grain)
  have fit : key.val < K:=key.isLt
  have advance:=Nat.mul_le_mul_right K hi
  apply (at_ s.banks.dictionary (by simp) _ _).trans (original.dictionary i hi key)
  apply Nat.lt_of_lt_of_le _ space.space.dictSize
  change i*K+key.val < (s.grain+1)*K
  rw [Nat.add_mul,Nat.one_mul];omega

theorem data_after {S Z U : Type} {bits : Z→ S→ Bool} {ok : (S→ Bool)→ Prop} {fd : U→ Z}
    (b : Chart bits ok fd) (z : b.Pin→ Bool) (old m : Memory w) (lo C r seed : ℕ) (count exterior : ℕ→ℕ)
    (same : DescentTerminalEpochDecoder.Uniform C b.layout) (pos : 0 < r) (seedLow : seed < lo)
    (lower : ∀p∈shelves r lo 0 b.layout,count p.ordinal < lo ∧ exterior p.ordinal < lo)
    (wide : ∀s∈b.layout,slots s.seats r*r < 2^w) (room : final lo C r b.layout+1 < 2^w)
    (retained : ∀a,lo ≤ a→ a < end_ (lo+extent r b.layout) C r→ m a=header lo C r b.layout z old a)
    : let ts:=controls lo C r b.layout count exterior
      let base:=end_ (lo+extent r b.layout) C r
      Order w base seed (final lo C r b.layout) ts ∧
      (∀s∈ts,Paid w base s) ∧ (∀s∈ts,Reads s.banks m s.source.pin z s.grain) ∧ ts.map Stage.source=b.layout := by
  let head:=lo+extent r b.layout
  let out:=end_ head C r
  let ts:=controls lo C r b.layout count exterior
  obtain ⟨seq,pr,initial,domain⟩:=ready lo C r seed b.layout count exterior z old same pos seedLow lower wide room
  refine ⟨seq,pr,?_,domain⟩
  intro s hs
  apply held_reads s lo out z _ m (pr s hs) _ retained (initial s hs)
  obtain ⟨p,hp,_,bs,_⟩:=phase_mem head C r count exterior out (shelves r lo 0 b.layout) s hs
  have low:=(placed r lo 0 b.layout p hp).1
  have high : lo ≤ head:=Nat.le_add_right _ _
  intro bank hb
  rw [bs] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h|h|h|h <;> subst bank
  · exact low
  · exact low.trans (Nat.le_add_right _ _)
  · exact high
  · exact high.trans (Nat.le_add_right _ _)

/-- The checker runs on the actual post-stage memory. The mutable seed, count,
and exterior registers are observed there, after the native matching passes;
the only equality with the initial input concerns its fixed packed archive. -/
theorem validate_after {S Z U : Type} {bits : Z→ S→ Bool} {ok : (S→ Bool)→ Prop} {fd : U→ Z}
    (b : Chart bits ok fd) (z : b.Pin→ Bool) (old m : Memory w) (lo C r seed : ℕ) (count exterior : ℕ→ℕ)
    (same : DescentTerminalEpochDecoder.Uniform C b.layout) (pos : 0 < r) (seedLow : seed < lo)
    (lower : ∀p∈shelves r lo 0 b.layout,count p.ordinal < lo ∧ exterior p.ordinal < lo)
    (wide : ∀s∈b.layout,slots s.seats r*r < 2^w) (room : final lo C r b.layout+1 < 2^w)
    (retained : ∀a,lo ≤ a→ a < end_ (lo+extent r b.layout) C r→ m a=header lo C r b.layout z old a)
    (seeded : m seed=0 ↔ ok (z∘b.seed))
    (counts : List.IsPrefix ((b.rows z).map Observation.count)
      ((controls lo C r b.layout count exterior).map fun s=>(m s.banks.count.base).val)) :
    let ts:=controls lo C r b.layout count exterior
    let dst:=final lo C r b.layout
    (fold w seed dst ts).Spec (·=m) (fun _ o=>
      (o dst=if (∃t,b.read z=some t) ∧ ∀s∈ts,m s.exterior=0 then 0 else 1) ∧
      ∀i < end_ (lo+extent r b.layout) C r,o i=m i) (bill seed dst ts) ∧ CheapCode (fold w seed dst ts) := by
  obtain ⟨seq,pr,inputs,domain⟩:=data_after b z old m lo C r seed count exterior same pos seedLow lower wide room retained
  exact validated b z m _ _ seed _ seq pr inputs seeded domain counts


end
end Hierarchy.DescentPackedEpochShelves

end OAI
