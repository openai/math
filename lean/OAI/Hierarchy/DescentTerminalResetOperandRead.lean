import OAI.Hierarchy.DescentTerminalResetBanks

namespace OAI
/-! # The final seven physical reset fields read the mounted query, old operand and selected candidate -/
namespace Hierarchy.DescentDatedAddressBook.ResetOutput
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM DescentSIMDLookup DescentPackedColony DescentPackedZip
open DescentOperandStateBanks DescentOperandCandidateLookup
noncomputable section
open scoped Fin.CommRing
variable (v : ResetOutput) (ri : v.RankInputs) (s : v.OperandInputs) (base degree : ℕ)
    (bank : v.setup.Sources) (laws : v.setup.Laws)
local notation "A" => v.receiver
local notation "rendered" => v.renderFromRanks ri base
local notation "srcBase" => v.operandDictionaryEnd base

/-- The actual reset program evaluates its argument proposal in this memory. -/
def terminalQueryMemory {w : ℕ} (m : Memory w) : Memory w :=
  (v.keepBook base w).image ((v.setup.code (v.operandFloor base) w bank laws).image
    ((v.controlPhase base bank w).image (v.renderMemory rendered base degree
      ((v.rankBook ri base).memory ((v.rankPortPhase base w).image m)))))

private theorem cast_data {a b H G M : ℕ} (same : a=b) (x : Fin H→Fin G→Cell a) (j : Row H G M) :
    (data (fun h g=>(x h g).cast (congrArg (2^·) same)) j).val=(data x j).val := by
  subst b
  rfl

theorem terminal_field_posted {w : ℕ} (m : Memory w) (nodes : s.nodes=v.nodes) (slots : s.slots=v.argumentSlots)
    (bits : s.coeff=v.nodeBits) (early : v.OperandEarly s rendered w base) (room : v.finalEnd base<2^w)
    (small : 2*(A).candidates<2^(A).queryBits)
    (q : Fin (A).fields→Fin (A).hosts→Fin (A).groups→Option (Fin (2*(A).candidates)))
    (raw : Fin (A).fields→Fin (2*(A).candidates)→Fin (A).hosts→Fin (A).groups→Cell (A).signedBits)
    (kept value : Fin (A).fields→Fin (A).hosts→Fin (A).groups→Cell s.coeff)
    (query : ∀i,Source (s.query i) (fun h g=>code small (q i h g)) (A).lanes
      (v.terminalQueryMemory ri base degree bank laws m))
    (old : ∀i,Source (s.kept i) (kept i) (A).lanes (v.terminalQueryMemory ri base degree bank laws m))
    (fresh : ∀i j,Source (v.previous s rendered base i j) (raw i j) (A).lanes
      (v.terminalQueryMemory ri base degree bank laws m))
    (combine : ∀i h g,(kept i h g).val+
      (selected (q i) (fun j h g=>((raw i j h g).val:Cell s.coeff)) h g).val=(value i h g).val)
    (f : Fin 7) (arg : Fin v.argumentSlots) (x : Fin (A).blocks) :
    Reads (v.terminalField base f arg x) (fun h g=>encode v.nodeBits v.nodes (fun n=>
      (value (v.operandOrdinal s f (arg.cast slots.symm) x (n.cast nodes.symm)) h g).cast (congrArg (2^·) bits)))
      (A).lanes (v.retainedMemory ri s base degree bank laws m) := by
  let index : Fin v.nodeNames→Fin v.nodes→Fin (A).fields := fun p n=>
    (finProdFinEquiv (p,n)).cast (by simpa only [nodeNames,slots,nodes] using s.channels.symm)
  let val := fun p n h g=>(value (index p n) h g).cast (congrArg (2^·) bits)
  have size : (A).fields=v.nodeNames*v.nodes := by simpa only [nodeNames,slots,nodes] using s.channels
  have prior : srcBase+(v.nodeNames*v.nodes)*DescentResetNodeBooks.rows (A).hosts (A).groups (A).lanes≤v.scalarEnd base := by
    change srcBase+_≤ srcBase+(A).fields*_
    rw [size]
    rfl
  have original := v.operand_read s rendered base (v.terminalQueryMemory ri base degree bank laws m) early
    ((v.final_ge base).trans_lt room) small q raw kept value query old fresh combine
  have holds (p:Fin v.nodeNames) (n:Fin v.nodes) :
      Reads (DescentResetNodeBooks.scalar srcBase v.nodes (A).hosts (A).groups (A).lanes p.val n)
        (val p n) (A).lanes (v.rankedMemory ri s base degree bank laws m) := by
    intro j
    have e : (index p n).val=p.val*v.nodes+n.val:=by
      simp [index,finProdFinEquiv_apply_val,Nat.mul_comm,Nat.add_comm]
    have rd:=original (index p n) j
    change _ = ((data (fun h g => (value (index p n) h g).cast (congrArg (2^·) bits)) j).val : Word w)
    rw [cast_data bits (value (index p n)) j]
    simp only [DescentResetNodeBooks.scalar, DescentResetNodeBooks.rows, address, bankBase, e] at rd ⊢
    exact rd
  let part : Fin v.nodeNames:=finProdFinEquiv (page f arg,x)
  have idx (n:Fin v.nodes) : index part n=v.operandOrdinal s f (arg.cast slots.symm) x (n.cast nodes.symm) := by
    apply Fin.ext
    rw [v.operandOrdinal_val]
    simp [index,part,finProdFinEquiv_apply_val,page,nodes,slots,Nat.add_comm,Nat.mul_comm]
  have packed:=DescentResetNodeBooks.posted (v.scalarEnd base) srcBase v.nodeNames v.nodes (A).hosts (A).groups
    v.nodeBits (A).lanes (v.rankedMemory ri s base degree bank laws m) prior room val holds part
  simp only [val, idx] at packed
  exact packed

end
end Hierarchy.DescentDatedAddressBook.ResetOutput

end OAI
