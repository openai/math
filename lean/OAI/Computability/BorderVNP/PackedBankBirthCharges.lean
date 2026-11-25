import OAI.Computability.BorderVNP.PackedBankInheritedSiteCharges
import OAI.Computability.BorderVNP.PackedInheritedPaidState

/-! # Exact resource accounting when a persistent seed site is born

The frozen packet and its actual private table determine the fixed costs.
Clipped-hook equalities contribute nine words and 1,025 public guard nodes
each. All paid visits resolve to the unique local table at the selected count.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited

open CellSparse Crossing BankCharges BankPacket Shortening Shortening.StaticRows
open scoped Classical

private theorem equalityCosts (rs : List Record)
    (hr : ∀ r ∈ rs, ∃ n w s t, r = .equal n w s t) :
    (rs.flatMap Packet.record).length = 9*rs.length ∧ Directory.recordNodes rs = 1025*rs.length := by
  induction rs with
  | nil => exact ⟨rfl,rfl⟩
  | cons r rs ih =>
    obtain ⟨n,w,s,t,rfl⟩ := hr r List.mem_cons_self
    obtain ⟨hword,hguard⟩ := ih (fun u hu => hr u (.tail _ hu))
    constructor
    · simp [Packet.record,Packet.port,hword,Nat.mul_succ]
    · change Directory.recordNodes ([Record.equal n w s t] ++ rs) = _
      rw [Directory.recordNodes_append,hguard]
      simp [Directory.recordNodes,Record.guardMassBound,Nat.mul_succ,Nat.add_comm]

variable {D m : ℕ} {K : Type*} [Field K] (e : PaidIdentity K D m)

/-- The complete intrinsic site directory created by a frozen seed template
with appended clipped equalities. The formulas hold for all installed bit
addresses and every attained count vector. -/
theorem Site.birth_metrics (s : Site) (position : e.Entry → ℕ) (first : Fin D × Bool)
    (v : TemplateSite e) (x : (format e first v).1 → ℕ) (extra : List Record) (j : ℕ) (h : Fin e.count → ℕ)
    (hb : s.boxes = metadata e position v)
    (hr : s.rows = (format e first v).2.map (RecordCode.read x) ++ extra)
    (he : ∀ r ∈ extra, ∃ n w a b, r = .equal n w a b)
    (hx : ResolvedOperands e position first s.boxes h v x) :
    s.staticNodes = InheritedBank.staticLoad e first v + 1034*extra.length ∧
      s.expandedLoad = s.work + bankUses e j h v := by
  let rs := (format e first v).2.map (RecordCode.read x)
  let bs := Directory.resolvedRows s.boxes rs
  have none : Directory.resolvedRows s.boxes extra = [] := by
    apply Directory.resolvedRows_wires
    intro r hm id b c st
    obtain ⟨n,w,a,d,rfl⟩ := he r hm
    simp
  have blocks : s.directory.blocks = bs := by
    change Directory.resolvedRows s.boxes s.rows = _
    rw [hr,Directory.resolvedRows_append,none,List.append_nil]
  have words := encoded_words e position first v x
  change (Packet.fieldList Packet.record rs).length +
    (Packet.fieldList (Packet.fieldList Packet.factor) (metadata e position v)).length = wordCount e first v at words
  obtain ⟨hw,hg⟩ := equalityCosts extra he
  have wg : (Packet.fieldList Packet.record s.rows).length = (Packet.fieldList Packet.record rs).length + 9*extra.length := by
    rw [hr]
    simp only [Packet.fieldList,List.length_cons,List.flatMap_append,List.length_append,hw,rs]
    omega
  have g : Directory.recordNodes s.rows = guardNodes e first v + 1025*extra.length := by
    rw [hr,Directory.recordNodes_append,emitted_recordNodes,hg]
  have t : Directory.tableNodes s.boxes = stored e v := hb ▸ emitted_tableNodes e position v
  obtain ⟨hs,hv⟩ := emitted_blocks e position first s.boxes j h v x hx
  change Directory.blockNodes bs = _ at hs
  change (bs.map fun b => b.copies*b.factors.length).sum = _ at hv
  constructor
  · rw [staticNodes,wg,g,t,blocks,hs,hb,InheritedBank.staticLoad]
    omega
  · rw [expandedLoad,Directory.visitCount,blocks,hv]

namespace PaidSite

variable (position : e.Entry → ℕ) (first : Fin D × Bool) (a : Fin e.count) (v : (e.net a).Site)
  (j : ℕ) (h : Fin e.count → ℕ) (incoming : ℕ)
  (starts : Fin (Fintype.card (PaidBox.Bundle (e.net a) v)) → ℕ)

/-- The actual intrinsic paid birth directory has its fixed sparse template
cost and the exact copy-dependent work/visit volume of the physical output. -/
theorem born_charges :
    let w := PaidBox.widths (e.net a) v
    let born := born w (h a) incoming starts (PaidBox.tableFactor e position a v)
    let site : TemplateSite e := .inr (.inr ⟨a,v⟩)
    born.staticNodes = InheritedBank.staticLoad e first site ∧ born.expandedLoad = volume e j h site := by
  intro w state site
  let x := PaidBinding.fields w (h a) 0 0 (source w (h a) starts)
  have hb : state.boxes = metadata e position site := rfl
  have hr : state.rows = (format e first site).2.map (RecordCode.read x) ++ [] := by
    simp [state,Site.rows,born,PaidBinding.fragment,x,site,format,w]
  have hx : ResolvedOperands e position first state.boxes h site x := ⟨rfl,rfl⟩
  obtain ⟨hs,he⟩ := state.birth_metrics e position first site x [] j h hb hr (by simp) hx
  refine ⟨by simpa using hs,he.trans ?_⟩
  change (h a*(∑ r,w r)+h a*(∑ r,w r)) + h a = h a*(1+2*(∑ r,w r))
  ring

end PaidSite

end Packing.Inherited

end BorderVNP
end Computability
end OAI
