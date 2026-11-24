import OAI.Computability.VPVNP.PairSimulationLeafFieldCode

/-! # Correctness of the private length and value rows for a scalar field -/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.LeafStartup.Staging

open BurstRAM PrivateRAM RAMTape PrimedCounter.GuessWord
open scoped Fin.CommRing

variable {d e w k p r pubs : ℕ}

/-- The staging bank contains the constants, dimensions, fuel, site words and public operands
of the specified virtual input. -/
structure Sources (x : VirtualSite.Input d e w) (pub : Fin k → Word w) (bank : Reg k → Word w) : Prop where
  zero : bank .zero = 0
  one : bank .one = 1
  d : bank .d = (d : Word w)
  width : bank .width = (w : Word w)
  bucket : bank .bucket = ((2^e : ℕ) : Word w)
  fuel : bank .fuel = (x.fuel : Word w)
  address : bank .address = x.addrWord
  initial : bank .initial = x.initialWord
  header : bank .header = x.headerWord
  operand : ∀ i, bank (.operand i) = pub i

private theorem cast_word {a : ℕ} (ha : a < 2^w) : (a : Word w) = ⟨a,ha⟩ :=
  Fin.ext (Nat.mod_eq_of_lt ha)

theorem stagedWords (x : VirtualSite.Input d e w) (pub : Fin k → Word w) (bank : Reg k → Word w)
    (ready : Sources x pub bank) (f : Field k) :
    let dst := (code f).foldl applyLine bank
    dst (.out .len) = ((source x pub f).2.1 : Word w) ∧ dst (.out .value) = (source x pub f).2.2 := by
  have ha : x.addrWord = (x.v.val : Word w) := (cast_word x.addrWord.isLt).symm
  have hlo : SiteEndpoints.startWord e w x.v x.hcap = ((x.v.val*2^e : ℕ) : Word w) :=
    (cast_word (SiteEndpoints.startWord e w x.v x.hcap).isLt).symm
  have hhi : SiteEndpoints.endWord e w x.v x.hcap = (((x.v.val+1)*2^e : ℕ) : Word w) :=
    (cast_word (SiteEndpoints.endWord e w x.v x.hcap).isLt).symm
  have hcap : (⟨2^d*2^e,x.hc⟩ : Word w) = ((2^d*2^e : ℕ) : Word w) := (cast_word x.hc).symm
  have hpos : 1 ≤ 2*2^e := by have := Nat.two_pow_pos e; omega
  have hd : d < w := (Nat.le_add_right d e).trans_lt x.hcap
  have dx : d % 2^w = d := Nat.mod_eq_of_lt (hd.trans (Nat.lt_two_pow_self (n := w)))
  have one : 1 % 2^w = 1 := Nat.mod_eq_of_lt (Nat.one_lt_two_pow (by have := x.hw; omega))
  cases f <;> simp [code,applyLine,Rhs.eval,source,ready.zero,ready.one,ready.d,ready.width,
    ready.bucket,ready.fuel,ready.address,ready.initial,ready.header,ready.operand,Function.update,
    dx,one,hd,Nat.shiftLeft_eq,ha,hlo,hhi,hcap,choiceBound,Nat.cast_sub hpos,BinaryOp.eval] <;> ring

/-- The staging rows feed the filler with its exact length and word, and leave
private memory and every register outside the three output slots untouched. -/
theorem stage_run (x : VirtualSite.Input d e w) (pub : Fin k → Word w) (f : Field k)
    (M : Machine w p r pubs) (ports : Reg k ↪ Fin r) (pc : Fin ((code f).length+1) → Fin p)
    (link : ∀ i : Fin (code f).length, M.code (pc i.castSucc) = instruction ports (pc i.succ) (code f)[i])
    (c : Config w p r) (entry : c.pc = pc 0) (ready : Sources x pub (c.reg ∘ ports)) (fit : SourceFit x) :
    ∃ post, Prefix M c (List.replicate (code f).length .tick) post ∧ post.pc = pc (Fin.last (code f).length) ∧
      post.privateMem = c.privateMem ∧ post.persistent = c.persistent ∧
      (post.reg (ports (.out .len))).val = (source x pub f).2.1 ∧
      post.reg (ports (.out .value)) = (source x pub f).2.2 ∧
      ∀ j, (∀ o, j ≠ ports (.out o)) → post.reg j = c.reg j := by
  have hr := run M ports (code f) pc link c entry
  have eq := physical_at ports (code f) c.reg
  have h := stagedWords x pub (c.reg ∘ ports) ready f
  have hl := (congrFun eq (.out .len)).trans h.1
  have hv := (congrFun eq (.out .value)).trans h.2
  have hn := congrArg Fin.val hl
  exact ⟨_, hr, rfl, rfl, rfl, hn.trans (Nat.mod_eq_of_lt (fit.length pub f)), hv, fun j hj => physical_outside ports (code f) c.reg j hj⟩

end PairSimulation.LeafStartup.Staging

end VPVNP
end Computability
end OAI
