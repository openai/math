import OAI.Hierarchy.ProtocolRAMSupergroupDirectory

namespace OAI
/-! # Both translated endpoint banks for every candidate, including dormant rows -/

namespace Hierarchy.ProtocolRAMPackedAnchorPair

open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure DescriptorExpr
open ProtocolRAM ProtocolRAMGeneratedWrite ProtocolRAMSupergroupPorts
open TaggedShorterSupergroups
open scoped Fin.CommRing
variable {W N K lanes H : ℕ} {G : Type*} {size : G→ℕ}

/-- Unconditional machine-word semantics: foreign dormant rows can index any wrapped
ROM slot and the physical published word is still specified. -/
theorem read_words (groupOut baseOut : ℕ) (groups offsets localBase : Bank) (old : Expr) (mem : Memory W)
    (low : old.Fits W groupOut) (bf : offsets.Fits W groupOut) (lf : localBase.Fits W groupOut)
    (sep : groupOut+N ≤ baseOut) (i : Fin N) :
    let result := ProtocolRAMSupergroupPorts.image N groupOut baseOut groups offsets localBase old mem
    let ref := old.eval mem (i.val:Word W)
    result (groupOut+i.val)=groups.read mem ref ∧
    result (baseOut+i.val)=offsets.read mem ref+localBase.read mem (i.val:Word W) := by
  intro result ref
  let first := ProtocolRAM.image groupOut N (groupExpr groups old) mem
  constructor
  · exact (frame_image baseOut N (baseExpr offsets localBase old) first (groupOut+i.val)
      (Or.inl ((Nat.add_lt_add_left i.isLt _).trans_le sep))).trans (read_image groupOut N _ mem i)
  · have ok : (baseExpr offsets localBase old).Fits W groupOut := ⟨⟨bf,low⟩,lf,trivial⟩
    exact (read_image baseOut N (baseExpr offsets localBase old) first i).trans
      (eval_below (baseExpr offsets localBase old) (i.val:Word W) mem first ok (fun a lo=>frame_image groupOut N _ mem a (.inl lo)))

/-- Only the row under consideration must have a real owner and an actual port; no
global choice of owners or ports for empty rows occurs in the directory lookup. -/
theorem read_live (groupOut baseOut start : ℕ) (owners : Fin K≃G) (dir : Directory size H)
    (localBase : Bank) (old : Expr) (mem : Memory W) (i : Fin N) (g : G) (port : Fin (size g))
    (fit : K ≤ 2^W) (low : old.Fits W groupOut) (bf : (ProtocolRAMSupergroupDirectory.offsetBank start K).Fits W groupOut)
    (lf : localBase.Fits W groupOut) (sep : groupOut+N ≤ baseOut)
    (oldData : old.eval (ProtocolRAMSupergroupDirectory.mount start lanes owners dir mem) (i.val:Word W)=
      ((owners.symm g).val:Word W))
    (baseData : localBase.read (ProtocolRAMSupergroupDirectory.mount start lanes owners dir mem) (i.val:Word W)=
      ((port.val*lanes:ℕ):Word W)) :
    let result := ProtocolRAMSupergroupPorts.image N groupOut baseOut (ProtocolRAMSupergroupDirectory.groupBank start K)
      (ProtocolRAMSupergroupDirectory.offsetBank start K) localBase old
      (ProtocolRAMSupergroupDirectory.mount start lanes owners dir mem)
    result (groupOut+i.val)=((dir.group g).val:Word W) ∧
    result (baseOut+i.val)=(((dir.slot g port).val*lanes:ℕ):Word W) := by
  intro result
  obtain ⟨gs,bs⟩ := read_words groupOut baseOut (ProtocolRAMSupergroupDirectory.groupBank start K) _ localBase old _ low bf lf sep i
  have rom := ProtocolRAMSupergroupDirectory.resident start lanes owners dir mem fit g
  rw [oldData,rom.1] at gs
  rw [oldData,rom.2,baseData] at bs
  refine ⟨gs,?_⟩
  simpa only [Directory.slot,Nat.add_mul,Nat.cast_add] using bs

def program (W N g₁ l g₂ r : ℕ) (groups offsets left right : Bank) (old : Expr) :=
  (ProtocolRAMSupergroupPorts.program W N g₁ l groups offsets left old).seq
    (ProtocolRAMSupergroupPorts.program W N g₂ r groups offsets right old)

theorem run (g₁ l g₂ r : ℕ) (groups offsets left right : Bank) (old : Expr) (mem : Memory W)
    (low : old.Fits W g₁) (gf : groups.Fits W g₁) (bf : offsets.Fits W g₁)
    (lf : left.Fits W g₁) (rf : right.Fits W g₁)
    (sep1 : g₁+N ≤ l) (apart : l+N ≤ g₂) (sep2 : g₂+N ≤ r) (endFit : r+N < 2^W) :
    ∃ out,(program W N g₁ l g₂ r groups offsets left right old).Exec mem out
      (ProtocolRAMSupergroupPorts.work N old+ProtocolRAMSupergroupPorts.work N old) ∧
      (∀ i : Fin N,let ref:=old.eval mem (i.val:Word W)
        out (g₂+i.val)=groups.read mem ref ∧ out (l+i.val)=offsets.read mem ref+left.read mem (i.val:Word W) ∧
        out (r+i.val)=offsets.read mem ref+right.read mem (i.val:Word W)) ∧
      ∀a < g₁,out a=mem a := by
  let m₁ := ProtocolRAMSupergroupPorts.image N g₁ l groups offsets left old mem
  let m₂ := ProtocolRAMSupergroupPorts.image N g₂ r groups offsets right old m₁
  have keep1 (a : ℕ) (ha : a < g₁) : m₁ a=mem a := ProtocolRAMSupergroupPorts.frame g₁ l groups offsets left old mem a (.inl ha) (.inl (by omega))
  have keep2 (a : ℕ) (ha : a < g₂) : m₂ a=m₁ a := ProtocolRAMSupergroupPorts.frame g₂ r groups offsets right old m₁ a (.inl ha) (.inl (by omega))
  have before (b : Bank) (h : b.Fits W g₁) : b.Fits W g₂ := ⟨h.1,h.2.1,h.2.2.trans (by omega)⟩
  have old2 := fits_mono old (show g₁ ≤ g₂ by omega) low
  have same (b : Bank) (h : b.Fits W g₁) (v : Word W) : b.read m₁ v=b.read mem v := by
    apply keep1
    exact (Nat.add_lt_add_left (Nat.mod_lt v.val h.1) _).trans_le h.2.2
  have p1 : (ProtocolRAMSupergroupPorts.program W N g₁ l groups offsets left old).Exec mem m₁
      (ProtocolRAMSupergroupPorts.work N old) := ProtocolRAMSupergroupPorts.run g₁ l _ _ _ _ mem low gf bf lf sep1 (by omega)
  have p2 : (ProtocolRAMSupergroupPorts.program W N g₂ r groups offsets right old).Exec m₁ m₂
      (ProtocolRAMSupergroupPorts.work N old) := ProtocolRAMSupergroupPorts.run g₂ r _ _ _ _ m₁ old2
        (before _ gf) (before _ bf) (before _ rf) sep2 endFit
  refine ⟨m₂,?_,?_,fun a ha=>(keep2 a (by omega)).trans (keep1 a ha)⟩
  · intro P R K mach pc reg pub exit install data cfg raw entry eq
    exact Procedure.Exec.then p1 p2 mach pc reg pub exit install data cfg raw entry eq
  · intro i ref
    obtain ⟨_,leftWord⟩ := read_words g₁ l groups offsets left old mem low bf lf sep1 i
    obtain ⟨gWord,rightWord⟩ := read_words g₂ r groups offsets right old m₁ old2 (before _ bf) (before _ rf) sep2 i
    have addr := eval_below old (i.val:Word W) mem m₁ low keep1
    rw [addr,same _ gf] at gWord
    rw [addr,same _ bf,same _ rf] at rightWord
    exact ⟨gWord,(keep2 _ (by have := i.isLt;omega)).trans leftWord,rightWord⟩


end Hierarchy.ProtocolRAMPackedAnchorPair

end OAI
