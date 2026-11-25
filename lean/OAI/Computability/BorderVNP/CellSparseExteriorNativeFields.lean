import OAI.Computability.BorderVNP.CellSparseExteriorNative

/-! # Genuine gap and live-field emissions of the sparse exterior writer -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.SparseExterior.Native

open VPVNP.BurstRAM CellPacketEncode RationalHitting.StackLanguage

variable {w : ℕ} {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8}

/-- Compose two physical writes while retaining their exact memory images
and the instruction trace of the first pass. -/
theorem append_run {a b : Code} {s : Bank w} {m : Memory w} {d f : ℕ} {bs cs : List Bool}
    (first : BoundedRun pub mac a s m d (Output (.ofWords s m) bs))
    (rest : ∀ t mt es, Runs pub mac a s m es t mt → Output (.ofWords s m) bs (.ofWords t mt) →
      BoundedRun pub mac b t mt f (Output (.ofWords t mt) cs)) :
    BoundedRun pub mac (.seq a b) s m (d+f) (Output (.ofWords s m) (bs++cs)) := by
  obtain ⟨es,t,mt,r,hr,eff⟩ := first
  obtain ⟨fs,z,mz,g,hg,out⟩ := rest t mt es r eff
  exact ⟨_,z,mz,r.seq g,(VPVNP.RAMBuckets.cost_append ..).trans_le (Nat.add_le_add hr hg),eff.append out⟩

/-- Physical preservation of the constants consumed by all field encoders. -/
theorem keeps_constants {c : Code} {s m t mt es} (r : Runs pub mac c s m es t mt)
    (h₀ : c.keeps 0=true) (h₁ : c.keeps 1=true) (h₂ : c.keeps 18=true)
    (h : Constants (readings s)) : Constants (readings t) :=
  ⟨(congrArg Fin.val (r.keepsReg h₀)).trans h.1,(congrArg Fin.val (r.keepsReg h₁)).trans h.2.1,
    (congrArg Fin.val (r.keepsReg h₂)).trans h.2.2⟩

/-- Write one list marker directly to shared memory. -/
theorem marker_run (v : Reg) (b : Bool) (s : Bank w) (m : Memory w) (const : Constants (readings s))
    (sep : v ≠ 20) (val : readings s v = b.toNat) (room : readings s 20+1<2^w) :
    BoundedRun pub mac (emit false v) s m 4 (Output (.ofWords s m) [b]) :=
  (emit_run false s m v sep b val const room).mono le_rfl fun _ h => ⟨h.cursor,h.mem⟩

/-- Encode an arbitrary fitting gap in time linear in its binary width. -/
theorem gap_run (s : Bank w) (m : Memory w) (a : ℕ) (const : Constants (readings s))
    (reg : readings s 16=a) (room : readings s 20+(codeWord a.bits).length<2^w) :
    BoundedRun pub mac gap s m (11*a.bits.length+3) (Output (.ofWords s m) (codeWord a.bits)) := by
  rw [codeWord_pair] at room ⊢
  simp only [List.length_append,List.length_singleton] at room
  have core := inner_run (pub:=pub) (macros:=mac) false a s m const reg
    (by change readings s 20+(pairWord a.bits).length<2^w; omega)
  apply (append_run (first := core.mono le_rfl fun z h => (⟨h.2.1,h.2.2⟩ : Output _ (pairWord a.bits) z))
    (f:=2) ?_).mono (by omega) fun _ h => h
  intro t mt es r eff
  have cursor : readings t 20=readings s 20+(pairWord a.bits).length := eff.cursor
  exact (CellPacketCopy.appendOne_run t mt (keeps_constants r (by decide) (by decide) (by decide) const)
    (by omega)).mono le_rfl fun _ h => ⟨h.cursor,h.mem⟩

/-- Read every true live bit once, quoting its value, then emit the delimiter. -/
theorem value_run (s : Bank w) (m : Memory w) (bs : List Bool) (const : Constants (readings s))
    (stop : readings s 15=readings s 14+bs.length) (input : CompactWrite.Source m (readings s 14) bs)
    (apart : CompactWrite.Disjoint (readings s 14) bs.length (readings s 20) (codeWord bs).length)
    (room : readings s 20+(codeWord bs).length<2^w) :
    BoundedRun pub mac value s m (7*bs.length+3) (Output (.ofWords s m) (codeWord bs)) := by
  rw [codeWord_pair] at apart room ⊢
  simp only [List.length_append,List.length_singleton] at apart room
  have core := CellPacketCopy.copy_run (pub:=pub) (macros:=mac) true s m bs const stop
    (fun i => input i i.isLt) (split_apart apart).1
    (by change readings s 20+(pairWord bs).length<2^w; omega)
  apply (append_run (first := core.mono le_rfl fun z h => (⟨h.2.2.1,h.2.2.2⟩ : Output _ (pairWord bs) z))
    (f:=2) ?_).mono (by omega) fun _ h => h
  intro t mt es r eff
  have cursor : readings t 20=readings s 20+(pairWord bs).length := eff.cursor
  exact (CellPacketCopy.appendOne_run t mt (keeps_constants r (by decide) (by decide) (by decide) const)
    (by omega)).mono le_rfl fun _ h => ⟨h.cursor,h.mem⟩

/-- An arbitrary disjoint raw source retains its bits after an encoded prefix. -/
theorem Output.source {s t : Bank w} {m mt : Memory w} {bs cs : List Bool}
    (effect : Output (.ofWords s m) bs (.ofWords t mt)) {addr : ℕ}
    (apart : CompactWrite.Disjoint addr cs.length (readings s 20) bs.length)
    (input : CompactWrite.Source m addr cs) : CompactWrite.Source mt addr cs := by
  intro i hi
  exact (effect.unchanged apart hi).trans (input i hi)

end RoutingISA.SparseExterior.Native

end BorderVNP
end Computability
end OAI
