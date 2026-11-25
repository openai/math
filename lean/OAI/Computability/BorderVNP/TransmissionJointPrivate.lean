import OAI.Computability.BorderVNP.TransmissionJointReads

/-! # The private site strings read back from the same physical processor literals -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction

open VPVNP BurstRAM RoutingISA RoutingISA.Pins

/-- The programmed literal's actual bit at the given team, processor and offset.
This includes the common code, control parameters and every distributed advice bit. -/
def Wiring.literalHead {R r t d link inner n : ℕ} {E : Type} (G : Wiring R r t d link inner n E)
    (u j i : ℕ) : Bool :=
  if h : u < R+1 ∧ j < r then (G.program ++ List.ofFn (G.literal ⟨u,h.1⟩ ⟨j,h.2⟩))[i]?.getD false
  else false

private theorem literalRow_eq {R r t d link inner n : ℕ} {E : Type}
    (G : Wiring R r t d link inner n E) (D : Packing.Directory.Layout)
    (u : Fin (R+1)) (j : Fin r) (pin : Fin d → Bool) (ext : Exterior R r link → Bool) (ib hb sb : ℕ)
    (strings : Fin D.entries → Fin D.description → Bool) (F := G.processorFields u pin ext ib hb sb)
    (hf : F = G.processorFields u pin ext ib hb sb := by rfl) (len : (F.literal j).length = D.literal)
    (tail : ∀ i : Fin D.literal, D.literal-D.literal/2 ≤ i.val →
      (F.literal j)[i.val]? = some (D.literalBit G.literalHead strings u j i)) :
    F.literal j = List.ofFn (fun i : Fin D.literal => D.literalBit G.literalHead strings u j i) := by
  subst F
  let row := (G.processorFields u pin ext ib hb sb).literal j
  apply List.ext_getElem
  · exact len.trans List.length_ofFn.symm
  · intro i hi hj
    have inside : i < D.literal := len ▸ hi
    simp only [List.getElem_ofFn]
    by_cases head : i < D.literal-D.literal/2
    · rw [D.literalBit_head _ _ _ _ _ head]
      simp only [Wiring.literalHead,dite_eq_left (And.intro u.isLt j.isLt)]
      change row[i] = row[i]?.getD false
      rw [List.getElem?_eq_getElem hi,Option.getD_some]
    · have h := tail ⟨i,inside⟩ (Nat.le_of_not_gt head)
      simpa only [List.getElem?_eq_getElem hi,Option.some_inj] using h

namespace ProcessorSlots

variable {pc reg k routines m g R r w a d link n e : ℕ} {Q Γ : Type} [Fintype Q]
variable (P : TeamOpcode.Program pc reg k routines) (lib : Fin routines → TeamSite.Macro Q Γ m g)
variable (S : SiteData R r reg k w a) (D : Packing.Directory.Layout) (pack : Fin (R+1) → ReferencePacket w d)
variable (boot geom : GeometryAdvice.Stripe) (bootBits geomBits : Fin (R+1) → List Bool)
variable (strings : Fin D.entries → Fin D.description → Bool)
variable (fit : Fits P lib r w a R link n e)
variable (pin : Fin d → Bool) (ext : Exterior R r link → Bool)

local notation "start" => freeStart P lib r w n
local notation "sites" => S.joint D start pack boot geom bootBits geomBits strings
local notation "wired" => wiring P lib sites d link n e fit

/-- Every word of the full self-reading literal coincides with the input expected by
the private-data directory. The head is the actual programmed literal, and every
reserved suffix bit is constructed from the original network's private descriptions. -/
theorem joint_literal_row (room : JointRoom D start a boot geom) (u : Fin (R+1)) (j : Fin r)
    (ib hb sb : ℕ) :
    ((wired).processorFields u pin ext ib hb sb).literal j =
      List.ofFn (fun i : Fin D.literal => D.literalBit (wired).literalHead strings u j i) := by
  let F := (wired).processorFields u pin ext ib hb sb
  obtain ⟨pref,len,eq⟩ := literal_split P lib sites link n e fit u j pin ext ib hb sb
  have lf : (F.literal j).length = D.literal := by
    change (((wired).processorFields u pin ext ib hb sb).literal j).length = _
    rw [eq,List.length_append,List.length_ofFn,len,room.literal]
  apply literalRow_eq (wired) D u j pin ext ib hb sb strings F rfl lf
  intro i before
  have hstart := room.bootStart
  have hboot := room.bootEnd
  have hgeo := room.geomEnd
  exact (joint_free_at P lib S D pack boot geom bootBits geomBits strings fit u pin ext ib hb sb
    room j (by omega : start ≤ i.val) i.isLt).trans
      (congrArg some (literalBit_tail D _ _ _ _ _ _ before))

/-- Original site bits occupy genuine populated delivery records on real source teams,
and are read verbatim after the substituted index has been prepared. The literals
are constructed jointly with the same two advice stripes and distributed H*. -/
theorem joint_private_source (room : JointRoom D start a boot geom) (teams : D.teams = R+1)
    (procs : D.processors = r) (pos : 0 < r) (tail : 0 < D.literal/2)
    (short : D.description ≤ D.literal/2) (capacity : D.entries*D.description ≤ D.teams*D.processors*(D.literal/2))
    (pp lp : ℕ → ℕ × ℕ) (entry : Fin D.entries) (b : Fin D.description)
    (ib hb sb : Fin (R+1) → ℕ) (guess : Fin (R+1) → ℕ → Bool) (mem : Fin (R+1) → Memory w)
    (loaded : ∀ u, ((wired).processorFields u pin ext (ib u) (hb u) (sb u)).ContainsInput (mem u))
    (scratch : ∀ u, let L := (wired).pinLayout u (ib u) (hb u) (sb u)
      L.processors*L.stride ≤ L.ibase ∧ L.processors*L.stride ≤ L.hbase) :
    ∃ row ∈ D.directory pp lp, ∃ j < row.width, ∃ u : Fin (R+1),
      row.team = u.val ∧ row.cell = (pp entry).1 ∧ row.slot+j = (pp entry).2+b.val ∧
        let L := (wired).pinLayout u (ib u) (hb u) (sb u)
        preparedMemory L (guess u) (mem u) L.count (row.sourceBase L+j) = Fin.ofNat _ (strings entry b).toNat := by
  obtain ⟨row,hm,j,hj,field,hu,hp,ho,hcell,hslot,hbit⟩ := D.private_literal_row pp lp (wired).literalHead strings entry b
    (procs ▸ pos) tail short capacity
  let u : Fin (R+1) := ⟨row.team, teams ▸ hu⟩
  let L := (wired).pinLayout u (ib u) (hb u) (sb u)
  let F := (wired).processorFields u pin ext (ib u) (hb u) (sb u)
  let q : Fin r := ⟨row.processor, procs ▸ hp⟩
  refine ⟨row,hm,j,hj,u,rfl,hcell,hslot,?_⟩
  have programmed := joint_literal_row P lib S D pack boot geom bootBits geomBits strings fit pin ext room u q
    (ib u) (hb u) (sb u)
  change F.literal q = _ at programmed
  have length : L.literal = D.literal := (F.literal_length q).symm.trans
    ((congrArg List.length programmed).trans List.length_ofFn)
  have read := row.literal_source L F (guess u) (mem u) (loaded u) j field q.isLt (length ▸ ho)
    (scratch u).1 (scratch u).2
  change preparedMemory L (guess u) (mem u) L.count (row.sourceBase L+j) = _
  rw [read]
  change TeamTapeInputEmit.headerWord w (F.literal q) (row.offset+j) = _
  rw [programmed]
  simp [TeamTapeInputEmit.headerWord, ho, u, q, hbit]

end ProcessorSlots
end TeamContraction

end BorderVNP
end Computability
end OAI
