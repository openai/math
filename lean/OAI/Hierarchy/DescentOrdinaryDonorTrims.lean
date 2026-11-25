import OAI.Hierarchy.DescentOrdinaryDonorRows

namespace OAI
/-! # Read the normalized endpoint labels from the physical previous donor word -/

namespace Hierarchy.DescentRawCablePanel
open DescentSIMDLookup DescentHostDirectory SiteDecode DescentSixParty GadgetNetwork
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM ThreeFlat.RAM PhysicalProcedure
open DescentSharedCableNames DescentCableDonorNames Computability.BorderVNP.Crossing
open scoped Classical Fin.CommRing
noncomputable section

def lowEnd {loc a : ℕ} (k g slots : ℕ) (e : Cell (loc+1+a)) : Cell a :=
  let decoded:=(endpoint loc a).symm e
  (trim k g slots (flag decoded.1.2) decoded.2.val : ℕ)

/-- The same selected-bit and motif-cluster fields used by the equality test
also determine the two labels within their reached common positions. -/
def roleLow {loc a c : ℕ} (k g slots : ℕ) (dst : Bool) (d : Donor loc a c) : Fin 11→Cell a :=
  let original:=if d.live && !d.picked then lowEnd k g slots (if dst then d.right else d.left) else 0
  let wire (j : Fin 8):=if d.first then lowEnd k g slots
    (d.anchors (cluster d.layout (if dst then supplyDst j else supplySrc j))) else 0
  Fin.cons original (Fin.append (fun _ : Fin 2=>0) wire)

def endpointROM (k g slots loc a c : ℕ) (side : Bool) (word : Cell (bundleBits loc a c)) : Cell (a*11) :=
  encode a 11 (roleLow k g slots side (unpackDonor word))

theorem lowEnd_rooted {V : Type} [Fintype V] [DecidableEq V] {k g slots a loc : ℕ}
    (hub : V→Bool) (x : Key V) (valid : x∈keys k slots) (room : 2^(k+1)*slots≤2^a) (code : Cell loc) :
    (lowEnd k g slots (rooted k slots loc a hub x code)).val=localNumber k slots (mergeHub hub k g x) := by
  have input : localNumber k slots x < 2^a := by
    simpa [trim] using (trim_lt k g slots (fun _=>false) x valid).trans_le room
  have output:= (trim_lt k g slots hub x valid).trans_le room
  rw [trim_key k g slots hub x valid] at output
  simp only [lowEnd,rooted,Equiv.symm_apply_apply,flag_tag,Fin.val_cast_of_lt input,
    trim_key k g slots hub x valid,Fin.val_cast_of_lt output]


section
variable {I P C V F J : Type} [Fintype I] [DecidableEq I] [Fintype V] [DecidableEq V]
    [Field F] [Fintype J] [DecidableEq J] {d : ℕ} {bits : P→ℕ}
variable {W : MarkedWorld F d P bits} {G : PoweredGadget F} {price ε : ℝ}
variable {H R k hCode i a s : ℕ}
variable (A : GroupStage W G price ε J V k) (S : DescentCompiler.AtomSchedule) (ready : A.StateBounds S i)
    (old : W.graph.Edge↪ℕ) (vertex : V↪Fin H) (group : J≃Fin R)
    (pick : I×Fin 2↪W.graph.Edge) (layout : Bool) (pack : W.graph.Site→C)
variable (rank : J×V↪ℕ) (key : Merged W.graph pick layout pack→Key (J×V))
    (hub : J×V→Bool) (g slots : ℕ) (valid : ∀q,key q∈keys hCode slots) (ids : 2^(hCode+1)*slots≤2^a)
variable (profile : I→Profile G.C) (fit : ∀t,W.graph.width (pick t)=A.z*G.b)
local notation "N" => W.graph
local notation "M" => GadgetNetwork.physical W.graph pick (branchWidth G (fun _=>A.z) profile)
local notation "p" => newSite W.graph pick layout pack
local notation "K" => fun u : W.graph.Site => key (p (Sum.inl u))
local notation "c" => normBits A.cap G.b G.C G.k


variable (localID : W.graph.Edge→W.graph.Site→Cell s)
local notation "donor" => measuredDonor (a:=a) (hCode:=hCode) A S ready pick layout pack key hub slots profile localID

include valid ids in
omit [DecidableEq I] in
/-- Every surviving physical role obtains both short labels from its own old
donor word. A selected original or arm has no surviving parent. -/
theorem survivor_label (side : Bool) (e : Live A pick)
    (survives : mergeHub hub hCode g (key (p ((M).src e.val)))≠mergeHub hub hCode g (key (p ((M).dst e.val)))) :
    (roleLow hCode g slots side (donor ⟨anchor pick e.val,e.property⟩) (role e.val)).val =
      localNumber hCode slots (mergeHub hub hCode g (key (p (if side then (M).dst e.val else (M).src e.val)))) := by
  rcases e with ⟨e|⟨j,t⟩|⟨j,t⟩,positive⟩
  · have missing : selected N pick e=none := by
      cases found:selected N pick e with
      | none=>rfl
      | some u=>
        obtain rfl := selected_spec N pick found
        exact False.elim (survives (congrArg (fun v => mergeHub hub hCode g (key v))
          (picked_old N pick layout pack u.1 u.2)))
    cases side
    · simpa [roleLow,measuredDonor,role,anchor,physical,source,target,missing] using
        (lowEnd_rooted (g:=g) hub (K (W.graph.src e)) (valid _) ids (localID e (W.graph.src e)))
    · simpa [roleLow,measuredDonor,role,anchor,physical,source,target,missing] using
        (lowEnd_rooted (g:=g) hub (K (W.graph.dst e)) (valid _) ids (localID e (W.graph.dst e)))
  · exact False.elim (survives (congrArg (fun v=>mergeHub hub hCode g (key v)) (picked_arm N pick layout pack j t)))
  · have rr : role (.inr (.inr (j,t)) : Raw W.graph.Edge I)=Fin.succ (Fin.natAdd 2 t) :=Fin.ext (by simp [role];omega)
    rw [rr]
    let rootedAt (n : Fin 6) := StarKeys.endpoint N pick j (cluster layout n)
    have term (n : Fin 6) := lowEnd_rooted (g:=g) hub (K (rootedAt n)) (valid _) ids
      (localID (pick (j,0)) (rootedAt n))
    cases side
    · simpa [roleLow,measuredDonor,anchor,first_pick,physical,source,target,anchored N pick layout pack,rootedAt]
        using term (supplySrc t)
    · simpa [roleLow,measuredDonor,anchor,first_pick,physical,source,target,anchored N pick layout pack,rootedAt]
        using term (supplyDst t)
end

attribute [local irreducible] Procedure.Exec in
theorem endpoints_emitted {k g slots loc a c H J M w : ℕ} (side : Bool) (banks : Banks) (out : ℕ) (hm : 0<M)
    (fit : Fits banks (bundleBits loc a c) (a*11) M H J w out)
    (rows : Fin H→Fin J→Donor loc a c) (m : Memory w)
    (loaded : PinFrame (M:=M) banks (endpointROM k g slots loc a c side) (fun v j=>packDonor (rows v j)) m) :
    let raw (v : Fin H) (r : Fin (J*11)) := let t:=finProdFinEquiv.symm r;roleLow k g slots side (rows v t.1) t.2
    let last:=image out (H*chunks J M) (lookup banks) m
    (program banks out H J M w).Exec m last (4+44*(H*chunks J M)) ∧
      (∀p : Row H (J*11) (M*11),last (out+(row H (J*11) (M*11) p).val)=((data raw p).val:Word w)) ∧
      ∀x,x<out ∨ out+H*chunks J M≤x→last x=m x := by
  dsimp only
  let raw (v : Fin H) (r : Fin (J*11)):=roleLow k g slots side (rows v (finProdFinEquiv.symm r).1) (finProdFinEquiv.symm r).2
  refine ⟨?_,?_,?_⟩
  · have clock : 4+44*(H*chunks J M)=4+(H*chunks J M)*(2*(lookup banks).work+4) := by
      rw [lookup_work]
      omega
    rw [clock]
    exact @ProtocolRAM.scan_exec w out (H*chunks J M) (lookup banks) m
      (by simp [lookup,Expr.Fits,fit.source,fit.mask,fit.dictionary]) fit.output
  · intro p
    have span:=chunks_group J M 11 hm (by decide)
    let q : Row H J M := (p.1,Fin.cast span p.2)
    have index : (row H (J*11) (M*11) p).val=(row H J M q).val := by
      change p.2.val+chunks (J*11) (M*11)*p.1.val=p.2.val+chunks J M*p.1.val
      exact congrArg (fun n : ℕ => p.2.val+n*p.1.val) span
    rw [index]
    have read:=DescentSixParty.PackedCensus.col_read banks out fit _ _ m loaded q
    have eqn : (fun v j=>endpointROM k g slots loc a c side (packDonor (rows v j)))=groupedRows raw := by
      funext v j
      change encode a 11 (roleLow k g slots side (unpackDonor (packDonor (rows v j)))) =
        encode a 11 (fun s : Fin 11 => raw v (finProdFinEquiv (j,s)))
      rw [unpack_pack]
      apply congrArg (encode a 11)
      funext s
      exact congrArg (fun z : Fin J × Fin 11 => roleLow k g slots side (rows v z.1) z.2)
        (finProdFinEquiv.symm_apply_apply (j,s)).symm
    rw [eqn] at read
    exact read.trans (congrArg (fun n : ℕ=>(n:Word w)) (data_group (by decide : 0<11) raw q p rfl rfl).symm)
  · rintro x (h|h)
    · simp [image,fillSegment,Nat.not_le.mpr h]
    · simp [image,fillSegment,Nat.not_lt.mpr h]


end
end Hierarchy.DescentRawCablePanel

end OAI
