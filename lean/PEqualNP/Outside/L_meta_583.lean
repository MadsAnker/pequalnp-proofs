import Mathlib
import PEqualNP.Defs
import PEqualNP.Defs.MetaComplexityLgpMono
import PEqualNP.MetaComplexity.Helpers.LocClean
import PEqualNP.MetaComplexity.Helpers.LocRemoval
import PEqualNP.MetaComplexity.Helpers.LocWires
import PEqualNP.MetaComplexity.L106
import PEqualNP.Outside.L_meta_575

set_option maxRecDepth 8192
set_option maxHeartbeats 5000000

namespace PequalNP583

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.Helpers
open PEqualNP.MetaComplexity.Helpers.Readers
open PEqualNP.MetaComplexity.Loc

private theorem restrictPayTwo {n : ℕ} {gs : List Gate} {o : ℕ} {i : Fin (n + 1)}
    (h : MClean (n + 1) gs)
    (hnc : ∃ x y : Fin (n + 1) → Bool,
      vl gs (Function.update x i false) o ≠ vl gs (Function.update y i false) o)
    {p q : ℕ} (hpq : p ≠ q) (hp : RC n gs i false p) (hq : RC n gs i false q) :
    ∃ s, s + 2 ≤ gs.length ∧
      HasMonoSize (n + 1) (fun x => vl gs (Function.update x i false) o) s := by
  classical
  have hcount := elim_count n (statAt n i false, []) gs (clean_nok _ gs h.1) {p, q} (by
    intro r hr
    have hR : RC n gs i false r := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hr
      rcases hr with rfl | rfl <;> assumption
    obtain ⟨g, hg, a, ha, c, hc⟩ := hR
    refine ⟨g, hg, a, ha, ?_, c, hc⟩
    change a < (statAt n i false).length + r
    rw [statAt_length]
    exact (h.1 r g hg).lt a ha)
  have hc2 : ({p, q} : Finset ℕ).card = 2 := by simp [hpq]
  rw [hc2] at hcount
  cases hst : stF n gs i false o with
  | const c =>
    obtain ⟨x, y, hxy⟩ := hnc
    exact False.elim (hxy ((restr_const h.1 (fun _ => rfl) i false c hst x).trans
      (restr_const h.1 (fun _ => rfl) i false c hst y).symm))
  | wire j =>
    have hc : CleanL n (passG n gs i false) :=
      clean_elim n (List.ofFn fun _ : Fin n => false) (by simp) gs _ _
        (fun g hg => (clean_nok _ gs h.1 g hg).1) (inv_at n i false _) (by intro r g hg; simp at hg)
    have hnf : NotFree (passG n gs i false) :=
      Loc.Clean.elim_mono n gs _ h.2 (by intro g hg; simp at hg)
    refine ⟨(passG n gs i false).length, by simpa [passG] using hcount, ?_⟩
    have e : (fun x : Fin (n + 1) → Bool => vl gs (Function.update x i false) o)
        = fun x => vl (passG n gs i false) (x ∘ Fin.succAbove i) j := by
      funext x
      rw [upd_ins, st_val_wire n gs h.1 i false o j hst]
      rfl
    rw [e]
    exact Loc.Clean.relabel_mono (Fin.succAbove i) _ _
      (Loc.Clean.ToolOfClean_proof n (passG n gs i false) j ⟨hc, hnf⟩)

private theorem wireAllTrue {m : ℕ} {gs : List Gate} (h : MClean m gs) :
    ∀ j, j < m + gs.length → vl gs (fun _ : Fin m => true) j = true := by
  intro j
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    intro hj
    by_cases hinput : j < m
    · rw [vl_input gs _ j hinput]
    · let p := j - m
      have hp : p < gs.length := by dsimp [p]; omega
      have hjp : j = m + p := by dsimp [p]; omega
      let g := gs[p]
      have hg : gs[p]? = some g := List.getElem?_eq_some_iff.mpr ⟨hp, rfl⟩
      rcases h.1 p g hg with ⟨hop, _⟩ | ⟨hop, a, b, ha, hb, hab⟩
      · exact False.elim (h.2 g (List.mem_of_getElem? hg) hop)
      · rw [hjp, vl_gate gs h.1 _ p g hg, hab]
        have ha' : vl gs (fun _ : Fin m => true) a = true := ih a (by omega) (by omega)
        have hb' : vl gs (fun _ : Fin m => true) b = true := ih b (by omega) (by omega)
        rcases hop with hop | hop <;> simp [hop, GateOp.eval, ha', hb']

theorem eliminateMarkedPart {n s : ℕ} {f : (Fin (n + 1) → Bool) → Bool}
    (A : Set (Fin (n + 1))) (hne : A.Nonempty)
    (hrest : ∀ i ∈ A, ∃ x y, f (Function.update x i false) ≠ f (Function.update y i false))
    (hact : ∀ i ∈ A, ∃ x y : Fin (n + 1) → Bool, (∀ j ∉ A, x j = true) ∧
      (∀ j, j ≠ i → x j = y j) ∧ f x ≠ f y)
    (hsep : ∀ i ∈ A, ∀ j ∈ A, i ≠ j → ∃ x y : Fin (n + 1) → Bool,
      x i = true ∧ y i = false ∧ x j = false ∧ y j = true ∧
      (∀ k, k ≠ i → k ≠ j → x k = y k) ∧ f x ≠ f y)
    (hs : HasMonoSize (n + 1) f s) :
    ∃ i ∈ A, ∃ t, t + 2 ≤ s ∧ HasMonoSize (n + 1) (fun x => f (Function.update x i false)) t := by
  classical
  obtain ⟨a, ha⟩ := hne
  obtain ⟨x, y, _, hxyEq, hxy⟩ := hact a ha
  have hnc : ∃ x y, f x ≠ f y := ⟨x, y, hxy⟩
  obtain ⟨gs, o, least, hsize⟩ := Loc.Clean.ToolLeast_proof _ _ _ hnc hs
  have clean := least.clean
  have computes (z : Fin (n + 1) → Bool) : vl gs z o = f z := least.2.2.1 z
  have rest (i : Fin (n + 1)) (hi : i ∈ A) :
      ∃ x y, vl gs (Function.update x i false) o ≠ vl gs (Function.update y i false) o := by
    simpa only [computes] using hrest i hi
  have notOutput (i : Fin (n + 1)) (hi : i ∈ A) : o ≠ (i : ℕ) := by
    intro ho
    obtain ⟨u, v, huv⟩ := rest i hi
    apply huv
    rw [ho, vl_input gs _ _ i.isLt, vl_input gs _ _ i.isLt]
    simp
  have readExists : ∃ p, ∃ i ∈ A, Reads gs p i := by
    by_contra! h
    apply hxy
    rw [← computes, ← computes]
    apply Loc.Wires.ToolProp_proof _ gs x y {(a : ℕ)} (o + 1) clean.1
    · intro j hj
      exact hxyEq j (by intro he; subst j; exact hj (by simp))
    · intro p g hp _ _
      exact Or.inl (fun w hw hwa => by
        have he : w = (a : ℕ) := hwa
        exact h p a ha ⟨g, hp, he ▸ hw⟩)
    · omega
    · exact notOutput a ha
  have finish (i : Fin (n + 1)) (hi : i ∈ A) {p q : ℕ}
      (hpq : p ≠ q) (hp : RC n gs i false p) (hq : RC n gs i false q) :
      ∃ i ∈ A, ∃ t, t + 2 ≤ s ∧ HasMonoSize (n + 1) (fun x => f (Function.update x i false)) t := by
    obtain ⟨t, hpay, ht⟩ := restrictPayTwo clean (rest i hi) hpq hp hq
    exact ⟨i, hi, t, by omega, by simpa only [computes] using ht⟩
  by_cases hmult : ∃ i ∈ A, ∃ p q, p ≠ q ∧ Reads gs p i ∧ Reads gs q i
  · obtain ⟨i, hi, p, q, hpq, hp, hq⟩ := hmult
    exact finish i hi hpq (rc_input false hp) (rc_input false hq)
  have unique (i : Fin (n + 1)) (hi : i ∈ A) {p q : ℕ}
      (hp : Reads gs p i) (hq : Reads gs q i) : p = q := by
    by_contra h
    exact hmult ⟨i, hi, p, q, h, hp, hq⟩
  let p := Nat.find readExists
  obtain ⟨i, hi, hread⟩ := Nat.find_spec readExists
  have hp0 : ∀ q < p, ∀ j ∈ A, ¬ Reads gs q j := by
    intro q hq j hj hread'
    exact (Nat.not_lt_of_ge (Nat.find_min' readExists ⟨j, hj, hread'⟩)) hq
  obtain ⟨g, hg, hin⟩ := hread
  have hread : Reads gs p i := ⟨g, hg, hin⟩
  have hbinary : ∃ w < n + 1 + p, g.inputs = [(i : ℕ), w] ∨ g.inputs = [w, (i : ℕ)] := by
    rcases clean.1 p g hg with ⟨hop, _⟩ | ⟨_, u, v, hu, hv, hgs⟩
    · exact False.elim (clean.2 g (List.mem_of_getElem? hg) hop)
    · rw [hgs] at hin
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hin
      rcases hin with he | he
      · subst u
        exact ⟨v, hv, Or.inl hgs⟩
      · subst v
        exact ⟨u, hu, Or.inr hgs⟩
  obtain ⟨w, hw, hinputs⟩ := hbinary
  have hgop : g.op = GateOp.and ∨ g.op = GateOp.or := by
    rcases clean.1 p g hg with ⟨he, _⟩ | ⟨he, _⟩
    · exact False.elim (clean.2 g (List.mem_of_getElem? hg) he)
    · exact he
  rcases hgop with hand | hor
  · have hst : ∃ c, stF n gs i false (n + 1 + p) = Stat.const c := by
      have h := const_of_read n gs (statAt n i false, []) p g hg
        (clean_nok _ gs clean.1 g (List.mem_of_getElem? hg)) i hin
      have hlt : (i : ℕ) < (statAt n i false, ([] : List Gate)).1.length + p := by
        change (i : ℕ) < (statAt n i false).length + p
        rw [statAt_length]
        omega
      have hfix : fixBit g = false := by simp [fixBit, hand]
      have h' := h hlt (by rw [hfix]; exact stF_self n gs i false)
      simpa [statAt_length, stF] using h'
    obtain ⟨c, hc⟩ := hst
    have ho : o ≠ n + 1 + p := by
      intro ho
      obtain ⟨u, v, huv⟩ := rest i hi
      have he : stF n gs i false o = Stat.const c := ho ▸ hc
      exact huv ((restr_const clean.1 (fun _ => rfl) i false c he u).trans
        (restr_const clean.1 (fun _ => rfl) i false c he v).symm)
    obtain ⟨_, hlive⟩ := Loc.Removal.ToolLive_proof _ _ _ _ least hnc
    obtain ⟨q, hq⟩ := hlive p (reads_len hread) ho
    have hr := mem_rdSet.mp hq
    have hlt := reads_lt clean.1 hr
    exact finish i hi (by omega) (rc_input false hread) (rc_of_reads hr ⟨c, hc⟩)
  · have gateOr (z : Fin (n + 1) → Bool) :
        vl gs z (n + 1 + p) = (z i || vl gs z w) := by
      rw [vl_gate gs clean.1 z p g hg, hor]
      rcases hinputs with h | h <;> simp [h, GateOp.eval, Bool.or_comm, vl_input gs z _ i.isLt]
    by_cases hwA : ∃ j ∈ A, (j : ℕ) = w
    · obtain ⟨j, hj, hjeq⟩ := hwA
      have hreadj : Reads gs p j := ⟨g, hg, by
        rcases hinputs with h | h <;> simp [h, hjeq]⟩
      by_cases hji : j = i
      · subst j
        have hAlias : ∀ z : Fin (n + 1) → Bool, vl gs z (n + 1 + p) = vl gs z i := by
          intro z
          rw [gateOr, ← hjeq] 
          simp [vl_input gs z _ i.isLt]
        exact False.elim (Loc.Removal.ToolNoAlias_proof _ _ _ _ least hnc p
          (reads_len hread) i (by omega) hAlias)
      · obtain ⟨u, v, hui, hvi, huj, hvj, huv, hneq⟩ := hsep i hi j hj (Ne.symm hji)
        apply False.elim
        apply hneq
        rw [← computes, ← computes]
        apply Loc.Wires.ToolProp_proof _ gs u v {(i : ℕ), (j : ℕ)} (o + 1) clean.1
        · intro k hk
          exact huv k (by intro he; subst k; exact hk (by simp))
            (by intro he; subst k; exact hk (by simp))
        · intro q gq hgq _ _
          by_cases hqp : q = p
          · subst q
            exact Or.inr (by rw [gateOr, gateOr, ← hjeq, vl_input gs u _ j.isLt,
              vl_input gs v _ j.isLt]; simp [hui, hvi, huj, hvj])
          · refine Or.inl (fun k hk hkd => ?_)
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hkd
            rcases hkd with rfl | rfl
            · exact hqp (unique i hi ⟨gq, hgq, hk⟩ hread)
            · exact hqp (unique j hj ⟨gq, hgq, hk⟩ hreadj)
        · omega
        · simp [notOutput i hi, notOutput j hj]
    · obtain ⟨u, v, hu, huv, hneq⟩ := hact i hi
      let D : Set ℕ := {k | ∃ j ∈ A, (j : ℕ) = k}
      have siblingTrue (z : Fin (n + 1) → Bool) (hz : ∀ j ∉ A, z j = true) :
          vl gs z w = true := by
        rw [← wireAllTrue clean w (by have := reads_len hread; omega)]
        apply Loc.Wires.ToolProp_proof _ gs z (fun _ => true) D (n + 1 + p) clean.1
        · intro k hk
          exact hz k (fun hk' => hk ⟨k, hk', rfl⟩)
        · intro q gq hgq hq _
          exact Or.inl (fun k hk hkd => by
            obtain ⟨j, hj, he⟩ := hkd
            exact hp0 q (by omega) j hj ⟨gq, hgq, he ▸ hk⟩)
        · exact hw
        · exact hwA
      have hv : ∀ j ∉ A, v j = true := by
        intro j hj
        rw [← huv j (fun he => hj (he ▸ hi))]
        exact hu j hj
      apply False.elim
      apply hneq
      rw [← computes, ← computes]
      apply Loc.Wires.ToolProp_proof _ gs u v {(i : ℕ)} (o + 1) clean.1
      · intro j hj
        exact huv j (by intro he; subst j; exact hj (by simp))
      · intro q gq hgq _ _
        by_cases hqp : q = p
        · subst q
          exact Or.inr (by rw [gateOr, gateOr, siblingTrue u hu, siblingTrue v hv]; simp)
        · refine Or.inl (fun k hk hkd => ?_)
          have he : k = (i : ℕ) := hkd
          exact hqp (unique i hi ⟨gq, hgq, he ▸ hk⟩ hread)
      · omega
      · exact notOutput i hi

end PequalNP583

namespace PequalNP583

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.Loc

def spoke (i : Fin 6) : Fin 10 := ⟨i.val + 4, by omega⟩

def ends : Fin 6 → Fin 10 × Fin 10 :=
  ![(0,1), (0,2), (0,3), (1,2), (1,3), (2,3)]

def endOf (i : Fin 6) (v : Fin 10) : Prop := v = (ends i).1 ∨ v = (ends i).2

instance endOfDecidable (i : Fin 6) (v : Fin 10) : Decidable (endOf i v) :=
  inferInstanceAs (Decidable (v = (ends i).1 ∨ v = (ends i).2))

theorem hubBound : ∀ i : Fin 6, (ends i).1.val < 4 ∧ (ends i).2.val < 4 := by decide

theorem separateEnds : ∀ i j : Fin 6, i ≠ j →
    ∃ v : Fin 10, v.val < 4 ∧ endOf i v ∧ ¬ endOf j v := by decide

theorem spoke_injective : Function.Injective spoke := by
  intro i j h
  have hv := congrArg Fin.val h
  apply Fin.ext
  simp only [spoke] at hv
  omega

def active (D : Finset (Fin 6)) : Set (Fin 10) := {v | ∃ i ∉ D, spoke i = v}

def source (D : Finset (Fin 6)) (x : Fin 10 → Bool) : Bool :=
  decide (∃ i : Fin 6, i ∉ D ∧ x (spoke i) = true ∧
    (x (ends i).1 = true ∨ x (ends i).2 = true))

theorem source_true (D : Finset (Fin 6)) (x : Fin 10 → Bool) :
    source D x = true ↔ ∃ i : Fin 6, i ∉ D ∧ x (spoke i) = true ∧
      ∃ v : Fin 10, endOf i v ∧ x v = true := by
  rw [source, decide_eq_true_eq]
  constructor
  · rintro ⟨i, hi, hsp, hu | hv⟩
    · exact ⟨i, hi, hsp, (ends i).1, Or.inl rfl, hu⟩
    · exact ⟨i, hi, hsp, (ends i).2, Or.inr rfl, hv⟩
  · rintro ⟨i, hi, hsp, v, hv, ht⟩
    rcases hv with hv | hv
    · exact ⟨i, hi, hsp, Or.inl (hv ▸ ht)⟩
    · exact ⟨i, hi, hsp, Or.inr (hv ▸ ht)⟩

theorem hub_not_active {D : Finset (Fin 6)} {v : Fin 10} (hv : v.val < 4) :
    v ∉ active D := by
  rintro ⟨i, _, hi⟩
  have h := congrArg Fin.val hi
  simp only [spoke] at h
  omega

theorem end_not_spoke {i j : Fin 6} {v : Fin 10} (hv : endOf i v) : v ≠ spoke j := by
  have hlt : v.val < 4 := by
    rcases hv with hv | hv
    · exact hv.symm ▸ (hubBound i).1
    · exact hv.symm ▸ (hubBound i).2
  intro e
  simp [e, spoke] at hlt

theorem restrictSource (D : Finset (Fin 6)) (i : Fin 6) (x : Fin 10 → Bool) :
    source D (Function.update x (spoke i) false) = source (insert i D) x := by
  apply Bool.eq_iff_iff.mpr
  rw [source_true, source_true]
  constructor
  · rintro ⟨j, hj, hsp, v, hv, hbit⟩
    have hji : j ≠ i := by intro h; subst j; simp at hsp
    have hs : spoke j ≠ spoke i := fun h => hji (spoke_injective h)
    exact ⟨j, by simp [hji, hj], by simpa [Function.update_of_ne hs] using hsp,
      v, hv, by simpa [Function.update_of_ne (end_not_spoke hv)] using hbit⟩
  · rintro ⟨j, hj, hsp, v, hv, hbit⟩
    obtain ⟨hji, hj⟩ : j ≠ i ∧ j ∉ D := by simpa using hj
    have hs : spoke j ≠ spoke i := fun h => hji (spoke_injective h)
    exact ⟨j, hj, by simpa [Function.update_of_ne hs] using hsp,
      v, hv, by simpa [Function.update_of_ne (end_not_spoke hv)] using hbit⟩

private theorem hasRemaining (D : Finset (Fin 6)) (hD : D.card ≤ 2) : ∃ i, i ∉ D := by
  by_contra! h
  have hu : D = Finset.univ := Finset.eq_univ_of_forall h
  simp [hu] at hD

private theorem sourceZero (D : Finset (Fin 6)) : source D (fun _ => false) = false := by
  apply Bool.eq_false_iff.mpr
  simp [source_true]

private theorem sourceOne (D : Finset (Fin 6)) (hD : D.card ≤ 2) :
    source D (fun _ => true) = true := by
  obtain ⟨i, hi⟩ := hasRemaining D hD
  exact (source_true _ _).mpr ⟨i, hi, rfl, (ends i).1, Or.inl rfl, rfl⟩

theorem removeSpoke {s : ℕ} (D : Finset (Fin 6)) (hD : D.card ≤ 1)
    (hs : HasMonoSize 10 (source D) s) :
    ∃ i ∉ D, ∃ t, t + 2 ≤ s ∧ HasMonoSize 10 (source (insert i D)) t := by
  classical
  let A := active D
  obtain ⟨i₀, hi₀⟩ := hasRemaining D (by omega)
  have hne : A.Nonempty := ⟨spoke i₀, i₀, hi₀, rfl⟩
  have hrest : ∀ i ∈ A, ∃ x y, source D (Function.update x i false) ≠
      source D (Function.update y i false) := by
    rintro _ ⟨i, _, rfl⟩
    have hc : (insert i D).card ≤ 2 := le_trans (Finset.card_insert_le i D) (by omega)
    exact ⟨fun _ => false, fun _ => true, by
      rw [restrictSource, restrictSource, sourceZero, sourceOne _ hc]
      decide⟩
  have hact : ∀ i ∈ A, ∃ x y : Fin 10 → Bool, (∀ j ∉ A, x j = true) ∧
      (∀ j, j ≠ i → x j = y j) ∧ source D x ≠ source D y := by
    rintro _ ⟨i, hi, rfl⟩
    let x : Fin 10 → Bool := fun j => decide (j ∉ A)
    let y := Function.update x (spoke i) true
    have hzero : source D x = false := by
      apply Bool.eq_false_iff.mpr
      intro htrue
      obtain ⟨j, hj, hsp, _⟩ := (source_true D x).mp htrue
      exact (of_decide_eq_true hsp) ⟨j, hj, rfl⟩
    have hone : source D y = true := by
      have hup : (ends i).1 ∉ A := hub_not_active (hubBound i).1
      have hneq : (ends i).1 ≠ spoke i := end_not_spoke (Or.inl rfl)
      exact (source_true _ _).mpr ⟨i, hi, by simp [y], (ends i).1, Or.inl rfl,
        by simp [x, y, Function.update_of_ne hneq, hup]⟩
    exact ⟨x, y, fun j hj => by simp [x, hj], fun j hj => by simp [y, Function.update_of_ne hj],
      by simp [hzero, hone]⟩
  have hsep : ∀ i ∈ A, ∀ j ∈ A, i ≠ j → ∃ x y : Fin 10 → Bool,
      x i = true ∧ y i = false ∧ x j = false ∧ y j = true ∧
      (∀ k, k ≠ i → k ≠ j → x k = y k) ∧ source D x ≠ source D y := by
    rintro _ ⟨i, hi, rfl⟩ _ ⟨j, hj, rfl⟩ hij
    have hij' : i ≠ j := fun e => hij (congrArg spoke e)
    obtain ⟨h, hhub, hih, hjh⟩ := separateEnds i j hij'
    have hni : h ≠ spoke i := end_not_spoke hih
    have hnj : h ≠ spoke j := end_not_spoke hih
    let x : Fin 10 → Bool := fun k => decide (k = h ∨ k = spoke i)
    let y : Fin 10 → Bool := fun k => decide (k = h ∨ k = spoke j)
    have hx : source D x = true :=
      (source_true _ _).mpr ⟨i, hi, by simp [x], h, hih, by simp [x]⟩
    have hy : source D y = false := by
      apply Bool.eq_false_iff.mpr
      intro htrue
      obtain ⟨k, _, hs, v, hv, hy⟩ := (source_true D y).mp htrue
      have hhsp : spoke k ≠ h := by
        intro e
        have e' := congrArg Fin.val e
        simp only [spoke] at e'
        omega
      have hkj : k = j := spoke_injective (by simpa [y, hhsp] using hs)
      subst k
      have he : v = h := by simpa [y, end_not_spoke hv] using hy
      exact hjh (he ▸ hv)
    refine ⟨x, y, by simp [x], by simp [y, hni.symm, hij], by simp [x, hnj.symm, hij.symm],
      by simp [y], ?_, by simp [hx, hy]⟩
    intro k hki hkj
    simp [x, y, hki, hkj]
  obtain ⟨v, ⟨i, hi, rfl⟩, t, ht, h⟩ :=
    eliminateMarkedPart A hne hrest hact hsep hs
  have he : (fun x => source D (Function.update x (spoke i) false)) = source (insert i D) :=
    funext (restrictSource D i)
  rw [he] at h
  exact ⟨i, hi, t, ht, h⟩

end PequalNP583

namespace PequalNP583

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.Loc

def relabelResidual (i j : Fin 6) : Fin 10 → Fin 8 :=
  match (min i.val j.val, max i.val j.val) with
  | (0, 1) => ![7, 2, 4, 0, 0, 0, 6, 3, 1, 5]
  | (0, 2) => ![7, 2, 0, 4, 0, 6, 0, 1, 3, 5]
  | (0, 3) => ![2, 7, 4, 0, 0, 3, 1, 0, 6, 5]
  | (0, 4) => ![2, 7, 0, 4, 0, 1, 3, 6, 0, 5]
  | (0, 5) => ![0, 4, 2, 6, 0, 1, 7, 3, 5, 0]
  | (1, 2) => ![7, 0, 2, 4, 6, 0, 0, 1, 5, 3]
  | (1, 3) => ![2, 4, 7, 0, 3, 0, 1, 0, 5, 6]
  | (1, 4) => ![0, 2, 4, 6, 1, 0, 7, 3, 0, 5]
  | (1, 5) => ![2, 0, 7, 4, 1, 0, 3, 6, 5, 0]
  | (2, 3) => ![0, 2, 6, 4, 1, 7, 0, 0, 3, 5]
  | (2, 4) => ![2, 4, 0, 7, 3, 1, 0, 5, 0, 6]
  | (2, 5) => ![2, 0, 4, 7, 1, 3, 0, 5, 6, 0]
  | (3, 4) => ![0, 7, 2, 4, 6, 1, 5, 0, 0, 3]
  | (3, 5) => ![0, 2, 7, 4, 1, 6, 5, 0, 3, 0]
  | (4, 5) => ![0, 2, 4, 7, 1, 5, 6, 3, 0, 0]
  | _ => fun _ => 0

def tailCase (i j : Fin 6) : Bool :=
  decide ((ends i).1 = (ends j).1 ∨ (ends i).1 = (ends j).2 ∨
    (ends i).2 = (ends j).1 ∨ (ends i).2 = (ends j).2)

def modelOriented (tail : Bool) (a b : Fin 8) : Prop :=
  if tail then
    (a.val < 6 ∧ b.val < 6 ∧ (a.val + 1) % 6 = b.val) ∨
      (a = 0 ∧ b = 6) ∨ (a = 6 ∧ b = 7)
  else
    (a.val + 1) % 8 = b.val

instance modelOrientedDecidable (tail : Bool) (a b : Fin 8) :
    Decidable (modelOriented tail a b) := by
  unfold modelOriented
  infer_instance

def mapped (i j : Fin 6) (a b : Fin 8) : Prop :=
  ∃ k : Fin 6, k ≠ i ∧ k ≠ j ∧ ∃ h : Fin 10, endOf k h ∧
    ((relabelResidual i j (spoke k) = a ∧ relabelResidual i j h = b) ∨
     (relabelResidual i j (spoke k) = b ∧ relabelResidual i j h = a))

instance mappedDecidable (i j : Fin 6) (a b : Fin 8) :
    Decidable (mapped i j a b) := by
  unfold mapped
  infer_instance

theorem residualEdges : ∀ i j : Fin 6, i ≠ j → ∀ a b : Fin 8,
    mapped i j a b ↔ modelOriented (tailCase i j) a b ∨ modelOriented (tailCase i j) b a := by
  decide

def cycleFunction (n : ℕ) (x : Fin n → Bool) : Bool :=
  decide (∃ i j : Fin n, (i.val + 1) % n = j.val ∧ x i = true ∧ x j = true)

def residualModel (tail : Bool) (x : Fin 8 → Bool) : Bool :=
  if tail then PEqualNP.Outside.Path575.terminalFun (cycleFunction 6) (0 : Fin 6) x
  else cycleFunction 8 x

theorem residualModel_true (tail : Bool) (x : Fin 8 → Bool) :
    residualModel tail x = true ↔ ∃ a b : Fin 8, modelOriented tail a b ∧ x a = true ∧ x b = true := by
  cases tail
  · simp [residualModel, cycleFunction, modelOriented]
  · simp only [residualModel, ite_true, PEqualNP.Outside.Path575.terminalFun,
      Bool.or_eq_true, Bool.and_eq_true, cycleFunction, decide_eq_true_eq]
    constructor
    · rintro (⟨a, b, hab, ha, hb⟩ | ⟨ha, hb | hb⟩)
      · refine ⟨a.castSucc.castSucc, b.castSucc.castSucc, ?_, ha, hb⟩
        exact Or.inl ⟨a.isLt, b.isLt, hab⟩
      · exact ⟨0, 6, Or.inr (Or.inl ⟨rfl, rfl⟩), hb, ha⟩
      · exact ⟨6, 7, Or.inr (Or.inr ⟨rfl, rfl⟩), ha, hb⟩
    · rintro ⟨a, b, h, ha, hb⟩
      change (a.val < 6 ∧ b.val < 6 ∧ (a.val + 1) % 6 = b.val) ∨
        (a = 0 ∧ b = 6) ∨ (a = 6 ∧ b = 7) at h
      rcases h with ⟨alt, blt, hab⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inl ⟨⟨a.val, alt⟩, ⟨b.val, blt⟩, hab, ha, hb⟩
      · exact Or.inr ⟨hb, Or.inl ha⟩
      · exact Or.inr ⟨ha, Or.inr hb⟩

theorem residualValue {i j : Fin 6} (hne : i ≠ j) (x : Fin 8 → Bool) :
    source {i, j} (x ∘ relabelResidual i j) = residualModel (tailCase i j) x := by
  apply Bool.eq_iff_iff.mpr
  rw [source_true, residualModel_true]
  constructor
  · rintro ⟨k, hk, hs, h, hh, ht⟩
    have hn : k ≠ i ∧ k ≠ j := by simpa using hk
    have hm : mapped i j (relabelResidual i j (spoke k)) (relabelResidual i j h) :=
      ⟨k, hn.1, hn.2, h, hh, Or.inl ⟨rfl, rfl⟩⟩
    rcases (residualEdges i j hne _ _).mp hm with he | he
    · exact ⟨_, _, he, hs, ht⟩
    · exact ⟨_, _, he, ht, hs⟩
  · rintro ⟨a, b, he, ha, hb⟩
    obtain ⟨k, hi, hj, h, hh, he | he⟩ :=
      (residualEdges i j hne a b).mpr (Or.inl he)
    · exact ⟨k, by simp [hi, hj], by simpa only [Function.comp_apply, he.1] using ha,
        h, hh, by simpa only [Function.comp_apply, he.2] using hb⟩
    · exact ⟨k, by simp [hi, hj], by simpa only [Function.comp_apply, he.1] using hb,
        h, hh, by simpa only [Function.comp_apply, he.2] using ha⟩

theorem residualLower {s : ℕ} {tail : Bool} (h : HasCircuitSize 8 (residualModel tail) s) :
    11 ≤ s := by
  cases tail
  · have h' : HasCircuitSize 8 (cycleFunction 8) s := h
    have hs := (PEqualNP.MetaComplexity.L106 8 s (by decide)).mp h'
    norm_num at hs
    omega
  · have h' : HasCircuitSize (6 + 2)
        (PEqualNP.Outside.Path575.terminalFun (cycleFunction 6) (0 : Fin 6)) s := h
    let x : Fin 6 → Bool := fun i => decide (i = 0 ∨ i = 1)
    let y : Fin 6 → Bool := fun _ => false
    let z : Fin 6 → Bool := fun i => decide (i = 0)
    have hx : cycleFunction 6 x = true := by decide
    have hy : cycleFunction 6 y = false := by decide
    have hz : cycleFunction 6 z = false := by decide
    obtain ⟨c, hc, hcs⟩ := PEqualNP.Outside.Path575.terminal_pair (cycleFunction 6) (0 : Fin 6)
      ⟨x, y, by simp [hx, hy]⟩ ⟨y, rfl, hy⟩ ⟨z, rfl, hz⟩ h'
    have hs := (PEqualNP.MetaComplexity.L106 6 c (by decide)).mp hc
    norm_num at hs
    omega

theorem fullLower {s : ℕ} (h : HasMonoSize 10 (source ∅) s) : 15 ≤ s := by
  obtain ⟨j, -, t, ht, hh⟩ := removeSpoke ∅ (by decide) h
  obtain ⟨i, hi, u, hu, hhu⟩ := removeSpoke {j} (by simp) hh
  have hne : i ≠ j := by simpa using hi
  have hres := Loc.Clean.relabel_mono (relabelResidual i j) _ _ hhu
  have he : (fun x => source {i, j} (x ∘ relabelResidual i j)) = residualModel (tailCase i j) :=
    funext (residualValue hne)
  rw [he] at hres
  have := residualLower hres.has
  omega

end PequalNP583

namespace PequalNP583

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.Loc

def postedEdges : List (ℕ × ℕ) :=
  [(0, 4), (4, 1), (0, 5), (5, 2), (0, 6), (6, 3),
    (1, 7), (7, 2), (1, 8), (8, 3), (2, 9), (9, 3)]

theorem postedEdgeEquiv : ∀ u v : Fin 10,
    ((u.val, v.val) ∈ postedEdges ∨ (v.val, u.val) ∈ postedEdges) ↔
      ∃ i : Fin 6, (u = spoke i ∧ endOf i v) ∨ (v = spoke i ∧ endOf i u) := by
  decide

theorem sourceMatches (x : Fin 10 → Bool) :
    source ∅ x = true ↔
      ∃ u v : Fin 10, (u.val, v.val) ∈ postedEdges ∧ x u = true ∧ x v = true := by
  rw [source_true]
  constructor
  · rintro ⟨i, _, hs, v, hv, ht⟩
    rcases (postedEdgeEquiv (spoke i) v).mpr ⟨i, Or.inl ⟨rfl, hv⟩⟩ with he | he
    · exact ⟨spoke i, v, he, hs, ht⟩
    · exact ⟨v, spoke i, he, ht, hs⟩
  · rintro ⟨u, v, he, hu, hv⟩
    obtain ⟨i, ⟨rfl, hend⟩ | ⟨rfl, hend⟩⟩ :=
      (postedEdgeEquiv u v).mp (Or.inl he)
    · exact ⟨i, by simp, hu, v, hend, hv⟩
    · exact ⟨i, by simp, hv, u, hend, hu⟩

theorem refutesPosted : ¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 14 ∧ (∀ x : Fin 10 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 10, (u.val, v.val) ∈ ([(0, 4), (4, 1), (0, 5), (5, 2), (0, 6), (6, 3), (1, 7), (7, 2), (1, 8), (8, 3), (2, 9), (9, 3)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true))) := by
  rintro ⟨C, hmono, hsize, hfun⟩
  have hfan : FanInTwo C := by
    intro g hg
    obtain ⟨hop, hlen⟩ := hmono g hg
    have hop' : g.op = GateOp.and ∨ g.op = GateOp.or := by simpa using hop
    exact ⟨by rcases hop' with h | h <;> simp [h], hlen⟩
  have hnf : NotFree C.gates := by
    intro g hg
    have hop : g.op = GateOp.and ∨ g.op = GateOp.or := by simpa using (hmono g hg).1
    rcases hop with he | he <;> simp [he]
  have exactEval (x : Fin 10 → Bool) : C.eval (List.ofFn x) = source ∅ x :=
    Bool.eq_iff_iff.mpr ((hfun x).trans (sourceMatches x).symm)
  have h := fullLower (s := 14) ⟨C, hfan, hnf, hsize, exactEval⟩
  omega

end PequalNP583

theorem PEqualNP.Outside.L_meta_583 : ¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 14 ∧ (∀ x : Fin 10 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 10, (u.val, v.val) ∈ ([(0, 4), (4, 1), (0, 5), (5, 2), (0, 6), (6, 3), (1, 7), (7, 2), (1, 8), (8, 3), (2, 9), (9, 3)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true))) := PequalNP583.refutesPosted
