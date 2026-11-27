import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Algebra.Order.Round
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Algebra.BigOperators.Module
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Complex.JensenFormula
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.MellinInversion
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.Meromorphic.Divisor
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Periodic
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.DirichletCharacter.Bounds
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Order.Filter.AtTopBot.Ring
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Choose
import Mathlib.Tactic.FunProp
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.NumberTheory.MulChar.Lemmas
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Order.Interval.Finset.SuccPred
import Mathlib.Tactic.GCongr
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.MeasureTheory.Integral.Bochner.Set

/- Adapted from DNZJSJ, Goldbach PR #2486 (f3613cf846dfb3e7fe7d04fe6ce51c6ee25e7d4f), Apache-2.0.
   Earlier source attributions are retained below. -/

section GoldbachDeepFourthPrimeDenominator

namespace GoldbachFourthMoment
open Finset

noncomputable def phase (x : ℝ) : ℂ := Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)

theorem phase_add (x y : ℝ) : phase (x + y) = phase x * phase y := by
  unfold phase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

-- Finite character calculation adapted from DFQDZZ, goldbach-proofs PR 316.
theorem full_phase_sum (q h : ℕ) (hq : 0 < q) :
    (∑ a ∈ range q, phase ((h : ℝ) * a / q)) = if q ∣ h then (q : ℂ) else 0 := by
  let : NeZero q := ⟨hq.ne'⟩
  calc
    _ = ∑ x : ZMod q, ZMod.stdAddChar ((h : ZMod q) * x) := by
      apply Finset.sum_bij (fun (a : ℕ) _ => (a : ZMod q))
      · intro a ha
        exact mem_univ _
      · intro a ha b hb hab
        simpa only [ZMod.val_natCast_of_lt (mem_range.mp ha),
          ZMod.val_natCast_of_lt (mem_range.mp hb)] using congrArg ZMod.val hab
      · intro x _
        exact ⟨x.val, mem_range.mpr x.val_lt, ZMod.natCast_zmod_val x⟩
      · intro a _
        have cast_eq : (h : ZMod q) * a = ((h * a : ℕ) : ℤ) := by push_cast; rfl
        rw [cast_eq, ZMod.stdAddChar_coe]
        dsimp [phase]
        congr 1
        push_cast
        ring
    _ = _ := by
      by_cases hd : q ∣ h
      · have hz : (h : ZMod q) = 0 := (ZMod.natCast_eq_zero_iff h q).mpr hd
        simp [hd, hz, ZMod.card]
      · have hz : (h : ZMod q) ≠ 0 := fun hz => hd ((ZMod.natCast_eq_zero_iff h q).mp hz)
        rw [ite_eq_right hd]
        exact AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar q hz)

theorem prime_phase_sum {q : ℕ} (hq : q.Prime) (h : ℕ) :
    (∑ a ∈ (range q).filter (fun a => a.Coprime q), phase ((h : ℝ) * a / q)) =
      (if q ∣ h then (q : ℂ) else 0) - 1 := by
  have hF : (range q).filter (fun a => a.Coprime q) = range q \ {0} := by
    ext a
    simp only [mem_filter, mem_sdiff, mem_singleton]
    constructor
    · rintro ⟨ha, hc⟩
      refine ⟨ha, ?_⟩
      rintro rfl
      exact hq.ne_one (by simpa using hc)
    · rintro ⟨ha, hz⟩
      refine ⟨ha, (hq.coprime_iff_not_dvd.mpr ?_).symm⟩
      exact fun hd => hz (Nat.eq_zero_of_dvd_of_lt hd (mem_range.mp ha))
  have hsub : ({0} : Finset ℕ) ⊆ range q := by simpa using hq.pos
  rw [hF]
  calc
    _ = (∑ a ∈ range q, phase ((h : ℝ) * a / q)) -
        (∑ a ∈ ({0} : Finset ℕ), phase ((h : ℝ) * a / q)) :=
      eq_sub_of_add_eq (sum_sdiff hsub)
    _ = _ := by rw [full_phase_sum q h hq.pos]; simp [phase]

noncomputable def primeWeight (k : ℕ) : ℝ := if k.Prime then Real.log (k : ℝ) else 0

noncomputable def primeSum (n : ℕ) (t : ℝ) : ℂ :=
  ∑ k ∈ range (n + 1), (primeWeight k : ℂ) * phase ((k : ℝ) * t)

theorem sum_prime_centers {n q : ℕ} (hq : q.Prime) (hqn : q ≤ n) (β : ℝ) :
    ∑ a ∈ (range q).filter (fun a => a.Coprime q), primeSum n ((a : ℝ) / q + β) =
      -primeSum n β + (q : ℂ) * (Real.log (q : ℝ) : ℂ) * phase ((q : ℝ) * β) := by
  let centers := (range q).filter (fun a => a.Coprime q)
  let term (k : ℕ) := (primeWeight k : ℂ) * phase ((k : ℝ) * β)
  have hphase (k a : ℕ) : (primeWeight k : ℂ) * phase ((k : ℝ) * (a / q + β)) =
      term k * phase ((k : ℝ) * a / q) := by
    rw [show (k : ℝ) * (a / q + β) = (k : ℝ) * a / q + k * β by ring, phase_add]
    dsimp [term]
    ring
  have hterm (k : ℕ) :
      term k * (∑ a ∈ centers, phase ((k : ℝ) * a / q)) =
        -term k + if k = q then (q : ℂ) * term q else 0 := by
    rw [prime_phase_sum hq]
    by_cases hk : k.Prime
    · have hd : q ∣ k ↔ k = q := by
        constructor
        · intro h
          exact ((Nat.dvd_prime hk).mp h).resolve_left hq.ne_one |>.symm
        · rintro rfl
          exact dvd_refl _
      by_cases h : k = q
      · subst k
        rw [ite_eq_left (dvd_refl _), ite_eq_left rfl]
        ring
      · rw [ite_eq_right (fun hh => h (hd.mp hh)), ite_eq_right h]
        ring
    · have hne : k ≠ q := by
        rintro rfl
        exact hk hq
      simp [term, primeWeight, hk, hne]
  unfold primeSum
  simp_rw [hphase]
  rw [sum_comm]
  simp_rw [← mul_sum]
  change (∑ k ∈ range (n + 1), term k * ∑ a ∈ centers, phase ((k : ℝ) * a / q)) = _
  simp_rw [hterm, sum_add_distrib, sum_neg_distrib]
  have hqmem : q ∈ range (n + 1) := mem_range.mpr (by omega)
  simp [hqmem, term, primeWeight, hq, mul_assoc]

theorem fourth_power_of_sum_le {ι : Type*} (s : Finset ι) (f : ι → ℂ) :
    ‖∑ i ∈ s, f i‖ ^ 4 ≤ (s.card : ℝ) ^ 3 * ∑ i ∈ s, ‖f i‖ ^ 4 := by
  let x := ∑ i ∈ s, ‖f i‖
  let y := ∑ i ∈ s, ‖f i‖ ^ 2
  let z := ∑ i ∈ s, ‖f i‖ ^ 4
  let k : ℝ := s.card
  have hx : ‖∑ i ∈ s, f i‖ ≤ x := norm_sum_le _ _
  have h₁ : x ^ 2 ≤ k * y := by
    simpa [x, y, k] using sum_mul_sq_le_sq_mul_sq s (fun _ => (1 : ℝ)) (fun i => ‖f i‖)
  have h₂ : y ^ 2 ≤ k * z := by
    calc
      y ^ 2 ≤ k * ∑ i ∈ s, (‖f i‖ ^ 2) ^ 2 := by
        simpa [y, k] using sum_mul_sq_le_sq_mul_sq s (fun _ => (1 : ℝ)) (fun i => ‖f i‖ ^ 2)
      _ = k * z := by
        congr 1
        exact sum_congr rfl (fun i _ => by ring)
  change _ ≤ k ^ 3 * z
  calc
    _ ≤ x ^ 4 := pow_le_pow_left₀ (norm_nonneg _) hx 4
    _ = (x ^ 2) ^ 2 := by ring
    _ ≤ (k * y) ^ 2 := pow_le_pow_left₀ (sq_nonneg _) h₁ 2
    _ = k ^ 2 * y ^ 2 := by ring
    _ ≤ k ^ 2 * (k * z) := mul_le_mul_of_nonneg_left h₂ (sq_nonneg _)
    _ = _ := by ring


theorem reduced_eq_Ico {q : ℕ} (hq : q.Prime) :
    (range q).filter (fun a => a.Coprime q) = Ico 1 q := by
  ext a
  simp only [mem_filter, mem_range, mem_Ico]
  constructor
  · rintro ⟨ha, hc⟩
    refine ⟨?_, ha⟩
    by_contra! hz
    obtain rfl : a = 0 := by omega
    exact hq.ne_one (by simpa using hc)
  · rintro ⟨ha₁, ha₂⟩
    refine ⟨ha₂, (hq.coprime_iff_not_dvd.mpr ?_).symm⟩
    intro hd
    have := Nat.eq_zero_of_dvd_of_lt hd ha₂
    omega

private theorem primeWeight_nonneg (k : ℕ) : 0 ≤ primeWeight k := by
  unfold primeWeight
  split_ifs with h
  · exact Real.log_nonneg (by exact_mod_cast h.one_le)
  · exact le_rfl

private theorem primeSum_re (n : ℕ) (β : ℝ) : (primeSum n β).re =
    ∑ k ∈ range (n + 1), primeWeight k * Real.cos (2 * Real.pi * (k : ℝ) * β) := by
  unfold primeSum
  rw [Complex.re_sum]
  apply sum_congr rfl
  intro k _
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    phase, Complex.exp_ofReal_mul_I_re, mul_assoc]

theorem one_prime_denominator {n q : ℕ} (hq : q.Prime) (hqn : q ≤ n)
    (β : ℝ) (hβ : |β| ≤ 1 / (20 * (n : ℝ)))
    (hθ : (n : ℝ) / 4 ≤ ∑ k ∈ range (n + 1), primeWeight k)
    (hsmall : (q : ℝ) * Real.log q ≤ (n : ℝ) / 16) :
    ((n : ℝ) / 16) ^ 4 / (q : ℝ) ^ 3 ≤
      ∑ a ∈ Ico 1 q, ‖primeSum n ((a : ℝ) / q + β)‖ ^ 4 := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq.pos
  have hnR : (0 : ℝ) < n := by exact_mod_cast hq.pos.trans_le hqn
  have hcos (k : ℕ) (hk : k ∈ range (n + 1)) :
      (1 / 2 : ℝ) ≤ Real.cos (2 * Real.pi * (k : ℝ) * β) := by
    have hkN : (k : ℝ) ≤ n := by exact_mod_cast Nat.le_of_lt_succ (mem_range.mp hk)
    have hangle : |2 * Real.pi * (k : ℝ) * β| ≤ Real.pi / 3 := by
      calc
        _ = 2 * Real.pi * (k : ℝ) * |β| := by
          rw [abs_mul, abs_of_nonneg (by positivity)]
        _ ≤ 2 * Real.pi * (n : ℝ) * (1 / (20 * (n : ℝ))) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hkN (by positivity)) hβ
            (abs_nonneg _) (by positivity)
        _ = Real.pi / 10 := by
          field_simp
          ring
        _ ≤ Real.pi / 3 := by linarith [Real.pi_pos]
    calc
      _ = Real.cos (Real.pi / 3) := Real.cos_pi_div_three.symm
      _ ≤ Real.cos |2 * Real.pi * (k : ℝ) * β| :=
        Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith [Real.pi_pos]) hangle
      _ = _ := Real.cos_abs _
  have hs : (n : ℝ) / 8 ≤ (primeSum n β).re := by
    rw [primeSum_re]
    calc
      _ ≤ (∑ k ∈ range (n + 1), primeWeight k) * (1 / 2 : ℝ) := by linarith
      _ = ∑ k ∈ range (n + 1), primeWeight k * (1 / 2 : ℝ) := by rw [sum_mul]
      _ ≤ _ := sum_le_sum fun k hk => mul_le_mul_of_nonneg_left (hcos k hk) (primeWeight_nonneg k)
  let C := Ico 1 q
  let F (a : ℕ) := primeSum n ((a : ℝ) / q + β)
  let Z : ℂ := (q : ℂ) * (Real.log (q : ℝ) : ℂ) * phase ((q : ℝ) * β)
  have hsum : (∑ a ∈ C, F a) = -primeSum n β + Z := by
    simpa only [C, F, ← reduced_eq_Ico hq, Z] using sum_prime_centers hq hqn β
  have hZ : ‖Z‖ = (q : ℝ) * Real.log q := by
    have hlog : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg (by exact_mod_cast hq.one_le)
    have hphase : ‖phase ((q : ℝ) * β)‖ = 1 := Complex.norm_exp_ofReal_mul_I _
    simp only [Z, norm_mul, Complex.norm_natCast, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hlog, hphase, mul_one]
  have hback : ‖primeSum n β‖ ≤ ‖-primeSum n β + Z‖ + ‖Z‖ := by
    simpa only [add_sub_cancel_right, norm_neg] using norm_sub_le (-primeSum n β + Z) Z
  have hnorm : (n : ℝ) / 16 ≤ ‖∑ a ∈ C, F a‖ := by
    have hre : (primeSum n β).re ≤ ‖primeSum n β‖ :=
      (le_abs_self _).trans (Complex.abs_re_le_norm _)
    rw [hZ] at hback
    rw [hsum]
    linarith
  have hC : C.card ≤ q := by
    calc
      _ ≤ (range q).card := card_le_card fun a ha => mem_range.mpr (mem_Ico.mp ha).2
      _ = _ := card_range _
  have hnonneg : 0 ≤ ∑ a ∈ C, ‖F a‖ ^ 4 := sum_nonneg fun _ _ => by positivity
  apply (div_le_iff₀ (pow_pos hqR 3)).2
  change ((n : ℝ) / 16) ^ 4 ≤ (∑ a ∈ C, ‖F a‖ ^ 4) * (q : ℝ) ^ 3
  calc
    _ ≤ ‖∑ a ∈ C, F a‖ ^ 4 := pow_le_pow_left₀ (by positivity) hnorm 4
    _ ≤ (C.card : ℝ) ^ 3 * ∑ a ∈ C, ‖F a‖ ^ 4 := fourth_power_of_sum_le C F
    _ ≤ (q : ℝ) ^ 3 * ∑ a ∈ C, ‖F a‖ ^ 4 :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) (by exact_mod_cast hC) 3) hnonneg
    _ = _ := mul_comm _ _

end GoldbachFourthMoment

end GoldbachDeepFourthPrimeDenominator

section GoldbachDeepFourthPrimeCount

open Filter Finset
open scoped BigOperators

namespace GoldbachFourthMoment

theorem theta_eq_prime_log_sum (n : ℕ) :
    Chebyshev.theta n =
      ∑ k ∈ Finset.range (n + 1), if Nat.Prime k then Real.log (k : ℝ) else 0 := by
  rw [Chebyshev.theta_eq_sum_Icc, Nat.floor_natCast, Finset.sum_filter,
    Nat.range_succ_eq_Icc_zero]

theorem eventually_theta_half : ∀ᶠ n : ℕ in atTop, (n : ℝ) / 2 ≤ Chebyshev.theta n := by
  have h := Chebyshev.isLittleO_psi_sub_theta_id.def (by norm_num : (0 : ℝ) < 1 / 10)
  filter_upwards [h.natCast_atTop, eventually_ge_atTop 7] with n hn h7
  have hn' : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  simp only [Pi.sub_apply, id_eq, Real.norm_eq_abs, abs_of_nonneg hn'] at hn
  have hlog : (3 / 5 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hlo := mul_le_mul_of_nonneg_left hlog hn'
  linarith [Chebyshev.psi_ge_of_seven_le h7, (abs_le.mp hn).2]

theorem eventually_theta_quarter : ∀ᶠ n : ℕ in atTop, (n : ℝ) / 4 ≤ Chebyshev.theta n := by
  filter_upwards [eventually_theta_half] with n hn
  have hnn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  linarith

private theorem prime_denominators_log_floor :
    ∀ᶠ R : ℕ in atTop,
      (R : ℝ) / 2 ≤
        (((Finset.Ioc R (4 * R)).filter Nat.Prime).card : ℝ) * Real.log (4 * (R : ℝ)) := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 eventually_theta_half
  filter_upwards [eventually_ge_atTop N] with R hR
  have hR4 : R ≤ 4 * R := by omega
  have hhigh := hN (4 * R) (hR.trans hR4)
  push_cast at hhigh
  have hlow := Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg R)
  have hlog : Real.log 4 ≤ (3 / 2 : ℝ) := by
    rw [Real.log_four_eq]
    linarith [Real.log_two_lt_d9]
  have hlow' := mul_le_mul_of_nonneg_right hlog (Nat.cast_nonneg R : 0 ≤ (R : ℝ))
  have hsplit : Chebyshev.theta (R : ℝ) +
      (∑ p ∈ (Finset.Ioc R (4 * R)).filter Nat.Prime, Real.log (p : ℝ)) =
        Chebyshev.theta ((4 * R : ℕ) : ℝ) := by
    simp only [Chebyshev.theta, Nat.floor_natCast, Finset.sum_filter]
    exact Finset.sum_Ioc_consecutive
      (fun p : ℕ => if Nat.Prime p then Real.log (p : ℝ) else 0) (Nat.zero_le R) hR4
  push_cast at hsplit
  have hupper :
      (∑ p ∈ (Finset.Ioc R (4 * R)).filter Nat.Prime, Real.log (p : ℝ)) ≤
        (((Finset.Ioc R (4 * R)).filter Nat.Prime).card : ℝ) * Real.log (4 * (R : ℝ)) := by
    rw [← nsmul_eq_mul, ← Finset.sum_const]
    apply Finset.sum_le_sum
    intro p hp
    obtain ⟨hpI, hpPrime⟩ := Finset.mem_filter.mp hp
    apply Real.log_le_log (by exact_mod_cast hpPrime.pos)
    exact_mod_cast (Finset.mem_Ioc.mp hpI).2
  linarith

private theorem eventually_log_le_mul_rpow (s c : ℝ) (hs : 0 < s) (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop, Real.log (n : ℝ) ≤ c * (n : ℝ) ^ s := by
  have h := (isLittleO_log_rpow_atTop hs).def hc
  filter_upwards [h.natCast_atTop] with n hn
  simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) s)]
    using (le_abs_self (Real.log (n : ℝ))).trans hn

private theorem cube_root_floor_tendsto :
    Tendsto (fun n : ℕ => ⌊(n : ℝ) ^ (1 / 3 : ℝ)⌋₊) atTop atTop := by
  have h := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 3)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  exact tendsto_atTop.2 fun m =>
    ((tendsto_atTop.1 h) (m : ℝ)).mono fun n hn => Nat.le_floor hn

theorem eventually_many_prime_denominators : ∀ᶠ n : ℕ in atTop,
    let R := ⌊(n : ℝ) ^ (1 / 3 : ℝ)⌋₊
    (n : ℝ) ^ (1 / 4 : ℝ) ≤ (((Finset.Ioc R (4*R)).filter Nat.Prime).card : ℝ) := by
  filter_upwards [cube_root_floor_tendsto.eventually prime_denominators_log_floor,
    eventually_log_le_mul_rpow (1 / 12) (1 / 8) (by norm_num) (by norm_num),
    eventually_ge_atTop 4] with n hc hlog hn
  let R := ⌊(n : ℝ) ^ (1 / 3 : ℝ)⌋₊
  change (R : ℝ) / 2 ≤ _ at hc
  change (n : ℝ) ^ (1 / 4 : ℝ) ≤ _
  have hnR : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by linarith
  have hnPos : 0 < (n : ℝ) := by linarith
  have hR1 : 1 ≤ R := Nat.le_floor (by simpa using Real.one_le_rpow hn1 (by norm_num : (0:ℝ) ≤ 1/3))
  have hR1' : (1 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR1
  have hRlo : (n : ℝ) ^ (1 / 3 : ℝ) / 2 ≤ (R : ℝ) := by
    have h := Nat.lt_floor_add_one ((n : ℝ) ^ (1 / 3 : ℝ))
    change (n : ℝ) ^ (1 / 3 : ℝ) < (R : ℝ) + 1 at h
    linarith
  have hRhi : (R : ℝ) ≤ (n : ℝ) := by
    calc
      _ ≤ (n : ℝ) ^ (1 / 3 : ℝ) := Nat.floor_le (Real.rpow_nonneg hnPos.le _)
      _ ≤ _ := by simpa using
        Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num : (1/3 : ℝ) ≤ 1)
  have hlogR : Real.log (4 * (R : ℝ)) ≤ 2 * Real.log (n : ℝ) := by
    calc
      _ ≤ Real.log ((n : ℝ) ^ 2) := Real.log_le_log (by linarith)
        (by nlinarith only [hRhi, hnR, sq_nonneg ((n : ℝ) - 4)])
      _ = _ := by rw [Real.log_pow]; norm_num
  have hpow : (n : ℝ) ^ (1 / 4 : ℝ) * (n : ℝ) ^ (1 / 12 : ℝ) =
      (n : ℝ) ^ (1 / 3 : ℝ) := by
    rw [← Real.rpow_add hnPos]
    congr 1
    norm_num
  apply le_of_mul_le_mul_right _ (Real.log_pos (by linarith : 1 < 4 * (R : ℝ)))
  calc
    _ ≤ (n : ℝ) ^ (1 / 4 : ℝ) * (2 * Real.log (n : ℝ)) :=
      mul_le_mul_of_nonneg_left hlogR (Real.rpow_nonneg hnPos.le _)
    _ ≤ (n : ℝ) ^ (1 / 4 : ℝ) * (2 * ((1 / 8 : ℝ) * (n : ℝ) ^ (1 / 12 : ℝ))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlog (by norm_num)) (by positivity)
    _ = (n : ℝ) ^ (1 / 3 : ℝ) / 4 := by rw [← hpow]; ring
    _ ≤ (R : ℝ) / 2 := by linarith
    _ ≤ _ := hc

theorem eventually_small_denominator_log : ∀ᶠ n : ℕ in atTop,
    ∀ q : ℕ, q ≤ 4 * ⌊(n : ℝ) ^ (1 / 3 : ℝ)⌋₊ →
      (q : ℝ) * Real.log (q : ℝ) ≤ (n : ℝ) / 16 := by
  filter_upwards [eventually_log_le_mul_rpow (2 / 3) (1 / 128) (by norm_num) (by norm_num),
    eventually_ge_atTop 4] with n hlog hn
  intro q hq
  rcases q.eq_zero_or_pos with rfl | hqPos
  · simp
    positivity
  have hnR : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by linarith
  have hnPos : 0 < (n : ℝ) := by linarith
  have hqPos' : 0 < (q : ℝ) := by exact_mod_cast hqPos
  have hqHi : (q : ℝ) ≤ 4 * (n : ℝ) ^ (1 / 3 : ℝ) := calc
    _ ≤ 4 * (⌊(n : ℝ) ^ (1 / 3 : ℝ)⌋₊ : ℝ) := by exact_mod_cast hq
    _ ≤ _ := mul_le_mul_of_nonneg_left (Nat.floor_le (Real.rpow_nonneg hnPos.le _)) (by norm_num)
  have hqHi' : (q : ℝ) ≤ 4 * (n : ℝ) := hqHi.trans <|
    mul_le_mul_of_nonneg_left
      (by simpa using Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num : (1/3 : ℝ) ≤ 1))
      (by norm_num)
  have hlogq : Real.log (q : ℝ) ≤ 2 * Real.log (n : ℝ) := calc
    _ ≤ Real.log ((n : ℝ) ^ 2) := Real.log_le_log hqPos'
      (by nlinarith only [hqHi', hnR, sq_nonneg ((n : ℝ) - 4)])
    _ = _ := by rw [Real.log_pow]; norm_num
  have hpow : (n : ℝ) ^ (1 / 3 : ℝ) * (n : ℝ) ^ (2 / 3 : ℝ) = (n : ℝ) := by
    rw [← Real.rpow_add hnPos]
    norm_num
  calc
    _ ≤ (4 * (n : ℝ) ^ (1 / 3 : ℝ)) * (2 * Real.log (n : ℝ)) := by
      apply mul_le_mul hqHi hlogq
      · exact Real.log_nonneg (by exact_mod_cast hqPos)
      · positivity
    _ ≤ (4 * (n : ℝ) ^ (1 / 3 : ℝ)) * (2 * ((1 / 128 : ℝ) * (n : ℝ) ^ (2 / 3 : ℝ))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlog (by norm_num)) (by positivity)
    _ = ((n : ℝ) ^ (1 / 3 : ℝ) * (n : ℝ) ^ (2 / 3 : ℝ)) / 16 := by ring
    _ = _ := congrArg (fun x : ℝ => x / 16) hpow

end GoldbachFourthMoment

end GoldbachDeepFourthPrimeCount

section GoldbachWideArcSeparation

open Filter
open scoped Topology

namespace GoldbachWideArcs

/-- The triangle inequality and spacing of rational centers give this general width condition.
    This uses the rational-separation argument from goldbach-proofs PR 153. -/
theorem reduced_centers_eq_of_common_point {n H B q r a b : ℕ} {t : ℝ}
    (hn : 2 * H * B < n) (hq : 1 ≤ q) (hr : 1 ≤ r) (hqB : q ≤ B) (hrB : r ≤ B)
    (hca : a.Coprime q) (hcb : b.Coprime r)
    (ha : |t - (a : ℝ)/q| ≤ (H : ℝ)/((q : ℝ)*n))
    (hb : |t - (b : ℝ)/r| ≤ (H : ℝ)/((r : ℝ)*n)) : q = r ∧ a = b := by
  have hqr : 0 < (q : ℝ) := by exact_mod_cast hq
  have hrr : 0 < (r : ℝ) := by exact_mod_cast hr
  have hnr : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hsmall : H*r + H*q < n := by
    nlinarith only [hn, Nat.mul_le_mul_left H hrB, Nat.mul_le_mul_left H hqB]
  have hradii : (H : ℝ)/(q*n) + H/(r*n) < 1/(q*r) := calc
    _ = ((H : ℝ)*r+H*q)/(q*r*n) := by field_simp
    _ < (n : ℝ)/(q*r*n) := (div_lt_div_iff_of_pos_right (by positivity)).mpr (by exact_mod_cast hsmall)
    _ = _ := by field_simp
  have he : a*r = b*q := by
    by_contra hne
    have hsep : 1/((q : ℝ)*r) ≤ |(a : ℝ)/q - b/r| := by
      rw [show (a:ℝ)/q - b/r = (a*r-b*q)/(q*r) by field_simp, abs_div, abs_of_pos (mul_pos hqr hrr)]
      apply (div_le_div_iff_of_pos_right (mul_pos hqr hrr)).mpr
      rcases lt_or_gt_of_ne hne with hab | hba
      · have hgap : (a:ℝ)*r + 1 ≤ b*q := by exact_mod_cast Nat.succ_le_of_lt hab
        linarith [neg_le_abs ((a:ℝ)*r - b*q)]
      · have hgap : (b:ℝ)*q + 1 ≤ a*r := by exact_mod_cast Nat.succ_le_of_lt hba
        linarith [le_abs_self ((a:ℝ)*r - b*q)]
    have htriangle := abs_sub_le ((a:ℝ)/q) t ((b:ℝ)/r)
    rw [abs_sub_comm ((a:ℝ)/q) t] at htriangle
    linarith
  have hdiv₁ : q ∣ r := hca.symm.dvd_of_dvd_mul_left (he ▸ dvd_mul_left q b)
  have hdiv₂ : r ∣ q := hcb.symm.dvd_of_dvd_mul_left (he.symm ▸ dvd_mul_left r a)
  obtain rfl := Nat.dvd_antisymm hdiv₁ hdiv₂
  exact ⟨rfl, Nat.eq_of_mul_eq_mul_right hq he⟩

theorem eventually_wide_arc_budget :
    ∃ N : ℕ, ∀ n ≥ N,
      let Q := (Nat.log 2 (n+2))^2
      let Q₁ := ⌊(n : ℝ)^(1/3 : ℝ)⌋₊
      let H := 256 * Q₁ * Q
      2 * H * Q₁ < n := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let c : ℝ := Real.log 2 / 2
  have hc : 0 < c := by dsimp [c]; positivity
  have hlim : Tendsto (fun x : ℝ => Real.log x ^ (2 : ℕ) / x^(1/3 : ℝ)) atTop (𝓝 0) := by
    have h := (isLittleO_log_rpow_rpow_atTop (s := 1/3) 2 (by norm_num)).tendsto_div_nhds_zero
    have heq (x : ℝ) : Real.log x ^ (2 : ℝ) = Real.log x ^ (2 : ℕ) := by
      simpa only [Nat.cast_ofNat] using Real.rpow_natCast (Real.log x) 2
    simpa only [heq] using h
  have hseq := hlim.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hε : 0 < c^2/512 := by positivity
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hseq.eventually_lt_const hε)
  refine ⟨max N 2, ?_⟩
  intro n hn Q Q₁ H
  have hnN : N ≤ n := (le_max_left _ _).trans hn
  have hn2 : 2 ≤ n := (le_max_right _ _).trans hn
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  let z := (n : ℝ)^(1/3 : ℝ)
  have hz : 0 < z := Real.rpow_pos_of_pos hnpos _
  have hpow : (2 : ℝ) ^ Nat.log 2 (n+2) ≤ ((n+2 : ℕ) : ℝ) := by
    exact_mod_cast Nat.pow_log_le_self 2 (by omega : n+2 ≠ 0)
  have hlogbase := Real.log_le_log (by positivity : 0 < (2 : ℝ) ^ Nat.log 2 (n+2)) hpow
  rw [Real.log_pow] at hlogbase
  have hlogplus : Real.log ((n+2 : ℕ) : ℝ) ≤ 2 * Real.log (n : ℝ) := by
    have hcomp : ((n+2 : ℕ) : ℝ) ≤ (n : ℝ)^2 := by
      push_cast
      nlinarith only [hnR, sq_nonneg ((n : ℝ) - 2)]
    simpa only [Real.log_pow, Nat.cast_ofNat] using
      Real.log_le_log (by positivity : 0 < ((n+2 : ℕ) : ℝ)) hcomp
  have hnatlog : (Nat.log 2 (n+2) : ℝ) ≤ Real.log (n : ℝ) / c := by
    apply (le_div_iff₀ hc).2
    dsimp [c]
    linarith only [hlogbase, hlogplus]
  have hsmall : Real.log (n : ℝ)^2 / z < c^2/512 := hN n hnN
  have hscaled : 512 * (Real.log (n : ℝ) / c)^2 < z := by
    have h1 := (div_lt_iff₀ hz).1 hsmall
    have h2 := (lt_div_iff₀ (by norm_num : (0 : ℝ) < 512)).1
      (show Real.log (n : ℝ)^2 < c^2*z/512 by simpa only [div_mul_eq_mul_div] using h1)
    rw [div_pow, ← mul_div_assoc]
    apply (div_lt_iff₀ (sq_pos_of_pos hc)).2
    simpa only [mul_comm] using h2
  have hQ : (512 : ℝ) * (Q : ℝ) < z := by
    have hsq : (Q : ℝ) ≤ (Real.log (n : ℝ) / c)^2 := by
      dsimp [Q]
      push_cast
      exact pow_le_pow_left₀ (by positivity) hnatlog _
    exact (mul_le_mul_of_nonneg_left hsq (by norm_num)).trans_lt hscaled
  have hB : (Q₁ : ℝ) ≤ z := Nat.floor_le hz.le
  have hz3 : z * z^2 = (n : ℝ) := by
    have heq : z^2 = (n : ℝ)^(2/3 : ℝ) := by
      dsimp [z]
      rw [← Real.rpow_natCast, ← Real.rpow_mul hnpos.le]
      norm_num
    rw [heq]
    dsimp [z]
    rw [← Real.rpow_add hnpos]
    norm_num
  have hr : (512 : ℝ) * (Q : ℝ) * (Q₁ : ℝ)^2 < (n : ℝ) := calc
    _ ≤ 512 * (Q : ℝ) * z^2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hB _) (by positivity)
    _ < z * z^2 := mul_lt_mul_of_pos_right hQ (sq_pos_of_pos hz)
    _ = _ := hz3
  have hnat : 512 * Q * Q₁^2 < n := by exact_mod_cast hr
  change 2 * (256 * Q₁ * Q) * Q₁ < n
  rw [show 2 * (256 * Q₁ * Q) * Q₁ = 512 * Q * Q₁^2 by ring]
  exact hnat

end GoldbachWideArcs

end GoldbachWideArcSeparation

section GoldbachDeepFourthGeometry

open Filter
open scoped Topology

private theorem eventuallyExtendedBudget :
    ∃ N : ℕ, ∀ n ≥ N,
      let Q := (Nat.log 2 (n+2))^2
      let Q₁ := ⌊(n : ℝ)^(1/3 : ℝ)⌋₊
      let H := 256 * Q₁ * Q
      2 * H * (4*Q₁) < n := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let c : ℝ := Real.log 2 / 2
  have hc : 0 < c := by dsimp [c]; positivity
  have hlim : Tendsto (fun x : ℝ => Real.log x ^ (2 : ℕ) / x^(1/3 : ℝ)) atTop (𝓝 0) := by
    have h := (isLittleO_log_rpow_rpow_atTop (s := 1/3) 2 (by norm_num)).tendsto_div_nhds_zero
    have heq (x : ℝ) : Real.log x ^ (2 : ℝ) = Real.log x ^ (2 : ℕ) := by
      simpa only [Nat.cast_ofNat] using Real.rpow_natCast (Real.log x) 2
    simpa only [heq] using h
  have hseq := hlim.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hε : 0 < c^2/2048 := by positivity
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hseq.eventually_lt_const hε)
  refine ⟨max N 2, ?_⟩
  intro n hn Q Q₁ H
  have hnN : N ≤ n := (le_max_left _ _).trans hn
  have hn2 : 2 ≤ n := (le_max_right _ _).trans hn
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  let z := (n : ℝ)^(1/3 : ℝ)
  have hz : 0 < z := Real.rpow_pos_of_pos hnpos _
  have hpow : (2 : ℝ) ^ Nat.log 2 (n+2) ≤ ((n+2 : ℕ) : ℝ) := by
    exact_mod_cast Nat.pow_log_le_self 2 (by omega : n+2 ≠ 0)
  have hlogbase := Real.log_le_log (by positivity : 0 < (2 : ℝ) ^ Nat.log 2 (n+2)) hpow
  rw [Real.log_pow] at hlogbase
  have hlogplus : Real.log ((n+2 : ℕ) : ℝ) ≤ 2 * Real.log (n : ℝ) := by
    have hcomp : ((n+2 : ℕ) : ℝ) ≤ (n : ℝ)^2 := by
      push_cast
      nlinarith only [hnR, sq_nonneg ((n : ℝ) - 2)]
    simpa only [Real.log_pow, Nat.cast_ofNat] using
      Real.log_le_log (by positivity : 0 < ((n+2 : ℕ) : ℝ)) hcomp
  have hnatlog : (Nat.log 2 (n+2) : ℝ) ≤ Real.log (n : ℝ) / c := by
    apply (le_div_iff₀ hc).2
    dsimp [c]
    linarith only [hlogbase, hlogplus]
  have hsmall : Real.log (n : ℝ)^2 / z < c^2/2048 := hN n hnN
  have hscaled : 2048 * (Real.log (n : ℝ) / c)^2 < z := by
    have h1 := (div_lt_iff₀ hz).1 hsmall
    have h2 := (lt_div_iff₀ (by norm_num : (0 : ℝ) < 2048)).1
      (show Real.log (n : ℝ)^2 < c^2*z/2048 by simpa only [div_mul_eq_mul_div] using h1)
    rw [div_pow, ← mul_div_assoc]
    apply (div_lt_iff₀ (sq_pos_of_pos hc)).2
    simpa only [mul_comm] using h2
  have hQ : (2048 : ℝ) * (Q : ℝ) < z := by
    have hsq : (Q : ℝ) ≤ (Real.log (n : ℝ) / c)^2 := by
      dsimp [Q]
      push_cast
      exact pow_le_pow_left₀ (by positivity) hnatlog _
    exact (mul_le_mul_of_nonneg_left hsq (by norm_num)).trans_lt hscaled
  have hB : (Q₁ : ℝ) ≤ z := Nat.floor_le hz.le
  have hz3 : z * z^2 = (n : ℝ) := by
    have heq : z^2 = (n : ℝ)^(2/3 : ℝ) := by
      dsimp [z]
      rw [← Real.rpow_natCast, ← Real.rpow_mul hnpos.le]
      norm_num
    rw [heq]
    dsimp [z]
    rw [← Real.rpow_add hnpos]
    norm_num
  have hr : (2048 : ℝ) * (Q : ℝ) * (Q₁ : ℝ)^2 < (n : ℝ) := calc
    _ ≤ 2048 * (Q : ℝ) * z^2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hB _) (by positivity)
    _ < z * z^2 := mul_lt_mul_of_pos_right hQ (sq_pos_of_pos hz)
    _ = _ := hz3
  have hnat : 2048 * Q * Q₁^2 < n := by exact_mod_cast hr
  change 2 * (256 * Q₁ * Q) * (4*Q₁) < n
  rw [show 2 * (256 * Q₁ * Q) * (4*Q₁) = 2048 * Q * Q₁^2 by ring]
  exact hnat

open Set

namespace GoldbachFourthGeometry

noncomputable def strip (n q a : ℕ) : Set ℝ :=
  Set.Icc ((a:ℝ)/q - 1/(20*(n:ℝ))) ((a:ℝ)/q + 1/(20*(n:ℝ)))

noncomputable def wide (n R H : ℕ) : Set ℝ :=
  {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤R ∧ a≤q ∧ Nat.Coprime a q ∧
    |t - (a:ℝ)/q| ≤ (H:ℝ)/((q:ℝ)*n)}

theorem mem_strip {n q a : ℕ} {t : ℝ} :
    t ∈ strip n q a ↔ |t-(a:ℝ)/q| ≤ 1/(20*(n:ℝ)) := by
  unfold strip
  rw [Set.mem_Icc, abs_le]
  constructor <;> rintro ⟨h₁,h₂⟩ <;> constructor <;> linarith

theorem center_coprime {q a : ℕ} (hq : q.Prime) (ha : a ∈ Finset.Ico 1 q) :
    a.Coprime q := by
  obtain ⟨ha₀,ha₁⟩ := Finset.mem_Ico.mp ha
  exact (hq.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt ha₀ ha₁)).symm

theorem bigger_radius {n q H : ℕ} (hn : 0 < n) (hq : 0 < q) (hqH : q ≤ H) :
    1/(20*(n:ℝ)) ≤ (H:ℝ)/((q:ℝ)*n) := by
  have hnr : 0 < (n:ℝ) := by exact_mod_cast hn
  have hqr : 0 < (q:ℝ) := by exact_mod_cast hq
  have hq' : (q:ℝ) ≤ (H:ℝ) := by exact_mod_cast hqH
  apply (div_le_div_iff₀ (by positivity) (by positivity)).2
  have hs := mul_le_mul_of_nonneg_right hq' hnr.le
  nlinarith only [hs, mul_nonneg (Nat.cast_nonneg H) hnr.le]

theorem point_in_unit {n q a : ℕ} (hn : 0 < n) (hqn : q ≤ n) (ha : a ∈ Finset.Ico 1 q)
    {t : ℝ} (ht : t ∈ strip n q a) : t ∈ Set.Icc (0:ℝ) 1 := by
  obtain ⟨ha₀,ha₁⟩ := Finset.mem_Ico.mp ha
  have hq : 0 < (q:ℝ) := by exact_mod_cast (show 0<q by omega)
  have hnr : 0 < (n:ℝ) := by exact_mod_cast hn
  have hqn' : (q:ℝ) ≤ (n:ℝ) := by exact_mod_cast hqn
  have hδ : 1/(20*(n:ℝ)) ≤ 1/(q:ℝ) := by
    apply (div_le_div_iff₀ (by positivity) hq).2
    linarith
  have hlow : 1/(q:ℝ) ≤ (a:ℝ)/q :=
    div_le_div_of_nonneg_right (by exact_mod_cast ha₀) hq.le
  have hhigh : (a:ℝ)/q ≤ 1-1/(q:ℝ) := by
    have ht : (a:ℝ)+1≤(q:ℝ) := by exact_mod_cast Nat.succ_le_of_lt ha₁
    calc
      _ ≤ ((q:ℝ)-1)/q := div_le_div_of_nonneg_right (by linarith) hq.le
      _ = _ := by rw [sub_div, div_self hq.ne']
  obtain ⟨h₁,h₂⟩ := abs_le.mp (mem_strip.mp ht)
  exact ⟨by linarith, by linarith⟩

theorem point_outside_wide {n R H q a : ℕ} (hcut : 2*H*(4*R)<n) (hH : 4*R ≤ H)
    (hq : q.Prime) (hqR : R < q) (hq4 : q ≤ 4*R) (ha : a ∈ Finset.Ico 1 q)
    {t : ℝ} (ht : t ∈ strip n q a) : t ∈ (wide n R H)ᶜ := by
  intro hw
  obtain ⟨r,b,hr,hrR,_,hcb,hradius⟩ := hw
  have hnr : 0 < n := by omega
  have hqa := center_coprime hq ha
  have hδ := (mem_strip.mp ht).trans (bigger_radius hnr hq.pos (hq4.trans hH))
  have ⟨heq,_⟩ := GoldbachWideArcs.reduced_centers_eq_of_common_point hcut hq.pos hr
    hq4 (hrR.trans (by omega)) hqa hcb hδ hradius
  omega

theorem strip_index_unique {n R H q r a b : ℕ} (hcut : 2*H*(4*R)<n) (hH : 4*R ≤ H)
    (hq : q.Prime) (hr : r.Prime) (hq4 : q ≤ 4*R) (hr4 : r ≤ 4*R)
    (ha : a ∈ Finset.Ico 1 q) (hb : b ∈ Finset.Ico 1 r) {t : ℝ}
    (htq : t ∈ strip n q a) (htr : t ∈ strip n r b) : q=r ∧ a=b := by
  have hnr : 0 < n := by omega
  exact GoldbachWideArcs.reduced_centers_eq_of_common_point hcut hq.pos hr.pos hq4 hr4
    (center_coprime hq ha) (center_coprime hr hb)
    ((mem_strip.mp htq).trans (bigger_radius hnr hq.pos (hq4.trans hH)))
    ((mem_strip.mp htr).trans (bigger_radius hnr hr.pos (hr4.trans hH)))

theorem eventually_strip_budget :
    ∃ N : ℕ, ∀ n ≥ N,
      let R := ⌊(n:ℝ)^(1/3:ℝ)⌋₊
      let H := 256 * R * (Nat.log 2 (n+2))^2
      2*H*(4*R) < n ∧ 4*R ≤ H ∧ 4*R ≤ n := by
  obtain ⟨N,hN⟩ := eventuallyExtendedBudget
  refine ⟨N, ?_⟩
  intro n hn R H
  have hbudget : 2*H*(4*R) < n := hN n hn
  have hlog : 1 ≤ Nat.log 2 (n+2) := Nat.log_pos (by decide) (by omega)
  have hH : 4*R ≤ H := calc
    _ ≤ 256*R := Nat.mul_le_mul_right _ (by decide)
    _ = 256*R*1 := by simp
    _ ≤ H := Nat.mul_le_mul_left _ (by
      have hx := Nat.pow_le_pow_left hlog 2
      simpa using hx)
  have hsize : 4*R ≤ n := by
    by_cases hzero : R=0
    · simp [hzero]
    · have hHp : 1 ≤ H := by omega
      exact (Nat.le_mul_of_pos_left _ (show 0<2*H by omega)).trans hbudget.le
  exact ⟨hbudget,hH,hsize⟩

end GoldbachFourthGeometry

end GoldbachDeepFourthGeometry

section GoldbachDiscreteWindowEstimate

open Finset MeasureTheory
open scoped ComplexConjugate Interval

namespace GoldbachWindow

open GoldbachFourthMoment (phase phase_add)

/-- The finite Fourier series with coefficient list indexed by `range N`. -/
noncomputable def poly (N : ℕ) (b : ℕ → ℂ) (t : ℝ) : ℂ :=
  ∑ j ∈ range N, b j * phase ((j : ℝ) * t)

private theorem phase_cont : Continuous phase := by unfold phase; fun_prop

private theorem poly_cont (N : ℕ) (b : ℕ → ℂ) : Continuous (poly N b) := by
  unfold poly
  exact continuous_finsetSum _ fun j _ => continuous_const.mul (phase_cont.comp (by fun_prop))

private theorem phase_int (m : ℤ) : phase (m : ℝ) = 1 := by
  unfold phase
  have h : (((2 * Real.pi * (m : ℝ) : ℝ) : ℂ) * Complex.I) =
      (m : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    push_cast
    ring
  rw [h, Complex.exp_int_mul_two_pi_mul_I]

-- The mode integral uses the same orthogonality as Clrs17, Goldbach PR 158.
private theorem mode_integral (m : ℤ) :
    (∫ t in (0 : ℝ)..1, phase ((m : ℝ) * t)) = if m = 0 then 1 else 0 := by
  by_cases hm : m = 0
  · subst m
    simp [phase]
  let c : ℂ := (m : ℂ) * (2 * Real.pi * Complex.I)
  have he (t : ℝ) : phase ((m : ℝ) * t) = Complex.exp (c * (t : ℂ)) := by
    unfold phase c
    congr 1
    push_cast
    ring
  have hc : c ≠ 0 := by
    dsimp [c]
    exact mul_ne_zero (by exact_mod_cast hm)
      (mul_ne_zero (mul_ne_zero two_ne_zero (by exact_mod_cast Real.pi_ne_zero))
        Complex.I_ne_zero)
  simp_rw [he]
  rw [integral_exp_mul_complex hc]
  simp [hm, c, Complex.exp_int_mul_two_pi_mul_I]

private theorem phase_conj (t : ℝ) : conj (phase t) = phase (-t) := by
  unfold phase
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

theorem parseval (N : ℕ) (b : ℕ → ℂ) :
    (∫ t in (0 : ℝ)..1, ‖poly N b t‖^2) = ∑ k ∈ range N, ‖b k‖^2 := by
  let term (k j : ℕ) (t : ℝ) :=
    (conj (b k) * b j) * phase ((((j : ℤ) - (k : ℤ)) : ℝ) * t)
  let cross (t : ℝ) := ∑ k ∈ range N, ∑ j ∈ range N, term k j t
  have hc (k j : ℕ) : Continuous (term k j) := by
    unfold term phase
    fun_prop
  have hcross : Continuous cross := continuous_finsetSum _ fun k _ =>
    continuous_finsetSum _ fun j _ => hc k j
  have hexpand (t : ℝ) : ((‖poly N b t‖^2 : ℝ) : ℂ) = cross t := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self]
    simp only [poly, cross, map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
    dsimp [term]
    simp only [map_mul, phase_conj]
    simp only [Int.cast_natCast]
    rw [show ((j : ℝ) - (k : ℝ)) * t =
      -((k : ℝ) * t) + (j : ℝ) * t by ring, phase_add]
    ring
  have hint : (∫ t in (0 : ℝ)..1, cross t) = (↑(∑ k ∈ range N, ‖b k‖^2) : ℂ) := by
    dsimp only [cross]
    rw [intervalIntegral.integral_finsetSum
      (fun k _ => (continuous_finsetSum _ fun j _ => hc k j).intervalIntegrable _ _),
      Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro k hk
    rw [intervalIntegral.integral_finsetSum fun j _ => (hc k j).intervalIntegrable _ _]
    have hmode (j : ℕ) : (∫ t in (0 : ℝ)..1, term k j t) =
        (conj (b k) * b j) * (if j = k then 1 else 0) := by
      have hm : (∫ t in (0 : ℝ)..1, phase (((j : ℝ) - (k : ℝ)) * t)) =
          if j = k then 1 else 0 := by
        simpa only [Int.cast_sub, Int.cast_natCast, sub_eq_zero, Int.ofNat_inj]
          using mode_integral ((j : ℤ) - (k : ℤ))
      unfold term
      rw [intervalIntegral.integral_const_mul]
      exact congrArg ((conj (b k) * b j) * ·) hm
    simp only [hmode]
    rw [Finset.sum_eq_single_of_mem k hk]
    · simp [← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self]
    · intro j _ hne
      simp [hne]
  have hre :
      (∫ t in (0 : ℝ)..1, (cross t).re) = (∫ t in (0 : ℝ)..1, cross t).re := by
    rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
      intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact integral_re (hcross.intervalIntegrable (0 : ℝ) 1).1
  calc
    _ = ∫ t in (0 : ℝ)..1, (cross t).re := by
      apply intervalIntegral.integral_congr
      intro t _
      simpa only [Complex.ofReal_re] using congrArg Complex.re (hexpand t)
    _ = _ := by rw [hre, hint, Complex.ofReal_re]

/-- The coefficient at frequency `m` after multiplying by the length-`h` box. -/
noncomputable def moving (N h : ℕ) (b : ℕ → ℂ) (m : ℕ) : ℂ :=
  ∑ x ∈ ((range N) ×ˢ (range h)).filter (fun x => x.1 + x.2 = m), b x.1

theorem moving_eq_sum (N h : ℕ) (b : ℕ → ℂ) (m : ℕ) :
    moving N h b m = ∑ k ∈ (range N).filter (fun k => m + 1 - h ≤ k ∧ k ≤ m), b k := by
  classical
  unfold moving
  refine Finset.sum_bij (fun x _ => x.1) ?_ ?_ ?_ (fun _ _ => rfl)
  · intro x hx
    obtain ⟨⟨hk, hj⟩, heq⟩ := (Finset.mem_filter.mp hx).imp (fun hp => Finset.mem_product.mp hp) id
    have hj' := mem_range.mp hj
    exact Finset.mem_filter.mpr ⟨hk, by omega, by omega⟩
  · intro x hx y hy hxy
    have heqx := (Finset.mem_filter.mp hx).2
    have heqy := (Finset.mem_filter.mp hy).2
    exact Prod.ext hxy (by omega)
  · intro k hk
    obtain ⟨hk', hlo, hhi⟩ := Finset.mem_filter.mp hk
    refine ⟨(k, m - k), ?_, rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hk', mem_range.mpr (by omega)⟩, by omega⟩

theorem poly_moving_mul (N h : ℕ) (b : ℕ → ℂ) (t : ℝ) :
    poly (N + h) (moving N h b) t = poly N b t * poly h (fun _ => 1) t := by
  unfold poly
  have hmaps (x : ℕ × ℕ) (hx : x ∈ (range N) ×ˢ (range h)) :
      x.1 + x.2 ∈ range (N + h) := by
    obtain ⟨hk, hj⟩ := Finset.mem_product.mp hx
    simp only [Finset.mem_range] at hk hj
    exact mem_range.mpr (by omega)
  calc
    _ = ∑ m ∈ range (N + h), ∑ x ∈ ((range N) ×ˢ (range h)).filter
        (fun x => x.1 + x.2 = m), b x.1 * phase ((x.1 : ℝ) * t + (x.2 : ℝ) * t) := by
      apply Finset.sum_congr rfl
      intro m _
      rw [moving, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro x hx
      have hsum := (Finset.mem_filter.mp hx).2
      have hsumR : (x.1 : ℝ) + x.2 = m := by exact_mod_cast hsum
      rw [← add_mul, hsumR]
    _ = ∑ x ∈ (range N) ×ˢ (range h), b x.1 * phase ((x.1 : ℝ) * t + (x.2 : ℝ) * t) :=
      Finset.sum_fiberwise_of_maps_to hmaps _
    _ = _ := by
      rw [Finset.sum_product, Finset.sum_mul_sum]
      simp only [one_mul, phase_add, mul_assoc]

private theorem box_lower {h : ℕ} {t : ℝ} (ht : 6 * (h : ℝ) * |t| ≤ 1) :
    (h : ℝ) / 2 ≤ ‖poly h (fun _ => 1) t‖ := by
  apply le_trans _ (Complex.re_le_norm _)
  unfold poly
  simp only [one_mul, Complex.re_sum, phase, Complex.exp_ofReal_mul_I_re]
  calc
    _ = ∑ _ ∈ range h, (1 / 2 : ℝ) := by rw [Finset.sum_const, card_range, nsmul_eq_mul]; ring
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro j hj
      have hjh : (j : ℝ) ≤ h := by exact_mod_cast (mem_range.mp hj).le
      have hfac := mul_le_mul_of_nonneg_right hjh (abs_nonneg t)
      have hangle : |2 * Real.pi * ((j : ℝ) * t)| ≤ Real.pi / 3 := by
        rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2 * Real.pi), abs_mul,
          abs_of_nonneg (Nat.cast_nonneg j : 0 ≤ (j : ℝ))]
        calc
          _ ≤ (2 * Real.pi) * ((h : ℝ) * |t|) := mul_le_mul_of_nonneg_left hfac (by positivity)
          _ ≤ _ := by
            have h' : (h : ℝ) * |t| ≤ 1 / 6 := by linarith only [ht]
            have h'' := mul_le_mul_of_nonneg_left h' (show 0 ≤ 2 * Real.pi by positivity)
            linarith only [h'']
      rw [← Real.cos_pi_div_three, ← Real.cos_abs (2 * Real.pi * ((j : ℝ) * t))]
      exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith [Real.pi_pos]) hangle

set_option maxHeartbeats 600000 in
/-- A finite version of the low-frequency window estimate, using exact Parseval on one period. -/
theorem low_frequency_le (N h : ℕ) (b : ℕ → ℂ) (δ : ℝ)
    (hpos : 0 < h) (hδ : 0 ≤ δ) (hwidth : 6 * (h : ℝ) * δ ≤ 1) :
    (h : ℝ)^2 / 4 * (∫ t in (-δ)..δ, ‖poly N b t‖^2) ≤
      ∑ m ∈ range (N + h), ‖moving N h b m‖^2 := by
  have hδsmall : δ ≤ 1 / 2 := by
    have hh : (1 : ℝ) ≤ h := by exact_mod_cast hpos
    have hmul := mul_le_mul_of_nonneg_right hh hδ
    nlinarith only [hmul, hwidth]
  have hre : -δ ≤ δ := by linarith
  have hline (t : ℝ) (ht : t ∈ Set.Icc (-δ) δ) :
      (h : ℝ)^2 / 4 * ‖poly N b t‖^2 ≤ ‖poly (N + h) (moving N h b) t‖^2 := by
    have ht' : |t| ≤ δ := abs_le.mpr ht
    have hb := box_lower ((mul_le_mul_of_nonneg_left ht'
      (by positivity : 0 ≤ 6 * (h : ℝ))).trans hwidth)
    rw [poly_moving_mul, norm_mul, mul_pow]
    have hb' := pow_le_pow_left₀ (by positivity : 0 ≤ (h : ℝ) / 2) hb 2
    rw [show (h : ℝ)^2 / 4 = ((h : ℝ) / 2)^2 by ring, mul_comm]
    exact mul_le_mul_of_nonneg_left hb' (by positivity)
  let F (t : ℝ) := ‖poly (N + h) (moving N h b) t‖^2
  have hF : Continuous F := (poly_cont _ _).norm.pow 2
  have hpolyper : Function.Periodic (poly (N + h) (moving N h b)) 1 := by
    intro t
    unfold poly
    apply Finset.sum_congr rfl
    intro m _
    have hm : phase (m : ℝ) = 1 := by
      simpa only [Int.cast_natCast] using phase_int (m : ℤ)
    rw [mul_add, phase_add, mul_one, hm, mul_one]
  have hper : Function.Periodic F 1 := by
    intro t
    dsimp only [F]
    rw [hpolyper t]
  calc
    _ = ∫ t in (-δ)..δ, (h : ℝ)^2 / 4 * ‖poly N b t‖^2 :=
      (intervalIntegral.integral_const_mul _ (fun t : ℝ => ‖poly N b t‖^2)).symm
    _ ≤ ∫ t in (-δ)..δ, F t :=
      intervalIntegral.integral_mono_on hre
        ((continuous_const.mul ((poly_cont _ _).norm.pow 2)).intervalIntegrable _ _)
        (hF.intervalIntegrable _ _) hline
    _ ≤ ∫ t in (-(1/2):ℝ)..(-(1/2)+1), F t :=
      intervalIntegral.integral_mono_interval (by linarith) hre (by linarith)
        (Filter.Eventually.of_forall (fun _ => by dsimp [F]; positivity)) (hF.intervalIntegrable _ _)
    _ = ∫ t in (0 : ℝ)..1, F t := by
      simpa only [zero_add] using hper.intervalIntegral_add_eq (-(1/2)) 0
    _ = _ := parseval _ _

end GoldbachWindow

end GoldbachDiscreteWindowEstimate

section GoldbachMinorArcAbelTail

open scoped BigOperators

theorem goldbach_geometric_sum_le_inv_twice_round_distance (θ : ℝ) (K : ℕ)
    (hθ : 0 < |θ - (round θ : ℝ)|) :
    ‖∑ j ∈ Finset.range K, Complex.exp (((2 * Real.pi * (j : ℝ) * θ : ℝ) : ℂ) * Complex.I)‖ ≤
      1 / (2 * |θ - (round θ : ℝ)|) := by
  let k : ℤ := round θ
  let d : ℝ := θ - (k : ℝ)
  let z : ℂ := Complex.exp (((2 * Real.pi * θ : ℝ) : ℂ) * Complex.I)
  have hpos : 0 < |d| := hθ
  have habs : |d| ≤ 1 / 2 := abs_sub_round θ
  have hphase : z = Complex.exp (Complex.I * ((2 * Real.pi * d : ℝ) : ℂ)) := by
    have hsplit :
        (((2 * Real.pi * θ : ℝ) : ℂ) * Complex.I) =
          Complex.I * ((2 * Real.pi * d : ℝ) : ℂ) +
            (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
      dsimp [d]
      push_cast
      ring
    dsimp only [z]
    rw [hsplit, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  have harg : |Real.pi * d| ≤ Real.pi / 2 := by
    rw [abs_mul, abs_of_pos Real.pi_pos, show Real.pi / 2 = Real.pi * (1 / 2) by ring]
    exact mul_le_mul_of_nonneg_left habs Real.pi_pos.le
  have hsin : 2 * |d| ≤ |Real.sin (Real.pi * d)| := calc
    _ = 2 / Real.pi * |Real.pi * d| := by
      rw [abs_mul, abs_of_pos Real.pi_pos]
      field_simp [Real.pi_pos.ne']
    _ ≤ _ := Real.mul_abs_le_abs_sin harg
  have hdenom : 4 * |d| ≤ ‖z - 1‖ := by
    rw [hphase, Complex.norm_exp_I_mul_ofReal_sub_one]
    rw [show (2 * Real.pi * d) / 2 = Real.pi * d by ring,
      Real.norm_eq_abs, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    linarith only [hsin]
  have hunit : ‖z‖ = 1 := Complex.norm_exp_ofReal_mul_I _
  have hprod : ‖∑ j ∈ Finset.range K, z ^ j‖ * ‖z - 1‖ ≤ 2 := by
    rw [← norm_mul, geom_sum_mul]
    calc
      _ ≤ ‖z ^ K‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by norm_num [norm_pow, hunit]
  have hscaled : ‖∑ j ∈ Finset.range K, z ^ j‖ * (4 * |d|) ≤ 2 :=
    (mul_le_mul_of_nonneg_left hdenom (norm_nonneg _)).trans hprod
  have hterm (j : ℕ) :
      Complex.exp (((2 * Real.pi * (j : ℝ) * θ : ℝ) : ℂ) * Complex.I) = z^j := by
    have he : (((2 * Real.pi * (j : ℝ) * θ : ℝ) : ℂ) * Complex.I) =
      (j : ℂ) * ((((2 * Real.pi * θ : ℝ) : ℂ)) * Complex.I) := by
      push_cast
      ring
    simpa only [z, he] using Complex.exp_nat_mul
      ((((2 * Real.pi * θ : ℝ) : ℂ)) * Complex.I) j
  simp_rw [hterm]
  change ‖∑ j ∈ Finset.range K, z ^ j‖ ≤ 1 / (2 * |d|)
  apply (le_div_iff₀ (mul_pos (by norm_num) hpos)).2
  nlinarith only [hscaled]


open MeasureTheory

theorem goldbach_periodic_integral_mul_nat
    (g : ℝ → ℝ) (hg : Function.Periodic g 1)
    (hi : IntervalIntegrable g volume 0 1) (m : ℕ) (hm : 0 < m) :
    (∫ t in (0 : ℝ)..1, g ((m : ℝ) * t)) = ∫ t in (0 : ℝ)..1, g t := by
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hperiod := hg.intervalIntegral_add_zsmul_eq (m : ℤ) 0
    (fun a b => hg.intervalIntegrable₀ (by norm_num) hi a b)
  have hscaled : (∫ t in (0 : ℝ)..(m : ℝ), g t) =
      (m : ℝ) * ∫ t in (0 : ℝ)..1, g t := by
    simpa only [zsmul_eq_mul, Int.cast_natCast, mul_one, zero_add] using hperiod
  rw [intervalIntegral.integral_comp_mul_left g hmR, mul_zero, mul_one, hscaled,
    smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hmR, one_mul]


open Set

noncomputable def goldbach_round_tail (δ x : ℝ) : ℝ :=
  if δ ≤ |x - (round x : ℝ)| then 1 / |x - (round x : ℝ)| ^ 2 else 0

theorem goldbach_round_tail_periodic (δ : ℝ) : Function.Periodic (goldbach_round_tail δ) 1 := by
  intro x
  simp only [goldbach_round_tail, round_add_one, Int.cast_add, Int.cast_one, add_sub_add_right_eq_sub]

theorem goldbach_round_tail_integral (δ : ℝ) (hδ : 0 < δ) (hd : δ ≤ 1 / 2) :
    IntervalIntegrable (goldbach_round_tail δ) volume 0 1 ∧
      (∫ x in (0 : ℝ)..1, goldbach_round_tail δ x) = 2 / δ - 4 := by
  let g := goldbach_round_tail δ
  let f : ℝ → ℝ := fun x => x ^ (-2 : ℤ)
  have hr {x : ℝ} (hx : x ∈ Ioo (-(1 / 2 : ℝ)) (1 / 2)) : round x = 0 :=
    round_eq_zero_iff.2 ⟨hx.1.le, hx.2⟩
  have hpow (x : ℝ) : f x = 1 / |x| ^ 2 := by
    simp [f, zpow_neg, sq_abs, one_div]
  have heL : (Ioo (-(1 / 2 : ℝ)) (-δ)).EqOn g f := by
    intro x hx
    have hxr : x < 1 / 2 := by linarith only [hx.2, hδ]
    have hx0 : x < 0 := by linarith only [hx.2, hδ]
    have hxd : δ ≤ |x| := by rw [abs_of_neg hx0]; linarith only [hx.2]
    rw [hpow]
    simp only [g, goldbach_round_tail, hr ⟨hx.1,hxr⟩, Int.cast_zero, sub_zero, ite_eq_left hxd]
  have heR : (Ioo δ (1 / 2 : ℝ)).EqOn g f := by
    intro x hx
    have hxl : -(1 / 2 : ℝ) < x := by linarith only [hx.1, hδ]
    have hx0 : 0 < x := by linarith only [hx.1, hδ]
    have hxd : δ ≤ |x| := by rw [abs_of_pos hx0]; exact hx.1.le
    rw [hpow]
    simp only [g, goldbach_round_tail, hr ⟨hxl,hx.2⟩, Int.cast_zero, sub_zero, ite_eq_left hxd]
  have heC : (Ioo (-δ) δ).EqOn g (fun _ : ℝ => (0 : ℝ)) := by
    intro x hx
    have hx₁ : -(1 / 2 : ℝ) < x := by linarith only [hd, hx.1]
    have hx₂ : x < (1 / 2 : ℝ) := hx.2.trans_le hd
    have hxd : |x| < δ := abs_lt.2 ⟨hx.1, hx.2⟩
    simp only [g, goldbach_round_tail, hr ⟨hx₁,hx₂⟩, Int.cast_zero, sub_zero,
      ite_eq_right hxd.not_ge]
  have hAway (l r : ℝ) (hab : l ≤ r) (h0 : (0 : ℝ) ∉ Icc l r) (he : (Ioo l r).EqOn g f) :
      IntervalIntegrable g volume l r ∧ (∫ x in l..r, g x) = l⁻¹ - r⁻¹ := by
    have hz : (0 : ℝ) ∉ uIcc l r := by simpa only [uIcc_of_le hab] using h0
    have hIf : IntervalIntegrable f volume l r :=
      intervalIntegral.intervalIntegrable_zpow (n := -2) (Or.inr hz)
    refine ⟨hIf.congr_uIoo (by simpa only [uIoo_of_le hab] using he.symm), ?_⟩
    rw [intervalIntegral.integral_congr_Ioo_of_le hab he]
    change (∫ x in l..r, x ^ (-2 : ℤ)) = _
    rw [integral_zpow (Or.inr ⟨by norm_num, hz⟩)]
    norm_num
    ring
  obtain ⟨hIL,hVL⟩ := hAway (-(1/2)) (-δ) (by linarith only [hd])
    (by intro hz; have hh := (mem_Icc.mp hz).2; linarith only [hh,hδ]) heL
  obtain ⟨hIR,hVR⟩ := hAway δ (1/2) hd
    (by intro hz; have hh := (mem_Icc.mp hz).1; linarith only [hh,hδ]) heR
  have hcent : -δ ≤ δ := by linarith only [hδ]
  have hIC : IntervalIntegrable g volume (-δ) δ :=
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (0 : ℝ)) volume (-δ) δ).congr_uIoo
      (by simpa only [uIoo_of_le hcent] using heC.symm)
  have hVC : (∫ x in -δ..δ, g x) = 0 := by
    rw [intervalIntegral.integral_congr_Ioo_of_le hcent heC]
    exact intervalIntegral.integral_zero
  have hp := goldbach_round_tail_periodic δ
  have hiBase : IntervalIntegrable g volume (-(1/2)) (1/2) := hIL.trans (hIC.trans hIR)
  have hBaseEnd : -(1/2 : ℝ) + 1 = 1/2 := by norm_num
  have hInt : IntervalIntegrable g volume 0 1 :=
    hp.intervalIntegrable (by norm_num) (t := -(1/2 : ℝ)) (by simpa only [hBaseEnd] using hiBase) 0 1
  refine ⟨hInt, ?_⟩
  have hperiod := hp.intervalIntegral_add_eq (-(1/2 : ℝ)) 0
  change (∫ x in (0 : ℝ)..1, g x) = _
  rw [show (∫ x in (0 : ℝ)..1, g x) = ∫ x in (-(1/2 : ℝ))..(1/2), g x by
      simpa only [hBaseEnd, zero_add] using hperiod.symm,
      ← intervalIntegral.integral_add_adjacent_intervals hIL (hIC.trans hIR),
      ← intervalIntegral.integral_add_adjacent_intervals hIC hIR,
      hVL, hVC, hVR]
  norm_num [inv_neg, div_eq_mul_inv]
  ring

theorem goldbach_sum_Icc_one_eq_shifted_range {E : Type*} [AddCommMonoid E]
    (f : ℕ → E) (K : ℕ) :
    (∑ j ∈ Finset.Icc 1 K, f j) = ∑ j ∈ Finset.range K, f (j+1) := by
  symm
  refine Finset.sum_bij (fun j _ => j+1) ?_ ?_ ?_ ?_
  · intro j hj
    have hj' := Finset.mem_range.mp hj
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  · intro i _ j _ hij
    omega
  · intro j hj
    obtain ⟨hj₁,hj₂⟩ := Finset.mem_Icc.mp hj
    exact ⟨j-1, Finset.mem_range.mpr (by omega), by omega⟩
  · intro j _
    rfl

theorem goldbach_exponential_shifted_range_norm (θ : ℝ) (K : ℕ) :
    ‖∑ j ∈ Finset.range K, Complex.exp (((2 * Real.pi * ((j+1 : ℕ) : ℝ) * θ : ℝ) : ℂ) *
        Complex.I)‖ =
      ‖∑ j ∈ Finset.range K, Complex.exp (((2 * Real.pi * (j : ℝ) * θ : ℝ) : ℂ) *
        Complex.I)‖ := by
  let e : ℕ → ℂ := fun j => Complex.exp (((2 * Real.pi * (j : ℝ) * θ : ℝ) : ℂ) * Complex.I)
  have hshift (j : ℕ) : e (j+1) = e 1 * e j := by
    dsimp [e]
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hunit : ‖e 1‖ = 1 := Complex.norm_exp_ofReal_mul_I _
  have hs : (∑ j ∈ Finset.range K, e (j+1)) = e 1 * (∑ j ∈ Finset.range K, e j) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun j _ => hshift j)
  change ‖∑ j ∈ Finset.range K, e (j+1)‖ = ‖∑ j ∈ Finset.range K, e j‖
  rw [hs, norm_mul, hunit, one_mul]

theorem goldbach_positive_exponential_prefix_norm (θ : ℝ) (K : ℕ) :
    ‖∑ j ∈ Finset.Icc 1 K, Complex.exp (((2 * Real.pi * (j : ℝ) * θ : ℝ) : ℂ) *
        Complex.I)‖ =
      ‖∑ j ∈ Finset.range K, Complex.exp (((2 * Real.pi * (j : ℝ) * θ : ℝ) : ℂ) *
        Complex.I)‖ := by
  rw [goldbach_sum_Icc_one_eq_shifted_range]
  exact goldbach_exponential_shifted_range_norm θ K

theorem goldbach_norm_weighted_prefix_le {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a : ℕ → E) (w : ℕ → ℝ) (K : ℕ) (B : ℝ)
    (hw : Monotone w) (hw₀ : ∀ j, 0 ≤ w j) (hB : 0 ≤ B)
    (hprefix : ∀ n ≤ K, ‖∑ j ∈ Finset.range n, a j‖ ≤ B) :
    ‖∑ j ∈ Finset.range K, w j • a j‖ ≤ 2 * w (K-1) * B := by
  have htel (N : ℕ) :
      (∑ j ∈ Finset.range N, (w (j+1) - w j)) = w N - w 0 := by
    induction N with
    | zero => simp
    | succ N ih => rw [Finset.sum_range_succ, ih]; ring
  have hlead :
      ‖w (K-1) • (∑ j ∈ Finset.range K, a j)‖ ≤ w (K-1) * B := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hw₀ _)]
    exact mul_le_mul_of_nonneg_left (hprefix K le_rfl) (hw₀ _)
  have hrest :
      ‖∑ j ∈ Finset.range (K-1), (w (j+1) - w j) • (∑ i ∈ Finset.range (j+1), a i)‖
        ≤ (w (K-1)-w 0) * B := by
    calc
      _ ≤ ∑ j ∈ Finset.range (K-1),
          ‖(w (j+1)-w j) • (∑ i ∈ Finset.range (j+1), a i)‖ := norm_sum_le _ _
      _ ≤ ∑ j ∈ Finset.range (K-1), (w (j+1)-w j)*B := by
        apply Finset.sum_le_sum
        intro j hj
        have hj' : j + 1 ≤ K := by
          have := Finset.mem_range.mp hj
          omega
        have hdiff : 0 ≤ w (j+1)-w j := sub_nonneg.mpr (hw (Nat.le_succ j))
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hdiff]
        exact mul_le_mul_of_nonneg_left (hprefix (j+1) hj') hdiff
      _ = _ := by rw [← Finset.sum_mul, htel]
  rw [Finset.sum_range_by_parts]
  calc
    _ ≤ _ := norm_sub_le _ _
    _ ≤ w (K-1)*B + (w (K-1)-w 0)*B := by exact add_le_add hlead hrest
    _ = (2*w (K-1)-w 0)*B := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (sub_le_self _ (hw₀ 0)) hB

theorem goldbach_log_exponential_prefix_bound (θ B : ℝ) (K : ℕ) (hB : 0 ≤ B)
    (hprefix : ∀ n ≤ K,
      ‖∑ j ∈ Finset.range n, Complex.exp (((2 * Real.pi * (j : ℝ) * θ : ℝ) : ℂ) * Complex.I)‖ ≤ B) :
    ‖∑ j ∈ Finset.Icc 1 K,
      (Real.log (j : ℝ) : ℂ) * Complex.exp (((2 * Real.pi * (j : ℝ) * θ : ℝ) : ℂ) * Complex.I)‖
      ≤ 2 * Real.log (K : ℝ) * B := by
  let e : ℕ → ℂ := fun j => Complex.exp (((2 * Real.pi * (j : ℝ) * θ : ℝ) : ℂ) * Complex.I)
  let w : ℕ → ℝ := fun j => Real.log ((j+1 : ℕ) : ℝ)
  have hw : Monotone w := by
    intro i j hij
    dsimp [w]
    exact Real.log_le_log (by positivity) (by exact_mod_cast Nat.succ_le_succ hij)
  have hw₀ (j : ℕ) : 0 ≤ w j :=
    Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ j + 1))
  have hshifted (n : ℕ) (hn : n ≤ K) :
      ‖∑ j ∈ Finset.range n, e (j+1)‖ ≤ B := by
    calc
      _ = ‖∑ j ∈ Finset.range n, e j‖ := goldbach_exponential_shifted_range_norm θ n
      _ ≤ _ := hprefix n hn
  have hreindex :
      (∑ j ∈ Finset.Icc 1 K, (Real.log (j : ℝ) : ℂ) * e j) =
        ∑ j ∈ Finset.range K, w j • e (j+1) := by
    simpa only [w, Complex.real_smul] using
      goldbach_sum_Icc_one_eq_shifted_range (fun j => (Real.log (j : ℝ) : ℂ) * e j) K
  change ‖∑ j ∈ Finset.Icc 1 K, (Real.log (j : ℝ) : ℂ) * e j‖ ≤ _
  rw [hreindex]
  by_cases hK : K = 0
  · simp [hK]
  · have hterm : w (K-1) = Real.log (K : ℝ) := by
      dsimp [w]
      rw [Nat.sub_add_cancel (by omega : 1 ≤ K)]
    simpa only [hterm] using
      goldbach_norm_weighted_prefix_le (fun j => e (j+1)) w K B hw hw₀ hB hshifted

theorem goldbach_truncated_square_comparison (F : ℝ → ℝ) (hF : Continuous F)
    (A : ℝ) (hA : 0 ≤ A) (m : ℕ) (hm : 0 < m) (δ : ℝ)
    (hδ : 0 < δ) (hd : δ ≤ 1 / 2) (s : Set ℝ) (hs : MeasurableSet s)
    (hcut : ∀ t ∈ Icc (0 : ℝ) 1, t ∈ s →
      δ ≤ |(m : ℝ) * t - (round ((m : ℝ) * t) : ℝ)|)
    (hpoint : ∀ t ∈ Icc (0 : ℝ) 1, t ∈ s →
      F t ≤ A * (1 / |(m : ℝ) * t - (round ((m : ℝ) * t) : ℝ)| ^ 2)) :
    (∫ t in (0 : ℝ)..1, s.indicator F t) ≤ A * (2/δ - 4) := by
  let g := goldbach_round_tail δ
  have hi : IntervalIntegrable F volume 0 1 := hF.intervalIntegrable 0 1
  have hiind : IntervalIntegrable (s.indicator F) volume 0 1 := by
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).2
    exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).1 hi).indicator hs
  obtain ⟨hiUnit, hvalue⟩ := goldbach_round_tail_integral δ hδ hd
  have hp := goldbach_round_tail_periodic δ
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hiWide : IntervalIntegrable g volume 0 (m : ℝ) :=
    hp.intervalIntegrable₀ one_ne_zero hiUnit 0 (m : ℝ)
  have hiScaled : IntervalIntegrable (fun t => g ((m : ℝ) * t)) volume 0 1 := by
    simpa only [zero_div, div_self hmR] using hiWide.comp_mul_left (c := (m : ℝ))
  have hnonneg (t : ℝ) : 0 ≤ g t := by dsimp [g, goldbach_round_tail]; split <;> positivity
  calc
    _ ≤ ∫ t in (0 : ℝ)..1, A * g ((m : ℝ)*t) := by
      apply intervalIntegral.integral_mono_on zero_le_one hiind (hiScaled.const_mul A)
      intro t ht
      by_cases hb : t ∈ s
      · rw [indicator_of_mem hb]
        dsimp [g]
        rw [goldbach_round_tail, ite_eq_left (hcut t ht hb)]
        exact hpoint t ht hb
      · rw [indicator_of_notMem hb]
        exact mul_nonneg hA (hnonneg _)
    _ = _ := by
      rw [intervalIntegral.integral_const_mul,
        goldbach_periodic_integral_mul_nat g hp hiUnit m hm, hvalue]

theorem goldbach_geometric_tail_l2 (K m : ℕ) (hm : 0 < m) (δ : ℝ)
    (hδ : 0 < δ) (hd : δ ≤ 1 / 2) (s : Set ℝ) (hs : MeasurableSet s)
    (hcut : ∀ t ∈ Icc (0 : ℝ) 1, t ∈ s →
      δ ≤ |(m : ℝ) * t - (round ((m : ℝ) * t) : ℝ)|) :
    (∫ t in (0 : ℝ)..1, s.indicator (fun t =>
      ‖∑ j ∈ Finset.range K,
        Complex.exp (((2 * Real.pi * (j : ℝ) * ((m : ℝ) * t) : ℝ) : ℂ) * Complex.I)‖ ^ 2) t)
      ≤ 1 / (2 * δ) := by
  let F : ℝ → ℝ := fun t =>
    ‖∑ j ∈ Finset.range K,
      Complex.exp (((2 * Real.pi * (j : ℝ) * ((m : ℝ) * t) : ℝ) : ℂ) * Complex.I)‖ ^ 2
  have hF : Continuous F := by dsimp [F]; fun_prop
  have hI : (∫ t in (0 : ℝ)..1, s.indicator F t) ≤ (1/4 : ℝ) * (2/δ - 4) := by
    apply goldbach_truncated_square_comparison F hF (1/4) (by norm_num) m hm δ hδ hd s hs hcut
    intro t ht hb
    have hpos := hδ.trans_le (hcut t ht hb)
    have hgeo := goldbach_geometric_sum_le_inv_twice_round_distance ((m : ℝ)*t) K hpos
    let d : ℝ := |(m : ℝ)*t - (round ((m : ℝ)*t) : ℝ)|
    have hn : 0 < d := hpos
    calc
      _ ≤ (1 / (2 * d)) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hgeo 2
      _ = (1/4 : ℝ) * (1 / d^2) := by
        field_simp [hn.ne']
        ring
  change (∫ t in (0 : ℝ)..1, s.indicator F t) ≤ _
  have hEq : (1/4 : ℝ) * (2/δ - 4) = 1/(2*δ) - 1 := by
    field_simp [hδ.ne']
    ring
  rw [hEq] at hI
  linarith only [hI]

theorem goldbach_positive_exponential_tail_l2 (K m : ℕ) (hm : 0 < m) (δ : ℝ)
    (hδ : 0 < δ) (hd : δ ≤ 1 / 2) (s : Set ℝ) (hs : MeasurableSet s)
    (hcut : ∀ t ∈ Icc (0 : ℝ) 1, t ∈ s →
      δ ≤ |(m : ℝ) * t - (round ((m : ℝ) * t) : ℝ)|) :
    (∫ t in (0 : ℝ)..1, s.indicator (fun t =>
      ‖∑ j ∈ Finset.Icc 1 K,
        Complex.exp (((2 * Real.pi * (j : ℝ) * ((m : ℝ) * t) : ℝ) : ℂ) * Complex.I)‖ ^ 2) t)
      ≤ 1 / (2 * δ) := by
  simp_rw [goldbach_positive_exponential_prefix_norm]
  exact goldbach_geometric_tail_l2 K m hm δ hδ hd s hs hcut

theorem goldbach_log_exponential_tail_l2 (K m : ℕ) (hm : 0 < m) (δ : ℝ)
    (hδ : 0 < δ) (hd : δ ≤ 1 / 2) (s : Set ℝ) (hs : MeasurableSet s)
    (hcut : ∀ t ∈ Icc (0 : ℝ) 1, t ∈ s →
      δ ≤ |(m : ℝ) * t - (round ((m : ℝ) * t) : ℝ)|) :
    (∫ t in (0 : ℝ)..1, s.indicator (fun t =>
      ‖∑ j ∈ Finset.Icc 1 K, (Real.log (j : ℝ) : ℂ) *
        Complex.exp (((2 * Real.pi * (j : ℝ) * ((m : ℝ) * t) : ℝ) : ℂ) * Complex.I)‖ ^ 2) t)
      ≤ 2 * Real.log (K : ℝ)^2 / δ := by
  let F : ℝ → ℝ := fun t =>
    ‖∑ j ∈ Finset.Icc 1 K, (Real.log (j : ℝ) : ℂ) *
      Complex.exp (((2 * Real.pi * (j : ℝ) * ((m : ℝ) * t) : ℝ) : ℂ) * Complex.I)‖ ^ 2
  let A : ℝ := Real.log (K : ℝ)^2
  have hA : 0 ≤ A := sq_nonneg _
  have hF : Continuous F := by dsimp [F]; fun_prop
  have hI : (∫ t in (0 : ℝ)..1, s.indicator F t) ≤ A * (2/δ - 4) := by
    apply goldbach_truncated_square_comparison F hF A hA m hm δ hδ hd s hs hcut
    intro t ht hb
    have hpos := hδ.trans_le (hcut t ht hb)
    let d : ℝ := |(m : ℝ)*t - (round ((m : ℝ)*t) : ℝ)|
    have hn : 0 < d := hpos
    have hgeo := goldbach_log_exponential_prefix_bound ((m : ℝ)*t) (1/(2*d)) K
      (by positivity) (fun n _ => goldbach_geometric_sum_le_inv_twice_round_distance ((m : ℝ)*t) n hpos)
    have hEq : 2 * Real.log (K : ℝ) * (1/(2*d)) = Real.log (K : ℝ)/d := by
      field_simp [hn.ne']
    rw [hEq] at hgeo
    calc
      _ ≤ (Real.log (K : ℝ)/d)^2 := pow_le_pow_left₀ (norm_nonneg _) hgeo 2
      _ = A * (1/d^2) := by dsimp [A]; rw [div_pow,one_div,div_eq_mul_inv]
  change (∫ t in (0 : ℝ)..1, s.indicator F t) ≤ _
  calc
    _ ≤ A * (2/δ - 4) := hI
    _ ≤ A * (2/δ) := mul_le_mul_of_nonneg_left (sub_le_self _ (by norm_num)) hA
    _ = _ := by dsimp [A]; ring

end GoldbachMinorArcAbelTail

section FrontierMedcoreModelHelpers

open scoped BigOperators ComplexConjugate

theorem frontierMedcoreWeightedPrefixLower (a w : ℕ → ℝ) (K : ℕ) (B : ℝ)
    (hw : Antitone w) (hw₀ : ∀ j, 0 ≤ w j)
    (hPrefix : ∀ m ≤ K, -B ≤ ∑ j ∈ Finset.range m, a j) :
    -(B * w 0) ≤ ∑ j ∈ Finset.range K, w j * a j := by
  have hTel (N : ℕ) :
      (∑ j ∈ Finset.range N, (w (j+1) - w j)) = w N - w 0 := by
    induction N with
    | zero => simp
    | succ N ih => rw [Finset.sum_range_succ, ih]; ring
  have hLast : -B * w (K-1) ≤ w (K-1) * (∑ j ∈ Finset.range K, a j) := by
    rw [mul_comm (-B)]
    exact mul_le_mul_of_nonneg_left (hPrefix K le_rfl) (hw₀ _)
  have hRest :
      (∑ j ∈ Finset.range (K-1),
        (w (j+1) - w j) * (∑ i ∈ Finset.range (j+1), a i)) ≤ (w (K-1) - w 0) * -B := by
    calc
      _ ≤ ∑ j ∈ Finset.range (K-1), (w (j+1) - w j) * -B := by
        apply Finset.sum_le_sum
        intro j hj
        have hjK : j + 1 ≤ K := by
          have := Finset.mem_range.mp hj
          omega
        exact mul_le_mul_of_nonpos_left (hPrefix (j+1) hjK)
          (sub_nonpos.mpr (hw (Nat.le_succ j)))
      _ = _ := by rw [← Finset.sum_mul, hTel]
  change -(B * w 0) ≤ ∑ j ∈ Finset.range K, w j • a j
  rw [Finset.sum_range_by_parts]
  simp only [smul_eq_mul]
  calc
    _ = -B * w (K-1) - (w (K-1) - w 0) * -B := by ring
    _ ≤ _ := sub_le_sub hLast hRest

private noncomputable def frontierMedcorePhase (x : ℝ) : ℂ :=
  Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)

theorem frontierMedcoreKernelReflection (n : ℕ) (β : ℝ) :
    let E := fun x : ℝ => Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)
    let K := ∑ k ∈ Finset.range (n+1), E ((k : ℝ) * β)
    K^2 * E (-(n : ℝ) * β) = (Complex.normSq K : ℂ) := by
  dsimp only
  let F : ℕ → ℂ := fun k => frontierMedcorePhase ((k : ℝ) * β)
  change (∑ k ∈ Finset.range (n+1), F k)^2 * frontierMedcorePhase (-(n : ℝ) * β) =
    (Complex.normSq (∑ k ∈ Finset.range (n+1), F k) : ℂ)
  have hPhaseAdd (x y : ℝ) : frontierMedcorePhase (x + y) =
      frontierMedcorePhase x * frontierMedcorePhase y := by
    unfold frontierMedcorePhase
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hPhaseConj (x : ℝ) : conj (frontierMedcorePhase x) = frontierMedcorePhase (-x) := by
    unfold frontierMedcorePhase
    rw [← Complex.exp_conj]
    congr 1
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
    push_cast
    ring
  have hConj : (∑ k ∈ Finset.range (n+1), F k) * frontierMedcorePhase (-(n : ℝ) * β) =
      conj (∑ k ∈ Finset.range (n+1), F k) := by
    rw [Finset.sum_mul, map_sum, ← Finset.sum_range_reflect (fun k => F k * _)]
    apply Finset.sum_congr rfl
    intro k hk
    have hk' : k ≤ n := by
      have := Finset.mem_range.mp hk
      omega
    have hIdx : n + 1 - 1 - k = n - k := by omega
    rw [hIdx]
    dsimp only [F]
    rw [← hPhaseAdd, hPhaseConj, Nat.cast_sub hk']
    congr 1
    ring
  rw [pow_two, mul_assoc, hConj, Complex.normSq_eq_conj_mul_self, mul_comm]

end FrontierMedcoreModelHelpers

section GoldbachGRHCharacterInput

/-
The averaged cutoff of width sqrt(X) has a Mellin transform with quadratic decay.
We shift its integral for the twisted von Mangoldt sum to real part 9/20. Uniform
Jensen estimates and local bounds for the logarithmic derivative control the sums
over zeros and the contour edges. The only additional residue comes from the
principal character at one. The estimates apply to every positive modulus and
every character. Removing the averaging and applying character orthogonality
gives the stated progression error.
-/

namespace GoldbachSmoothing

open Complex MeasureTheory Set

noncomputable section

/-- The piecewise linear function supported to the left of `x`. -/
def triangle (x t : ℝ) : ℂ := (max (x - t) 0 : ℝ)

/-- The average of the cutoffs at the points of `[x, x+h]`. -/
def cutoff (x h t : ℝ) : ℂ := (triangle (x + h) t - triangle x t) / (h : ℂ)

/-- The Mellin transform of the averaged cutoff. -/
def kernel (x h : ℝ) (s : ℂ) : ℂ :=
  (((x + h : ℝ) : ℂ) ^ (s + 1) - (x : ℂ) ^ (s + 1)) / ((h : ℂ) * s * (s + 1))

private theorem shift_nonzero {s : ℂ} (hs : 0 < s.re) : s + 1 ≠ 0 := by
  intro he
  have hz := congrArg Complex.re he
  simp only [add_re, one_re, zero_re] at hz
  linarith

private theorem triangle_one_hasMellin {s : ℂ} (hs : 0 < s.re) :
    HasMellin (triangle 1) s (1 / (s * (s + 1))) := by
  have h1 := hasMellin_one_Ioc hs
  have h2 := hasMellin_cpow_Ioc (1 : ℂ) (s := s) (by simp only [one_re]; linarith)
  have hdiff := hasMellin_sub h1.1 h2.1
  have heq : EqOn (triangle 1)
      (fun t => (Ioc 0 1).indicator (fun _ : ℝ => 1 : ℝ → ℂ) t -
        (Ioc 0 1).indicator (fun t : ℝ => (t : ℂ) ^ (1 : ℂ)) t) (Ioi 0) := by
    intro t ht
    have ht0 : 0 < t := ht
    by_cases ht1 : t ≤ 1
    · have hm : t ∈ Ioc (0 : ℝ) 1 := ⟨ht0, ht1⟩
      simp [triangle, hm, max_eq_left (sub_nonneg.mpr ht1)]
    · have hm : t ∉ Ioc (0 : ℝ) 1 := fun h => ht1 h.2
      simp [triangle, hm, max_eq_right (sub_nonpos.mpr (le_of_not_ge ht1))]
  have heqMul : EqOn (fun t : ℝ => (t : ℂ) ^ (s - 1) • triangle 1 t) _ (Ioi 0) :=
    fun t ht => congrArg (fun w : ℂ => (t : ℂ) ^ (s - 1) • w) (heq ht)
  refine ⟨(integrableOn_congr_fun heqMul measurableSet_Ioi).2 hdiff.1, ?_⟩
  have h0 : s ≠ 0 := fun hz => by simp [hz] at hs
  calc
    mellin (triangle 1) s = _ := setIntegral_congr_fun measurableSet_Ioi heqMul
    _ = _ := hdiff.2
    _ = _ := by
      rw [h1.2, h2.2]
      field_simp [h0, shift_nonzero hs]
      ring

/-- The Mellin transform of the triangle on a positive interval. -/
theorem triangle_hasMellin {x : ℝ} (hx : 0 < x) {s : ℂ} (hs : 0 < s.re) :
    HasMellin (triangle x) s ((x : ℂ) ^ (s + 1) / (s * (s + 1))) := by
  have h1 := triangle_one_hasMellin hs
  have hxInv : 0 < x⁻¹ := inv_pos.mpr hx
  have hxC : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.ne'
  have hscale : triangle x = fun t => (x : ℂ) • triangle 1 (x⁻¹ * t) := by
    funext t
    have hxmul : x * (1 - x⁻¹ * t) = x - t := by field_simp [hx.ne']
    simp only [triangle, smul_eq_mul, ← ofReal_mul, mul_max_of_nonneg _ _ hx.le,
      mul_zero, hxmul]
  have hscaled := (MellinConvergent.comp_mul_left hxInv).mpr h1.1
  have hsmul := hasMellin_const_smul hscaled (x : ℂ)
  refine ⟨hscale ▸ hsmul.1, ?_⟩
  rw [hscale, hsmul.2, mellin_comp_mul_left _ _ hxInv, h1.2, ofReal_inv,
    inv_cpow_ofReal_nonneg hx.le, cpow_neg, inv_inv, cpow_add _ _ hxC, cpow_one]
  simp only [smul_eq_mul]
  ring

/-- Exact Mellin transform of the continuous cutoff, including convergence. -/
theorem cutoff_hasMellin {x h : ℝ} (hx : 0 < x) (hh : 0 < h) {s : ℂ} (hs : 0 < s.re) :
    HasMellin (cutoff x h) s (kernel x h s) := by
  have hLeft := triangle_hasMellin hx hs
  have hRight := triangle_hasMellin (add_pos hx hh) hs
  have hsub := hasMellin_sub hRight.1 hLeft.1
  refine ⟨hsub.1.div_const _, ?_⟩
  change mellin (fun t => (triangle (x + h) t - triangle x t) / (h : ℂ)) s = _
  rw [mellin_div_const, hsub.2, hRight.2, hLeft.2, ← sub_div, div_div, kernel]
  congr 1
  ring

/-- The kernel can also be written as an interval average of `y^s/s`. -/
theorem kernel_eq_interval {x h : ℝ} {s : ℂ} (hs : 0 < s.re) :
    kernel x h s = (∫ y in x..x+h, (y : ℂ) ^ s) / ((h : ℂ) * s) := by
  rw [integral_cpow (Or.inl (show -1 < s.re by linarith)), div_div, kernel]
  congr 1
  ring

/-- The interval form bounds the kernel by one power of the vertical denominator. -/
theorem norm_kernel_le {x h : ℝ} (hx : 0 < x) (hh : 0 < h) {s : ℂ} (hs : 0 < s.re) :
    ‖kernel x h s‖ ≤ (x + h) ^ s.re / ‖s‖ := by
  have h0 : s ≠ 0 := fun hz => by simp [hz] at hs
  have hb : ∀ y ∈ uIoc x (x + h), ‖(y : ℂ) ^ s‖ ≤ (x + h) ^ s.re := by
    intro y hy
    rw [uIoc_of_le (le_add_of_nonneg_right hh.le)] at hy
    have hy0 := hx.trans hy.1
    rw [norm_cpow_eq_rpow_re_of_pos hy0]
    exact Real.rpow_le_rpow hy0.le hy.2 hs.le
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const hb
  rw [show x + h - x = h by ring, abs_of_pos hh] at hi
  rw [kernel_eq_interval hs, norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hh]
  calc
    _ ≤ (x + h) ^ s.re * h / (h * ‖s‖) :=
      div_le_div_of_nonneg_right hi (mul_nonneg hh.le (norm_nonneg s))
    _ = _ := by field_simp [hh.ne', norm_ne_zero_iff.mpr h0]

/-- The difference form gives quadratic vertical decay. -/
theorem norm_kernel_le_tail {x h : ℝ} (hx : 0 < x) (hh : 0 < h) {s : ℂ} :
    ‖kernel x h s‖ ≤
      ((x + h) ^ (s.re + 1) + x ^ (s.re + 1)) / (h * ‖s‖ * ‖s + 1‖) := by
  rw [kernel, norm_div, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hh]
  apply div_le_div_of_nonneg_right _ (by positivity)
  refine (norm_sub_le _ _).trans_eq ?_
  rw [norm_cpow_eq_rpow_re_of_pos (add_pos hx hh), norm_cpow_eq_rpow_re_of_pos hx,
    Complex.add_re, Complex.one_re]

theorem cutoff_continuous (x h : ℝ) : Continuous (cutoff x h) := by
  unfold cutoff triangle
  fun_prop

theorem kernel_verticalIntegrable {x h σ : ℝ} (hx : 0 < x) (hh : 0 < h) (hσ : 0 < σ) :
    VerticalIntegrable (kernel x h) σ := by
  let A := (x + h) ^ (σ + 1) + x ^ (σ + 1)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have h₀ (t : ℝ) : ((σ : ℂ) + (t : ℂ) * I) ≠ 0 := by
    intro he
    have := congrArg Complex.re he
    simp at this
    exact hσ.ne' this
  have h₁ (t : ℝ) : ((σ : ℂ) + (t : ℂ) * I) + 1 ≠ 0 := by
    apply shift_nonzero
    simpa using hσ
  have hcontinuous : Continuous (fun t : ℝ => kernel x h ((σ : ℂ) + (t : ℂ) * I)) := by
    let line (t : ℝ) : ℂ := (σ : ℂ) + (t : ℂ) * I
    have hline : Continuous line := continuous_const.add (continuous_ofReal.mul continuous_const)
    have hshift : Continuous (fun t => line t + 1) := hline.add continuous_const
    have hp (b : ℝ) (hb : 0 < b) : Continuous (fun t => (b : ℂ) ^ (line t + 1)) := by
      simp_rw [cpow_def_of_ne_zero (ofReal_ne_zero.mpr hb.ne')]
      exact continuous_exp.comp (continuous_const.mul hshift)
    change Continuous fun t => kernel x h (line t)
    unfold kernel
    refine ((hp (x + h) (add_pos hx hh)).sub (hp x hx)).div
      ((continuous_const.mul hline).mul hshift) fun t => ?_
    exact mul_ne_zero (mul_ne_zero (ofReal_ne_zero.mpr hh.ne') (h₀ t)) (h₁ t)
  have hb := (integrable_inv_one_add_mul_sq (inv_ne_zero hσ.ne')).const_mul (A / (h * σ ^ 2))
  apply hb.mono' hcontinuous.aestronglyMeasurable
  filter_upwards with t
  let z : ℂ := (σ : ℂ) + (t : ℂ) * I
  have hzRe : z.re = σ := by simp [z]
  have hzIm : z.im = t := by simp [z]
  have hzSquare : ‖z‖ ^ 2 = σ ^ 2 + t ^ 2 := by
    rw [Complex.sq_norm, normSq_apply, hzRe, hzIm]
    ring
  have hzNextSquare : ‖z + 1‖ ^ 2 = (σ + 1) ^ 2 + t ^ 2 := by
    rw [Complex.sq_norm, normSq_apply]
    simp only [Complex.add_re, Complex.one_re, Complex.add_im, Complex.one_im, add_zero, hzRe, hzIm]
    ring
  have hn : ‖z‖ ≤ ‖z + 1‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [hzSquare, hzNextSquare]
    nlinarith
  have hden : h * σ ^ 2 * (1 + (σ⁻¹ * t) ^ 2) ≤ h * ‖z‖ * ‖z + 1‖ := by
    calc
      _ = h * (σ ^ 2 + t ^ 2) := by field_simp [hσ.ne']
      _ = h * (‖z‖ * ‖z‖) := by rw [← hzSquare, pow_two]
      _ ≤ h * (‖z‖ * ‖z + 1‖) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hn (norm_nonneg _)) hh.le
      _ = _ := by ring
  calc
    _ ≤ A / (h * ‖z‖ * ‖z + 1‖) := by simpa [hzRe, A] using norm_kernel_le_tail hx hh (s := z)
    _ ≤ A / (h * σ ^ 2 * (1 + (σ⁻¹ * t) ^ 2)) :=
      div_le_div_of_nonneg_left hA (by positivity) hden
    _ = _ := by simp only [div_eq_mul_inv, mul_inv_rev]; ring

/-- The inverse Mellin integral recovers the continuous cutoff at every positive point. -/
theorem mellinInv_kernel_eq {x h σ y : ℝ} (hx : 0 < x) (hh : 0 < h) (hσ : 0 < σ)
    (hy : 0 < y) : mellinInv σ (kernel x h) y = cutoff x h y := by
  have hline (t : ℝ) : mellin (cutoff x h) ((σ : ℂ) + (t : ℂ) * I) =
      kernel x h ((σ : ℂ) + (t : ℂ) * I) :=
    (cutoff_hasMellin hx hh (by simpa using hσ)).2
  have hvert : VerticalIntegrable (mellin (cutoff x h)) σ := by
    unfold VerticalIntegrable
    simp only [hline]
    exact kernel_verticalIntegrable hx hh hσ
  have hm := (cutoff_hasMellin hx hh (s := (σ : ℂ)) (by simpa using hσ)).1
  have hi := mellinInv_mellin_eq σ (cutoff x h) hy hm hvert (cutoff_continuous x h).continuousAt
  simpa only [mellinInv, hline] using hi

theorem cutoff_eq_one {x h t : ℝ} (hh : 0 < h) (ht : t ≤ x) : cutoff x h t = 1 := by
  unfold cutoff triangle
  rw [max_eq_left (by linarith : 0 ≤ x + h - t), max_eq_left (sub_nonneg.mpr ht),
    ← ofReal_sub, show x + h - t - (x - t) = h by ring,
    div_self (ofReal_ne_zero.mpr hh.ne')]

theorem cutoff_eq_zero {x h t : ℝ} (hh : 0 ≤ h) (ht : x + h ≤ t) : cutoff x h t = 0 := by
  unfold cutoff triangle
  rw [max_eq_right (sub_nonpos.mpr ht), max_eq_right (by linarith : x - t ≤ 0)]
  simp

theorem norm_cutoff_le_one (x : ℝ) {h : ℝ} (hh : 0 < h) (t : ℝ) : ‖cutoff x h t‖ ≤ 1 := by
  by_cases ht : t ≤ x
  · simp [cutoff_eq_one hh ht]
  by_cases hu : x + h ≤ t
  · simp [cutoff_eq_zero hh.le hu]
  unfold cutoff triangle
  have hp : 0 ≤ x + h - t := by linarith [le_of_not_ge hu]
  rw [max_eq_left hp, max_eq_right (sub_nonpos.mpr (le_of_not_ge ht)), ofReal_zero,
    sub_zero, ← ofReal_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact (div_le_one hh).mpr (by linarith [le_of_not_ge ht])

theorem kernel_at_one {x h : ℝ} (hh : 0 < h) : kernel x h 1 = (x + h / 2 : ℝ) := by
  have hhC : (h : ℂ) ≠ 0 := ofReal_ne_zero.mpr hh.ne'
  rw [kernel, show (1 : ℂ) + 1 = ((2 : ℕ) : ℂ) by norm_num, cpow_natCast, cpow_natCast]
  push_cast
  field_simp [hhC]
  ring

theorem kernel_analytic {x h : ℝ} (hx : 0 < x) (hh : 0 < h) :
    AnalyticOnNhd ℂ (kernel x h) {s | 0 < s.re} := by
  intro s hs
  have hsR : 0 < s.re := hs
  have hs0 : s ≠ 0 := fun hz => by simp [hz] at hsR
  have hshift : AnalyticAt ℂ (fun z : ℂ => z + 1) s := analyticAt_id.add analyticAt_const
  have hp (a : ℝ) (ha : 0 < a) : AnalyticAt ℂ (fun z : ℂ => (a : ℂ) ^ (z + 1)) s := by
    simp_rw [cpow_def_of_ne_zero (ofReal_ne_zero.mpr ha.ne')]
    exact (analyticAt_const.mul hshift).cexp'
  exact ((hp (x + h) (add_pos hx hh)).sub (hp x hx)).div
    ((analyticAt_const.mul analyticAt_id).mul hshift)
    (mul_ne_zero (mul_ne_zero (ofReal_ne_zero.mpr hh.ne') hs0) (shift_nonzero hsR))

end

end GoldbachSmoothing

namespace GoldbachSmoothing

open Complex
open scoped BigOperators

/-- The weight changes a sharp sum only on the next `h` units. -/
theorem norm_cutoff_sub_sharp (a : ℕ → ℂ) (X : ℕ) {h M : ℝ} (hh : 0 < h) (hM : 0 ≤ M)
    (ha : ∀ n : ℕ, (n : ℝ) ≤ (X : ℝ) + h → ‖a n‖ ≤ M) :
    ‖(∑' n, a n * cutoff (X : ℝ) h n) - ∑ n ∈ Finset.range (X + 1), a n‖ ≤ h * M := by
  let B := ⌊(X : ℝ) + h⌋₊
  have hXB : X ≤ B := Nat.le_floor (le_add_of_nonneg_right hh.le)
  have hB : (B : ℝ) ≤ (X : ℝ) + h := Nat.floor_le (by positivity)
  have hfinite : (∑' n, a n * cutoff (X : ℝ) h n) =
      ∑ n ∈ Finset.range (B + 1), a n * cutoff (X : ℝ) h n := by
    apply tsum_eq_sum
    intro n hn
    have hnB : B + 1 ≤ n := by
      rw [Finset.mem_range] at hn
      omega
    have hnBR : (B : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hnB
    have htop : (X : ℝ) + h < (B : ℝ) + 1 := Nat.lt_floor_add_one _
    rw [cutoff_eq_zero hh.le (htop.le.trans hnBR), mul_zero]
  have hbelow : (∑ n ∈ Finset.range (X + 1), a n * cutoff (X : ℝ) h n) =
      ∑ n ∈ Finset.range (X + 1), a n := by
    refine Finset.sum_congr rfl fun n hn => ?_
    have hnX : n ≤ X := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
    rw [cutoff_eq_one hh (by exact_mod_cast hnX), mul_one]
  have hcount : ((Finset.Ico (X + 1) (B + 1)).card : ℝ) ≤ h := by
    rw [Nat.card_Ico, Nat.add_sub_add_right, Nat.cast_sub hXB]
    linarith
  rw [hfinite, ← Finset.sum_range_add_sum_Ico _ (Nat.add_le_add_right hXB 1),
    hbelow, add_sub_cancel_left]
  calc
    _ ≤ ∑ n ∈ Finset.Ico (X + 1) (B + 1), ‖a n * cutoff (X : ℝ) h n‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ Finset.Ico (X + 1) (B + 1), M := by
      refine Finset.sum_le_sum fun n hn => ?_
      have hnB : n ≤ B := Nat.lt_succ_iff.mp (Finset.mem_Ico.mp hn).2
      have hnBR : (n : ℝ) ≤ (B : ℝ) := by exact_mod_cast hnB
      rw [norm_mul]
      calc
        _ ≤ ‖a n‖ * 1 := mul_le_mul_of_nonneg_left (norm_cutoff_le_one X hh n) (norm_nonneg _)
        _ ≤ M := by simpa only [mul_one] using ha n (hnBR.trans hB)
    _ = ((Finset.Ico (X + 1) (B + 1)).card : ℝ) * M := by simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right hcount hM

end GoldbachSmoothing

namespace GoldbachSmoothing

open Complex MeasureTheory Set Filter
open scoped Topology

noncomputable section

private theorem term_norm_vertical (a : ℕ → ℂ) (σ t : ℝ) (n : ℕ) :
    ‖LSeries.term a ((σ : ℂ) + (t : ℂ) * I) n‖ = ‖LSeries.term a (σ : ℂ) n‖ := by
  by_cases hn : n = 0
  · subst n
    simp
  · simp only [LSeries.term_of_ne_zero hn, norm_div,
      norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn), add_re, ofReal_re, mul_I_re, ofReal_im,
      neg_zero, add_zero]

private theorem term_continuous_vertical (a : ℕ → ℂ) (σ : ℝ) (n : ℕ) :
    Continuous (fun t : ℝ => LSeries.term a ((σ : ℂ) + (t : ℂ) * I) n) := by
  by_cases hn : n = 0
  · subst n
    simpa only [LSeries.term_zero] using (continuous_const : Continuous fun _ : ℝ => (0 : ℂ))
  · have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn
    have hline : Continuous (fun t : ℝ => (σ : ℂ) + (t : ℂ) * I) :=
      continuous_const.add (continuous_ofReal.mul continuous_const)
    simp_rw [LSeries.term_of_ne_zero hn, cpow_def_of_ne_zero hnC]
    exact continuous_const.div (continuous_exp.comp (continuous_const.mul hline))
      (fun _ => exp_ne_zero _)

theorem integrable_LSeries_mul_kernel (a : ℕ → ℂ) {x h σ : ℝ} (hx : 0 < x) (hh : 0 < h)
    (hσ : 0 < σ) (hAbs : Summable fun n => ‖LSeries.term a (σ : ℂ) n‖) :
    Integrable (fun t : ℝ => LSeries a ((σ : ℂ) + (t : ℂ) * I) *
      kernel x h ((σ : ℂ) + (t : ℂ) * I)) := by
  let z (t : ℝ) : ℂ := (σ : ℂ) + (t : ℂ) * I
  have hK : Integrable (fun t : ℝ => kernel x h (z t)) := kernel_verticalIntegrable hx hh hσ
  have hc : Continuous (fun t : ℝ => LSeries a (z t)) := by
    exact continuous_tsum (term_continuous_vertical a σ) hAbs
      (fun n t => le_of_eq (term_norm_vertical a σ t n))
  refine (hK.norm.const_mul (∑' n, ‖LSeries.term a (σ : ℂ) n‖)).mono'
    (hc.aestronglyMeasurable.mul hK.aestronglyMeasurable) ?_
  filter_upwards with t
  rw [norm_mul]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  have hS : Summable (fun n => ‖LSeries.term a (z t) n‖) :=
    hAbs.congr (fun n => (term_norm_vertical a σ t n).symm)
  exact (norm_tsum_le_tsum_norm hS).trans_eq (tsum_congr (term_norm_vertical a σ t))

/-- Mellin inversion with an absolutely convergent Dirichlet series. -/
theorem cutoff_tsum_eq_vertical (a : ℕ → ℂ) (ha0 : a 0 = 0)
    {x h σ : ℝ} (hx : 0 < x) (hh : 0 < h) (hσ : 0 < σ)
    (hAbs : Summable fun n => ‖LSeries.term a (σ : ℂ) n‖) :
    (∑' n, a n * cutoff x h n) =
      (1 / (2 * Real.pi)) • (∫ t : ℝ,
        LSeries a ((σ : ℂ) + (t : ℂ) * I) * kernel x h ((σ : ℂ) + (t : ℂ) * I)) := by
  let z (t : ℝ) : ℂ := (σ : ℂ) + (t : ℂ) * I
  let F (n : ℕ) (t : ℝ) : ℂ := LSeries.term a (z t) n * kernel x h (z t)
  have hK : Integrable (fun t : ℝ => kernel x h (z t)) := kernel_verticalIntegrable hx hh hσ
  have hN (n : ℕ) (t : ℝ) : ‖F n t‖ =
      ‖LSeries.term a (σ : ℂ) n‖ * ‖kernel x h (z t)‖ := by
    dsimp only [F]
    rw [norm_mul, term_norm_vertical]
  have hF (n : ℕ) : Integrable (F n) := by
    refine (hK.norm.const_mul ‖LSeries.term a (σ : ℂ) n‖).mono' ?_ ?_
    · exact (term_continuous_vertical a σ n).aestronglyMeasurable.mul hK.aestronglyMeasurable
    · filter_upwards with t
      exact le_of_eq (hN n t)
  have hFsum : Summable fun n => ∫ t : ℝ, ‖F n t‖ := by
    simp_rw [hN, integral_const_mul]
    exact hAbs.mul_right _
  have hInv (n : ℕ) : a n * cutoff x h n =
      (1 / (2 * Real.pi)) • (∫ t : ℝ, F n t) := by
    by_cases hn : n = 0
    · subst n
      simp [F, ha0]
    have hnR : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
    rw [← mellinInv_kernel_eq hx hh hσ hnR]
    unfold mellinInv
    simp only [F, z, LSeries.term_def₀ ha0, ofReal_natCast, smul_eq_mul, mul_assoc]
    rw [integral_const_mul]
    simp only [Algebra.smul_def]
    ring
  calc
    _ = ∑' n, (1 / (2 * Real.pi)) • (∫ t : ℝ, F n t) := tsum_congr hInv
    _ = (1 / (2 * Real.pi)) • (∑' n, ∫ t : ℝ, F n t) := tsum_const_smul'' _
    _ = (1 / (2 * Real.pi)) • (∫ t : ℝ, ∑' n, F n t) :=
      congrArg ((1 / (2 * Real.pi)) • ·) (integral_tsum_of_summable_integral_norm hF hFsum)
    _ = _ := by
      congr 1
      apply integral_congr_ae
      filter_upwards with t
      simp only [F, z, LSeries, tsum_mul_right]

end

end GoldbachSmoothing

namespace GoldbachSmoothing

open Complex DirichletCharacter MeasureTheory
open scoped BigOperators

noncomputable section

def twistedCoefficient {q : ℕ} (χ : DirichletCharacter ℂ q) : ℕ → ℂ :=
  (fun n : ℕ => χ (n : ZMod q)) * (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ))

theorem twistedCoefficient_zero {q : ℕ} (χ : DirichletCharacter ℂ q) :
    twistedCoefficient χ 0 = 0 := by
  simp [twistedCoefficient]

theorem LSeries_twistedCoefficient_eq {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 1 < s.re) :
    LSeries (twistedCoefficient χ) s = -logDeriv (LFunction χ) s := by
  rw [twistedCoefficient, χ.LSeries_twist_vonMangoldt_eq hs,
    ← χ.deriv_LFunction_eq_deriv_LSeries hs, ← χ.LFunction_eq_LSeries hs]
  simp only [logDeriv, Pi.div_apply, neg_div]

theorem smoothed_twist_eq_vertical {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {x h : ℝ} (hx : 0 < x) (hh : 0 < h) :
    (∑' n, twistedCoefficient χ n * cutoff x h n) =
      (1 / (2 * Real.pi)) • (∫ t : ℝ,
        (-logDeriv (LFunction χ) (2 + (t : ℂ) * I)) * kernel x h (2 + (t : ℂ) * I)) := by
  have hAbs : Summable fun n => ‖LSeries.term (twistedCoefficient χ) (2 : ℂ) n‖ :=
    summable_norm_iff.mpr (χ.LSeriesSummable_twist_vonMangoldt (by norm_num))
  have hEq (t : ℝ) : LSeries (twistedCoefficient χ) (2 + (t : ℂ) * I) =
      -logDeriv (LFunction χ) (2 + (t : ℂ) * I) :=
    LSeries_twistedCoefficient_eq χ (by norm_num)
  simpa only [ofReal_ofNat, hEq] using
    cutoff_tsum_eq_vertical (twistedCoefficient χ) (twistedCoefficient_zero χ) hx hh
      (σ := 2) (by norm_num) hAbs

theorem integrable_twist_vertical {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {x h : ℝ} (hx : 0 < x) (hh : 0 < h) :
    Integrable (fun t : ℝ =>
      (-logDeriv (LFunction χ) (2 + (t : ℂ) * I)) * kernel x h (2 + (t : ℂ) * I)) := by
  have hAbs : Summable fun n => ‖LSeries.term (twistedCoefficient χ) (2 : ℂ) n‖ :=
    summable_norm_iff.mpr (χ.LSeriesSummable_twist_vonMangoldt (by norm_num))
  have hEq (t : ℝ) : LSeries (twistedCoefficient χ) (2 + (t : ℂ) * I) =
      -logDeriv (LFunction χ) (2 + (t : ℂ) * I) :=
    LSeries_twistedCoefficient_eq χ (by norm_num)
  simpa only [ofReal_ofNat, hEq] using
    integrable_LSeries_mul_kernel (twistedCoefficient χ) hx hh (σ := 2) (by norm_num) hAbs

theorem norm_twisted_smoothing_error {q : ℕ} (χ : DirichletCharacter ℂ q) (X : ℕ)
    (hX : 2 ≤ X) :
    ‖(∑' n, twistedCoefficient χ n * cutoff (X : ℝ) (Real.sqrt X) n) -
        ∑ n ∈ Finset.range (X + 1), twistedCoefficient χ n‖ ≤
      Real.sqrt (X : ℝ) * Real.log (2 * (X : ℝ)) := by
  have hXR : 2 ≤ (X : ℝ) := by exact_mod_cast hX
  have hsqrt : Real.sqrt (X : ℝ) ≤ (X : ℝ) := by
    calc
      _ ≤ Real.sqrt ((X : ℝ) ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
      _ = _ := Real.sqrt_sq (by positivity)
  apply norm_cutoff_sub_sharp _ _ (by positivity) (Real.log_nonneg (by linarith))
  intro n hn
  by_cases hn0 : n = 0
  · subst n
    rw [twistedCoefficient_zero, norm_zero]
    exact Real.log_nonneg (by linarith)
  have hnR : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn0
  change ‖χ (n : ZMod q) * (ArithmeticFunction.vonMangoldt n : ℂ)‖ ≤ _
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
  calc
    _ ≤ 1 * ArithmeticFunction.vonMangoldt n :=
      mul_le_mul_of_nonneg_right (χ.norm_le_one _) ArithmeticFunction.vonMangoldt_nonneg
    _ ≤ Real.log (n : ℝ) := by simpa only [one_mul] using ArithmeticFunction.vonMangoldt_le_log
    _ ≤ _ := Real.log_le_log hnR (by linarith)

end

end GoldbachSmoothing

open scoped BigOperators
open ArithmeticFunction

namespace GoldbachProgression

/-- The von Mangoldt sum twisted by `χ`, including the endpoint `X`. -/
noncomputable def twistedVonMangoldt {q : ℕ} (χ : DirichletCharacter ℂ q) (X : ℕ) : ℂ :=
  ∑ k ∈ Finset.range (X + 1), χ (k : ZMod q) * (vonMangoldt k : ℂ)

open scoped Classical in
/-- Only the principal character contributes a main term. -/
noncomputable def principalMainTerm {q : ℕ} (χ : DirichletCharacter ℂ q) (X : ℕ) : ℂ :=
  if χ = 1 then (X : ℂ) else 0

/-- A uniform bound for the twisted errors implies the progression bound with the same constant. -/
theorem progressionBound_of_twistedBound
    (hTwisted : ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q]
      (χ : DirichletCharacter ℂ q) (X : ℕ), 2 ≤ X →
        ‖twistedVonMangoldt χ X - principalMainTerm χ X‖ ≤
          C * Real.sqrt (X : ℝ) * (Real.log (2 * (q : ℝ) * (X : ℝ))) ^ 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ q a X : ℕ, 0 < q → Nat.Coprime a q → 2 ≤ X →
      |(Finset.sum ((Finset.range (X + 1)).filter (fun k => k % q = a % q))
        (fun k => ArithmeticFunction.vonMangoldt k)) - (X : ℝ) / (Nat.totient q : ℝ)| ≤
        C * Real.sqrt (X : ℝ) * (Real.log (2 * (q : ℝ) * (X : ℝ))) ^ 2 := by
  classical
  obtain ⟨C, hC, hEstimate⟩ := hTwisted
  refine ⟨C, hC, ?_⟩
  intro q a X hq ha hX
  have : NeZero q := ⟨Nat.ne_of_gt hq⟩
  have haUnit : IsUnit (a : ZMod q) := (ZMod.isUnit_iff_coprime a q).mpr ha
  have haInv : IsUnit ((a : ZMod q)⁻¹) :=
    isUnit_of_dvd_one ⟨(a : ZMod q), (ZMod.inv_mul_of_unit _ haUnit).symm⟩
  have hTotient : (0 : ℝ) < (q.totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr hq
  have hCount : Fintype.card (DirichletCharacter ℂ q) = q.totient := by
    simpa only [Nat.card_eq_fintype_card] using
      DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q
  let weight (χ : DirichletCharacter ℂ q) : ℂ := χ ((a : ZMod q)⁻¹)
  let apSum : ℝ := ∑ k ∈ (Finset.range (X + 1)).filter (fun k => k % q = a % q), vonMangoldt k
  let bound : ℝ := C * Real.sqrt (X : ℝ) * (Real.log (2 * (q : ℝ) * (X : ℝ))) ^ 2

  have hResidueSum : apSum =
      ∑ k ∈ Finset.range (X + 1), vonMangoldt.residueClass (a : ZMod q) k := by
    simp only [apSum, Finset.sum_filter, vonMangoldt.residueClass, Set.indicator_apply,
      Set.mem_ofPred_eq, ZMod.natCast_eq_natCast_iff']
  have hProjection : (apSum : ℂ) = (q.totient : ℂ)⁻¹ *
      ∑ χ : DirichletCharacter ℂ q, weight χ * twistedVonMangoldt χ X := by
    calc
      (apSum : ℂ) =
          ∑ k ∈ Finset.range (X + 1), (vonMangoldt.residueClass (a : ZMod q) k : ℂ) := by
        change Complex.ofRealHom apSum = _
        rw [hResidueSum, map_sum]
        simp only [Complex.ofRealHom_eq_coe]
      _ = ∑ k ∈ Finset.range (X + 1), (q.totient : ℂ)⁻¹ *
          ∑ χ : DirichletCharacter ℂ q, weight χ * (χ (k : ZMod q) * (vonMangoldt k : ℂ)) := by
        apply Finset.sum_congr rfl
        intro k _
        simpa only [weight, mul_assoc] using vonMangoldt.residueClass_apply haUnit k
      _ = _ := by
        rw [← Finset.mul_sum, Finset.sum_comm]
        simp only [twistedVonMangoldt, Finset.mul_sum]
  have hMain : (∑ χ : DirichletCharacter ℂ q, weight χ * principalMainTerm χ X) = (X : ℂ) := by
    rw [Finset.sum_eq_single_of_mem (1 : DirichletCharacter ℂ q) (Finset.mem_univ _)]
    · simp [weight, principalMainTerm, MulChar.one_apply haInv]
    · intro χ _ hχ
      simp [principalMainTerm, hχ]

  have hDiscrepancy : ((apSum - (X : ℝ) / (q.totient : ℝ) : ℝ) : ℂ) =
      (q.totient : ℂ)⁻¹ * ∑ χ : DirichletCharacter ℂ q,
        weight χ * (twistedVonMangoldt χ X - principalMainTerm χ X) := by
    rw [Complex.ofReal_sub, Complex.ofReal_div]
    simp only [Complex.ofReal_natCast, hProjection, mul_sub, Finset.sum_sub_distrib, hMain,
      div_eq_inv_mul]
  have hBound : ‖(q.totient : ℂ)⁻¹ * ∑ χ : DirichletCharacter ℂ q,
      weight χ * (twistedVonMangoldt χ X - principalMainTerm χ X)‖ ≤ bound := by
    rw [norm_mul, norm_inv, Complex.norm_natCast, ← div_eq_inv_mul, div_le_iff₀ hTotient]
    calc
      ‖∑ χ : DirichletCharacter ℂ q, weight χ *
          (twistedVonMangoldt χ X - principalMainTerm χ X)‖ ≤
          ∑ χ : DirichletCharacter ℂ q,
            ‖weight χ * (twistedVonMangoldt χ X - principalMainTerm χ X)‖ := norm_sum_le _ _
      _ ≤ ∑ _ : DirichletCharacter ℂ q, bound := by
        apply Finset.sum_le_sum
        intro χ _
        rw [norm_mul]
        calc
          ‖weight χ‖ * ‖twistedVonMangoldt χ X - principalMainTerm χ X‖ ≤
              1 * ‖twistedVonMangoldt χ X - principalMainTerm χ X‖ :=
            mul_le_mul_of_nonneg_right (χ.norm_le_one _) (norm_nonneg _)
          _ ≤ bound := by simpa only [one_mul, bound] using hEstimate q χ X hX
      _ = bound * (q.totient : ℝ) := by
        simp only [Finset.sum_const, Finset.card_univ, hCount, nsmul_eq_mul, mul_comm]
  change |apSum - (X : ℝ) / (q.totient : ℝ)| ≤ bound
  rw [← Real.norm_eq_abs, ← Complex.norm_real, hDiscrepancy]
  exact hBound

end GoldbachProgression

open scoped BigOperators Topology
open Asymptotics Complex Filter Finset MeasureTheory Set

noncomputable section

namespace GoldbachGrhGrowth

variable {q : ℕ} [NeZero q]

/-- The average value of a Dirichlet character over a full period. -/
def charMean (χ : DirichletCharacter ℂ q) : ℂ :=
  (q : ℂ)⁻¹ * ∑ a : ZMod q, χ a

open scoped Classical in
theorem charMean_eq (χ : DirichletCharacter ℂ q) :
    charMean χ = if χ = 1 then (q.totient : ℂ) / (q : ℂ) else 0 := by
  by_cases hχ : χ = 1
  · subst χ
    simp [charMean, MulChar.sum_one_eq_card_units,
      ZMod.card_units_eq_totient, div_eq_inv_mul]
  · simp only [charMean, MulChar.sum_eq_zero_of_ne_one hχ, mul_zero, ite_eq_right hχ]

private theorem level_mul_charMean (χ : DirichletCharacter ℂ q) :
    (q : ℂ) * charMean χ = ∑ a : ZMod q, χ a := by
  have hq : (q : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne q
  simp only [charMean, ← mul_assoc, mul_inv_cancel₀ hq, one_mul]

theorem norm_charMean_le_one (χ : DirichletCharacter ℂ q) : ‖charMean χ‖ ≤ 1 := by
  classical
  by_cases hχ : χ = 1
  · simp only [charMean_eq, ite_eq_left hχ, norm_div, Complex.norm_natCast]
    apply (div_le_one (by exact_mod_cast q.pos_of_neZero)).2
    exact_mod_cast q.totient_le
  · simp [charMean_eq, hχ]

/-- The character sum over the positive integers at most `n`. -/
def charPartialSum (χ : DirichletCharacter ℂ q) (n : ℕ) : ℂ :=
  ∑ k ∈ range n, χ ((k + 1 : ℕ) : ZMod q)

omit [NeZero q] in
theorem norm_charPartialSum_le (χ : DirichletCharacter ℂ q) (n : ℕ) :
    ‖charPartialSum χ n‖ ≤ (n : ℝ) := by
  calc
    _ ≤ ∑ k ∈ range n, ‖χ ((k + 1 : ℕ) : ZMod q)‖ := norm_sum_le _ _
    _ ≤ ∑ _k ∈ range n, (1 : ℝ) := Finset.sum_le_sum fun k _ => χ.norm_le_one _
    _ = n := by simp

private theorem sum_character_block (χ : DirichletCharacter ℂ q) (m : ℕ) :
    (∑ k ∈ range q, χ ((m + k : ℕ) : ZMod q)) = ∑ a : ZMod q, χ a := by
  let e : Fin q ≃ ZMod q :=
    { toFun := fun k => (k.val : ZMod q)
      invFun := fun a => ⟨a.val, a.val_lt⟩
      left_inv := fun k => Fin.ext (by simp [Nat.mod_eq_of_lt k.isLt])
      right_inv := ZMod.natCast_zmod_val }
  rw [← Fin.sum_univ_eq_sum_range (fun k : ℕ => χ ((m + k : ℕ) : ZMod q)) q]
  refine Fintype.sum_equiv (e.trans (Equiv.addRight (m : ZMod q))) _ _ fun k => ?_
  change χ ((m + k.val : ℕ) : ZMod q) = χ ((k.val : ZMod q) + (m : ZMod q))
  rw [Nat.cast_add, add_comm]

/-- The centered character sum at a natural-number endpoint. -/
def integerRemainder (χ : DirichletCharacter ℂ q) (n : ℕ) : ℂ :=
  charPartialSum χ n - (n : ℂ) * charMean χ

theorem integerRemainder_periodic (χ : DirichletCharacter ℂ q) :
    Function.Periodic (integerRemainder χ) q := by
  intro n
  have hBlock : (∑ k ∈ range q, χ ((n + k + 1 : ℕ) : ZMod q)) = ∑ a : ZMod q, χ a := by
    simpa only [Nat.add_assoc, Nat.add_comm 1] using sum_character_block χ (n + 1)
  simp only [integerRemainder, charPartialSum, Finset.sum_range_add]
  rw [hBlock]
  simp only [Nat.cast_add, add_mul, level_mul_charMean]
  abel

theorem norm_integerRemainder_le (χ : DirichletCharacter ℂ q) (n : ℕ) :
    ‖integerRemainder χ n‖ ≤ 2 * (q : ℝ) := by
  rw [← (integerRemainder_periodic χ).map_mod_nat n]
  let r := n % q
  have hr : (r : ℝ) ≤ (q : ℝ) := by exact_mod_cast (Nat.mod_lt n q.pos_of_neZero).le
  calc
    _ ≤ ‖charPartialSum χ r‖ + ‖(r : ℂ) * charMean χ‖ := norm_sub_le _ _
    _ ≤ (r : ℝ) + (r : ℝ) := by
      refine add_le_add (norm_charPartialSum_le χ r) ?_
      rw [norm_mul, Complex.norm_natCast]
      simpa only [mul_one] using mul_le_mul_of_nonneg_left (norm_charMean_le_one χ) r.cast_nonneg
    _ ≤ _ := by linarith

/-- The centered character sum for real endpoints, extended by zero at `x ≤ 1`. -/
def periodicRemainder (χ : DirichletCharacter ℂ q) : ℝ → ℂ :=
  (Ioi (1 : ℝ)).indicator fun x => charPartialSum χ ⌊x⌋₊ - (x : ℂ) * charMean χ

theorem norm_periodicRemainder_le (χ : DirichletCharacter ℂ q) (x : ℝ) :
    ‖periodicRemainder χ x‖ ≤ 3 * (q : ℝ) := by
  by_cases hx : x ∈ Ioi (1 : ℝ)
  · have hx0 : 0 ≤ x := zero_le_one.trans (mem_Ioi.mp hx).le
    have hd : ‖(⌊x⌋₊ : ℂ) - (x : ℂ)‖ ≤ 1 := by
      rw [← Complex.ofReal_natCast, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonpos (sub_nonpos.mpr (Nat.floor_le hx0))]
      linarith [Nat.lt_floor_add_one x]
    have hsplit : charPartialSum χ ⌊x⌋₊ - (x : ℂ) * charMean χ =
        integerRemainder χ ⌊x⌋₊ + ((⌊x⌋₊ : ℂ) - (x : ℂ)) * charMean χ := by
      unfold integerRemainder
      ring
    rw [periodicRemainder, indicator_of_mem hx, hsplit]
    calc
      _ ≤ ‖integerRemainder χ ⌊x⌋₊‖ + ‖((⌊x⌋₊ : ℂ) - (x : ℂ)) * charMean χ‖ :=
        norm_add_le _ _
      _ ≤ 2 * (q : ℝ) + 1 := by
        refine add_le_add (norm_integerRemainder_le χ _) ?_
        rw [norm_mul]
        simpa only [one_mul] using mul_le_mul hd (norm_charMean_le_one χ) (norm_nonneg _) zero_le_one
      _ ≤ _ := by
        have hq : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast (Nat.succ_le_of_lt q.pos_of_neZero)
        linarith
  · rw [periodicRemainder, indicator_of_notMem hx, norm_zero]
    positivity

omit [NeZero q] in
private theorem measurable_partialSum_floor (χ : DirichletCharacter ℂ q) :
    Measurable (fun x : ℝ => charPartialSum χ ⌊x⌋₊) :=
  (measurable_of_countable (charPartialSum χ)).comp measurable_id.nat_floor

private theorem measurable_centeredCharSum (χ : DirichletCharacter ℂ q) :
    Measurable (fun x : ℝ => charPartialSum χ ⌊x⌋₊ - (x : ℂ) * charMean χ) :=
  (measurable_partialSum_floor χ).sub (continuous_ofReal.measurable.mul_const _)

theorem measurable_periodicRemainder (χ : DirichletCharacter ℂ q) :
    Measurable (periodicRemainder χ) :=
  (measurable_centeredCharSum χ).indicator measurableSet_Ioi

/-- The Mellin transform of the centered sum, with exponent `-s-1` in the integral. -/
def remainderMellin (χ : DirichletCharacter ℂ q) (s : ℂ) : ℂ :=
  mellin (periodicRemainder χ) (-s)

theorem remainderMellin_eq_integral (χ : DirichletCharacter ℂ q) (s : ℂ) :
    remainderMellin χ s = ∫ x : ℝ in Ioi (1 : ℝ), (x : ℂ) ^ (-s - 1) *
      (charPartialSum χ ⌊x⌋₊ - (x : ℂ) * charMean χ) := by
  have hIntegrand : (fun x : ℝ => (x : ℂ) ^ (-s - 1) • periodicRemainder χ x) =
      (Ioi (1 : ℝ)).indicator (fun x => (x : ℂ) ^ (-s - 1) *
        (charPartialSum χ ⌊x⌋₊ - (x : ℂ) * charMean χ)) := by
    ext x
    by_cases hx : x ∈ Ioi (1 : ℝ)
    · simp only [periodicRemainder, indicator_of_mem hx, smul_eq_mul]
    · simp only [periodicRemainder, indicator_of_notMem hx, smul_zero]
  rw [remainderMellin, mellin, hIntegrand, integral_indicator measurableSet_Ioi,
    Measure.restrict_restrict_of_subset (Set.Ioi_subset_Ioi zero_le_one)]

private theorem norm_weightedRemainder_le (χ : DirichletCharacter ℂ q) (s : ℂ)
    {x : ℝ} (hx : x ∈ Ioi (1 : ℝ)) :
    ‖(x : ℂ) ^ (-s - 1) * (charPartialSum χ ⌊x⌋₊ - (x : ℂ) * charMean χ)‖ ≤
      (3 * (q : ℝ)) * x ^ (-s.re - 1) := by
  have hx0 : 0 < x := zero_lt_one.trans (mem_Ioi.mp hx)
  have hBound := norm_periodicRemainder_le χ x
  rw [periodicRemainder, indicator_of_mem hx] at hBound
  rw [norm_mul, norm_cpow_eq_rpow_re_of_pos hx0, sub_re, neg_re, one_re]
  exact (mul_le_mul_of_nonneg_left hBound (Real.rpow_nonneg hx0.le _)).trans_eq (mul_comm _ _)

private theorem weightedRemainder_integrableOn (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 0 < s.re) : IntegrableOn (fun x : ℝ => (x : ℂ) ^ (-s - 1) *
      (charPartialSum χ ⌊x⌋₊ - (x : ℂ) * charMean χ)) (Ioi (1 : ℝ)) := by
  have hp : -s.re - 1 < -1 := by linarith
  have hBound := (integrableOn_Ioi_rpow_of_lt hp zero_lt_one).const_mul (3 * (q : ℝ))
  refine Integrable.mono' hBound ?_ ?_
  · have hKernel : ContinuousOn (fun x : ℝ => (x : ℂ) ^ (-s - 1)) (Ioi (1 : ℝ)) := by
      intro x hx
      exact (continuousAt_ofReal_cpow_const x _ (Or.inr (zero_lt_one.trans (mem_Ioi.mp hx)).ne')).continuousWithinAt
    exact (hKernel.aestronglyMeasurable measurableSet_Ioi).mul
      (measurable_centeredCharSum χ).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact norm_weightedRemainder_le χ s hx

theorem norm_remainderMellin_le (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : 0 < s.re) :
    ‖remainderMellin χ s‖ ≤ (3 * (q : ℝ)) / s.re := by
  rw [remainderMellin_eq_integral]
  have hp : -s.re - 1 < -1 := by linarith
  have hBound := (integrableOn_Ioi_rpow_of_lt hp zero_lt_one).const_mul (3 * (q : ℝ))
  refine (norm_integral_le_of_norm_le hBound ?_).trans_eq ?_
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact norm_weightedRemainder_le χ s hx
  · rw [integral_const_mul, integral_Ioi_rpow_of_lt hp zero_lt_one]
    rw [show -s.re - 1 + 1 = -s.re by ring, Real.one_rpow]
    simp only [div_neg, neg_div, neg_neg, mul_one_div]

theorem differentiableAt_remainderMellin (χ : DirichletCharacter ℂ q) {s : ℂ}
    (hs : 0 < s.re) : DifferentiableAt ℂ (remainderMellin χ) s := by
  have hLoc : LocallyIntegrableOn (periodicRemainder χ) (Ioi (0 : ℝ)) := by
    refine (locallyIntegrableOn_iff isOpen_Ioi.isLocallyClosed).2 fun K _ hK => ?_
    exact Measure.integrableOn_of_bounded hK.measure_lt_top.ne
      (measurable_periodicRemainder χ).aestronglyMeasurable
      (Eventually.of_forall (norm_periodicRemainder_le χ))
  have hTop : periodicRemainder χ =O[atTop] fun x : ℝ => x ^ (-(0 : ℝ)) := by
    refine IsBigO.of_bound (3 * (q : ℝ)) (Eventually.of_forall fun x => ?_)
    simpa only [neg_zero, Real.rpow_zero, norm_one, mul_one] using norm_periodicRemainder_le χ x
  have hBot : periodicRemainder χ =O[𝓝[>] (0 : ℝ)] fun x : ℝ => x ^ (-(-s.re - 1)) := by
    refine IsBigO.of_bound 0 ?_
    have hNear : Iio (1 : ℝ) ∈ 𝓝[>] (0 : ℝ) := nhdsWithin_le_nhds (Iio_mem_nhds zero_lt_one)
    filter_upwards [hNear] with x hx
    have hOutside : x ∉ Ioi (1 : ℝ) := fun h => (mem_Iio.mp hx).not_gt (mem_Ioi.mp h)
    simp only [periodicRemainder, indicator_of_notMem hOutside, norm_zero, zero_mul, le_refl]
  have hNeg : (-s).re < 0 := by simpa only [neg_re, neg_lt_zero] using hs
  have hAbove : -s.re - 1 < (-s).re := by rw [neg_re]; linarith
  exact (mellin_differentiableAt_of_isBigO_rpow hLoc hTop hNeg hBot hAbove).comp s
    differentiableAt_id.neg

omit [NeZero q] in
private def seriesCoefficient (χ : DirichletCharacter ℂ q) (n : ℕ) : ℂ :=
  if n = 0 then 0 else χ (n : ZMod q)

omit [NeZero q] in
private theorem sum_seriesCoefficient_eq (χ : DirichletCharacter ℂ q) (n : ℕ) :
    (∑ k ∈ Finset.Icc 0 n, seriesCoefficient χ k) = charPartialSum χ n := by
  rw [← Nat.range_succ_eq_Icc_zero, Finset.sum_range_succ']
  simp [seriesCoefficient, charPartialSum]

private theorem integral_centeringTerm (χ : DirichletCharacter ℂ q) {s : ℂ}
    (hs : 1 < s.re) :
    IntegrableOn (fun x : ℝ => (x : ℂ) ^ (-s - 1) * ((x : ℂ) * charMean χ)) (Ioi (1 : ℝ)) ∧
      (∫ x : ℝ in Ioi (1 : ℝ), (x : ℂ) ^ (-s - 1) * ((x : ℂ) * charMean χ)) =
        charMean χ / (s - 1) := by
  have hPower : (-s).re < -1 := by rw [neg_re]; linarith
  have hIntegrand (x : ℝ) (hx : x ∈ Ioi (1 : ℝ)) :
      (x : ℂ) ^ (-s - 1) * ((x : ℂ) * charMean χ) = charMean χ * (x : ℂ) ^ (-s) := by
    have hx0 : 0 < x := zero_lt_one.trans (Set.mem_Ioi.mp hx)
    have hProd : (x : ℂ) ^ (-s - 1) * (x : ℂ) = (x : ℂ) ^ (-s) := by
      simpa only [sub_add_cancel, cpow_one] using
        (cpow_add (-s - 1) 1 (ofReal_ne_zero.mpr hx0.ne')).symm
    rw [← mul_assoc, hProd, mul_comm]
  constructor
  · have hInt : IntegrableOn (fun x : ℝ => charMean χ * (x : ℂ) ^ (-s)) (Ioi (1 : ℝ)) :=
      (integrableOn_Ioi_cpow_of_lt hPower zero_lt_one).const_mul (charMean χ)
    exact hInt.congr_fun (fun x hx => (hIntegrand x hx).symm) measurableSet_Ioi
  · rw [setIntegral_congr_fun measurableSet_Ioi hIntegrand, integral_const_mul,
      integral_Ioi_cpow_of_lt hPower zero_lt_one]
    rw [show -s + 1 = -(s - 1) by ring]
    simp only [ofReal_one, one_cpow, div_neg, neg_div, neg_neg, mul_one_div]

/-- Abel summation on the half-plane of absolute convergence. -/
theorem LFunction_eq_centeredMellin_of_one_lt_re (χ : DirichletCharacter ℂ q) {s : ℂ}
    (hs : 1 < s.re) : DirichletCharacter.LFunction χ s =
      s * (remainderMellin χ s + charMean χ / (s - 1)) := by
  let f : ℝ → ℂ := fun x => (x : ℂ) ^ (-s)
  have hs0 : s ≠ 0 := by
    intro h
    norm_num [h] at hs
  have hDiff : ∀ x ∈ Ici (1 : ℝ), DifferentiableAt ℝ f x := by
    intro x hx
    exact (hasDerivAt_ofReal_cpow_const (zero_lt_one.trans_le (Set.mem_Ici.mp hx)).ne'
      (neg_ne_zero.mpr hs0)).differentiableAt
  have hDerivLoc : LocallyIntegrableOn (deriv f) (Ici (1 : ℝ)) := by
    have hNeg : (-s).re < 0 := by rw [neg_re]; linarith
    refine ((integrableOn_Ioi_deriv_ofReal_cpow (t := (1 / 2 : ℝ)) (by norm_num) hNeg).mono_set
      (fun x hx => ?_)).locallyIntegrableOn
    exact (by norm_num : (1 / 2 : ℝ) < 1).trans_le (Set.mem_Ici.mp hx)
  have hPowerLim : Tendsto (fun n : ℕ => (n : ℝ) ^ (1 - s.re)) atTop (𝓝 0) := by
    simpa only [neg_sub, Function.comp_def] using
      (tendsto_rpow_neg_atTop (sub_pos.mpr hs)).comp tendsto_natCast_atTop_atTop
  have hBoundary : Tendsto (fun n : ℕ => f n * ∑ k ∈ Finset.Icc 0 n, seriesCoefficient χ k)
      atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hPowerLim
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    simp only [f, norm_mul, Complex.ofReal_natCast, norm_natCast_cpow_of_pos hn, neg_re,
      sum_seriesCoefficient_eq]
    calc
      _ ≤ (n : ℝ) ^ (-s.re) * (n : ℝ) :=
        mul_le_mul_of_nonneg_left (norm_charPartialSum_le χ n) (Real.rpow_nonneg n.cast_nonneg _)
      _ = _ := by
        rw [← Real.rpow_add_one (Nat.cast_ne_zero.mpr hn.ne'), neg_add_eq_sub]
  have hSumDom : (fun x : ℝ => ∑ k ∈ Finset.Icc 0 ⌊x⌋₊, seriesCoefficient χ k) =O[atTop]
      fun x : ℝ => x := by
    refine IsBigO.of_bound 1 ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    rw [sum_seriesCoefficient_eq, one_mul, Real.norm_of_nonneg hx.le]
    exact (norm_charPartialSum_le χ _).trans (Nat.floor_le hx.le)
  have hDerivativeDom : (fun x : ℝ => deriv f x * ∑ k ∈ Finset.Icc 0 ⌊x⌋₊, seriesCoefficient χ k)
      =O[atTop] fun x : ℝ => x ^ (-s.re) := by
    refine ((isBigO_deriv_ofReal_cpow_const_atTop (-s)).mul hSumDom).congr' EventuallyEq.rfl ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    rw [neg_re, ← Real.rpow_add_one hx.ne', sub_add_cancel]
  have hDominatingIntegral : IntegrableAtFilter (fun x : ℝ => x ^ (-s.re)) atTop :=
    ⟨Ioi (1 : ℝ), Ioi_mem_atTop _, integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one⟩
  have hAbel := tendsto_sum_mul_atTop_nhds_one_sub_integral₀ (seriesCoefficient χ)
    (by simp [seriesCoefficient]) hDiff hDerivLoc hBoundary hDerivativeDom hDominatingIntegral
  have hCoeff (n : ℕ) : f n * seriesCoefficient χ n =
      LSeries.term (fun k : ℕ => χ (k : ZMod q)) s n := by
    by_cases hn : n = 0
    · subst n
      simp [seriesCoefficient]
    · simp [f, seriesCoefficient, hn, cpow_neg, div_eq_inv_mul]
  have hSum : Tendsto (fun n : ℕ => ∑ k ∈ Finset.Icc 0 n,
      f k * seriesCoefficient χ k) atTop (𝓝 (LSeries (fun k : ℕ => χ (k : ZMod q)) s)) := by
    simp_rw [hCoeff, ← Nat.range_succ_eq_Icc_zero]
    exact (χ.LSeriesSummable_of_one_lt_re hs).hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
  have hSeriesIdentity : DirichletCharacter.LFunction χ s = (0 : ℂ) -
      ∫ x : ℝ in Ioi (1 : ℝ), deriv f x * ∑ k ∈ Finset.Icc 0 ⌊x⌋₊, seriesCoefficient χ k := by
    rw [DirichletCharacter.LFunction_eq_LSeries χ hs]
    exact tendsto_nhds_unique hSum hAbel
  calc
    _ = (0 : ℂ) - ∫ x : ℝ in Ioi (1 : ℝ), (-s) *
        ((x : ℂ) ^ (-s - 1) * charPartialSum χ ⌊x⌋₊) := by
      rw [hSeriesIdentity]
      congr 1
      refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
      have hx0 : x ≠ 0 := (zero_lt_one.trans (Set.mem_Ioi.mp hx)).ne'
      simp only [f, deriv_ofReal_cpow_const (-s) hx0, sum_seriesCoefficient_eq, mul_assoc]
    _ = s * (∫ x : ℝ in Ioi (1 : ℝ), (x : ℂ) ^ (-s - 1) * charPartialSum χ ⌊x⌋₊) := by
      rw [integral_const_mul, zero_sub, neg_mul, neg_neg]
    _ = _ := by
      have hSplit (x : ℝ) : (x : ℂ) ^ (-s - 1) * charPartialSum χ ⌊x⌋₊ =
          (x : ℂ) ^ (-s - 1) * (charPartialSum χ ⌊x⌋₊ - (x : ℂ) * charMean χ) +
            (x : ℂ) ^ (-s - 1) * ((x : ℂ) * charMean χ) := by ring
      simp_rw [hSplit]
      rw [integral_add (weightedRemainder_integrableOn χ (zero_lt_one.trans hs))
        (integral_centeringTerm χ hs).1, ← remainderMellin_eq_integral, (integral_centeringTerm χ hs).2]

private theorem eq_on_right_halfPlane {f g : ℂ → ℂ}
    (hf : ∀ z : ℂ, 0 < z.re → DifferentiableAt ℂ f z)
    (hg : ∀ z : ℂ, 0 < z.re → DifferentiableAt ℂ g z)
    (hfg : ∀ z : ℂ, 1 < z.re → f z = g z) {s : ℂ} (hs : 0 < s.re) : f s = g s := by
  let U : Set ℂ := {z | 0 < z.re}
  have hUOpen : IsOpen U := isOpen_lt continuous_const continuous_re
  have hUConnected : IsPreconnected U :=
    ((convex_Ioi (0 : ℝ)).linear_preimage reCLM.toLinearMap).isPreconnected
  have hFA : AnalyticOnNhd ℂ f U :=
    DifferentiableOn.analyticOnNhd (fun z hz => (hf z hz).differentiableWithinAt) hUOpen
  have hGA : AnalyticOnNhd ℂ g U :=
    DifferentiableOn.analyticOnNhd (fun z hz => (hg z hz).differentiableWithinAt) hUOpen
  have h2 : (2 : ℂ) ∈ U := by norm_num [U]
  have hAbsConv : {z : ℂ | 1 < z.re} ∈ 𝓝 (2 : ℂ) :=
    (isOpen_lt continuous_const continuous_re).mem_nhds (by norm_num)
  have hEq : f =ᶠ[𝓝 (2 : ℂ)] g := by
    filter_upwards [hAbsConv] with z hz
    exact hfg z hz
  exact hFA.eqOn_of_preconnected_of_eventuallyEq hGA hUConnected h2 hEq hs

/-- The centered Mellin representation of a nonprincipal L-function on the right half-plane. -/
theorem LFunction_eq_remainderMellin (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    {s : ℂ} (hs : 0 < s.re) : DirichletCharacter.LFunction χ s = s * remainderMellin χ s := by
  refine eq_on_right_halfPlane (f := DirichletCharacter.LFunction χ)
    (g := fun z : ℂ => z * remainderMellin χ z)
    (fun z _ => DirichletCharacter.differentiable_LFunction hχ z) ?_ ?_ hs
  · intro z hz
    exact differentiableAt_id.mul (differentiableAt_remainderMellin χ hz)
  · intro z hz
    rw [LFunction_eq_centeredMellin_of_one_lt_re χ hz]
    simp only [charMean_eq, ite_eq_right hχ, zero_div, add_zero]

/-- The Mellin representation of the principal L-function after removing its pole. -/
theorem LFunctionTrivChar₁_eq_remainderMellin {s : ℂ} (hs : 0 < s.re) :
    DirichletCharacter.LFunctionTrivChar₁ q s =
      (s - 1) * s * remainderMellin (1 : DirichletCharacter ℂ q) s +
        s * charMean (1 : DirichletCharacter ℂ q) := by
  let χ : DirichletCharacter ℂ q := 1
  refine eq_on_right_halfPlane (f := DirichletCharacter.LFunctionTrivChar₁ q)
    (g := fun z : ℂ => (z - 1) * z * remainderMellin χ z + z * charMean χ)
    (fun z _ => DirichletCharacter.differentiable_LFunctionTrivChar₁ q z) ?_ ?_ hs
  · intro z hz
    have hId : DifferentiableAt ℂ (fun w : ℂ => w) z := differentiableAt_id
    have hSub : DifferentiableAt ℂ (fun w : ℂ => w - 1) z := hId.sub_const 1
    exact (((hSub.mul hId).mul (differentiableAt_remainderMellin χ hz)).add (hId.mul_const _))
  · intro z hz
    have hz1 : z ≠ 1 := by
      intro h
      norm_num [h] at hz
    rw [DirichletCharacter.LFunctionTrivChar₁, Function.update_of_ne hz1]
    change (z - 1) * DirichletCharacter.LFunction χ z = _
    rw [LFunction_eq_centeredMellin_of_one_lt_re χ hz]
    field_simp [sub_ne_zero.mpr hz1]

open scoped Classical in
/-- A uniform growth bound for the Dirichlet L-function, with the principal pole removed. -/
theorem norm_regularizedLFunction_le (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : 1 / 8 ≤ s.re) :
    ‖(if χ = 1 then DirichletCharacter.LFunctionTrivChar₁ q s
      else DirichletCharacter.LFunction χ s)‖ ≤ 25 * (q : ℝ) * (1 + ‖s‖) ^ 2 := by
  have hs0 : 0 < s.re := (by norm_num : (0 : ℝ) < 1 / 8).trans_le hs
  have hRemainder : ‖remainderMellin χ s‖ ≤ 24 * (q : ℝ) := by
    calc
      _ ≤ (3 * (q : ℝ)) / s.re := norm_remainderMellin_le χ hs0
      _ ≤ (3 * (q : ℝ)) / (1 / 8 : ℝ) := div_le_div_of_nonneg_left (by positivity) (by norm_num) hs
      _ = _ := by ring
  let M := 1 + ‖s‖
  have hM : 1 ≤ M := by
    dsimp [M]
    linarith [norm_nonneg s]
  have hM0 : 0 ≤ M := zero_le_one.trans hM
  have hSM : ‖s‖ ≤ M := by
    dsimp [M]
    linarith
  have hSubM : ‖s - 1‖ ≤ M := by
    simpa only [M, norm_one, add_comm] using norm_sub_le s (1 : ℂ)
  have hMSq : M ≤ M ^ 2 := by
    rw [pow_two]
    exact le_mul_of_one_le_right hM0 hM
  have hq : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast (Nat.succ_le_of_lt q.pos_of_neZero)
  have hMq : M ≤ (q : ℝ) * M ^ 2 :=
    hMSq.trans (le_mul_of_one_le_left (sq_nonneg _) hq)
  change ‖(if χ = 1 then _ else _)‖ ≤ 25 * (q : ℝ) * M ^ 2
  by_cases hχ : χ = 1
  · subst χ
    rw [ite_eq_left rfl, LFunctionTrivChar₁_eq_remainderMellin hs0]
    calc
      _ ≤ ‖(s - 1) * s * remainderMellin (1 : DirichletCharacter ℂ q) s‖ +
          ‖s * charMean (1 : DirichletCharacter ℂ q)‖ := norm_add_le _ _
      _ ≤ M ^ 2 * (24 * (q : ℝ)) + M := by
        apply add_le_add
        · simp only [norm_mul, pow_two]
          exact mul_le_mul (mul_le_mul hSubM hSM (norm_nonneg _) hM0) hRemainder
            (norm_nonneg _) (mul_nonneg hM0 hM0)
        · rw [norm_mul]
          simpa only [mul_one] using mul_le_mul hSM (norm_charMean_le_one (1 : DirichletCharacter ℂ q))
            (norm_nonneg _) hM0
      _ ≤ M ^ 2 * (24 * (q : ℝ)) + (q : ℝ) * M ^ 2 := add_le_add le_rfl hMq
      _ = _ := by ring
  · rw [ite_eq_right hχ, LFunction_eq_remainderMellin χ hχ hs0, norm_mul]
    calc
      _ ≤ M ^ 2 * (24 * (q : ℝ)) :=
        mul_le_mul (hSM.trans hMSq) hRemainder (norm_nonneg _) (sq_nonneg _)
      _ = 24 * (q : ℝ) * M ^ 2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by norm_num) q.cast_nonneg) (sq_nonneg _)

end GoldbachGrhGrowth

namespace Goldbach

private theorem summable_inv_sq_shift (k : ℕ) :
    Summable (fun n : ℕ ↦ (((n + k : ℕ) : ℝ) ^ 2)⁻¹) :=
  (summable_nat_add_iff (f := fun n : ℕ ↦ ((n : ℝ) ^ 2)⁻¹) k).mpr
    (Real.summable_nat_pow_inv.mpr (by decide))

private theorem inv_sq_tail_le_three_fourths :
    (∑' n : ℕ, (((n + 2 : ℕ) : ℝ) ^ 2)⁻¹) ≤ (3 / 4 : ℝ) := by
  let u : ℕ → ℝ := fun n ↦ ((n + 2 : ℕ) : ℝ)⁻¹
  have hTail : (∑' n : ℕ, (((n + 3 : ℕ) : ℝ) ^ 2)⁻¹) ≤ (1 / 2 : ℝ) := by
    apply le_of_tendsto' (summable_inv_sq_shift 3).hasSum.tendsto_sum_nat
    intro n
    calc
      _ ≤ ∑ m ∈ Finset.range n, (u m - u (m + 1)) := by
        apply Finset.sum_le_sum
        intro m _
        have hm₂ : 0 < (m : ℝ) + 2 := by positivity
        have hm₃ : 0 < (m : ℝ) + 3 := by positivity
        calc
          _ ≤ (((m : ℝ) + 2) * ((m : ℝ) + 3))⁻¹ := by
            rw [Nat.cast_add, Nat.cast_ofNat]
            apply inv_anti₀ (mul_pos hm₂ hm₃)
            rw [pow_two]
            exact mul_le_mul_of_nonneg_right (by linarith) hm₃.le
          _ = _ := by
            simp only [u, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
            rw [show (m : ℝ) + 1 + 2 = (m : ℝ) + 3 by ring]
            field_simp [hm₂.ne', hm₃.ne']
            ring
      _ = u 0 - u n := Finset.sum_range_sub' u n
      _ ≤ _ := (sub_le_self _ (by dsimp [u]; positivity)).trans_eq (by norm_num [u])
  have hSplit := (summable_inv_sq_shift 2).sum_add_tsum_nat_add 1
  simp only [Finset.sum_range_one, Nat.zero_add, Nat.add_assoc,
    show (1 + 2 : ℕ) = 3 by decide, Nat.cast_ofNat] at hSplit
  rw [← hSplit, show ((2 : ℝ) ^ 2)⁻¹ = 1 / 4 by norm_num]
  linarith only [hTail]

/-- A uniform positive lower bound for the Dirichlet L-function on `Re s = 2`. -/
theorem one_fourth_le_norm_LFunction_anchor {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (t : ℝ) :
    (1 / 4 : ℝ) ≤ ‖χ.LFunction (⟨2, t⟩ : ℂ)‖ := by
  let s : ℂ := ⟨2, t⟩
  let term : ℕ → ℂ := LSeries.term (fun n : ℕ ↦ χ (n : ZMod q)) s
  have hs : 1 < s.re := by norm_num [s]
  have hTerm : Summable term := χ.LSeriesSummable_of_one_lt_re hs
  have hLFunction : χ.LFunction s = ∑' n : ℕ, term n := χ.LFunction_eq_LSeries hs
  have hTerm01 : (∑ n ∈ Finset.range 2, term n) = 1 := by
    rw [show (2 : ℕ) = 1 + 1 by decide, Finset.sum_range_succ, Finset.sum_range_one]
    simp [term]
  have hSplit := hTerm.sum_add_tsum_nat_add 2
  rw [hTerm01] at hSplit
  have hTermTail : Summable (fun n : ℕ ↦ term (n + 2)) :=
    (summable_nat_add_iff (f := term) 2).mpr hTerm
  have hTermNorm (n : ℕ) : ‖term (n + 2)‖ ≤ (((n + 2 : ℕ) : ℝ) ^ 2)⁻¹ := by
    dsimp [term]
    rw [LSeries.norm_term_eq, ite_eq_right (by omega : n + 2 ≠ 0), show s.re = 2 from rfl,
      show (((n + 2 : ℕ) : ℝ) ^ (2 : ℝ)) = (((n + 2 : ℕ) : ℝ) ^ (2 : ℕ)) by
        exact Real.rpow_natCast _ 2, ← one_div]
    exact div_le_div_of_nonneg_right (χ.norm_le_one _) (by positivity)
  have hNormTail : ‖∑' n : ℕ, term (n + 2)‖ ≤ (3 / 4 : ℝ) :=
    (norm_tsum_le_tsum_norm hTermTail.norm).trans
      ((hTermTail.norm.tsum_le_tsum hTermNorm (summable_inv_sq_shift 2)).trans
        inv_sq_tail_le_three_fourths)
  have hSumNorm : (1 : ℝ) ≤ ‖χ.LFunction s‖ + ‖∑' n : ℕ, term (n + 2)‖ := calc
    _ = ‖(1 : ℂ)‖ := norm_one.symm
    _ = ‖χ.LFunction s - ∑' n : ℕ, term (n + 2)‖ := by
      rw [hLFunction, ← hSplit, add_sub_cancel_right]
    _ ≤ _ := norm_sub_le _ _
  change (1 / 4 : ℝ) ≤ ‖χ.LFunction s‖
  linarith only [hNormTail, hSumNorm]

/-- The same anchor bound after multiplication by the factor that cancels a pole at one. -/
theorem one_fourth_le_norm_mul_sub_one_LFunction_anchor {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (t : ℝ) :
    (1 / 4 : ℝ) ≤ ‖((⟨2, t⟩ : ℂ) - 1) * χ.LFunction (⟨2, t⟩ : ℂ)‖ := by
  have hFactor : (1 : ℝ) ≤ ‖(⟨2, t⟩ : ℂ) - 1‖ := by
    have h := Complex.re_le_norm ((⟨2, t⟩ : ℂ) - 1)
    change (2 : ℝ) - 1 ≤ _ at h
    linarith only [h]
  rw [norm_mul]
  exact (one_fourth_le_norm_LFunction_anchor χ t).trans
    (le_mul_of_one_le_left (norm_nonneg _) hFactor)

end Goldbach

namespace Goldbach

open Metric Set MeromorphicOn

/-- The zeros in the open critical strip at height at most one from `t`. -/
def criticalZeroSlice (f : ℂ → ℂ) (t : ℝ) : Set ℂ :=
  {z | 0 < z.re ∧ z.re < 1 ∧ |z.im - t| ≤ 1 ∧ f z = 0}

private theorem jensen_mem_inner {z : ℂ} {t : ℝ} (hre : z.re = 1 / 2)
    (him : |z.im - t| ≤ 1) : z ∈ closedBall (⟨2, t⟩ : ℂ) (29 / 16) := by
  rw [mem_closedBall, dist_eq_norm]
  apply (sq_le_sq₀ (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 29 / 16)).mp
  have himSq : (z.im - t) ^ 2 ≤ 1 := by
    simpa only [sq_abs, one_pow] using
      (sq_le_sq₀ (abs_nonneg _) zero_le_one).mpr him
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, hre]
  nlinarith only [himSq]

private theorem jensen_re_of_mem_outer {z : ℂ} {t : ℝ}
    (hz : z ∈ closedBall (⟨2, t⟩ : ℂ) (15 / 8)) : 1 / 8 ≤ z.re := by
  rw [mem_closedBall, dist_eq_norm] at hz
  have hre := (Complex.abs_re_le_norm (z - (⟨2, t⟩ : ℂ))).trans hz
  simp only [Complex.sub_re] at hre
  linarith only [(abs_le.mp hre).1]

private theorem jensen_norm_of_mem_outer {z : ℂ} {t : ℝ}
    (hz : z ∈ closedBall (⟨2, t⟩ : ℂ) (15 / 8)) : 1 + ‖z‖ ≤ 3 * (2 + |t|) := by
  rw [mem_closedBall, dist_eq_norm] at hz
  let center : ℂ := ⟨2, t⟩
  have hcenter : ‖center‖ ≤ 2 + |t| := by
    simpa [center] using Complex.norm_le_abs_re_add_abs_im center
  have hnorm : ‖z‖ ≤ ‖z - center‖ + ‖center‖ := by
    simpa only [sub_add_cancel] using norm_add_le (z - center) center
  linarith only [hz, hcenter, hnorm, abs_nonneg t]

private theorem jensen_analytic_outer {f : ℂ → ℂ} {t : ℝ}
    (hAnalytic : AnalyticOnNhd ℂ f {z | 0 < z.re}) :
    AnalyticOnNhd ℂ f (closedBall (⟨2, t⟩ : ℂ) (15 / 8)) := by
  intro z hz
  exact hAnalytic z (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 8)
    (jensen_re_of_mem_outer hz))

/-- For a holomorphic function with fixed growth and anchor bounds, the total divisor mass
in the closed disk of radius `29 / 16` about `2 + it` grows at most logarithmically. -/
theorem jensen_diskDivisor_bound {A b : ℝ} (hA : 0 < A) (hb : 0 < b) :
    ∃ K : ℝ, 0 < K ∧ ∀ (q : ℕ) (f : ℂ → ℂ) (t : ℝ), 0 < q →
      AnalyticOnNhd ℂ f {z | 0 < z.re} →
      (∀ z : ℂ, 1 / 8 ≤ z.re → ‖f z‖ ≤ A * (q : ℝ) * (1 + ‖z‖) ^ 2) →
      b ≤ ‖f (⟨2, t⟩ : ℂ)‖ →
      ((∑ᶠ z : ℂ, divisor f (closedBall (⟨2, t⟩ : ℂ) (29 / 16)) z : ℤ) : ℝ) ≤
        K * Real.log (2 * (q : ℝ) * (2 + |t|)) := by
  classical
  let r : ℝ := 29 / 16
  let R : ℝ := 15 / 8
  have hr : 0 < r := by norm_num [r]
  have hR : 0 < R := by norm_num [R]
  have hrR : r < R := by norm_num [r, R]
  let B : ℝ := 1 + 9 * A
  let bMin : ℝ := min 1 b
  let D : ℝ := B / bMin
  let logRatio : ℝ := Real.log (R / r)
  let logFactor : ℝ := 2 + Real.log D / Real.log 2
  have hB : 1 ≤ B := by dsimp [B]; linarith only [hA]
  have hbMin : 0 < bMin := lt_min zero_lt_one hb
  have hD : 1 ≤ D := by
    apply (le_div_iff₀ hbMin).mpr
    simpa only [one_mul] using (min_le_left (1 : ℝ) b).trans hB
  have hlogD : 0 ≤ Real.log D := Real.log_nonneg hD
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogRatio : 0 < logRatio := Real.log_pos ((one_lt_div hr).mpr hrR)
  have hlogCoeff : 0 ≤ Real.log D / Real.log 2 := div_nonneg hlogD hlog2.le
  have hlogFactor : 0 < logFactor := by dsimp [logFactor]; linarith only [hlogCoeff]
  refine ⟨logFactor / logRatio, div_pos hlogFactor hlogRatio, ?_⟩
  intro q f t hq hAnalytic hGrowth hAnchor
  let c : ℂ := ⟨2, t⟩
  let v : ℝ := 2 + |t|
  let w : ℝ := 2 * (q : ℝ) * v
  let M : ℝ := B * w ^ 2
  have hq₁ : (1 : ℝ) ≤ q := by exact_mod_cast Nat.succ_le_of_lt hq
  have hq₀ : (0 : ℝ) ≤ q := by positivity
  have hv : 2 ≤ v := by dsimp [v]; linarith only [abs_nonneg t]
  have hw : 2 ≤ w := by
    have hq₂ : (1 : ℝ) ≤ 2 * (q : ℝ) := by linarith only [hq₁]
    exact hv.trans (le_mul_of_one_le_left (by linarith only [hv]) hq₂)
  have hw₀ : 0 < w := by linarith only [hw]
  have hM : 1 ≤ M := by
    have hWs : 1 ≤ w ^ 2 := by nlinarith only [hw, sq_nonneg (w - 2)]
    exact one_le_mul_of_one_le_of_one_le hB hWs
  have hAnchorMin : bMin ≤ ‖f c‖ := (min_le_right 1 b).trans hAnchor
  have hFpos : 0 < ‖f c‖ := hbMin.trans_le hAnchorMin
  have hFc : f c ≠ 0 := norm_pos_iff.mp hFpos
  have hOuter : AnalyticOnNhd ℂ f (closedBall c R) := by
    exact jensen_analytic_outer hAnalytic
  have hBound : ∀ z ∈ closedBall c R, ‖f z‖ ≤ M := by
    intro z hz
    have hnorm : 1 + ‖z‖ ≤ 3 * v := jensen_norm_of_mem_outer hz
    have hnormSq : (1 + ‖z‖) ^ 2 ≤ (3 * v) ^ 2 :=
      (sq_le_sq₀ (by positivity) (by linarith only [hv])).mpr hnorm
    have hqSq : (q : ℝ) ≤ (2 * (q : ℝ)) ^ 2 := by
      have hqSelf : (q : ℝ) ≤ (q : ℝ) * (q : ℝ) := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hq₁ hq₀
      nlinarith only [hqSelf, sq_nonneg (q : ℝ)]
    have hqvSq : (q : ℝ) * v ^ 2 ≤ w ^ 2 := calc
      _ ≤ (2 * (q : ℝ)) ^ 2 * v ^ 2 := mul_le_mul_of_nonneg_right hqSq (sq_nonneg v)
      _ = _ := by dsimp [w]; ring
    calc
      ‖f z‖ ≤ A * (q : ℝ) * (1 + ‖z‖) ^ 2 := hGrowth z (jensen_re_of_mem_outer hz)
      _ ≤ A * (q : ℝ) * (3 * v) ^ 2 := mul_le_mul_of_nonneg_left hnormSq (mul_nonneg hA.le hq₀)
      _ = 9 * A * ((q : ℝ) * v ^ 2) := by ring
      _ ≤ 9 * A * w ^ 2 := mul_le_mul_of_nonneg_left hqvSq (by positivity)
      _ ≤ M := mul_le_mul_of_nonneg_right (by dsimp [B]; linarith) (sq_nonneg w)
  have hJensen : ((∑ᶠ z : ℂ, divisor f (closedBall c |r|) z : ℤ) : ℝ) ≤
      Real.log (M / ‖f c‖) / logRatio := by
    have hOuterAbs : AnalyticOnNhd ℂ f (closedBall c |R|) := by simpa [abs_of_pos hR] using hOuter
    have hCircle : ∀ z ∈ sphere c |R|, ‖f z‖ ≤ M := by
      intro z hz
      apply hBound z
      simpa only [abs_of_pos hR] using sphere_subset_closedBall hz
    exact AnalyticOnNhd.sum_divisor_le (r := r) (R := R) (M := M)
      (by simpa only [abs_of_pos hr] using hr)
      (by simpa only [abs_of_pos hr, abs_of_pos hR] using hrR)
      hM hOuterAbs hFc hCircle
  have hLogW : Real.log 2 ≤ Real.log w := Real.log_le_log (by norm_num) hw
  have hLogBound : Real.log (M / ‖f c‖) ≤ logFactor * Real.log w := by
    have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one hM
    have hDivBound : M / ‖f c‖ ≤ D * w ^ 2 := calc
      _ ≤ M / bMin := div_le_div_of_nonneg_left hMpos.le hbMin hAnchorMin
      _ = _ := by dsimp [M, D]; ring
    calc
      _ ≤ Real.log (D * w ^ 2) := Real.log_le_log (div_pos hMpos hFpos) hDivBound
      _ = 2 * Real.log w + Real.log D := by
        rw [Real.log_mul (by linarith only [hD]) (pow_ne_zero _ hw₀.ne'), Real.log_pow]
        norm_num [add_comm]
      _ = 2 * Real.log w + (Real.log D / Real.log 2) * Real.log 2 := by
        rw [div_mul_cancel₀ _ hlog2.ne']
      _ ≤ 2 * Real.log w + (Real.log D / Real.log 2) * Real.log w :=
        (add_le_add le_rfl (mul_le_mul_of_nonneg_left hLogW hlogCoeff))
      _ = _ := by dsimp [logFactor]; ring
  change ((∑ᶠ z : ℂ, divisor f (closedBall c r) z : ℤ) : ℝ) ≤
    (logFactor / logRatio) * Real.log w
  calc
    _ = ((∑ᶠ z : ℂ, divisor f (closedBall c |r|) z : ℤ) : ℝ) :=
      congrArg (fun U : Set ℂ ↦ ((∑ᶠ z : ℂ, divisor f U z : ℤ) : ℝ))
        (congrArg (closedBall c) (abs_of_pos hr).symm)
    _ ≤ Real.log (M / ‖f c‖) / logRatio := hJensen
    _ ≤ (logFactor * Real.log w) / logRatio :=
      div_le_div_of_nonneg_right hLogBound hlogRatio.le
    _ = _ := by ring

/-- A fixed polynomial growth bound and a positive anchor bound give a uniform logarithmic
bound on the number of critical-strip zeros, counted with multiplicity, in each height slice.
The zero-line hypothesis places the entire slice in the smaller Jensen disk. -/
theorem jensen_criticalZeroSlice_bound {A b : ℝ} (hA : 0 < A) (hb : 0 < b) :
    ∃ K : ℝ, 0 < K ∧ ∀ (q : ℕ) (f : ℂ → ℂ) (t : ℝ), 0 < q →
      AnalyticOnNhd ℂ f {z | 0 < z.re} →
      (∀ z : ℂ, 1 / 8 ≤ z.re → ‖f z‖ ≤ A * (q : ℝ) * (1 + ‖z‖) ^ 2) →
      b ≤ ‖f (⟨2, t⟩ : ℂ)‖ →
      (∀ z : ℂ, 0 < z.re → z.re < 1 → f z = 0 → z.re = 1 / 2) →
      (criticalZeroSlice f t).Finite ∧
        (∑ᶠ z : ℂ, (criticalZeroSlice f t).indicator
          (fun z ↦ (analyticOrderNatAt f z : ℝ)) z) ≤
          K * Real.log (2 * (q : ℝ) * (2 + |t|)) := by
  classical
  obtain ⟨K, hK, hDiskBound⟩ := jensen_diskDivisor_bound hA hb
  refine ⟨K, hK, ?_⟩
  intro q f t hq hAnalytic hGrowth hAnchor hLine
  let c : ℂ := ⟨2, t⟩
  let r : ℝ := 29 / 16
  let R : ℝ := 15 / 8
  have hFc : f c ≠ 0 := norm_pos_iff.mp (hb.trans_le hAnchor)
  have hCenter : c ∈ closedBall c R := mem_closedBall_self (by norm_num [R])
  have hOuter : AnalyticOnNhd ℂ f (closedBall c R) := jensen_analytic_outer hAnalytic
  have hInnerSubset : closedBall c r ⊆ closedBall c R :=
    closedBall_subset_closedBall (by norm_num [r, R])
  have hInner : AnalyticOnNhd ℂ f (closedBall c r) := hOuter.mono hInnerSubset
  have hOrderCenter : analyticOrderAt f c ≠ ⊤ := by
    rw [(hOuter c hCenter).analyticOrderAt_eq_zero.mpr hFc]
    exact ENat.zero_ne_top
  let countDivisor : ℂ → ℤ := fun z ↦ divisor f (closedBall c r) z
  let countSlice : ℂ → ℝ := (criticalZeroSlice f t).indicator
    (fun z ↦ (analyticOrderNatAt f z : ℝ))
  have hSliceOrder (z : ℂ) (hz : z ∈ criticalZeroSlice f t) :
      countDivisor z = (analyticOrderNatAt f z : ℤ) ∧ 0 < analyticOrderNatAt f z := by
    have hre := hLine z hz.1 hz.2.1 hz.2.2.2
    have hzInner : z ∈ closedBall c r := jensen_mem_inner hre hz.2.2.1
    have hzOuter : z ∈ closedBall c R := hInnerSubset hzInner
    have hOrder : analyticOrderAt f z ≠ ⊤ := hOuter.analyticOrderAt_ne_top_of_isPreconnected
      isPreconnected_closedBall hCenter hzOuter hOrderCenter
    constructor
    · change divisor f (closedBall c r) z = _
      rw [hInner.divisor_apply hzInner, ← Nat.cast_analyticOrderNatAt hOrder,
        ENat.map_natCast, WithTop.untop₀_coe]
    · apply Nat.pos_of_ne_zero
      intro hZero
      apply (hInner z hzInner).analyticOrderAt_ne_zero.mpr hz.2.2.2
      rw [← Nat.cast_analyticOrderNatAt hOrder, hZero, Nat.cast_zero]
  have hDivFinite : (Function.support countDivisor).Finite :=
    (divisor f (closedBall c r)).finiteSupport (isCompact_closedBall c r)
  have hSliceFinite : (criticalZeroSlice f t).Finite := by
    apply hDivFinite.subset
    intro z hz
    change countDivisor z ≠ 0
    rw [(hSliceOrder z hz).1]
    exact_mod_cast (hSliceOrder z hz).2.ne'
  refine ⟨hSliceFinite, ?_⟩
  have hSliceCountFinite : (Function.support countSlice).Finite := by
    apply hSliceFinite.subset
    intro z hz
    by_contra hNot
    exact hz (Set.indicator_of_notMem hNot _)
  let divisorOverReal : ℂ → ℝ := fun z ↦ (countDivisor z : ℝ)
  have hDivCountFinite : (Function.support divisorOverReal).Finite := by
    apply hDivFinite.subset
    intro z hz
    simpa [Function.mem_support, divisorOverReal] using hz
  change (∑ᶠ z : ℂ, countSlice z) ≤ K * Real.log (2 * (q : ℝ) * (2 + |t|))
  calc
    _ ≤ ∑ᶠ z : ℂ, divisorOverReal z := by
      apply finsum_le_finsum hSliceCountFinite hDivCountFinite
      intro z
      by_cases hz : z ∈ criticalZeroSlice f t
      · simp [countSlice, divisorOverReal, Set.indicator_of_mem hz, (hSliceOrder z hz).1]
      · rw [show countSlice z = 0 from Set.indicator_of_notMem hz _]
        have hNonnegative : (0 : ℤ) ≤ countDivisor z := hInner.divisor_nonneg z
        change (0 : ℝ) ≤ (countDivisor z : ℝ)
        exact_mod_cast hNonnegative
    _ = ((∑ᶠ z : ℂ, countDivisor z : ℤ) : ℝ) :=
      (map_finsum (Int.castRingHom ℝ) hDivFinite).symm
    _ ≤ _ := hDiskBound q f t hq hAnalytic hGrowth hAnchor

end Goldbach

namespace Goldbach

open Complex DirichletCharacter Set

abbrev GRH := ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ),
  0 < s.re → s.re < 1 → LFunction χ s = 0 → s.re = 1 / 2

noncomputable def regularizedL {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) : ℂ → ℂ := by
  classical
  exact if χ = 1 then LFunctionTrivChar₁ q else LFunction χ

noncomputable def principalFlag {q : ℕ} (χ : DirichletCharacter ℂ q) : ℂ := by
  classical
  exact if χ = 1 then 1 else 0

theorem analytic_regularizedL {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    AnalyticOnNhd ℂ (regularizedL χ) univ := by
  intro s _
  by_cases hχ : χ = 1
  · simpa only [regularizedL, hχ, ite_true] using (differentiable_LFunctionTrivChar₁ q).analyticAt s
  · simpa only [regularizedL, hχ, ite_false] using (differentiable_LFunction hχ).analyticAt s

theorem regularizedL_zero_line {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hGRH : GRH)
    {s : ℂ} (hs : 0 < s.re) (hz : regularizedL χ s = 0) : s.re = 1 / 2 := by
  by_cases hχ : χ = 1
  · subst χ
    have hzero : LFunctionTrivChar₁ q s = 0 := by simpa only [regularizedL, eq_self, ite_true] using hz
    by_cases hs1 : s = 1
    · subst s
      exact False.elim (LFunctionTrivChar₁_apply_one_ne_zero q hzero)
    rw [LFunctionTrivChar₁, Function.update_of_ne hs1, mul_eq_zero] at hzero
    have hL : LFunction (1 : DirichletCharacter ℂ q) s = 0 :=
      hzero.resolve_left (sub_ne_zero.mpr hs1)
    have hslt : s.re < 1 := lt_of_not_ge fun hge =>
      LFunction_ne_zero_of_one_le_re (1 : DirichletCharacter ℂ q) (Or.inr hs1) hge hL
    exact hGRH q 1 s hs hslt hL
  · have hL : LFunction χ s = 0 := by simpa only [regularizedL, hχ, ite_false] using hz
    have hslt : s.re < 1 := lt_of_not_ge fun hge =>
      LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) hge hL
    exact hGRH q χ s hs hslt hL

theorem norm_regularizedL_anchor {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (t : ℝ) :
    (1 / 4 : ℝ) ≤ ‖regularizedL χ (⟨2, t⟩ : ℂ)‖ := by
  by_cases hχ : χ = 1
  · subst χ
    have hs : (⟨2, t⟩ : ℂ) ≠ 1 := by
      intro h
      have he := congrArg Complex.re h
      norm_num at he
    simp only [regularizedL, eq_self, ite_true]
    rw [LFunctionTrivChar₁, Function.update_of_ne hs]
    exact one_fourth_le_norm_mul_sub_one_LFunction_anchor (1 : DirichletCharacter ℂ q) t
  · simpa only [regularizedL, hχ, ite_false] using one_fourth_le_norm_LFunction_anchor χ t

theorem uniform_dirichlet_zero_slice (hGRH : GRH) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (t : ℝ),
      (criticalZeroSlice (regularizedL χ) t).Finite ∧
        (∑ᶠ z : ℂ, (criticalZeroSlice (regularizedL χ) t).indicator
          (fun z => (analyticOrderNatAt (regularizedL χ) z : ℝ)) z) ≤
          C * Real.log (2 * (q : ℝ) * (2 + |t|)) := by
  obtain ⟨C, hC, hJensen⟩ :=
    jensen_criticalZeroSlice_bound (A := 25) (b := 1 / 4) (by norm_num) (by norm_num)
  refine ⟨C, hC, ?_⟩
  intro q _ χ t
  exact hJensen q (regularizedL χ) t (Nat.pos_of_ne_zero (NeZero.ne q))
    ((analytic_regularizedL χ).mono (subset_univ _))
    (fun s hs => by
      have hg := GoldbachGrhGrowth.norm_regularizedLFunction_le χ hs
      by_cases hχ : χ = 1
      · simpa only [regularizedL, hχ, ite_true] using hg
      · simpa only [regularizedL, hχ, ite_false] using hg)
    (norm_regularizedL_anchor χ t) (fun s hs _ hzero => regularizedL_zero_line χ hGRH hs hzero)

theorem logDeriv_regularizedL_eq {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : s ≠ 1) (hL : LFunction χ s ≠ 0) :
    logDeriv (regularizedL χ) s = logDeriv (LFunction χ) s + principalFlag χ / (s - 1) := by
  by_cases hχ : χ = 1
  · subst χ
    simp only [regularizedL, principalFlag, eq_self, ite_true, logDeriv, Pi.div_apply]
    rw [deriv_LFunctionTrivChar₁_apply_of_ne_one q hs,
      LFunctionTrivChar₁, Function.update_of_ne hs]
    field_simp [sub_ne_zero.mpr hs, hL]
  · simp [regularizedL, principalFlag, hχ]

end Goldbach

open scoped BigOperators Topology
open Complex Filter Metric Set

noncomputable section

namespace GoldbachGrhLogDerivative

/- The argument uses the local zero separation and Borel–Carathéodory method in
`Zeta23/WeilEF/Landau.lean` (Anthropic, PBC), with direct Mathlib lemmas for primitives,
Jensen's inequality, factorized meromorphic functions and Cauchy's derivative bound. -/

private theorem exists_normalizedLog_on_ball {g : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hg : AnalyticOnNhd ℂ g (ball (0 : ℂ) R))
    (hg0 : ∀ z ∈ ball (0 : ℂ) R, g z ≠ 0) :
    ∃ J : ℂ → ℂ, J 0 = 0 ∧
      (∀ z ∈ ball (0 : ℂ) R, HasDerivAt J (logDeriv g z) z) ∧
      (∀ z ∈ ball (0 : ℂ) R, (J z).re = Real.log ‖g z‖ - Real.log ‖g 0‖) := by
  let U : Set ℂ := ball 0 R
  have hLog : DifferentiableOn ℂ (logDeriv g) U := by
    intro z hz
    change DifferentiableWithinAt ℂ (fun w => deriv g w / g w) U z
    exact ((hg z hz).deriv.differentiableAt.div (hg z hz).differentiableAt
      (hg0 z hz)).differentiableWithinAt
  obtain ⟨J, hJ0, hJ⟩ := hLog.isExactOn_ball.with_val_at 0 0
  refine ⟨J, hJ0, hJ, ?_⟩
  let k : ℂ → ℂ := fun z => exp (-J z) * g z
  have hk (z : ℂ) (hz : z ∈ U) : HasDerivAt k 0 z := by
    have hD := (hJ z hz).neg.cexp.mul (hg z hz).differentiableAt.hasDerivAt
    convert hD using 1
    simp only [logDeriv_apply]
    field_simp [hg0 z hz]
    norm_num
  have hc : (0 : ℂ) ∈ U := mem_ball_self hR
  have hConst : EqOn k (fun _ => g 0) U := by
    refine isOpen_ball.eqOn_of_deriv_eq (convex_ball _ _).isPreconnected
      (fun z hz => (hk z hz).differentiableAt.differentiableWithinAt) (differentiableOn_const (g 0))
      ?_ hc (by simp [k, hJ0])
    intro z hz
    rw [(hk z hz).deriv, deriv_const]
  intro z hz
  have hAt := hConst hz
  change exp (-J z) * g z = g 0 at hAt
  have hExp : exp (J z) * g 0 = g z := by
    rw [← hAt, ← mul_assoc, ← exp_add, add_neg_cancel, exp_zero, one_mul]
  have hNorm := congrArg norm hExp
  rw [norm_mul, norm_exp] at hNorm
  have hLn := congrArg Real.log hNorm
  rw [Real.log_mul (Real.exp_ne_zero _) (norm_ne_zero_iff.mpr (hg0 0 hc)), Real.log_exp] at hLn
  linarith

/-- On the inner disk, the derivative of the normalized logarithm is bounded by its upper real
part bound on the outer disk. The constants arise from Borel–Carathéodory and a Cauchy circle. -/
theorem norm_logDeriv_of_zeroFree_ball {g : ℂ → ℂ} {M : ℝ} (hM : 0 < M)
    (hg : AnalyticOnNhd ℂ g (ball (0 : ℂ) (22 / 25)))
    (hg0 : ∀ z ∈ ball (0 : ℂ) (22 / 25), g z ≠ 0)
    (hgBound : ∀ z ∈ ball (0 : ℂ) (22 / 25),
      Real.log ‖g z‖ - Real.log ‖g 0‖ ≤ M) {z : ℂ} (hz : ‖z‖ ≤ 83 / 100) :
    ‖logDeriv g z‖ ≤ 4200 * M := by
  have hR : (0 : ℝ) < 22 / 25 := by norm_num
  obtain ⟨J, hJ0, hJDeriv, hJRe⟩ := exists_normalizedLog_on_ball hR hg hg0
  have hJDiff : DifferentiableOn ℂ J (ball (0 : ℂ) (22 / 25)) :=
    fun w hw => (hJDeriv w hw).differentiableAt.differentiableWithinAt
  have hRadius : (0 : ℝ) < 1 / 100 := by norm_num
  have hLocalNorm (w : ℂ) (hw : w ∈ closedBall z (1 / 100)) : ‖w‖ ≤ 21 / 25 := by
    rw [mem_closedBall, Complex.dist_eq] at hw
    linarith [norm_le_norm_sub_add w z]
  have hLocal : closedBall z (1 / 100) ⊆ ball (0 : ℂ) (22 / 25) := by
    intro w hw
    exact mem_ball_zero_iff.mpr ((hLocalNorm w hw).trans_lt (by norm_num))
  have hLocalDiff : DiffContOnCl ℂ J (ball z (1 / 100)) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball _ hRadius.ne']
    exact hJDiff.mono hLocal
  have hJImage : MapsTo J (ball (0 : ℂ) (22 / 25)) {w | w.re ≤ M} := by
    intro w hw
    change (J w).re ≤ M
    rw [hJRe w hw]
    exact hgBound w hw
  have hLocalBound (w : ℂ) (hw : w ∈ sphere z (1 / 100)) : ‖J w‖ ≤ 42 * M := by
    have hws := sphere_subset_closedBall hw
    have hwBig := hLocal hws
    have hSmall := hLocalNorm w hws
    have hDpos : 0 < (22 / 25 : ℝ) - ‖w‖ := by linarith
    refine (borelCaratheodory_zero hM hJDiff hJImage hR hwBig hJ0).trans ?_
    apply (div_le_iff₀ hDpos).mpr
    nlinarith [mul_nonneg hM.le (sub_nonneg.mpr hSmall)]
  have hCauchy := norm_deriv_le_of_forall_mem_sphere_norm_le hRadius hLocalDiff hLocalBound
  have hzBig : z ∈ ball (0 : ℂ) (22 / 25) :=
    mem_ball_zero_iff.mpr (hz.trans_lt (by norm_num))
  rw [(hJDeriv z hzBig).deriv] at hCauchy
  calc
    _ ≤ (42 * M) / (1 / 100 : ℝ) := hCauchy
    _ = _ := by ring

open MeromorphicOn in
private theorem factor_inner_divisor {f : ℂ → ℂ} {U V : Set ℂ}
    (hVU : V ⊆ U) (hCompact : IsCompact V) (hf : AnalyticOnNhd ℂ f U)
    (hFiniteOrder : ∀ z ∈ U, meromorphicOrderAt f z ≠ ⊤) :
    ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g U ∧ (∀ z ∈ V, g z ≠ 0) ∧
      EqOn f ((∏ᶠ ρ, (· - ρ) ^ divisor f V ρ) * g)
        (U \ Function.support (divisor f V)) := by
  let D := divisor f V
  let P : ℂ → ℂ := ∏ᶠ ρ, (· - ρ) ^ D ρ
  let Q : ℂ → ℂ := P⁻¹ • f
  let g := toMeromorphicNFOn Q U
  have hDfin : (D : ℂ → ℤ).HasFiniteSupport := D.finiteSupport hCompact
  have hPNF : MeromorphicNFOn P U := Function.FactorizedRational.meromorphicNFOn D U
  have hQMer : MeromorphicOn Q U := hPNF.meromorphicOn.inv.smul hf.meromorphicOn
  have hGNF : MeromorphicNFOn g U := meromorphicNFOn_toMeromorphicNFOn Q U
  have hPOrd (z : ℂ) : meromorphicOrderAt P z = (D z : WithTop ℤ) :=
    Function.FactorizedRational.meromorphicOrderAt_eq D hDfin
  have hGOrd (z : ℂ) (hz : z ∈ U) :
      meromorphicOrderAt g z = -(D z : WithTop ℤ) + meromorphicOrderAt f z := by
    rw [← meromorphicOrderAt_congr (hQMer.toMeromorphicNFOn_eq_self_on_nhdsNE hz).symm]
    change meromorphicOrderAt (P⁻¹ • f) z = _
    rw [meromorphicOrderAt_smul (hPNF.meromorphicOn z hz).inv (hf.meromorphicOn z hz),
      meromorphicOrderAt_inv, hPOrd]
  have hOrdInner (z : ℂ) (hz : z ∈ V) : (D z : WithTop ℤ) = meromorphicOrderAt f z := by
    change (divisor f V z : WithTop ℤ) = _
    rw [(hf.mono hVU).meromorphicOn.divisor_apply hz]
    lift meromorphicOrderAt f z to ℤ using hFiniteOrder z (hVU hz) with n hn
    simp
  have hGZeroOrder (z : ℂ) (hz : z ∈ V) : meromorphicOrderAt g z = 0 := by
    rw [hGOrd z (hVU hz), ← hOrdInner z hz, ← WithTop.LinearOrderedAddCommGroup.coe_neg,
      ← WithTop.coe_add]
    simp
  refine ⟨g, ?_, ?_, ?_⟩
  · intro z hz
    apply (hGNF hz).meromorphicOrderAt_nonneg_iff_analyticAt.mp
    by_cases hzV : z ∈ V
    · rw [hGZeroOrder z hzV]
    · have hzD : D z = 0 := by
        by_contra h
        exact hzV (D.supportWithinDomain h)
      rw [hGOrd z hz, hzD, WithTop.coe_zero, neg_zero, zero_add]
      exact (hf z hz).meromorphicNFAt.meromorphicOrderAt_nonneg_iff_analyticAt.mpr (hf z hz)
  · intro z hz
    exact (hGNF (hVU hz)).meromorphicOrderAt_eq_zero_iff.mp (hGZeroOrder z hz)
  · intro z hz
    have hzD : D z = 0 := by simpa only [Function.mem_support, not_not] using hz.2
    have hPOrd0 : meromorphicOrderAt P z = 0 := by rw [hPOrd, hzD, WithTop.coe_zero]
    have hPNZ : P z ≠ 0 := (hPNF hz.1).meromorphicOrderAt_eq_zero_iff.mp hPOrd0
    have hPA : AnalyticAt ℂ P z :=
      (hPNF hz.1).meromorphicOrderAt_nonneg_iff_analyticAt.mp hPOrd0.ge
    have hQA : AnalyticAt ℂ Q z := (hPA.inv hPNZ).mul (hf z hz.1)
    have hGQ : g z = Q z := by
      change toMeromorphicNFOn Q U z = Q z
      rw [toMeromorphicNFOn_eq_toMeromorphicNFAt hQMer hz.1,
        toMeromorphicNFAt_eq_self.mpr hQA.meromorphicNFAt]
    change f z = P z * g z
    rw [hGQ]
    change f z = P z * ((P z)⁻¹ * f z)
    rw [← mul_assoc, mul_inv_cancel₀ hPNZ, one_mul]

private theorem logDeriv_finset_zeroFactors {Z : Finset ℂ} {m : ℂ → ℕ} {z : ℂ}
    (hz : ∀ ρ ∈ Z, z ≠ ρ) :
    logDeriv (fun w : ℂ => ∏ ρ ∈ Z, (w - ρ) ^ m ρ) z =
      ∑ ρ ∈ Z, (m ρ : ℂ) / (z - ρ) := by
  have hd (ρ : ℂ) : HasDerivAt (fun w : ℂ => w - ρ) 1 z := (hasDerivAt_id z).sub_const ρ
  have hProd : (fun w : ℂ => ∏ ρ ∈ Z, (w - ρ) ^ m ρ) =
      ∏ ρ ∈ Z, (fun w : ℂ => (w - ρ) ^ m ρ) := by
    funext w
    rw [Finset.prod_apply]
  rw [hProd, logDeriv_prod (f := fun ρ w => (w - ρ) ^ m ρ)
    (fun ρ hρ => pow_ne_zero _ (sub_ne_zero.mpr (hz ρ hρ)))
    (fun ρ _ => (hd ρ).differentiableAt.pow _)]
  apply Finset.sum_congr rfl
  intro ρ _
  rw [logDeriv_fun_pow (hd ρ).differentiableAt, logDeriv_apply, (hd ρ).deriv]
  ring

open MeromorphicOn in
/-- Landau's approximation by simple poles in a normalized unit disk. Jensen's inequality
bounds the sum of multiplicities. The remaining analytic factor is controlled on the smaller disk. -/
theorem logDeriv_partial_fraction_unit {f : ℂ → ℂ} {B : ℝ}
    (hf : AnalyticOnNhd ℂ f (closedBall (0 : ℂ) 1)) (hf0 : f 0 = 1) (hB : 2 ≤ B)
    (hfB : ∀ w ∈ sphere (0 : ℂ) (24 / 25), ‖f w‖ ≤ B) :
    ∃ Z : Finset ℂ,
      (↑Z = {ρ ∈ closedBall (0 : ℂ) (22 / 25) | f ρ = 0}) ∧
      ((∑ ρ ∈ Z, (analyticOrderNatAt f ρ : ℝ)) ≤ Real.log B / Real.log (12 / 11)) ∧
      ∀ z : ℂ, ‖z‖ ≤ 83 / 100 → f z ≠ 0 →
        ‖logDeriv f z - ∑ ρ ∈ Z, (analyticOrderNatAt f ρ : ℂ) / (z - ρ)‖ ≤
          130200 * Real.log B := by
  classical
  let U := closedBall (0 : ℂ) 1
  let V := closedBall (0 : ℂ) (22 / 25)
  let W := closedBall (0 : ℂ) (24 / 25)
  have hVU : V ⊆ U := closedBall_subset_closedBall (by norm_num)
  have hWU : W ⊆ U := closedBall_subset_closedBall (by norm_num)
  have hVW : V ⊆ W := closedBall_subset_closedBall (by norm_num)
  have h0U : (0 : ℂ) ∈ U := mem_closedBall_self (by norm_num)
  have hf0NZ : f 0 ≠ 0 := by rw [hf0]; exact one_ne_zero
  have hFinA (z : ℂ) (hz : z ∈ U) : analyticOrderAt f z ≠ ⊤ :=
    hf.analyticOrderAt_ne_top_of_isPreconnected (convex_closedBall _ _).isPreconnected h0U hz
      (by simp [(hf 0 h0U).analyticOrderAt_eq_zero.mpr hf0NZ])
  have hFinM (z : ℂ) (hz : z ∈ U) : meromorphicOrderAt f z ≠ ⊤ := by
    rw [(hf z hz).meromorphicOrderAt_eq]
    lift analyticOrderAt f z to ℕ using hFinA z hz with n hn
    simp
  let D := divisor f V
  have hDfin : (D : ℂ → ℤ).HasFiniteSupport := D.finiteSupport (isCompact_closedBall ..)
  let Z := hDfin.toFinset
  let K := ∑ ρ ∈ Z, analyticOrderNatAt f ρ
  have hSupport : V ∩ f ⁻¹' {0} = Function.support D :=
    (hf.mono hVU).meromorphicNFOn.zero_set_eq_divisor_support (fun v => hFinM v (hVU v.2))
  have hZeq : (↑Z : Set ℂ) = {ρ ∈ V | f ρ = 0} := by
    rw [show (↑Z : Set ℂ) = Function.support D from hDfin.coe_toFinset, ← hSupport]
    rfl
  have hρV (ρ : ℂ) (hρ : ρ ∈ Z) : ρ ∈ V := D.supportWithinDomain (hDfin.mem_toFinset.mp hρ)
  have hm (ρ : ℂ) (hρ : ρ ∈ Z) : D ρ = (analyticOrderNatAt f ρ : ℤ) := by
    change divisor f V ρ = _
    rw [(hf.mono hVU).divisor_apply (hρV ρ hρ), ← Nat.cast_analyticOrderNatAt (hFinA ρ (hVU (hρV ρ hρ)))]
    simp
  have hCount : (K : ℝ) ≤ Real.log B / Real.log (12 / 11) := by
    have hFsum : (∑ᶠ u, D u) = ∑ ρ ∈ Z, D ρ :=
      finsum_eq_sum_of_support_subset _ fun _ hu => hDfin.mem_toFinset.mpr hu
    have hK : (K : ℤ) = ∑ ρ ∈ Z, D ρ := by
      simp only [K, Nat.cast_sum]
      exact Finset.sum_congr rfl fun ρ hρ => (hm ρ hρ).symm
    have hJ := AnalyticOnNhd.sum_divisor_le (r := (22 / 25 : ℝ)) (R := 24 / 25) (M := B)
      (by norm_num) (by norm_num) (by linarith)
      (by simpa only [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 24 / 25)] using hf.mono hWU)
      hf0NZ (by simpa only [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 24 / 25)] using hfB)
    have hRatio : (24 / 25 : ℝ) / (22 / 25) = 12 / 11 := by norm_num
    have hAbs : |(22 / 25 : ℝ)| = 22 / 25 := abs_of_nonneg (by norm_num)
    rw [hAbs] at hJ
    have hJ' : ((∑ᶠ u, D u : ℤ) : ℝ) ≤ Real.log B / Real.log (12 / 11) := by
      simpa only [D, V, hf0, norm_one, div_one, hRatio] using hJ
    rw [hFsum, ← hK, Int.cast_natCast] at hJ'
    exact hJ'
  obtain ⟨g, hg, hgNZ, hFactor⟩ := factor_inner_divisor hVU (isCompact_closedBall ..) hf hFinM
  let P : ℂ → ℂ := fun w => ∏ ρ ∈ Z, (w - ρ) ^ analyticOrderNatAt f ρ
  have hProd : (∏ᶠ ρ, (· - ρ) ^ D ρ) = P := by
    have hDiff : (fun ρ : ℂ => (· - ρ) ^ D ρ).mulSupport ⊆ Z := by
      intro ρ hρ
      refine hDfin.mem_toFinset.mpr ?_
      by_contra hOutside
      have hD0 : D ρ = 0 := by simpa only [Function.mem_support, not_not] using hOutside
      exact hρ (by simp [hD0])
    rw [finprod_eq_prod_of_mulSupport_subset _ hDiff]
    funext w
    rw [Finset.prod_apply]
    exact Finset.prod_congr rfl fun ρ hρ => by simp [hm ρ hρ]
  have hFac : EqOn f (P * g) (U \ Function.support D) := by
    simpa only [← hProd] using hFactor
  have hOuter (w : ℂ) (hw : w ∈ sphere (0 : ℂ) (24 / 25)) :
      ‖g w‖ ≤ B * (25 / 2 : ℝ) ^ K := by
    have hwNorm : ‖w‖ = 24 / 25 := mem_sphere_zero_iff_norm.mp hw
    have hwU : w ∈ U := hWU (sphere_subset_closedBall hw)
    have hwNot : w ∉ Function.support D := by
      intro hwD
      have hwV : w ∈ V := D.supportWithinDomain hwD
      have hN : ‖w‖ ≤ 22 / 25 := by simpa only [V, mem_closedBall_iff_norm, sub_zero] using hwV
      linarith
    have hEq : f w = P w * g w := hFac ⟨hwU, hwNot⟩
    have hDist (ρ : ℂ) (hρ : ρ ∈ Z) : (2 / 25 : ℝ) ≤ ‖w - ρ‖ := by
      have hRho : ‖ρ‖ ≤ 22 / 25 := by
        simpa only [V, mem_closedBall_iff_norm, sub_zero] using hρV ρ hρ
      exact (show (2 / 25 : ℝ) ≤ ‖w‖ - ‖ρ‖ by linarith).trans (norm_sub_norm_le w ρ)
    have hPBound : (2 / 25 : ℝ) ^ K ≤ ‖P w‖ := by
      simp only [P, norm_prod, norm_pow, K, ← Finset.prod_pow_eq_pow_sum]
      exact Finset.prod_le_prod₀ (fun _ _ => by positivity)
        (fun ρ hρ => pow_le_pow_left₀ (by norm_num) (hDist ρ hρ) _)
    have hAt := hfB w hw
    rw [hEq, norm_mul] at hAt
    have hMul : ‖g w‖ * (2 / 25 : ℝ) ^ K ≤ B := by
      rw [mul_comm]
      exact (mul_le_mul_of_nonneg_right hPBound (norm_nonneg _)).trans hAt
    have hDiv := (le_div_iff₀ (pow_pos (by norm_num : (0 : ℝ) < 2 / 25) K)).mpr hMul
    rw [div_eq_mul_inv, ← inv_pow, show ((2 / 25 : ℝ)⁻¹) = 25 / 2 by norm_num] at hDiv
    exact hDiv
  have hMax (w : ℂ) (hw : w ∈ W) : ‖g w‖ ≤ B * (25 / 2 : ℝ) ^ K := by
    apply norm_le_of_forall_mem_frontier_norm_le (U := W) isBounded_closedBall
    · apply DifferentiableOn.diffContOnCl
      simpa only [W, closure_closedBall] using (hg.mono hWU).differentiableOn
    · simpa only [W, frontier_closedBall'] using hOuter
    · simpa only [W, closure_closedBall] using hw
  have h0Not : (0 : ℂ) ∉ Function.support D := by
    rw [← hSupport]
    simp [hf0]
  have hP0 : ‖P 0‖ ≤ 1 := by
    simp only [P, norm_prod, norm_pow, zero_sub, norm_neg]
    refine Finset.prod_le_one₀ (fun _ _ => by positivity) fun ρ hρ => ?_
    have hρN : ‖ρ‖ ≤ 22 / 25 := by
      simpa only [V, mem_closedBall_iff_norm, sub_zero] using hρV ρ hρ
    exact pow_le_one₀ (norm_nonneg _) (hρN.trans (by norm_num))
  have hG0 : 1 ≤ ‖g 0‖ := by
    have hFactor0 : f 0 = P 0 * g 0 := hFac ⟨h0U, h0Not⟩
    calc
      1 = ‖f 0‖ := by simp [hf0]
      _ = ‖P 0‖ * ‖g 0‖ := by rw [hFactor0, norm_mul]
      _ ≤ _ := by simpa only [one_mul] using mul_le_mul_of_nonneg_right hP0 (norm_nonneg _)
  have hLogB : 0 < Real.log B := Real.log_pos (by linarith)
  have hLogRatio : 0 < Real.log (12 / 11 : ℝ) := Real.log_pos (by norm_num)
  have hLogPow : Real.log (25 / 2 : ℝ) ≤ 30 * Real.log (12 / 11 : ℝ) := by
    calc
      _ ≤ Real.log ((12 / 11 : ℝ) ^ (30 : ℕ)) := Real.log_le_log (by norm_num) (by norm_num)
      _ = _ := by rw [Real.log_pow]; norm_num
  have hKLog : (K : ℝ) * Real.log (25 / 2 : ℝ) ≤ 30 * Real.log B := by
    calc
      _ ≤ (K : ℝ) * (30 * Real.log (12 / 11 : ℝ)) := mul_le_mul_of_nonneg_left hLogPow K.cast_nonneg
      _ = 30 * ((K : ℝ) * Real.log (12 / 11 : ℝ)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left ((le_div_iff₀ hLogRatio).mp hCount) (by norm_num)
  have hReg (w : ℂ) (hw : w ∈ ball (0 : ℂ) (22 / 25)) :
      Real.log ‖g w‖ - Real.log ‖g 0‖ ≤ 31 * Real.log B := by
    have hwV := ball_subset_closedBall hw
    have hL : Real.log ‖g w‖ ≤ Real.log (B * (25 / 2 : ℝ) ^ K) :=
      Real.log_le_log (norm_pos_iff.mpr (hgNZ w hwV)) (hMax w (hVW hwV))
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow] at hL
    linarith [Real.log_nonneg hG0]
  refine ⟨Z, hZeq, ?_, ?_⟩
  · simpa only [K, Nat.cast_sum] using hCount
  · intro z hz hfz
    have hzI : z ∈ ball (0 : ℂ) 1 := mem_ball_zero_iff.mpr (hz.trans_lt (by norm_num))
    have hzNot : z ∉ Function.support D := by
      rw [← hSupport]
      simp [hfz]
    have hLocal : f =ᶠ[𝓝 z] fun w => P w * g w := by
      filter_upwards [(isOpen_ball.sdiff hDfin.isClosed).mem_nhds ⟨hzI, hzNot⟩] with w hw
      exact hFac ⟨ball_subset_closedBall hw.1, hw.2⟩
    have hfacZ : f z = P z * g z := hLocal.eq_of_nhds
    have hPZ : P z ≠ 0 := fun h => hfz (by simp [hfacZ, h])
    have hGZ : g z ≠ 0 := fun h => hfz (by simp [hfacZ, h])
    have hdP : DifferentiableAt ℂ P z := DifferentiableAt.fun_finsetProd fun ρ _ =>
      ((differentiable_id.sub_const ρ).differentiableAt).pow _
    have hFrac : logDeriv f z = logDeriv P z + logDeriv g z := by
      have hEq : logDeriv f z = logDeriv (fun w => P w * g w) z := by
        simp only [logDeriv_apply, hLocal.deriv_eq, hfacZ]
      rw [hEq]
      exact logDeriv_mul z hPZ hGZ hdP (hg z (ball_subset_closedBall hzI)).differentiableAt
    have hNonzero (ρ : ℂ) (hρ : ρ ∈ Z) : z ≠ ρ := by
      intro h
      have hρD : ρ ∈ Function.support D := hDfin.mem_toFinset.mp hρ
      exact hzNot (h ▸ hρD)
    rw [hFrac, show logDeriv P z = _ from logDeriv_finset_zeroFactors hNonzero, add_sub_cancel_left]
    calc
      _ ≤ 4200 * (31 * Real.log B) := norm_logDeriv_of_zeroFree_ball (by positivity)
        (hg.mono (ball_subset_closedBall.trans hVU))
        (fun w hw => hgNZ w (ball_subset_closedBall hw)) hReg hz
      _ = _ := by ring

/-- Landau's approximation on an arbitrary closed disk, obtained by affine scaling of the
normalized unit-disk statement. -/
theorem logDeriv_partial_fraction_disk {f : ℂ → ℂ} {c : ℂ} {R B : ℝ} (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (closedBall c R)) (hf0 : f c ≠ 0) (hB : 2 ≤ B)
    (hfB : ∀ w ∈ closedBall c (24 / 25 * R), ‖f w‖ ≤ B * ‖f c‖) :
    ∃ Z : Finset ℂ,
      (↑Z = {ρ ∈ closedBall c (22 / 25 * R) | f ρ = 0}) ∧
      ((∑ ρ ∈ Z, (analyticOrderNatAt f ρ : ℝ)) ≤ Real.log B / Real.log (12 / 11)) ∧
      ∀ s ∈ closedBall c (83 / 100 * R), f s ≠ 0 →
        ‖logDeriv f s - ∑ ρ ∈ Z, (analyticOrderNatAt f ρ : ℂ) / (s - ρ)‖ ≤
          130200 / R * Real.log B := by
  let A : ℂ → ℂ := fun w => c + (R : ℂ) * w
  let G : ℂ → ℂ := fun w => (f c)⁻¹ * f (A w)
  have hRC : (R : ℂ) ≠ 0 := ofReal_ne_zero.mpr hR.ne'
  have hAanalytic (w : ℂ) : AnalyticAt ℂ A w :=
    analyticAt_const.add (analyticAt_const.mul analyticAt_id)
  have hADeriv (w : ℂ) : deriv A w = (R : ℂ) := by
    simp [A]
  have hAinj : Function.Injective A := by
    intro z w hEq
    change c + (R : ℂ) * z = c + (R : ℂ) * w at hEq
    exact mul_left_cancel₀ hRC (add_left_cancel hEq)
  have hANorm (w : ℂ) : ‖A w - c‖ = R * ‖w‖ := by
    simp only [A, add_sub_cancel_left, norm_mul, Complex.norm_of_nonneg hR.le]
  have hAInv (s : ℂ) : A ((s - c) / (R : ℂ)) = s := by
    simp only [A]
    field_simp [hRC]
    ring
  have hAMem {w : ℂ} {r : ℝ} (hw : ‖w‖ ≤ r) : A w ∈ closedBall c (r * R) := by
    rw [mem_closedBall_iff_norm, hANorm]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left hw hR.le
  have hInvNorm {s : ℂ} {r : ℝ} (hs : s ∈ closedBall c (r * R)) :
      ‖(s - c) / (R : ℂ)‖ ≤ r := by
    rw [mem_closedBall_iff_norm] at hs
    rw [norm_div, Complex.norm_of_nonneg hR.le]
    exact (div_le_iff₀ hR).mpr hs
  have hAMemOne {w : ℂ} (hw : ‖w‖ ≤ 1) : A w ∈ closedBall c R := by
    simpa only [one_mul] using hAMem hw
  have hGanalytic : AnalyticOnNhd ℂ G (closedBall (0 : ℂ) 1) := by
    intro w hw
    have hwNorm : ‖w‖ ≤ 1 := by simpa only [mem_closedBall_iff_norm, sub_zero] using hw
    exact analyticAt_const.mul ((hf (A w) (hAMemOne hwNorm)).comp (hAanalytic w))
  have hG0 : G 0 = 1 := by simp [G, A, hf0]
  have hGBound (w : ℂ) (hw : w ∈ sphere (0 : ℂ) (24 / 25)) : ‖G w‖ ≤ B := by
    have hwNorm : ‖w‖ ≤ 24 / 25 := (mem_sphere_zero_iff_norm.mp hw).le
    have hNormPos := norm_pos_iff.mpr hf0
    calc
      _ = ‖f c‖⁻¹ * ‖f (A w)‖ := by simp only [G, norm_mul, norm_inv]
      _ ≤ ‖f c‖⁻¹ * (B * ‖f c‖) := mul_le_mul_of_nonneg_left (hfB (A w) (hAMem hwNorm))
        (inv_nonneg.mpr hNormPos.le)
      _ = B := by rw [mul_comm B, ← mul_assoc, inv_mul_cancel₀ hNormPos.ne', one_mul]
  have hOrd (w : ℂ) (hw : ‖w‖ ≤ 1) :
      analyticOrderNatAt G w = analyticOrderNatAt f (A w) := by
    have hComp : AnalyticAt ℂ (f ∘ A) w := (hf (A w) (hAMemOne hw)).comp (hAanalytic w)
    calc
      _ = analyticOrderNatAt (f ∘ A) w := analyticOrderNatAt_fun_const_mul hComp (inv_ne_zero hf0)
      _ = _ := by
        unfold analyticOrderNatAt
        rw [analyticOrderAt_comp_of_deriv_ne_zero (hAanalytic w) (by rw [hADeriv]; exact hRC)]
  obtain ⟨Z₀, hZ₀, hCount, hBound⟩ := logDeriv_partial_fraction_unit hGanalytic hG0 hB hGBound
  have hZero (w : ℂ) : w ∈ Z₀ ↔ ‖w‖ ≤ 22 / 25 ∧ f (A w) = 0 := by
    change w ∈ (↑Z₀ : Set ℂ) ↔ _
    rw [hZ₀]
    simp [G, hf0]
  have hZeroNorm (w : ℂ) (hw : w ∈ Z₀) : ‖w‖ ≤ 1 :=
    ((hZero w).mp hw).1.trans (by norm_num)
  let embedding : ℂ ↪ ℂ := ⟨A, hAinj⟩
  let Z := Z₀.map embedding
  refine ⟨Z, ?_, ?_, ?_⟩
  · ext ρ
    change ρ ∈ Z ↔ ρ ∈ closedBall c (22 / 25 * R) ∧ f ρ = 0
    simp only [Z, Finset.mem_map]
    constructor
    · rintro ⟨w, hw, rfl⟩
      obtain ⟨hwNorm, hwZero⟩ := (hZero w).mp hw
      exact ⟨hAMem hwNorm, hwZero⟩
    · rintro ⟨hρ, hρZero⟩
      refine ⟨(ρ - c) / (R : ℂ), (hZero _).mpr ⟨hInvNorm hρ, ?_⟩, hAInv ρ⟩
      rwa [hAInv]
  · simp only [Z, Finset.sum_map]
    have hSum : (∑ w ∈ Z₀, (analyticOrderNatAt f (A w) : ℝ)) =
        ∑ w ∈ Z₀, (analyticOrderNatAt G w : ℝ) :=
      Finset.sum_congr rfl fun w hw => by rw [hOrd w (hZeroNorm w hw)]
    exact hSum.le.trans hCount
  · intro s hs hfs
    let w := (s - c) / (R : ℂ)
    have hAw : A w = s := hAInv s
    have hw : ‖w‖ ≤ 83 / 100 := hInvNorm hs
    have hw₁ : ‖w‖ ≤ 1 := hw.trans (by norm_num)
    have hGw : G w ≠ 0 := by simp [G, hAw, hf0, hfs]
    have hG := hBound w hw hGw
    have hLD : logDeriv G w = (R : ℂ) * logDeriv f s := by
      calc
        _ = logDeriv (f ∘ A) w := logDeriv_const_mul w _ (inv_ne_zero hf0)
        _ = _ := by
          rw [logDeriv_comp (hf (A w) (hAMemOne hw₁)).differentiableAt
            (hAanalytic w).differentiableAt, hADeriv, hAw, mul_comm]
    have hLDF : logDeriv f s = (R : ℂ)⁻¹ * logDeriv G w := by
      rw [hLD, ← mul_assoc, inv_mul_cancel₀ hRC, one_mul]
    have hTerms : (∑ ρ ∈ Z, (analyticOrderNatAt f ρ : ℂ) / (s - ρ)) =
        (R : ℂ)⁻¹ * ∑ u ∈ Z₀, (analyticOrderNatAt G u : ℂ) / (w - u) := by
      simp only [Z, Finset.sum_map, Finset.mul_sum]
      refine Finset.sum_congr rfl fun u hu => ?_
      change (analyticOrderNatAt f (A u) : ℂ) / (s - A u) = _
      rw [← hOrd u (hZeroNorm u hu)]
      have hShift : s - A u = (R : ℂ) * (w - u) := by
        rw [← hAw]
        simp only [A]
        ring
      calc
        _ = ((analyticOrderNatAt G u : ℂ) / (w - u)) / (R : ℂ) := by
          rw [hShift, div_div, mul_comm]
        _ = _ := div_eq_inv_mul _ _
    rw [hLDF, hTerms, ← mul_sub, norm_mul, norm_inv, Complex.norm_of_nonneg hR.le]
    calc
      _ ≤ R⁻¹ * (130200 * Real.log B) := mul_le_mul_of_nonneg_left hG (inv_nonneg.mpr hR.le)
      _ = _ := by ring

end GoldbachGrhLogDerivative

namespace Goldbach

open Complex Metric Set
open scoped BigOperators

/-- Uniform logarithmic derivative bound on the right of Re s = 9/20, at a point with a
given positive separation from the zeros of the regularized L-function. -/
theorem norm_logDeriv_regularizedL_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (t σ d : ℝ),
      9 / 20 ≤ σ → σ ≤ 2 → 0 < d →
      (∀ ρ : ℂ, 0 < ρ.re → regularizedL χ ρ = 0 → d ≤ ‖(⟨σ, t⟩ : ℂ) - ρ‖) →
      ‖logDeriv (regularizedL χ) (⟨σ, t⟩ : ℂ)‖ ≤
        C * Real.log (2 * (q : ℝ) * (2 + |t|)) * (1 + d⁻¹) := by
  let R : ℝ := 15 / 8
  let A : ℝ := 130200 / R
  let E : ℝ := (Real.log (12 / 11 : ℝ))⁻¹
  have hR : 0 < R := by norm_num [R]
  have hA : 0 < A := div_pos (by norm_num) hR
  have hE : 0 < E := inv_pos.mpr (Real.log_pos (by norm_num))
  refine ⟨13 * (A + E), mul_pos (by norm_num) (add_pos hA hE), ?_⟩
  intro q _ χ t σ d hσlo hσhi hd hSep
  let f := regularizedL χ
  let c : ℂ := ⟨2, t⟩
  let s : ℂ := ⟨σ, t⟩
  let K : ℝ := 2 + |t|
  let B : ℝ := 900 * (q : ℝ) * K ^ 2
  let L : ℝ := Real.log (2 * (q : ℝ) * K)
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast Nat.succ_le_of_lt q.pos_of_neZero
  have hq0 : 0 < (q : ℝ) := zero_lt_one.trans_le hq1
  have hK2 : 2 ≤ K := le_add_of_nonneg_right (abs_nonneg t)
  have hK1 : 1 ≤ K := by linarith
  have hK0 : 0 < K := zero_lt_one.trans_le hK1
  have hB0 : 0 < B := by
    dsimp only [B]
    positivity
  have hB2 : 2 ≤ B := by
    calc
      (2 : ℝ) ≤ 900 * 1 * 1 := by norm_num
      _ ≤ B := mul_le_mul (mul_le_mul_of_nonneg_left hq1 (by norm_num))
        (one_le_pow₀ hK1) zero_le_one (by positivity)
  have hReLower (w : ℂ) (hw : w ∈ closedBall c R) : (1 / 8 : ℝ) ≤ w.re := by
    have hDist := mem_closedBall_iff_norm.mp hw
    have hRe := abs_re_le_norm (w - c)
    rw [sub_re, show c.re = 2 from rfl] at hRe
    have hLower := neg_le_abs (w.re - 2)
    dsimp only [R] at hDist
    linarith
  have hcform : c = (2 : ℂ) + (t : ℂ) * I := by
    apply Complex.ext <;> simp [c, Complex.mul_re, Complex.mul_im]
  have hcnorm : ‖c‖ ≤ K := by
    rw [hcform]
    calc
      _ ≤ ‖(2 : ℂ)‖ + ‖(t : ℂ) * I‖ := norm_add_le _ _
      _ = _ := by simp [K, norm_real, Real.norm_eq_abs]
  have hAnchor : (1 / 4 : ℝ) ≤ ‖f c‖ := norm_regularizedL_anchor χ t
  have hf0 : f c ≠ 0 := norm_pos_iff.mp ((by norm_num : (0 : ℝ) < 1 / 4).trans_le hAnchor)
  have hf : AnalyticOnNhd ℂ f (closedBall c R) := (analytic_regularizedL χ).mono (subset_univ _)
  have hfB (w : ℂ) (hw : w ∈ closedBall c (24 / 25 * R)) : ‖f w‖ ≤ B * ‖f c‖ := by
    have hwBig := closedBall_subset_closedBall (show (24 / 25 : ℝ) * R ≤ R by norm_num [R]) hw
    have hDist := mem_closedBall_iff_norm.mp hwBig
    have hwNorm : 1 + ‖w‖ ≤ 3 * K := by
      dsimp only [R] at hDist
      linarith only [norm_le_norm_sub_add w c, hDist, hcnorm, hK2]
    have hGrowth : ‖f w‖ ≤ 25 * (q : ℝ) * (1 + ‖w‖) ^ 2 := by
      have hRaw := GoldbachGrhGrowth.norm_regularizedLFunction_le χ (hReLower w hwBig)
      by_cases hχ : χ = 1 <;> simpa [f, regularizedL, hχ] using hRaw
    calc
      _ ≤ 25 * (q : ℝ) * (1 + ‖w‖) ^ 2 := hGrowth
      _ ≤ 25 * (q : ℝ) * (3 * K) ^ 2 := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) hwNorm 2) (by positivity)
      _ = B * (1 / 4 : ℝ) := by
        dsimp only [B]
        ring
      _ ≤ B * ‖f c‖ := mul_le_mul_of_nonneg_left hAnchor hB0.le
  have hS : s ∈ closedBall c (83 / 100 * R) := by
    have hSub : s - c = ((σ - 2 : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [s, c]
    rw [mem_closedBall_iff_norm, hSub, norm_real, Real.norm_eq_abs,
      abs_of_nonpos (sub_nonpos.mpr hσhi)]
    dsimp only [R]
    linarith
  have hS0 : f s ≠ 0 := by
    intro hsz
    have hs : 0 < s.re := (by norm_num : (0 : ℝ) < 9 / 20).trans_le hσlo
    have h := hSep s hs hsz
    rw [sub_self, norm_zero] at h
    exact hd.not_ge h
  obtain ⟨Z, hZ, hMass, hApprox⟩ :=
    GoldbachGrhLogDerivative.logDeriv_partial_fraction_disk hR hf hf0 hB2 hfB
  have hTerms : ‖∑ ρ ∈ Z, (analyticOrderNatAt f ρ : ℂ) / (s - ρ)‖ ≤
      (∑ ρ ∈ Z, (analyticOrderNatAt f ρ : ℝ)) * d⁻¹ := by
    refine (norm_sum_le _ _).trans ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun ρ hρ => ?_
    have hZmem : ρ ∈ (↑Z : Set ℂ) := hρ
    rw [hZ] at hZmem
    have hρLarge := closedBall_subset_closedBall (show (22 / 25 : ℝ) * R ≤ R by norm_num [R])
      hZmem.1
    have hρPos := (by norm_num : (0 : ℝ) < 1 / 8).trans_le (hReLower ρ hρLarge)
    have hρdist : d ≤ ‖s - ρ‖ := hSep ρ hρPos hZmem.2
    have hRecip : ‖s - ρ‖⁻¹ ≤ d⁻¹ := by
      simpa only [one_div] using one_div_le_one_div_of_le hd hρdist
    rw [norm_div, Complex.norm_natCast, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left hRecip (Nat.cast_nonneg _)
  have hLFormula : L = Real.log 2 + Real.log (q : ℝ) + Real.log K := by
    dsimp only [L]
    rw [Real.log_mul (by positivity) hK0.ne', Real.log_mul (by norm_num) hq0.ne']
  have hBLFormula : Real.log B = Real.log 900 + Real.log (q : ℝ) + 2 * Real.log K := by
    dsimp only [B]
    rw [Real.log_mul (by positivity) (pow_ne_zero _ hK0.ne'),
      Real.log_mul (by norm_num) hq0.ne', Real.log_pow]
    norm_num
  have hLog900 : Real.log 900 ≤ 10 * Real.log 2 := by
    calc
      _ ≤ Real.log ((2 : ℝ) ^ (10 : ℕ)) := Real.log_le_log (by norm_num) (by norm_num)
      _ = _ := by
        rw [Real.log_pow]
        norm_num
  have hLPos : 0 < L := by
    rw [hLFormula]
    linarith only [Real.log_nonneg hq1, Real.log_nonneg hK1, Real.log_pos (by norm_num : (1 : ℝ) < 2)]
  have hScaleLog : Real.log B ≤ 13 * L := by
    rw [hBLFormula, hLFormula]
    linarith only [hLog900, Real.log_nonneg hq1, Real.log_nonneg hK1,
      Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)]
  have hRecip0 : 0 ≤ d⁻¹ := inv_nonneg.mpr hd.le
  have hBudget : A + E * d⁻¹ ≤ (A + E) * (1 + d⁻¹) := by
    nlinarith only [hE.le, mul_nonneg hA.le hRecip0]
  have hMass' := mul_le_mul_of_nonneg_right hMass hRecip0
  change ‖logDeriv f s‖ ≤ 13 * (A + E) * L * (1 + d⁻¹)
  calc
    _ ≤ ‖logDeriv f s - ∑ ρ ∈ Z, (analyticOrderNatAt f ρ : ℂ) / (s - ρ)‖ +
        ‖∑ ρ ∈ Z, (analyticOrderNatAt f ρ : ℂ) / (s - ρ)‖ := norm_le_norm_sub_add _ _
    _ ≤ A * Real.log B + (Real.log B / Real.log (12 / 11)) * d⁻¹ :=
      (add_le_add (hApprox s hS hS0) (hTerms.trans hMass'))
    _ = Real.log B * (A + E * d⁻¹) := by
      dsimp only [E]
      rw [div_eq_mul_inv]
      ring
    _ ≤ (13 * L) * (A + E * d⁻¹) := mul_le_mul_of_nonneg_right hScaleLog (by positivity)
    _ ≤ (13 * L) * ((A + E) * (1 + d⁻¹)) := mul_le_mul_of_nonneg_left hBudget (by positivity)
    _ = _ := by ring

end Goldbach

namespace Goldbach

/-- A unit interval contains a height separated by `1 / (2 * (1 + S.card))`
from all ordinates in a finite family. -/
theorem exists_goodHeight {α : Type*} (S : Finset α) (ordinate : α → ℝ) (T : ℝ) :
    ∃ u ∈ Set.Icc T (T + 1),
      ∀ a ∈ S, (1 : ℝ) / (2 * (1 + (S.card : ℝ))) ≤ |u - ordinate a| := by
  classical
  let den : ℝ := 1 + (S.card : ℝ)
  let gap : ℝ := 1 / (2 * den)
  let grid (j : Fin (S.card + 1)) : ℝ := T + (j.val : ℝ) / den
  have hDen : 0 < den := by dsimp [den]; positivity
  have hGrid (j : Fin (S.card + 1)) : grid j ∈ Set.Icc T (T + 1) := by
    have hj : (j.val : ℝ) ≤ S.card := by exact_mod_cast Nat.le_of_lt_succ j.isLt
    have hLower : 0 ≤ (j.val : ℝ) / den := div_nonneg (by positivity) hDen.le
    have hUpper : (j.val : ℝ) / den ≤ 1 := by
      apply (div_le_one hDen).mpr
      dsimp [den]
      linarith only [hj]
    exact ⟨by dsimp [grid]; linarith only [hLower], add_le_add le_rfl hUpper⟩
  have hGridGap {j k : Fin (S.card + 1)} (hjk : j ≠ k) :
      gap + gap ≤ |grid j - grid k| := by
    have hNat : j.val ≠ k.val := fun heq ↦ hjk (Fin.ext heq)
    have hInt : (j.val : ℤ) ≠ (k.val : ℤ) := by exact_mod_cast hNat
    have hAbsInt : (1 : ℤ) ≤ |(j.val : ℤ) - (k.val : ℤ)| :=
      Int.one_le_abs (sub_ne_zero.mpr hInt)
    have hAbs : (1 : ℝ) ≤ |(j.val : ℝ) - (k.val : ℝ)| := by exact_mod_cast hAbsInt
    have hGridSub : grid j - grid k = ((j.val : ℝ) - (k.val : ℝ)) / den := by
      dsimp [grid]
      ring
    calc
      gap + gap = 1 / den := by
        dsimp [gap]
        field_simp [hDen.ne']
        norm_num
      _ ≤ |(j.val : ℝ) - (k.val : ℝ)| / den := div_le_div_of_nonneg_right hAbs hDen.le
      _ = |grid j - grid k| := by rw [hGridSub, abs_div, abs_of_pos hDen]
  by_contra hNoGood
  have hBad (j : Fin (S.card + 1)) : ∃ a : S, |grid j - ordinate a| < gap := by
    by_contra hNoBad
    apply hNoGood
    refine ⟨grid j, hGrid j, ?_⟩
    intro a ha
    exact le_of_not_gt (fun h ↦ hNoBad ⟨⟨a, ha⟩, h⟩)
  let badAt (j : Fin (S.card + 1)) : S := (hBad j).choose
  have hBadAt (j : Fin (S.card + 1)) : |grid j - ordinate (badAt j)| < gap :=
    (hBad j).choose_spec
  have hInjective : Function.Injective badAt := by
    intro j k hEqual
    by_contra hDifferent
    have hPair : |grid j - ordinate (badAt j)| + |grid k - ordinate (badAt j)| < gap + gap :=
      (add_lt_add (hBadAt j) (by simpa only [hEqual] using hBadAt k))
    have hTri : |grid j - grid k| ≤
        |grid j - ordinate (badAt j)| + |grid k - ordinate (badAt j)| := by
      simpa only [abs_sub_comm (ordinate (badAt j)) (grid k)] using
        abs_sub_le (grid j) (ordinate (badAt j)) (grid k)
    exact not_lt_of_ge (hGridGap hDifferent) (hTri.trans_lt hPair)
  have hCard : S.card + 1 ≤ S.card := by
    simpa only [Fintype.card_fin, Fintype.card_coe] using
      Fintype.card_le_of_injective badAt hInjective
  omega

/-- A bound on the actual zero multiplicities in the unit neighborhood of the midpoint
gives a height separated from every zero in the open critical strip. -/
theorem exists_goodHeight_of_stripCount {f : ℂ → ℂ} (T countBound : ℝ)
    (hAnalytic : AnalyticOnNhd ℂ f {z : ℂ | 0 < z.re})
    (hAnchor : f (⟨2, T + 1 / 2⟩ : ℂ) ≠ 0) :
    let slice : Set ℂ := {z | 0 < z.re ∧ z.re < 1 ∧ |z.im - (T + 1 / 2)| ≤ 1 ∧ f z = 0}
    slice.Finite →
      (∑ᶠ z : ℂ, slice.indicator (fun z ↦ (analyticOrderNatAt f z : ℝ)) z) ≤ countBound →
      ∃ u ∈ Set.Icc T (T + 1), ∀ z : ℂ, 0 < z.re → z.re < 1 → f z = 0 →
        (1 : ℝ) / (2 * (1 + countBound)) ≤ |u - z.im| := by
  classical
  intro slice hFinite hCount
  let zeros := hFinite.toFinset
  let weight : ℂ → ℝ := fun z ↦ (analyticOrderNatAt f z : ℝ)
  have hSupport : Function.support (slice.indicator weight) ⊆ (zeros : Set ℂ) := by
    intro z hz
    apply hFinite.mem_toFinset.mpr
    by_contra hNot
    exact hz (Set.indicator_of_notMem hNot _)
  have hCountEq : (∑ᶠ z : ℂ, slice.indicator weight z) = ∑ z ∈ zeros, weight z := by
    rw [finsum_eq_sum_of_support_subset _ hSupport]
    exact Finset.sum_congr rfl fun z hz ↦ Set.indicator_of_mem (hFinite.mem_toFinset.mp hz) _
  let center : ℂ := ⟨2, T + 1 / 2⟩
  have hCenterMem : center ∈ {z : ℂ | 0 < z.re} := by norm_num [center]
  have hCenterOrder : analyticOrderAt f center ≠ ⊤ := by
    rw [(hAnalytic center hCenterMem).analyticOrderAt_eq_zero.mpr hAnchor]
    exact ENat.zero_ne_top
  have hWeight (z : ℂ) (hz : z ∈ zeros) : 1 ≤ weight z := by
    have hzSlice : 0 < z.re ∧ z.re < 1 ∧ |z.im - (T + 1 / 2)| ≤ 1 ∧ f z = 0 :=
      hFinite.mem_toFinset.mp hz
    have hFiniteOrder : analyticOrderAt f z ≠ ⊤ :=
      hAnalytic.analyticOrderAt_ne_top_of_isPreconnected (convex_halfSpace_re_gt 0).isPreconnected
        hCenterMem hzSlice.1 hCenterOrder
    have hNonzero : analyticOrderNatAt f z ≠ 0 := by
      intro hZero
      apply (hAnalytic z hzSlice.1).analyticOrderAt_ne_zero.mpr hzSlice.2.2.2
      rw [← Nat.cast_analyticOrderNatAt hFiniteOrder, hZero, Nat.cast_zero]
    change (1 : ℝ) ≤ (analyticOrderNatAt f z : ℝ)
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr hNonzero
  have hCard : (zeros.card : ℝ) ≤ countBound := calc
    _ = ∑ _z ∈ zeros, (1 : ℝ) := by simp
    _ ≤ ∑ z ∈ zeros, weight z := Finset.sum_le_sum hWeight
    _ = ∑ᶠ z : ℂ, slice.indicator weight z := hCountEq.symm
    _ ≤ countBound := hCount
  have hCountNonnegative : 0 ≤ countBound := (by positivity : (0 : ℝ) ≤ zeros.card).trans hCard
  have hGapBound : (1 : ℝ) / (2 * (1 + countBound)) ≤ 1 / (2 * (1 + (zeros.card : ℝ))) :=
    one_div_le_one_div_of_le (by positivity) (by linarith only [hCard])
  obtain ⟨u, hu, hNear⟩ := exists_goodHeight zeros Complex.im T
  refine ⟨u, hu, ?_⟩
  intro z hzPos hzLt hzZero
  by_cases hz : z ∈ slice
  · exact hGapBound.trans (hNear z (hFinite.mem_toFinset.mpr hz))
  · have hFar : 1 < |z.im - (T + 1 / 2)| := by
      apply lt_of_not_ge
      intro h
      exact hz ⟨hzPos, hzLt, h, hzZero⟩
    have hMid : |u - (T + 1 / 2)| ≤ 1 / 2 := by
      have huLower := hu.1
      have huUpper := hu.2
      exact abs_le.mpr ⟨by linarith only [huLower], by linarith only [huUpper]⟩
    have hTri : |z.im - (T + 1 / 2)| ≤ |u - z.im| + |u - (T + 1 / 2)| := by
      simpa only [abs_sub_comm z.im u] using abs_sub_le z.im u (T + 1 / 2)
    have hFarGap : (1 / 2 : ℝ) ≤ |u - z.im| := by linarith only [hFar, hMid, hTri]
    exact (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2)
      (by linarith only [hCountNonnegative])).trans hFarGap

end Goldbach

namespace Goldbach

open Filter Set

/-- Good heights in unit intervals on both sides of zero give lower and upper contour
sequences with explicit enclosures, signs, and divergence of their absolute values. -/
theorem exists_height_sequences (P : ℝ → Prop)
    (hFind : ∀ T : ℝ, (1 ≤ T ∨ T + 1 ≤ -1) → ∃ u ∈ Icc T (T + 1), P u) :
    ∃ lower upper : ℕ → ℝ,
      (∀ n : ℕ, lower n ∈ Icc (-(n : ℝ) - 2) (-(n : ℝ) - 1) ∧
        upper n ∈ Icc ((n : ℝ) + 1) ((n : ℝ) + 2)) ∧
      (∀ n, lower n < 0 ∧ 0 < upper n) ∧ (∀ n, P (lower n) ∧ P (upper n)) ∧
      Tendsto lower atTop atBot ∧ Tendsto upper atTop atTop ∧
      Tendsto (fun n ↦ |lower n|) atTop atTop ∧ Tendsto (fun n ↦ |upper n|) atTop atTop := by
  classical
  have hFindLower (n : ℕ) : ∃ u ∈ Icc (-(n : ℝ) - 2) (-(n : ℝ) - 1), P u := by
    have hn : (0 : ℝ) ≤ n := by positivity
    have hT : -(n : ℝ) - 2 + 1 ≤ -1 := by linarith only [hn]
    simpa only [show -(n : ℝ) - 2 + 1 = -(n : ℝ) - 1 by ring] using
      hFind (-(n : ℝ) - 2) (Or.inr hT)
  have hFindUpper (n : ℕ) : ∃ u ∈ Icc ((n : ℝ) + 1) ((n : ℝ) + 2), P u := by
    have hn : (0 : ℝ) ≤ n := by positivity
    have hT : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith only [hn]
    simpa only [show (n : ℝ) + 1 + 1 = (n : ℝ) + 2 by ring] using
      hFind ((n : ℝ) + 1) (Or.inl hT)
  choose lower hLower hLowerP using hFindLower
  choose upper hUpper hUpperP using hFindUpper
  have hSign (n : ℕ) : lower n < 0 ∧ 0 < upper n := by
    have hn : (0 : ℝ) ≤ n := by positivity
    exact ⟨by linarith only [(hLower n).2, hn], by linarith only [(hUpper n).1, hn]⟩
  have hNat : Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hNegNat : Tendsto (fun n : ℕ ↦ -(n : ℝ)) atTop atBot := tendsto_neg_atTop_atBot.comp hNat
  have hLowerLim : Tendsto lower atTop atBot :=
    tendsto_atBot_mono (fun n ↦ by linarith only [(hLower n).2]) hNegNat
  have hUpperLim : Tendsto upper atTop atTop :=
    tendsto_atTop_mono (fun n ↦ by linarith only [(hUpper n).1]) hNat
  have hLowerAbs : Tendsto (fun n ↦ |lower n|) atTop atTop := by
    apply tendsto_atTop_mono _ hNat
    intro n
    rw [abs_of_nonpos (hSign n).1.le]
    linarith only [(hLower n).2]
  have hUpperAbs : Tendsto (fun n ↦ |upper n|) atTop atTop := by
    apply tendsto_atTop_mono _ hNat
    intro n
    rw [abs_of_pos (hSign n).2]
    linarith only [(hUpper n).1]
  exact ⟨lower, upper, fun n ↦ ⟨hLower n, hUpper n⟩, hSign,
    fun n ↦ ⟨hLowerP n, hUpperP n⟩, hLowerLim, hUpperLim, hLowerAbs, hUpperAbs⟩

end Goldbach

namespace Goldbach

open Complex Set

noncomputable section

def logHeight (q : ℕ) (t : ℝ) : ℝ := Real.log (2 * (q : ℝ) * (2 + |t|))

def contourLog {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (z : ℂ) : ℂ :=
  -logDeriv (regularizedL χ) z + principalFlag χ / (z - 1)

def UniformDirichletLogDerivative (C : ℝ) : Prop :=
  ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (σ t d : ℝ),
    σ ∈ Icc (9 / 20 : ℝ) 2 → 0 < d →
    (∀ ρ : ℂ, 0 < ρ.re → regularizedL χ ρ = 0 → d ≤ ‖((σ : ℂ) + (t : ℂ) * I) - ρ‖) →
    ‖logDeriv (regularizedL χ) ((σ : ℂ) + (t : ℂ) * I)‖ ≤ C * logHeight q t * (1 + d⁻¹)

theorem logHeight_ge_one (q : ℕ) [NeZero q] (t : ℝ) : 1 ≤ logHeight q t := by
  have hq : 1 ≤ (q : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne q))
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 2 by norm_num)
    linarith
  have hlog4 : 1 ≤ Real.log 4 := by
    rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
    linarith
  have harg : (4 : ℝ) ≤ 2 * (q : ℝ) * (2 + |t|) := calc
    _ ≤ 2 * (1 : ℝ) * (2 + |t|) := by linarith [abs_nonneg t]
    _ ≤ _ := by gcongr
  exact hlog4.trans (Real.log_le_log (by norm_num) harg)

private theorem logHeight_compare {q : ℕ} [NeZero q] {t u : ℝ} (ht : |t| ≤ |u| + 1) :
    logHeight q t ≤ 2 * logHeight q u := by
  let v : ℝ := 2 * (q : ℝ) * (2 + |u|)
  have hq : 1 ≤ (q : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne q))
  have hv : 2 ≤ v := by
    calc
      _ ≤ 2 * (1 : ℝ) * (2 + |u|) := by linarith [abs_nonneg u]
      _ ≤ _ := by dsimp [v]; gcongr
  have hx : 2 * (q : ℝ) * (2 + |t|) ≤ v ^ 2 := by
    have ht' : 2 + |t| ≤ 2 * (2 + |u|) := by linarith [abs_nonneg u]
    calc
      _ ≤ 2 * (q : ℝ) * (2 * (2 + |u|)) := by gcongr
      _ = 2 * v := by dsimp [v]; ring
      _ ≤ _ := by nlinarith [mul_nonneg (show 0 ≤ v by linarith) (show 0 ≤ v - 2 by linarith)]
  have hh := Real.log_le_log (show 0 < 2 * (q : ℝ) * (2 + |t|) by positivity) hx
  rw [Real.log_pow] at hh
  simpa only [logHeight, v, Nat.cast_ofNat] using hh

private theorem norm_flag_pole_le {q : ℕ} (χ : DirichletCharacter ℂ q) {z : ℂ} {d : ℝ}
    (hd : 0 < d) (hz : d ≤ ‖z - 1‖) : ‖principalFlag χ / (z - 1)‖ ≤ 1 / d := by
  have hFlag : ‖principalFlag χ‖ ≤ 1 := by
    by_cases hχ : χ = 1 <;> simp [principalFlag, hχ]
  rw [norm_div]
  exact (div_le_div_of_nonneg_right hFlag (norm_nonneg _)).trans (one_div_le_one_div_of_le hd hz)

set_option maxHeartbeats 6000000 in
theorem contourLog_continuous_left {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hGRH : GRH) : Continuous (fun t : ℝ => contourLog χ (((9 / 20 : ℝ) : ℂ) + (t : ℂ) * I)) := by
  let z (t : ℝ) : ℂ := ((9 / 20 : ℝ) : ℂ) + (t : ℂ) * I
  have hcz : Continuous z := continuous_const.add (continuous_ofReal.mul continuous_const)
  have hzr (t : ℝ) : (z t).re = 9 / 20 := by
    simp only [z, add_re, ofReal_re, mul_I_re, ofReal_im, neg_zero, add_zero]
  have hnz (t : ℝ) : regularizedL χ (z t) ≠ 0 := by
    intro hz
    have h := regularizedL_zero_line χ hGRH (by rw [hzr]; norm_num) hz
    rw [hzr] at h
    norm_num at h
  have ho (t : ℝ) : z t - 1 ≠ 0 := by
    apply sub_ne_zero.mpr
    intro h
    have hh := congrArg Complex.re h
    rw [hzr, one_re] at hh
    norm_num at hh
  apply continuous_iff_continuousAt.mpr
  intro t
  have hF : AnalyticAt ℂ (regularizedL χ) (z t) :=
    analytic_regularizedL χ (z t) (Set.mem_univ _)
  have hLog : AnalyticAt ℂ (logDeriv (regularizedL χ)) (z t) := by
    simpa only [logDeriv, Pi.div_apply] using hF.deriv.div hF (hnz t)
  have hDen : AnalyticAt ℂ (fun w : ℂ => w - 1) (z t) := analyticAt_id.sub analyticAt_const
  have hFlag : AnalyticAt ℂ (fun _ : ℂ => principalFlag χ) (z t) := analyticAt_const
  have hPole : AnalyticAt ℂ (fun w : ℂ => principalFlag χ / (w - 1)) (z t) :=
    hFlag.div hDen (ho t)
  have hContour : AnalyticAt ℂ (contourLog χ) (z t) := hLog.neg.add hPole
  exact hContour.continuousAt.comp (hcz.continuousAt : ContinuousAt z t)

set_option maxHeartbeats 2000000 in
theorem dirichlet_contour_bounds (hGRH : GRH)
    (hLocal : ∃ C : ℝ, 0 < C ∧ UniformDirichletLogDerivative C) :
    ∃ A B : ℝ, 0 < A ∧ 0 < B ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      (∀ t : ℝ, ‖contourLog χ (((9 / 20 : ℝ) : ℂ) + (t : ℂ) * I)‖ ≤ A * logHeight q t) ∧
      ∀ T : ℝ, (1 ≤ T ∨ T + 1 ≤ -1) → ∃ u ∈ Icc T (T + 1),
        (∀ ρ : ℂ, 0 < ρ.re → regularizedL χ ρ = 0 → ρ.im ≠ u) ∧
        (∀ σ ∈ Icc (9 / 20 : ℝ) 2,
          ‖contourLog χ ((σ : ℂ) + (u : ℂ) * I)‖ ≤ B * logHeight q u ^ 2) := by
  obtain ⟨C, hC, hLog⟩ := hLocal
  obtain ⟨K, hK, hCount⟩ := uniform_dirichlet_zero_slice hGRH
  refine ⟨21 * C + 2, C * (3 + 4 * K) + 1, by positivity, by positivity, ?_⟩
  intro q _ χ
  constructor
  · intro t
    let z : ℂ := ((9 / 20 : ℝ) : ℂ) + (t : ℂ) * I
    have hzr : z.re = 9 / 20 := by simp [z]
    have hDist (ρ : ℂ) (hρ : 0 < ρ.re) (hz : regularizedL χ ρ = 0) :
        (1 / 20 : ℝ) ≤ ‖z - ρ‖ := by
      have h := Complex.re_le_norm (ρ - z)
      rw [sub_re, regularizedL_zero_line χ hGRH hρ hz, hzr, norm_sub_rev] at h
      norm_num at h ⊢
      exact h
    have hPole : (1 / 2 : ℝ) ≤ ‖z - 1‖ := by
      have h := Complex.re_le_norm (1 - z)
      rw [sub_re, one_re, hzr, norm_sub_rev] at h
      linarith
    have hld := hLog q χ (9 / 20) t (1 / 20) (by norm_num) (by norm_num) hDist
    have hpd := norm_flag_pole_le χ (by norm_num) hPole
    have hl := logHeight_ge_one q t
    calc
      _ ≤ ‖logDeriv (regularizedL χ) z‖ + ‖principalFlag χ / (z - 1)‖ := by
        simpa only [contourLog, norm_neg, z] using
          norm_add_le (-logDeriv (regularizedL χ) z) (principalFlag χ / (z - 1))
      _ ≤ C * logHeight q t * (1 + (1 / 20 : ℝ)⁻¹) + 1 / (1 / 2 : ℝ) := add_le_add hld hpd
      _ ≤ _ := by norm_num; nlinarith
  · intro T hT
    let middle := T + 1 / 2
    let Cnt := K * logHeight q middle
    have hCnt : 0 ≤ Cnt := mul_nonneg hK.le (zero_le_one.trans (logHeight_ge_one q middle))
    obtain ⟨hFinit, hN⟩ := hCount q χ middle
    have hF := (analytic_regularizedL χ).mono (subset_univ {z : ℂ | 0 < z.re})
    have hAn := norm_pos_iff.mp ((by norm_num : (0 : ℝ) < 1 / 4).trans_le
      (norm_regularizedL_anchor χ middle))
    obtain ⟨u, hu, hGap⟩ := exists_goodHeight_of_stripCount T Cnt hF hAn hFinit hN
    let d := 1 / (2 * (1 + Cnt))
    have hd : 0 < d := by dsimp [d]; positivity
    have sep (ρ : ℂ) (hρ : 0 < ρ.re) (hZ : regularizedL χ ρ = 0) : d ≤ |u - ρ.im| :=
      hGap ρ hρ (by rw [regularizedL_zero_line χ hGRH hρ hZ]; norm_num) hZ
    refine ⟨u, hu, ?_, ?_⟩
    · intro ρ hρ hZ hEq
      have e := sep ρ hρ hZ
      rw [hEq, sub_self, abs_zero] at e
      exact (not_le_of_gt hd) e
    · intro σ hσ
      let z : ℂ := (σ : ℂ) + (u : ℂ) * I
      have huAbs : 1 ≤ |u| := by
        rcases hT with ht | ht
        · have hu1 := ht.trans hu.1
          rwa [abs_of_nonneg (by linarith)]
        · have hu1 := hu.2.trans ht
          rw [abs_of_nonpos (by linarith)]
          linarith
      have hdist (ρ : ℂ) (hρ : 0 < ρ.re) (hZ : regularizedL χ ρ = 0) : d ≤ ‖z - ρ‖ :=
        (sep ρ hρ hZ).trans (by simpa [z] using Complex.abs_im_le_norm (z - ρ))
      have hPole : 1 ≤ ‖z - 1‖ := huAbs.trans
        (by simpa [z] using Complex.abs_im_le_norm (z - 1))
      have hdiff : |middle - u| ≤ 1 / 2 :=
        abs_le.mpr ⟨by dsimp [middle]; linarith [hu.2], by dsimp [middle]; linarith [hu.1]⟩
      have hmabs : |middle| ≤ |u| + 1 := calc
        _ = |(middle - u) + u| := by rw [sub_add_cancel]
        _ ≤ |middle - u| + |u| := abs_add_le _ _
        _ ≤ _ := by linarith
      have hB : Cnt ≤ 2 * K * logHeight q u := calc
        _ ≤ K * (2 * logHeight q u) := mul_le_mul_of_nonneg_left (logHeight_compare hmabs) hK.le
        _ = _ := by ring
      have hInv : 1 + d⁻¹ = 3 + 2 * Cnt := by dsimp [d]; rw [one_div, inv_inv]; ring
      have hl := logHeight_ge_one q u
      have hFactor : 1 + d⁻¹ ≤ (3 + 4 * K) * logHeight q u := by
        rw [hInv]
        nlinarith only [hB, hl]
      have hSq : 1 ≤ logHeight q u ^ 2 := by
        nlinarith [mul_nonneg (show 0 ≤ logHeight q u - 1 by linarith)
          (show 0 ≤ logHeight q u by linarith)]
      have hld := hLog q χ σ u d hσ hd hdist
      have hpd := norm_flag_pole_le χ (by norm_num) hPole
      calc
        _ ≤ ‖logDeriv (regularizedL χ) z‖ + ‖principalFlag χ / (z - 1)‖ := by
          simpa only [contourLog, norm_neg, z] using
            norm_add_le (-logDeriv (regularizedL χ) z) (principalFlag χ / (z - 1))
        _ ≤ C * logHeight q u * (1 + d⁻¹) + 1 / 1 := add_le_add hld hpd
        _ ≤ C * logHeight q u * ((3 + 4 * K) * logHeight q u) + 1 / 1 :=
          (add_le_add (mul_le_mul_of_nonneg_left hFactor
            (mul_nonneg hC.le (zero_le_one.trans hl))) le_rfl)
        _ ≤ _ := by nlinarith only [hSq]

end

end Goldbach

namespace Goldbach

open Complex DirichletCharacter MeromorphicOn Set

/-- The regularized Dirichlet L-function is nonzero at one. -/
theorem regularizedL_ne_zero_at_one {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    regularizedL χ 1 ≠ 0 := by
  by_cases hχ : χ = 1
  · simpa only [regularizedL, hχ, ite_true] using LFunctionTrivChar₁_apply_one_ne_zero q
  · simpa only [regularizedL, hχ, ite_false] using LFunction_apply_one_ne_zero hχ

/-- The anchor gives finite order of the regularized L-function at every complex point. -/
theorem regularizedL_analyticOrder_ne_top {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (z : ℂ) : analyticOrderAt (regularizedL χ) z ≠ ⊤ := by
  let c : ℂ := ⟨2, 0⟩
  have hC : regularizedL χ c ≠ 0 := norm_pos_iff.mp
    ((by norm_num : (0 : ℝ) < 1 / 4).trans_le (norm_regularizedL_anchor χ 0))
  have hOrderC : analyticOrderAt (regularizedL χ) c ≠ ⊤ := by
    rw [((analytic_regularizedL χ) c (mem_univ c)).analyticOrderAt_eq_zero.mpr hC]
    exact ENat.zero_ne_top
  exact (analytic_regularizedL χ).analyticOrderAt_ne_top_of_isPreconnected
    isPreconnected_univ (mem_univ c) (mem_univ z) hOrderC

theorem regularizedL_analyticOrderNatAt_pos_iff {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (z : ℂ) :
    0 < analyticOrderNatAt (regularizedL χ) z ↔ regularizedL χ z = 0 := by
  constructor
  · intro h
    exact apply_eq_zero_of_analyticOrderNatAt_ne_zero h.ne'
  · intro h
    apply Nat.pos_of_ne_zero
    intro hzero
    apply ((analytic_regularizedL χ) z (mem_univ z)).analyticOrderAt_ne_zero.mpr h
    rw [← Nat.cast_analyticOrderNatAt (regularizedL_analyticOrder_ne_top χ z), hzero, Nat.cast_zero]

theorem regularizedL_divisor_apply {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {U : Set ℂ} {z : ℂ} (hz : z ∈ U) :
    divisor (regularizedL χ) U z = (analyticOrderNatAt (regularizedL χ) z : ℤ) := by
  rw [((analytic_regularizedL χ).mono (subset_univ U)).divisor_apply hz,
    ← Nat.cast_analyticOrderNatAt (regularizedL_analyticOrder_ne_top χ z),
    ENat.map_natCast, WithTop.untop₀_coe]

/-- The zeros of the regularized L-function on the closed contour rectangle form a finite
family. GRH and the choice of horizontal heights place every such zero strictly inside. -/
theorem exists_regularizedL_contourZeros {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hGRH : GRH) (lower upper : ℝ)
    (hLower : ∀ z : ℂ, 0 < z.re → regularizedL χ z = 0 → z.im ≠ lower)
    (hUpper : ∀ z : ℂ, 0 < z.re → regularizedL χ z = 0 → z.im ≠ upper) :
    ∃ S : Finset ℂ,
      (∀ z : ℂ, z ∈ S ↔ z ∈ (Icc (9 / 20 : ℝ) 2 ×ℂ Icc lower upper) ∧ regularizedL χ z = 0) ∧
      (∀ z ∈ S, z ∈ (Ioo (9 / 20 : ℝ) 2 ×ℂ Ioo lower upper)) ∧
      (∀ z ∈ S, 0 < z.re ∧ regularizedL χ z = 0) := by
  classical
  let rectangle : Set ℂ := Icc (9 / 20 : ℝ) 2 ×ℂ Icc lower upper
  let zeros : Set ℂ := {z | z ∈ rectangle ∧ regularizedL χ z = 0}
  have hCompact : IsCompact rectangle := isCompact_Icc.reProdIm isCompact_Icc
  have hSupportFinite := (divisor (regularizedL χ) rectangle).finiteSupport hCompact
  have hFinite : zeros.Finite := by
    apply hSupportFinite.subset
    intro z hz
    change divisor (regularizedL χ) rectangle z ≠ 0
    rw [regularizedL_divisor_apply χ hz.1]
    exact_mod_cast ((regularizedL_analyticOrderNatAt_pos_iff χ z).mpr hz.2).ne'
  let S := hFinite.toFinset
  have hPos (z : ℂ) (hz : z ∈ S) : 0 < z.re ∧ regularizedL χ z = 0 := by
    have hmem := hFinite.mem_toFinset.mp hz
    exact ⟨(by norm_num : (0 : ℝ) < 9 / 20).trans_le (mem_reProdIm.mp hmem.1).1.1, hmem.2⟩
  refine ⟨S, fun z ↦ hFinite.mem_toFinset, ?_, hPos⟩
  intro z hz
  have hmem := hFinite.mem_toFinset.mp hz
  have him := (mem_reProdIm.mp hmem.1).2
  have hzPos := hPos z hz
  have hre := regularizedL_zero_line χ hGRH hzPos.1 hzPos.2
  apply mem_reProdIm.mpr
  refine ⟨?_, ?_⟩
  · change (9 / 20 : ℝ) < z.re ∧ z.re < 2
    rw [hre]
    norm_num
  · exact ⟨lt_of_le_of_ne him.1 (hLower z hzPos.1 hzPos.2).symm,
      lt_of_le_of_ne him.2 (hUpper z hzPos.1 hzPos.2)⟩

end Goldbach

namespace Goldbach

private theorem one_le_log_four_for_tail : (1 : ℝ) ≤ Real.log 4 := by
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := calc
    _ = 1 - (2 : ℝ)⁻¹ := by norm_num
    _ ≤ _ := Real.one_sub_inv_le_log_of_pos (by norm_num)
  have hlog4 : Real.log 4 = Real.log 2 + Real.log 2 := by
    convert Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by norm_num : (2 : ℝ) ≠ 0) using 1
    norm_num
  linarith only [hlog2, hlog4]

/-- The summand is dominated by twice the drop of the discrete antiderivative. -/
private theorem log_tail_step {q j : ℝ} (hq : 1 ≤ q) (hj : 1 ≤ j) :
    Real.log (2 * q * (j + 1)) / j ^ 2 ≤
      2 * ((Real.log (2 * q * j) + 2) / j - (Real.log (2 * q * (j + 1)) + 2) / (j + 1)) := by
  have hq₀ : 0 < q := by linarith only [hq]
  have hj₀ : 0 < j := by linarith only [hj]
  have hNext₀ : 0 < j + 1 := by linarith only [hj]
  let L := Real.log (2 * q * j)
  let Lnext := Real.log (2 * q * (j + 1))
  have hJump : Lnext - L ≤ 1 / j := by
    have hRatio : (2 * q * (j + 1)) / (2 * q * j) = (j + 1) / j := by
      field_simp [hq₀.ne', hj₀.ne']
    dsimp [L, Lnext]
    rw [← Real.log_div (by positivity) (by positivity), hRatio]
    calc
      _ ≤ (j + 1) / j - 1 := Real.log_le_sub_one_of_pos (div_pos hNext₀ hj₀)
      _ = _ := by field_simp [hj₀.ne']; ring
  have hJumpOne : Lnext - L ≤ 1 := hJump.trans ((div_le_one hj₀).mpr hj)
  have hScaledJump : (Lnext - L) * j ≤ 1 := (le_div_iff₀ hj₀).mp hJump
  have hNumerator : Lnext ≤ (L + 2) * (j + 1) - j * (Lnext + 2) := by
    nlinarith only [hJumpOne, hScaledJump]
  have hDrop : Lnext / (j * (j + 1)) ≤ (L + 2) / j - (Lnext + 2) / (j + 1) := calc
    _ ≤ ((L + 2) * (j + 1) - j * (Lnext + 2)) / (j * (j + 1)) :=
      div_le_div_of_nonneg_right hNumerator (mul_pos hj₀ hNext₀).le
    _ = _ := (div_sub_div (L + 2) (Lnext + 2) hj₀.ne' hNext₀.ne').symm
  have hNextLog : 0 ≤ Lnext := Real.log_nonneg
    (one_le_mul_of_one_le_of_one_le (by linarith only [hq]) (by linarith only [hj]))
  have hDen : j * (j + 1) ≤ 2 * j ^ 2 := calc
    _ ≤ j * (2 * j) := mul_le_mul_of_nonneg_left (by linarith only [hj]) hj₀.le
    _ = _ := by ring
  change Lnext / j ^ 2 ≤ 2 * ((L + 2) / j - (Lnext + 2) / (j + 1))
  calc
    _ = (2 * Lnext) / (2 * j ^ 2) := by field_simp [hj₀.ne']
    _ ≤ (2 * Lnext) / (j * (j + 1)) :=
      div_le_div_of_nonneg_left (mul_nonneg (by norm_num) hNextLog) (mul_pos hj₀ hNext₀) hDen
    _ = 2 * (Lnext / (j * (j + 1))) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hDrop (by norm_num)

/-- The finite tail of `log(2q(k+2))/(k+1)^2` is bounded uniformly in its upper endpoint. -/
theorem log_tail_Icc_le {q : ℝ} (hq : 1 ≤ q) (N M : ℕ) (hN : 1 ≤ N) (hNM : N ≤ M) :
    (∑ k ∈ Finset.Icc N M, Real.log (2 * q * ((k : ℝ) + 2)) / ((k : ℝ) + 1) ^ 2) ≤
      6 * Real.log (2 * q * ((N : ℝ) + 1)) / ((N : ℝ) + 1) := by
  let F (k : ℕ) := (Real.log (2 * q * ((k : ℝ) + 1)) + 2) / ((k : ℝ) + 1)
  have hstep (k : ℕ) : Real.log (2 * q * ((k : ℝ) + 2)) / ((k : ℝ) + 1) ^ 2 ≤
      2 * (F k - F (k + 1)) := by
    have hj : (1 : ℝ) ≤ (k : ℝ) + 1 := by
      linarith only [(by positivity : (0 : ℝ) ≤ (k : ℝ))]
    simpa only [F, Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two] using
      log_tail_step hq hj
  have hTel : (∑ k ∈ Finset.Icc N M, (F k - F (k + 1))) = F N - F (M + 1) := by
    simpa only [neg_sub_neg] using Finset.sum_Icc_sub hNM (fun k ↦ -F k)
  have hFend : 0 ≤ F (M + 1) := by
    have hDen : (1 : ℝ) ≤ ((M + 1 : ℕ) : ℝ) + 1 := by
      linarith only [(by positivity : (0 : ℝ) ≤ ((M + 1 : ℕ) : ℝ))]
    have hLog : 0 ≤ Real.log (2 * q * (((M + 1 : ℕ) : ℝ) + 1)) := Real.log_nonneg
      (one_le_mul_of_one_le_of_one_le (by linarith only [hq]) hDen)
    dsimp [F]
    exact div_nonneg (add_nonneg hLog (by norm_num)) (by positivity)
  have hDenN : (2 : ℝ) ≤ (N : ℝ) + 1 := by
    have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
    linarith only [hNR]
  have hArgN : (4 : ℝ) ≤ 2 * q * ((N : ℝ) + 1) := calc
    _ = 2 * 2 := by norm_num
    _ ≤ _ := mul_le_mul (by linarith only [hq]) hDenN (by norm_num) (by linarith only [hq])
  have hLogN : 1 ≤ Real.log (2 * q * ((N : ℝ) + 1)) :=
    one_le_log_four_for_tail.trans (Real.log_le_log (by norm_num) hArgN)
  calc
    _ ≤ ∑ k ∈ Finset.Icc N M, 2 * (F k - F (k + 1)) := Finset.sum_le_sum fun k _ ↦ hstep k
    _ = 2 * (F N - F (M + 1)) := by rw [← Finset.mul_sum, hTel]
    _ ≤ 2 * F N := mul_le_mul_of_nonneg_left (sub_le_self _ hFend) (by norm_num)
    _ = (2 * (Real.log (2 * q * ((N : ℝ) + 1)) + 2)) / ((N : ℝ) + 1) := by
      dsimp [F]
      ring
    _ ≤ _ := div_le_div_of_nonneg_right (by linarith only [hLogN]) (by positivity)

/-- A logarithmic upper bound on each weight gives the same uniform finite tail estimate. -/
theorem weighted_log_tail_Icc_le {q K : ℝ} (hq : 1 ≤ q) (hK : 0 ≤ K)
    (N M : ℕ) (hN : 1 ≤ N) (hNM : N ≤ M) (w : ℕ → ℝ)
    (hw : ∀ k ∈ Finset.Icc N M, w k ≤ K * Real.log (2 * q * ((k : ℝ) + 2))) :
    (∑ k ∈ Finset.Icc N M, w k / ((k : ℝ) + 1) ^ 2) ≤
      6 * K * Real.log (2 * q * ((N : ℝ) + 1)) / ((N : ℝ) + 1) := by
  calc
    _ ≤ ∑ k ∈ Finset.Icc N M, (K * Real.log (2 * q * ((k : ℝ) + 2))) / ((k : ℝ) + 1) ^ 2 :=
      Finset.sum_le_sum fun k hk ↦ div_le_div_of_nonneg_right (hw k hk) (sq_nonneg _)
    _ = K * (∑ k ∈ Finset.Icc N M, Real.log (2 * q * ((k : ℝ) + 2)) / ((k : ℝ) + 1) ^ 2) := by
      rw [Finset.mul_sum]
      simp only [mul_div_assoc]
    _ ≤ K * (6 * Real.log (2 * q * ((N : ℝ) + 1)) / ((N : ℝ) + 1)) :=
      mul_le_mul_of_nonneg_left (log_tail_Icc_le hq N M hN hNM) hK
    _ = _ := by ring

end Goldbach

namespace Goldbach

private theorem half_bucket_le_norm {s : ℂ} (hre : (1 / 2 : ℝ) ≤ s.re) :
    ((Nat.floor |s.im| : ℝ) + 1) / 2 ≤ ‖s‖ := by
  let k := Nat.floor |s.im|
  change ((k : ℝ) + 1) / 2 ≤ ‖s‖
  have hhalf := hre.trans (Complex.re_le_norm s)
  have hfloor : (k : ℝ) ≤ ‖s‖ :=
    (Nat.floor_le (abs_nonneg _)).trans (Complex.abs_im_le_norm s)
  by_cases hk : k = 0
  · simpa only [hk, Nat.cast_zero, zero_add] using hhalf
  · have hk₁ : (1 : ℝ) ≤ k := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hk
    linarith only [hk₁, hfloor]

private theorem sqrt_le_self_for_smoothing {x : ℝ} (hx : 2 ≤ x) : Real.sqrt x ≤ x := by
  refine Real.sqrt_le_iff.mpr ⟨by linarith only [hx], ?_⟩
  nlinarith only [hx, sq_nonneg (x - 1)]

/-- Pointwise linear and quadratic decay in the absolute-height bucket of a critical-line zero. -/
theorem norm_smoothed_kernel_le_bucket {x : ℝ} (hx : 2 ≤ x) {s : ℂ}
    (hre : s.re = 1 / 2) :
    let k := Nat.floor |s.im|
    ‖GoldbachSmoothing.kernel x (Real.sqrt x) s‖ ≤ 4 * Real.sqrt x / ((k : ℝ) + 1) ∧
    ‖GoldbachSmoothing.kernel x (Real.sqrt x) s‖ ≤ 20 * x / ((k : ℝ) + 1) ^ 2 := by
  intro k
  let h := Real.sqrt x
  let d := ((k : ℝ) + 1) / 2
  have hx₀ : 0 < x := by linarith only [hx]
  have hh : 0 < h := Real.sqrt_pos.mpr hx₀
  have hhSq : h ^ 2 = x := Real.sq_sqrt hx₀.le
  have hSelf : h ≤ x := sqrt_le_self_for_smoothing hx
  have hd : 0 < d := by dsimp [d]; positivity
  have hSqrtSum : Real.sqrt (x + h) ≤ 2 * h := by
    refine Real.sqrt_le_iff.mpr ⟨by positivity, ?_⟩
    nlinarith only [hx, hSelf, hhSq]
  have hsDen : d ≤ ‖s‖ := half_bucket_le_norm (le_of_eq hre.symm)
  have hsNextDen : d ≤ ‖s + 1‖ := by
    have hreNext : (1 / 2 : ℝ) ≤ (s + 1).re := by
      rw [Complex.add_re, Complex.one_re, hre]
      norm_num
    simpa only [d, k, Complex.add_im, Complex.one_im, add_zero] using
      half_bucket_le_norm hreNext
  have hks : ‖GoldbachSmoothing.kernel x h s‖ ≤ Real.sqrt (x + h) / ‖s‖ := by
    have hs : 0 < s.re := by rw [hre]; norm_num
    simpa only [hre, ← Real.sqrt_eq_rpow] using GoldbachSmoothing.norm_kernel_le hx₀ hh hs
  constructor
  · calc
      _ ≤ Real.sqrt (x + h) / ‖s‖ := hks
      _ ≤ 2 * h / ‖s‖ := div_le_div_of_nonneg_right hSqrtSum (norm_nonneg _)
      _ ≤ 2 * h / d := div_le_div_of_nonneg_left (by positivity) hd hsDen
      _ = _ := by dsimp [d]; rw [div_div_eq_mul_div]; ring
  · have hPowSum : (x + h) ^ ((1 / 2 : ℝ) + 1) + x ^ ((1 / 2 : ℝ) + 1) ≤ 5 * x * h := calc
      _ = Real.sqrt (x + h) * (x + h) + h * x := by
        rw [Real.rpow_add_one (add_pos hx₀ hh).ne', Real.rpow_add_one hx₀.ne', ← Real.sqrt_eq_rpow,
          ← Real.sqrt_eq_rpow]
      _ ≤ (2 * h) * (2 * x) + h * x :=
        (add_le_add (mul_le_mul hSqrtSum (by linarith only [hSelf]) (by positivity) (by positivity)) le_rfl)
      _ = _ := by ring
    have hDen : h * d ^ 2 ≤ h * ‖s‖ * ‖s + 1‖ := calc
      h * d ^ 2 = h * (d * d) := by rw [pow_two]
      _ ≤ h * (‖s‖ * ‖s + 1‖) :=
        mul_le_mul_of_nonneg_left (mul_le_mul hsDen hsNextDen hd.le (norm_nonneg _)) hh.le
      _ = _ := by ring
    calc
      _ ≤ ((x + h) ^ ((1 / 2 : ℝ) + 1) + x ^ ((1 / 2 : ℝ) + 1)) /
          (h * ‖s‖ * ‖s + 1‖) := by
        simpa only [hre] using GoldbachSmoothing.norm_kernel_le_tail hx₀ hh (s := s)
      _ ≤ (5 * x * h) / (h * ‖s‖ * ‖s + 1‖) :=
        div_le_div_of_nonneg_right hPowSum (by positivity)
      _ ≤ (5 * x * h) / (h * d ^ 2) := div_le_div_of_nonneg_left (by positivity) (by positivity) hDen
      _ = _ := by
        have hk₀ : (0 : ℝ) < (k : ℝ) + 1 := by positivity
        dsimp [d]
        field_simp [hh.ne', hk₀.ne']
        ring

/-- A finite smoothed zero contribution is uniformly bounded given logarithmic mass in each
absolute-height bucket. The weights can be the orders of vanishing of the zeros. -/
theorem smoothed_zero_sum_le {q x K : ℝ} (hq : 1 ≤ q) (hx : 2 ≤ x) (hK : 0 ≤ K)
    (S : Finset ℂ) (m : ℂ → ℝ) (hm : ∀ s ∈ S, 0 ≤ m s)
    (hre : ∀ s ∈ S, s.re = 1 / 2)
    (hbuckets : ∀ k : ℕ,
      (∑ s ∈ S.filter (fun s ↦ Nat.floor |s.im| = k), m s) ≤
        K * Real.log (2 * q * ((k : ℝ) + 2))) :
    (∑ s ∈ S, m s * ‖GoldbachSmoothing.kernel x (Real.sqrt x) s‖) ≤
      256 * K * Real.sqrt x * Real.log (2 * q * x) ^ 2 := by
  classical
  let h := Real.sqrt x
  let N := Nat.floor h
  let height (s : ℂ) := Nat.floor |s.im|
  let M := max N (S.sup height)
  let mass (k : ℕ) := ∑ s ∈ S.filter (fun s ↦ height s = k), m s
  let weight (k : ℕ) : ℝ :=
    if k < N then 4 * h / ((k : ℝ) + 1) else 20 * x / ((k : ℝ) + 1) ^ 2
  let L := Real.log (2 * q * x)
  have hx₀ : 0 < x := by linarith only [hx]
  have hq₀ : 0 < q := by linarith only [hq]
  have hh : 0 < h := Real.sqrt_pos.mpr hx₀
  have hh₁ : 1 ≤ h := by
    apply (Real.le_sqrt (by norm_num : (0 : ℝ) ≤ 1) hx₀.le).mpr
    norm_num
    linarith only [hx]
  have hhLe : h ≤ x := sqrt_le_self_for_smoothing hx
  have hN : 1 ≤ N := (Nat.one_le_floor_iff h).mpr hh₁
  have hNLe : (N : ℝ) ≤ x := (Nat.floor_le hh.le).trans hhLe
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast (Nat.zero_lt_one.trans_le hN)
  have hNM : N ≤ M := le_max_left _ _
  have hBUpper : ∀ k : ℕ, mass k ≤ K * Real.log (2 * q * ((k : ℝ) + 2)) := hbuckets
  have hFourW : (4 : ℝ) ≤ 2 * q * x := calc
    _ = 2 * 2 := by norm_num
    _ ≤ _ := mul_le_mul (by linarith only [hq]) hx (by norm_num) (by positivity)
  have hOneL : 1 ≤ L := by
    have hTwo := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 2 by norm_num)
    norm_num at hTwo
    have hFour : (1 : ℝ) ≤ Real.log 4 := by
      rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
      linarith only [hTwo]
    exact hFour.trans (Real.log_le_log (by norm_num) hFourW)
  have hL₀ : 0 ≤ L := zero_le_one.trans hOneL
  have hLsq : L ≤ L ^ 2 := by
    rw [pow_two]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hOneL hL₀
  have hLog2 : Real.log 2 ≤ L := Real.log_le_log (by norm_num) (by linarith only [hFourW])
  have hLogScaled {y : ℝ} (hy₀ : 0 < y) (hy : y ≤ 2 * x) : Real.log (2 * q * y) ≤ 2 * L := calc
    _ ≤ Real.log (2 * q * (2 * x)) :=
      Real.log_le_log (by positivity) (mul_le_mul_of_nonneg_left hy (by positivity))
    _ = Real.log 2 + L := by
      rw [show 2 * q * (2 * x) = 2 * (2 * q * x) by ring, Real.log_mul (by norm_num) (by positivity)]
    _ ≤ _ := by linarith only [hLog2]
  have hLowLog (k : ℕ) (hk : k < N) : Real.log (2 * q * ((k : ℝ) + 2)) ≤ 2 * L := by
    have hkR : (k : ℝ) + 1 ≤ (N : ℝ) := by exact_mod_cast Nat.succ_le_of_lt hk
    exact hLogScaled (by positivity) (by linarith only [hNLe, hkR, hx])
  have hLogN : Real.log (N : ℝ) ≤ L :=
    Real.log_le_log hNpos (hNLe.trans (le_mul_of_one_le_left hx₀.le (by linarith only [hq])))
  have hHarmonic : (harmonic N : ℝ) ≤ 2 * L :=
    (harmonic_le_one_add_log N).trans (by linarith only [hLogN, hOneL])
  have hHarmonicEq : (harmonic N : ℝ) = ∑ k ∈ Finset.range N, 1 / ((k : ℝ) + 1) := by
    simp only [harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
    simp only [Nat.cast_add, Nat.cast_one, one_div]
  have hLow : (∑ k ∈ Finset.range N, mass k * (4 * h / ((k : ℝ) + 1))) ≤ 16 * K * h * L ^ 2 := calc
    _ ≤ ∑ k ∈ Finset.range N, (K * (2 * L)) * (4 * h / ((k : ℝ) + 1)) := by
      refine Finset.sum_le_sum fun k hk ↦ mul_le_mul_of_nonneg_right ?_ (by positivity)
      exact (hBUpper k).trans (mul_le_mul_of_nonneg_left (hLowLog k (Finset.mem_range.mp hk)) hK)
    _ = (8 * K * h * L) * (harmonic N : ℝ) := by
      rw [hHarmonicEq, Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ ↦ by ring
    _ ≤ (8 * K * h * L) * (2 * L) := mul_le_mul_of_nonneg_left hHarmonic (by positivity)
    _ = _ := by ring
  let LN := Real.log (2 * q * ((N : ℝ) + 1))
  have hLN₀ : 0 ≤ LN := Real.log_nonneg (one_le_mul_of_one_le_of_one_le (by linarith only [hq])
    (by linarith only [(by positivity : (0 : ℝ) ≤ (N : ℝ))]))
  have hLN : LN ≤ 2 * L := hLogScaled (by positivity) (by linarith only [hNLe, hx])
  have hXdiv : x / ((N : ℝ) + 1) ≤ h := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < (N : ℝ) + 1)).mpr
    calc
      x = h * h := (Real.mul_self_sqrt hx₀.le).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left (Nat.lt_floor_add_one h).le hh.le
  have hHigh : (∑ k ∈ Finset.Icc N M, mass k * (20 * x / ((k : ℝ) + 1) ^ 2)) ≤
      240 * K * h * L ^ 2 := calc
    _ = (20 * x) * (∑ k ∈ Finset.Icc N M, mass k / ((k : ℝ) + 1) ^ 2) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ ↦ by ring
    _ ≤ (20 * x) * (6 * K * LN / ((N : ℝ) + 1)) := mul_le_mul_of_nonneg_left
      (weighted_log_tail_Icc_le hq hK N M hN hNM mass fun k _ ↦ hBUpper k) (by positivity)
    _ = 120 * K * (x / ((N : ℝ) + 1)) * LN := by ring
    _ ≤ 120 * K * h * LN :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hXdiv (by positivity)) hLN₀
    _ ≤ (120 * K * h) * (2 * L) := mul_le_mul_of_nonneg_left hLN (by positivity)
    _ = (240 * K * h) * L := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hLsq (by positivity)
  have hMaps : ∀ s ∈ S, height s ∈ Finset.range (M + 1) := by
    intro s hs
    apply Finset.mem_range.mpr
    exact Nat.lt_succ_of_le ((Finset.le_sup (f := height) hs).trans (le_max_right _ _))
  have hSplit : (∑ k ∈ Finset.range (M + 1), mass k * weight k) =
      (∑ k ∈ Finset.range N, mass k * (4 * h / ((k : ℝ) + 1))) +
        (∑ k ∈ Finset.Icc N M, mass k * (20 * x / ((k : ℝ) + 1) ^ 2)) := by
    have hIco : Finset.Ico N M.succ = Finset.Icc N M := by
      ext k
      simp only [Finset.mem_Ico, Finset.mem_Icc, Nat.lt_succ_iff]
    rw [← Finset.sum_range_add_sum_Ico (fun k ↦ mass k * weight k) (Nat.le_succ_of_le hNM),
      hIco]
    congr 1
    · exact Finset.sum_congr rfl fun k hk ↦ by simp only [weight, ite_eq_left (Finset.mem_range.mp hk)]
    · exact Finset.sum_congr rfl fun k hk ↦ by
        simp only [weight, ite_eq_right (not_lt_of_ge (Finset.mem_Icc.mp hk).1)]
  change (∑ s ∈ S, m s * ‖GoldbachSmoothing.kernel x h s‖) ≤ 256 * K * h * L ^ 2
  calc
    _ ≤ ∑ s ∈ S, m s * weight (height s) := by
      refine Finset.sum_le_sum fun s hs ↦ mul_le_mul_of_nonneg_left ?_ (hm s hs)
      have hTerm := norm_smoothed_kernel_le_bucket hx (hre s hs)
      by_cases hk : height s < N
      · simpa only [weight, ite_eq_left hk] using hTerm.1
      · simpa only [weight, ite_eq_right hk] using hTerm.2
    _ = ∑ k ∈ Finset.range (M + 1),
        ∑ s ∈ S.filter (fun s ↦ height s = k), m s * weight (height s) :=
      (Finset.sum_fiberwise_of_maps_to hMaps (fun s ↦ m s * weight (height s))).symm
    _ = ∑ k ∈ Finset.range (M + 1), mass k * weight k := by
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      unfold mass
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun s hs ↦ by rw [(Finset.mem_filter.mp hs).2]
    _ = _ := hSplit
    _ ≤ 16 * K * h * L ^ 2 + 240 * K * h * L ^ 2 := add_le_add hLow hHigh
    _ = _ := by ring

end Goldbach

namespace Goldbach

open Complex Set
open scoped BigOperators

theorem uniform_smoothed_dirichlet_residues (hGRH : GRH) :
    ∃ D : ℝ, 0 < D ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
      (x : ℝ) (S : Finset ℂ), 2 ≤ x →
      (∀ ρ ∈ S, 0 < ρ.re ∧ regularizedL χ ρ = 0) →
      ‖∑ ρ ∈ S, (analyticOrderNatAt (regularizedL χ) ρ : ℂ) *
          GoldbachSmoothing.kernel x (Real.sqrt x) ρ‖ ≤
        D * Real.sqrt x * Real.log (2 * (q : ℝ) * x) ^ 2 := by
  classical
  obtain ⟨K, hK, hCount⟩ := uniform_dirichlet_zero_slice hGRH
  refine ⟨1024 * K, by positivity, ?_⟩
  intro q _ χ x S hx hS
  let F := regularizedL χ
  let m (z : ℂ) : ℝ := analyticOrderNatAt F z
  have hm (z : ℂ) : 0 ≤ m z := by dsimp [m]; positivity
  have hq : 1 ≤ (q : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne q))
  have hLine : ∀ ρ ∈ S, ρ.re = 1 / 2 := fun ρ hρ =>
    regularizedL_zero_line χ hGRH (hS ρ hρ).1 (hS ρ hρ).2
  have hCount' (t : ℝ) :
      (∑ ρ ∈ S.filter (fun ρ => ρ ∈ criticalZeroSlice F t), m ρ) ≤
        K * Real.log (2 * (q : ℝ) * (2 + |t|)) := by
    obtain ⟨hfin, hbound⟩ := hCount q χ t
    let zeros := hfin.toFinset
    have hSub : S.filter (fun ρ => ρ ∈ criticalZeroSlice F t) ⊆ zeros := by
      intro ρ hρ
      exact hfin.mem_toFinset.mpr (Finset.mem_filter.mp hρ).2
    have hSupp : Function.support ((criticalZeroSlice F t).indicator m) ⊆ (zeros : Set ℂ) := by
      intro ρ hρ
      apply hfin.mem_toFinset.mpr
      by_contra hn
      exact hρ (indicator_of_notMem hn _)
    have hEq : (∑ᶠ ρ : ℂ, (criticalZeroSlice F t).indicator m ρ) = ∑ ρ ∈ zeros, m ρ := by
      rw [finsum_eq_sum_of_support_subset _ hSupp]
      exact Finset.sum_congr rfl fun ρ hρ => indicator_of_mem (hfin.mem_toFinset.mp hρ) _
    exact (Finset.sum_le_sum_of_subset_of_nonneg hSub (fun ρ _ _ => hm ρ)).trans
      (hEq.symm.le.trans hbound)
  have hBucket (k : ℕ) : (∑ ρ ∈ S.filter (fun ρ => Nat.floor |ρ.im| = k), m ρ) ≤
      (4 * K) * Real.log (2 * (q : ℝ) * ((k : ℝ) + 2)) := by
    let t : ℝ := (k : ℝ) + 1 / 2
    have ht : 0 ≤ t := by dsimp [t]; positivity
    have hincl (ρ : ℂ) (hρ : ρ ∈ S) (hk : Nat.floor |ρ.im| = k) :
        ρ ∈ criticalZeroSlice F t ∨ ρ ∈ criticalZeroSlice F (-t) := by
      have hlo := Nat.floor_le (abs_nonneg ρ.im)
      have hhi := Nat.lt_floor_add_one |ρ.im|
      rw [hk] at hlo hhi
      have hre := hLine ρ hρ
      have hpos := (hS ρ hρ).1
      have hlt : ρ.re < 1 := by linarith
      have hz := (hS ρ hρ).2
      by_cases hsign : 0 ≤ ρ.im
      · left
        rw [abs_of_nonneg hsign] at hlo hhi
        exact ⟨hpos, hlt, abs_le.mpr ⟨by dsimp [t]; linarith, by dsimp [t]; linarith⟩, hz⟩
      · right
        rw [abs_of_neg (lt_of_not_ge hsign)] at hlo hhi
        exact ⟨hpos, hlt, abs_le.mpr ⟨by dsimp [t]; linarith, by dsimp [t]; linarith⟩, hz⟩
    have hsplit : (∑ ρ ∈ S.filter (fun ρ => Nat.floor |ρ.im| = k), m ρ) ≤
        (∑ ρ ∈ S.filter (fun ρ => ρ ∈ criticalZeroSlice F t), m ρ) +
        (∑ ρ ∈ S.filter (fun ρ => ρ ∈ criticalZeroSlice F (-t)), m ρ) := by
      simp only [Finset.sum_filter, ← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun ρ hρ => ?_
      have hnneg (p : Prop) [Decidable p] : 0 ≤ (if p then m ρ else 0) := by
        split
        · exact hm ρ
        · exact le_rfl
      by_cases hk : Nat.floor |ρ.im| = k
      · rcases hincl ρ hρ hk with hp | hn
        · simp only [hk, ite_true, hp]
          exact le_add_of_nonneg_right (hnneg _)
        · simp only [hk, ite_true, hn]
          exact le_add_of_nonneg_left (hnneg _)
      · simp only [hk, ite_false]
        exact add_nonneg (hnneg _) (hnneg _)
    let U : ℝ := 2 * (q : ℝ) * ((k : ℝ) + 2)
    have hU : 2 ≤ U := by
      have k0 : (0 : ℝ) ≤ k := by positivity
      calc
        _ ≤ 2 * (1 : ℝ) * ((k : ℝ) + 2) := by linarith
        _ ≤ _ := by dsimp [U]; gcongr
    have hArg : 2 * (q : ℝ) * (2 + |t|) ≤ U ^ 2 := by
      rw [abs_of_nonneg ht]
      have h0 : 2 + t ≤ 2 * ((k : ℝ) + 2) := by dsimp [t]; linarith [Nat.cast_nonneg (α := ℝ) k]
      calc
        _ ≤ 2 * (q : ℝ) * (2 * ((k : ℝ) + 2)) := by gcongr
        _ = 2 * U := by dsimp [U]; ring
        _ ≤ _ := by nlinarith [mul_nonneg (show 0 ≤ U by linarith) (show 0 ≤ U - 2 by linarith)]
    have hlog := Real.log_le_log (show 0 < 2 * (q : ℝ) * (2 + |t|) by positivity) hArg
    rw [Real.log_pow] at hlog
    norm_num at hlog
    have hs := hsplit.trans (add_le_add (hCount' t) (hCount' (-t)))
    rw [abs_neg] at hs
    change _ ≤ (4 * K) * Real.log U
    have htBound := mul_le_mul_of_nonneg_left hlog hK.le
    exact hs.trans ((add_le_add htBound htBound).trans_eq (by ring))
  calc
    _ ≤ ∑ ρ ∈ S, ‖(analyticOrderNatAt F ρ : ℂ) * GoldbachSmoothing.kernel x (Real.sqrt x) ρ‖ :=
      norm_sum_le _ _
    _ = ∑ ρ ∈ S, m ρ * ‖GoldbachSmoothing.kernel x (Real.sqrt x) ρ‖ := by
      refine Finset.sum_congr rfl fun ρ _ => ?_
      simp [m]
    _ ≤ 256 * (4 * K) * Real.sqrt x * Real.log (2 * (q : ℝ) * x) ^ 2 :=
      smoothed_zero_sum_le hq hx (by positivity) S m (fun ρ _ => hm ρ) hLine hBucket
    _ = _ := by ring

end Goldbach

open Complex Set MeasureTheory
open scoped BigOperators Interval

namespace Goldbach

/- For a reference statement, see PrimeNumberTheoremAnd's ResidueCalcOnRectangles.lean at
   2c476fa6441c607096d93c8fc7ac0a227a655dae, licensed under Apache 2.0.
   The argument below uses the complex logarithm on each side of the rectangle. -/

/-- Counterclockwise boundary integral for the rectangle with real sides a and b
and imaginary sides c and d. -/
noncomputable def rectBoundaryIntegral (f : ℂ → ℂ) (a b c d : ℝ) : ℂ :=
  (∫ x : ℝ in a..b, f (x + c * I)) - (∫ x : ℝ in a..b, f (x + d * I)) +
    I * (∫ y : ℝ in c..d, f (b + y * I)) - I * (∫ y : ℝ in c..d, f (a + y * I))

private lemma integral_div_affine (u v : ℂ) (a b : ℝ)
    (hpath : ∀ t ∈ [[a, b]], (t : ℂ) * v + u ∈ slitPlane) :
    (∫ t : ℝ in a..b, v / ((t : ℂ) * v + u)) =
      log ((b : ℂ) * v + u) - log ((a : ℂ) * v + u) := by
  have hint : IntervalIntegrable (fun t : ℝ => v / ((t : ℂ) * v + u)) volume a b :=
    (continuousOn_const.div (by fun_prop) fun t ht => slitPlane_ne_zero (hpath t ht)).intervalIntegrable
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun s : ℝ => log ((s : ℂ) * v + u)) (fun t ht => ?_) hint
  have hreal : HasDerivAt (fun s : ℝ => (s : ℂ)) (1 : ℂ) t := by
    have hf : (ofRealCLM : ℝ → ℂ) = (fun s : ℝ => (s : ℂ)) := rfl
    simpa only [hf, ofRealCLM_apply, ofReal_one] using (ofRealCLM.hasDerivAt (x := t))
  have haff : HasDerivAt (fun s : ℝ => (s : ℂ) * v + u) v t := by
    simpa only [one_mul] using (hreal.mul_const v).add_const u
  simpa only [Function.comp_def, smul_eq_mul, div_eq_mul_inv] using
    (hasDerivAt_log (hpath t ht)).scomp t haff

private lemma horizontal_inv (p : ℂ) (a b y : ℝ) (hy : y ≠ p.im) :
    (∫ x : ℝ in a..b, ((x : ℂ) + y * I - p)⁻¹) =
      log ((b : ℂ) + y * I - p) - log ((a : ℂ) + y * I - p) := by
  have hs (t : ℝ) : (t : ℂ) * 1 + ((y : ℂ) * I - p) ∈ slitPlane := by
    apply mem_slitPlane_iff.mpr
    right
    simpa [add_im, sub_im, mul_im] using sub_ne_zero.mpr hy
  simpa only [mul_one, one_div, add_sub_assoc] using
    integral_div_affine ((y : ℂ) * I - p) 1 a b (fun t _ => hs t)

private lemma vertical_inv_right (p : ℂ) (x a b : ℝ) (hx : p.re < x) :
    I * (∫ y : ℝ in a..b, ((x : ℂ) + y * I - p)⁻¹) =
      log ((x : ℂ) + b * I - p) - log ((x : ℂ) + a * I - p) := by
  have hs (t : ℝ) : (t : ℂ) * I + ((x : ℂ) - p) ∈ slitPlane := by
    apply mem_slitPlane_iff.mpr
    left
    simpa [add_re, sub_re, mul_re] using sub_pos.mpr hx
  rw [← intervalIntegral.integral_const_mul]
  simpa only [div_eq_mul_inv, ← add_sub_assoc, add_comm ((x : ℂ))] using
    integral_div_affine ((x : ℂ) - p) I a b (fun t _ => hs t)

private lemma vertical_inv_left (p : ℂ) (x a b : ℝ) (hx : x < p.re) :
    I * (∫ y : ℝ in a..b, ((x : ℂ) + y * I - p)⁻¹) =
      log (-((x : ℂ) + b * I - p)) - log (-((x : ℂ) + a * I - p)) := by
  have harg (t : ℝ) : (t : ℂ) * (-I) + (p - (x : ℂ)) = -((x : ℂ) + t * I - p) := by ring
  have hs (t : ℝ) : (t : ℂ) * (-I) + (p - (x : ℂ)) ∈ slitPlane := by
    apply mem_slitPlane_iff.mpr
    left
    simpa [add_re, sub_re, mul_re, neg_re, neg_im] using sub_pos.mpr hx
  rw [← intervalIntegral.integral_const_mul]
  have h := integral_div_affine (p - (x : ℂ)) (-I) a b (fun t _ => hs t)
  simp only [harg] at h
  simpa only [div_eq_mul_inv, inv_neg, neg_mul, mul_neg, neg_neg] using h

private lemma log_sub_log_neg_pos {z : ℂ} (hz : 0 < z.im) :
    log z - log (-z) = (Real.pi : ℂ) * I := by
  apply Complex.ext
  · simp [sub_re, log_re, mul_re]
  · simp [sub_im, log_im, mul_im, arg_neg_eq_arg_sub_pi_of_im_pos hz]

private lemma log_sub_log_neg_neg {z : ℂ} (hz : z.im < 0) :
    log z - log (-z) = -(Real.pi : ℂ) * I := by
  apply Complex.ext
  · simp [sub_re, log_re, mul_re, neg_re]
  · simp [sub_im, log_im, mul_im, arg_neg_eq_arg_add_pi_of_im_neg hz]

/-- The rectangle encloses p strictly, and the reciprocal has residue one there. -/
theorem rectBoundaryIntegral_inv_sub {a b c d : ℝ} {p : ℂ}
    (ha : a < p.re) (hb : p.re < b) (hc : c < p.im) (hd : p.im < d) :
    rectBoundaryIntegral (fun z => (z - p)⁻¹) a b c d = 2 * (Real.pi : ℂ) * I := by
  have htop : 0 < ((a : ℂ) + d * I - p).im := by
    simpa [add_im, sub_im, mul_im] using sub_pos.mpr hd
  have hbot : ((a : ℂ) + c * I - p).im < 0 := by
    simpa [add_im, sub_im, mul_im] using sub_neg.mpr hc
  unfold rectBoundaryIntegral
  rw [horizontal_inv p a b c hc.ne, horizontal_inv p a b d hd.ne',
    vertical_inv_right p b c d hb, vertical_inv_left p a c d ha]
  calc
    _ = (log ((a : ℂ) + d * I - p) - log (-((a : ℂ) + d * I - p))) -
        (log ((a : ℂ) + c * I - p) - log (-((a : ℂ) + c * I - p))) := by ring
    _ = _ := by rw [log_sub_log_neg_pos htop, log_sub_log_neg_neg hbot]; ring

private lemma integral_decompose {a b : ℝ} {f g : ℂ → ℂ}
    (S : Finset ℂ) (r : ℂ → ℂ) (γ : ℝ → ℂ) (hγ : Continuous γ)
    (hg : ContinuousOn (g ∘ γ) [[a, b]]) (haway : ∀ t ∈ [[a, b]], γ t ∉ S)
    (he : ∀ t ∈ [[a, b]], f (γ t) = g (γ t) + ∑ p ∈ S, r p / (γ t - p)) :
    (∫ t : ℝ in a..b, f (γ t)) =
      (∫ t : ℝ in a..b, g (γ t)) + ∑ p ∈ S, r p * (∫ t : ℝ in a..b, (γ t - p)⁻¹) := by
  have hterms (p : ℂ) (hp : p ∈ S) :
      ContinuousOn (fun t : ℝ => r p / (γ t - p)) [[a, b]] := by
    have hnum : ContinuousOn (fun _ : ℝ => r p) [[a, b]] := continuousOn_const
    have hdenom : ContinuousOn (fun t : ℝ => γ t - p) [[a, b]] :=
      (hγ.sub continuous_const).continuousOn
    exact hnum.div hdenom fun t ht => sub_ne_zero.mpr fun htp => haway t ht (htp.symm ▸ hp)
  have hsum : ContinuousOn (fun t : ℝ => ∑ p ∈ S, r p / (γ t - p)) [[a, b]] :=
    continuousOn_finsetSum S hterms
  calc
    _ = ∫ t : ℝ in a..b, g (γ t) + ∑ p ∈ S, r p / (γ t - p) :=
      intervalIntegral.integral_congr he
    _ = (∫ t : ℝ in a..b, g (γ t)) + ∑ p ∈ S, ∫ t : ℝ in a..b, r p / (γ t - p) := by
      have hgi : IntervalIntegrable (fun t : ℝ => g (γ t)) volume a b := hg.intervalIntegrable
      have hsi : IntervalIntegrable (fun t : ℝ => ∑ p ∈ S, r p / (γ t - p)) volume a b :=
        hsum.intervalIntegrable
      rw [intervalIntegral.integral_add hgi hsi]
      congr 1
      exact intervalIntegral.integral_finsetSum (fun p hp => (hterms p hp).intervalIntegrable)
    _ = _ := by simp_rw [div_eq_mul_inv, intervalIntegral.integral_const_mul]

private lemma rect_sum_combine (S : Finset ℂ) (r bot top right left : ℂ → ℂ) :
    (∑ p ∈ S, r p * bot p) - (∑ p ∈ S, r p * top p) +
      I * (∑ p ∈ S, r p * right p) - I * (∑ p ∈ S, r p * left p) =
    ∑ p ∈ S, r p * (bot p - top p + I * right p - I * left p) := by
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun p _ => by ring

/-- Boundary integration computes the sum of the residues at interior simple
poles if subtracting the principal parts leaves a continuous remainder that
is complex differentiable away from the poles. -/
theorem rectBoundaryIntegral_eq_sum_residues {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d)
    (f g : ℂ → ℂ) (S : Finset ℂ) (r : ℂ → ℂ)
    (hpoles : ∀ p ∈ S, a < p.re ∧ p.re < b ∧ c < p.im ∧ p.im < d)
    (hg : ContinuousOn g (Icc a b ×ℂ Icc c d))
    (hgd : ∀ z ∈ (Ioo a b ×ℂ Ioo c d) \ (S : Set ℂ), DifferentiableAt ℂ g z)
    (hfg : EqOn f (fun z => g z + ∑ p ∈ S, r p / (z - p))
      ((Icc a b ×ℂ Icc c d) \ (S : Set ℂ))) :
    rectBoundaryIntegral f a b c d = (2 * (Real.pi : ℂ) * I) * ∑ p ∈ S, r p := by
  have hgc : ContinuousOn g ([[a, b]] ×ℂ [[c, d]]) := by
    simpa only [uIcc_of_le hab, uIcc_of_le hcd] using hg
  have hgd' : ∀ z ∈ (Ioo (min a b) (max a b) ×ℂ Ioo (min c d) (max c d)) \ (S : Set ℂ),
      DifferentiableAt ℂ g z := by
    simpa only [min_eq_left hab, max_eq_right hab, min_eq_left hcd, max_eq_right hcd] using hgd
  have hzero : rectBoundaryIntegral g a b c d = 0 := by
    simpa only [rectBoundaryIntegral, smul_eq_mul] using
      Complex.integral_boundary_rect_eq_zero_of_differentiable_on_off_countable
        g (⟨a, c⟩ : ℂ) (⟨b, d⟩ : ℂ) (S : Set ℂ) S.finite_toSet.countable hgc hgd'
  have edge {u v : ℝ} (γ : ℝ → ℂ) (hγ : Continuous γ)
      (hmem : MapsTo γ [[u, v]] (Icc a b ×ℂ Icc c d))
      (haway : ∀ t ∈ [[u, v]], γ t ∉ S) :=
    integral_decompose S r γ hγ (hg.comp hγ.continuousOn hmem) haway
      (fun t ht => hfg ⟨hmem ht, haway t ht⟩)
  have horizontal (y : ℝ) (hy : y ∈ Icc c d) (hy' : ∀ p ∈ S, y ≠ p.im) :=
    edge (u := a) (v := b) (fun x : ℝ => x + y * I) (by fun_prop)
      (fun t ht => by
        rw [mem_reProdIm]
        constructor
        · simpa [add_re, mul_re, uIcc_of_le hab] using ht
        · simpa [add_im, mul_im] using hy)
      (fun t _ hp => (hy' _ hp) (by simp [add_im, mul_im]))
  have vertical (x : ℝ) (hx : x ∈ Icc a b) (hx' : ∀ p ∈ S, x ≠ p.re) :=
    edge (u := c) (v := d) (fun y : ℝ => x + y * I) (by fun_prop)
      (fun t ht => by
        rw [mem_reProdIm]
        constructor
        · simpa [add_re, mul_re] using hx
        · simpa [add_im, mul_im, uIcc_of_le hcd] using ht)
      (fun t _ hp => (hx' _ hp) (by simp [add_re, mul_re]))
  have hdecomp :
      rectBoundaryIntegral f a b c d =
        rectBoundaryIntegral g a b c d +
          ∑ p ∈ S, r p * rectBoundaryIntegral (fun z => (z - p)⁻¹) a b c d := by
    unfold rectBoundaryIntegral
    rw [horizontal c ⟨le_rfl, hcd⟩ (fun p hp => (hpoles p hp).2.2.1.ne),
        horizontal d ⟨hcd, le_rfl⟩ (fun p hp => (hpoles p hp).2.2.2.ne'),
        vertical b ⟨hab, le_rfl⟩ (fun p hp => (hpoles p hp).2.1.ne'),
        vertical a ⟨le_rfl, hab⟩ (fun p hp => (hpoles p hp).1.ne)]
    rw [← rect_sum_combine]
    ring
  rw [hdecomp, hzero, zero_add, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p hp => ?_
  obtain ⟨ha, hb, hc, hd⟩ := hpoles p hp
  rw [rectBoundaryIntegral_inv_sub ha hb hc hd]
  ring

end Goldbach

open Filter Set
open scoped BigOperators Topology

namespace Goldbach

private lemma analyticAt_logDeriv_of_ne_zero {F : ℂ → ℂ} {w : ℂ}
    (hF : AnalyticAt ℂ F w) (hFw : F w ≠ 0) : AnalyticAt ℂ (logDeriv F) w :=
  hF.deriv.div hF hFw

/-- The weighted logarithmic derivative at a finite-order zero has principal
part equal to its order times the weight at that zero, divided by the local
coordinate. The same formula applies at order zero. -/
theorem logDeriv_mul_local_polar_part {F K : ℂ → ℂ} {w : ℂ}
    (hF : AnalyticAt ℂ F w) (horder : analyticOrderAt F w ≠ ⊤)
    (hK : AnalyticAt ℂ K w) :
    ∃ G : ℂ → ℂ, AnalyticAt ℂ G w ∧
      (fun z => logDeriv F z * K z - (analyticOrderNatAt F w : ℂ) * K w / (z - w))
        =ᶠ[𝓝[≠] w] G := by
  obtain ⟨A, hA, hA0, hfactor⟩ := hF.analyticOrderAt_ne_top.mp horder
  let m := analyticOrderNatAt F w
  let D : ℂ → ℂ := fun z => z - w
  have hD : Differentiable ℂ D := by dsimp [D]; fun_prop
  have hlogD (z : ℂ) : logDeriv D z = 1 / (z - w) := by
    simp [D, logDeriv_apply]
  have hfac : F =ᶠ[𝓝 w] fun z => D z ^ m * A z := by
    simpa only [D, m, smul_eq_mul] using hfactor
  have hz_ne : ∀ᶠ z in 𝓝[≠] w, z ≠ w := by
    simpa using (eventually_mem_nhdsWithin (a := w) (s := {w}ᶜ))
  have hlog : logDeriv F =ᶠ[𝓝[≠] w] fun z => (m : ℂ) / (z - w) + logDeriv A z := by
    filter_upwards [(logDeriv_congr_nhds hfac).filter_mono nhdsWithin_le_nhds,
      hA.eventually_analyticAt.filter_mono nhdsWithin_le_nhds,
      (hA.continuousAt.eventually_ne hA0).filter_mono nhdsWithin_le_nhds, hz_ne]
      with z hdz hAz hAnz hzne
    have hDz : D z ≠ 0 := sub_ne_zero.mpr hzne
    rw [hdz, logDeriv_fun_mul (f := fun t => D t ^ m) (g := A) z (pow_ne_zero m hDz) hAnz
      (hD.differentiableAt.pow m) hAz.differentiableAt,
      logDeriv_fun_pow (f := D) hD.differentiableAt m, hlogD, mul_one_div]
  refine ⟨fun z => (m : ℂ) * dslope K w z + logDeriv A z * K z, ?_, ?_⟩
  · exact (analyticAt_const.mul (hK.dslope w)).add
      ((analyticAt_logDeriv_of_ne_zero hA hA0).mul hK)
  · filter_upwards [hlog, hz_ne] with z hz hzne
    have hds : dslope K w z = (K z - K w) / (z - w) := by
      apply (eq_div_iff (sub_ne_zero.mpr hzne)).mpr
      simpa only [smul_eq_mul, mul_comm] using sub_smul_dslope K w z
    change logDeriv F z * K z - (m : ℂ) * K w / (z - w) =
      (m : ℂ) * dslope K w z + logDeriv A z * K z
    rw [hz, hds]
    ring

private lemma analyticAt_principal_term (r p z : ℂ) (hz : z ≠ p) :
    AnalyticAt ℂ (fun t : ℂ => r / (t - p)) z := by
  have hnum : AnalyticAt ℂ (fun _ : ℂ => r) z := analyticAt_const
  have hdenom : AnalyticAt ℂ (fun t : ℂ => t - p) z := by fun_prop
  exact hnum.div hdenom (sub_ne_zero.mpr hz)

/-- Subtracting all principal parts of a weighted logarithmic derivative
leaves an analytic remainder. The equality is stated away from the finitely
many points where the principal parts have poles. -/
theorem logDeriv_mul_exists_analytic_remainder {F K : ℂ → ℂ} {U : Set ℂ}
    (S : Finset ℂ) (hSU : (S : Set ℂ) ⊆ U) (hF : AnalyticOnNhd ℂ F U)
    (hK : AnalyticOnNhd ℂ K U) (hzeros : ∀ z ∈ U, F z = 0 → z ∈ S)
    (horder : ∀ p ∈ S, analyticOrderAt F p ≠ ⊤) :
    ∃ G : ℂ → ℂ, AnalyticOnNhd ℂ G U ∧
      EqOn (fun z => logDeriv F z * K z)
        (fun z => G z + ∑ p ∈ S, (analyticOrderNatAt F p : ℂ) * K p / (z - p))
        (U \ (S : Set ℂ)) := by
  classical
  let r : ℂ → ℂ := fun p => (analyticOrderNatAt F p : ℂ) * K p
  have hlocal (p : ℂ) (hp : p ∈ S) :
      ∃ g : ℂ → ℂ, AnalyticAt ℂ g p ∧
        (fun z => logDeriv F z * K z - r p / (z - p)) =ᶠ[𝓝[≠] p] g :=
    logDeriv_mul_local_polar_part (hF p (hSU hp)) (horder p hp) (hK p (hSU hp))
  choose localPart hlocalA hlocalEq using hlocal
  let regular : ℂ → ℂ := fun z => logDeriv F z * K z - ∑ p ∈ S, r p / (z - p)
  let G : ℂ → ℂ := fun z =>
    if hz : z ∈ S then localPart z hz z - ∑ p ∈ S.erase z, r p / (z - p) else regular z
  refine ⟨G, ?_, ?_⟩
  · intro z hz
    by_cases hzS : z ∈ S
    · have havoid : ∀ᶠ t in 𝓝 z, t ∉ S.erase z :=
        (S.erase z).finite_toSet.isClosed.isOpen_compl.mem_nhds (by simp)
      have heq : ∀ᶠ t in 𝓝 z, t ≠ z →
          logDeriv F t * K t - r z / (t - z) = localPart z hzS t := by
        simpa using (eventually_nhdsWithin_iff.mp (hlocalEq z hzS))
      have hG : G =ᶠ[𝓝 z] fun t =>
          localPart z hzS t - ∑ p ∈ S.erase z, r p / (t - p) := by
        filter_upwards [havoid, heq] with t ht hEq
        by_cases htz : t = z
        · subst t
          simp only [G, dite_eq_left hzS]
        · have htS : t ∉ S := fun h => ht (Finset.mem_erase.mpr ⟨htz, h⟩)
          simp only [G, dite_eq_right htS, regular]
          rw [← Finset.sum_erase_add S (fun p => r p / (t - p)) hzS, ← hEq htz]
          ring
      have hA : AnalyticAt ℂ (fun t => ∑ p ∈ S.erase z, r p / (t - p)) z :=
        (S.erase z).analyticAt_fun_sum fun p hp =>
          analyticAt_principal_term (r p) p z (Finset.ne_of_mem_erase hp).symm
      exact ((hlocalA z hzS).sub hA).congr hG.symm
    · have havoid : ∀ᶠ t in 𝓝 z, t ∉ S :=
        S.finite_toSet.isClosed.isOpen_compl.mem_nhds hzS
      have hG : G =ᶠ[𝓝 z] regular := by
        filter_upwards [havoid] with t ht
        simp only [G, dite_eq_right ht]
      have hFz : F z ≠ 0 := fun hzF => hzS (hzeros z hz hzF)
      have hsum : AnalyticAt ℂ (fun t => ∑ p ∈ S, r p / (t - p)) z :=
        S.analyticAt_fun_sum fun p hp =>
          analyticAt_principal_term (r p) p z (fun h => hzS (h.symm ▸ hp))
      exact (((analyticAt_logDeriv_of_ne_zero (hF z hz) hFz).mul (hK z hz)).sub hsum).congr
        hG.symm
  · intro z hz
    have hzS : z ∉ S := hz.2
    change logDeriv F z * K z = G z + ∑ p ∈ S, r p / (z - p)
    simp only [G, dite_eq_right hzS, regular, sub_add_cancel]

end Goldbach

open Complex Filter Set MeasureTheory
open scoped BigOperators Interval Topology

namespace Goldbach

/-- Finite contour identity for the weighted logarithmic derivative with the
principal pole at one restored explicitly. -/
theorem rectBoundaryIntegral_neg_logDeriv_add_pole_mul
    {a b c d : ℝ} (F K : ℂ → ℂ) (S : Finset ℂ) (δ : ℂ)
    (ha : a < 1) (hb : 1 < b) (hc : c < 0) (hd : 0 < d)
    (hF : AnalyticOnNhd ℂ F (Icc a b ×ℂ Icc c d))
    (hK : AnalyticOnNhd ℂ K (Icc a b ×ℂ Icc c d))
    (hzeros : ∀ z ∈ Icc a b ×ℂ Icc c d, F z = 0 ↔ z ∈ S)
    (hinterior : ∀ p ∈ S, a < p.re ∧ p.re < b ∧ c < p.im ∧ p.im < d)
    (horder : ∀ p ∈ S, analyticOrderAt F p ≠ ⊤) (hF1 : F 1 ≠ 0) :
    rectBoundaryIntegral (fun z => (-logDeriv F z + δ / (z - 1)) * K z) a b c d =
      (2 * (Real.pi : ℂ) * I) * (δ * K 1 - ∑ p ∈ S, (analyticOrderNatAt F p : ℂ) * K p) := by
  classical
  let U := Icc a b ×ℂ Icc c d
  let T := insert (1 : ℂ) S
  let r : ℂ → ℂ := fun p => (analyticOrderNatAt F p : ℂ) * K p
  let coeff : ℂ → ℂ := fun p => if p = 1 then δ * K 1 else -r p
  have h1U : (1 : ℂ) ∈ U := by
    exact mem_reProdIm.mpr ⟨by simpa only [one_re] using Set.mem_Icc.mpr ⟨ha.le, hb.le⟩,
      by simpa only [one_im] using Set.mem_Icc.mpr ⟨hc.le, hd.le⟩⟩
  have h1S : (1 : ℂ) ∉ S := fun h => hF1 ((hzeros 1 h1U).mpr h)
  have hSU : (S : Set ℂ) ⊆ U := by
    intro p hp
    obtain ⟨hpa, hpb, hpc, hpd⟩ := hinterior p hp
    exact mem_reProdIm.mpr ⟨⟨hpa.le, hpb.le⟩, ⟨hpc.le, hpd.le⟩⟩
  have hT : ∀ p ∈ T, a < p.re ∧ p.re < b ∧ c < p.im ∧ p.im < d := by
    intro p hp
    rcases Finset.mem_insert.mp hp with rfl | hp
    · simpa only [one_re, one_im] using And.intro ha (And.intro hb (And.intro hc hd))
    · exact hinterior p hp
  have hcoeff1 : coeff 1 = δ * K 1 := ite_eq_left rfl
  have hcoeff (p : ℂ) (hp : p ∈ S) : coeff p = -r p := by
    have hp1 : p ≠ (1 : ℂ) := fun heq => h1S (heq ▸ hp)
    exact ite_eq_right hp1
  have hsum (z : ℂ) :
      (∑ p ∈ T, coeff p / (z - p)) =
        δ * K 1 / (z - 1) - ∑ p ∈ S, r p / (z - p) := by
    have hsumS : (∑ p ∈ S, coeff p / (z - p)) = -(∑ p ∈ S, r p / (z - p)) := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun p hp => by rw [hcoeff p hp, neg_div]
    change (∑ p ∈ insert (1 : ℂ) S, coeff p / (z - p)) = _
    rw [Finset.sum_insert h1S, hcoeff1, hsumS]
    exact (sub_eq_add_neg _ _).symm
  have hsum_coeff : (∑ p ∈ T, coeff p) = δ * K 1 - ∑ p ∈ S, r p := by
    have hsumS : (∑ p ∈ S, coeff p) = -(∑ p ∈ S, r p) := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl hcoeff
    change (∑ p ∈ insert (1 : ℂ) S, coeff p) = _
    rw [Finset.sum_insert h1S, hcoeff1, hsumS, sub_eq_add_neg]
  obtain ⟨G, hG, hG_eq⟩ := logDeriv_mul_exists_analytic_remainder S hSU hF hK
    (fun z hz => (hzeros z hz).mp) horder
  let J : ℂ → ℂ := fun z => -G z + δ * dslope K 1 z
  have hJ : AnalyticOnNhd ℂ J U := by
    intro z hz
    exact (hG z hz).neg.add (analyticAt_const.mul ((hK z hz).dslope 1))
  have hJ_diff : ∀ z ∈ (Ioo a b ×ℂ Ioo c d) \ (T : Set ℂ), DifferentiableAt ℂ J z := by
    intro z hz
    obtain ⟨hr, hi⟩ := mem_reProdIm.mp hz.1
    exact (hJ z (mem_reProdIm.mpr ⟨Ioo_subset_Icc_self hr, Ioo_subset_Icc_self hi⟩)).differentiableAt
  have hEq : EqOn (fun z => (-logDeriv F z + δ / (z - 1)) * K z)
      (fun z => J z + ∑ p ∈ T, coeff p / (z - p)) (U \ (T : Set ℂ)) := by
    intro z hz
    have hzT : z ∉ T := hz.2
    have hzS : z ∉ S := fun h => hzT (Finset.mem_insert_of_mem h)
    have hz1 : z ≠ (1 : ℂ) := fun h => hzT (Finset.mem_insert.mpr (Or.inl h))
    have hGK := hG_eq ⟨hz.1, hzS⟩
    change logDeriv F z * K z = G z + ∑ p ∈ S, r p / (z - p) at hGK
    have hds : dslope K 1 z = (K z - K 1) / (z - 1) := by
      apply (eq_div_iff (sub_ne_zero.mpr hz1)).mpr
      simpa only [smul_eq_mul, mul_comm] using sub_smul_dslope K 1 z
    change (-logDeriv F z + δ / (z - 1)) * K z =
      (-G z + δ * dslope K 1 z) + ∑ p ∈ T, coeff p / (z - p)
    rw [hsum, hds]
    calc
      _ = -(logDeriv F z * K z) + δ / (z - 1) * K z := by ring
      _ = _ := by rw [hGK]; ring
  rw [rectBoundaryIntegral_eq_sum_residues (ha.le.trans hb.le) (hc.le.trans hd.le)
    _ J T coeff hT hJ.continuousOn hJ_diff hEq, hsum_coeff]

/-- Solve a rectangular contour identity for its right vertical integral. -/
theorem right_vertical_integral_of_rect {f : ℂ → ℂ} {a b c d : ℝ} {R : ℂ}
    (h : rectBoundaryIntegral f a b c d = 2 * (Real.pi : ℂ) * I * R) :
    (∫ y : ℝ in c..d, f (b + y * I)) =
      (∫ y : ℝ in c..d, f (a + y * I)) + 2 * (Real.pi : ℂ) * R +
        I * ((∫ x : ℝ in a..b, f (x + c * I)) - ∫ x : ℝ in a..b, f (x + d * I)) := by
  unfold rectBoundaryIntegral at h
  set bottom := (∫ x : ℝ in a..b, f (x + c * I))
  set top := (∫ x : ℝ in a..b, f (x + d * I))
  set left := (∫ y : ℝ in c..d, f (a + y * I))
  set right := (∫ y : ℝ in c..d, f (b + y * I))
  calc
    right = left - I * (bottom - top + I * right - I * left) + I * (bottom - top) := by
      ring_nf
      simp only [I_sq]
      ring
    _ = _ := by
      rw [h]
      ring_nf
      simp only [I_sq]
      ring

end Goldbach

open Filter MeasureTheory
open scoped Topology Interval

namespace Goldbach

/-- Pass from an eventual family of finite contour identities to a bound on
the normalized right-hand limit. The left integrals and the finite residue
sums need only be bounded. -/
theorem scaled_contour_error_le {ι E : Type*} {l : Filter ι} [NeBot l]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {R L Z H : ι → E} {fullRight main : E} {scale Lbound Zbound : ℝ}
    (hscale : 0 < scale) (hR : Tendsto R l (𝓝 fullRight)) (hH : Tendsto H l (𝓝 0))
    (hrect : ∀ᶠ i in l, R i = L i + scale • (main - Z i) + H i)
    (hL : ∀ᶠ i in l, ‖L i‖ ≤ Lbound) (hZ : ∀ᶠ i in l, ‖Z i‖ ≤ Zbound) :
    ‖(1 / scale) • fullRight - main‖ ≤ (1 / scale) * Lbound + Zbound := by
  have hfactor : 0 ≤ 1 / scale := one_div_nonneg.mpr hscale.le
  have hlim : Tendsto (fun i => ‖(1 / scale) • (R i - H i) - main‖) l
      (𝓝 ‖(1 / scale) • fullRight - main‖) := by
    simpa only [sub_zero] using (((hR.sub hH).const_smul (1 / scale)).sub_const main).norm
  refine le_of_tendsto hlim ?_
  filter_upwards [hrect, hL, hZ] with i hi hLi hZi
  have herror : (1 / scale) • (R i - H i) - main = (1 / scale) • L i - Z i := by
    rw [hi, add_sub_cancel_right, smul_add, smul_smul, one_div_mul_cancel hscale.ne', one_smul]
    abel
  have hLn : ‖(1 / scale) • L i‖ ≤ (1 / scale) * Lbound := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hfactor]
    exact mul_le_mul_of_nonneg_left hLi hfactor
  rw [herror]
  exact (norm_sub_le _ _).trans (add_le_add hLn hZi)

/-- Apply the finite contour bounds to the full right vertical integral when
the endpoint heights diverge and the right integrand is Bochner integrable. -/
theorem vertical_contour_error_le {ι E : Type*} {l : Filter ι}
    [NeBot l] [IsCountablyGenerated l] [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} (hf : Integrable f) {lower upper : ι → ℝ}
    (hlower : Tendsto lower l atBot) (hupper : Tendsto upper l atTop)
    {L Z H : ι → E} {main : E} {Lbound Zbound : ℝ}
    (hH : Tendsto H l (𝓝 0))
    (hrect : ∀ᶠ i in l,
      (∫ t : ℝ in lower i..upper i, f t) = L i + (2 * Real.pi) • (main - Z i) + H i)
    (hL : ∀ᶠ i in l, ‖L i‖ ≤ Lbound) (hZ : ∀ᶠ i in l, ‖Z i‖ ≤ Zbound) :
    ‖(1 / (2 * Real.pi)) • (∫ t : ℝ, f t) - main‖ ≤
      (1 / (2 * Real.pi)) * Lbound + Zbound :=
  scaled_contour_error_le (mul_pos zero_lt_two Real.pi_pos)
    (intervalIntegral_tendsto_integral hf hlower hupper) hH hrect hL hZ

end Goldbach

open Complex Filter MeasureTheory
open scoped Interval

namespace GoldbachSmoothing

private lemma rpow_eq_sqrt_rpow_mul_two {x : ℝ} (hx : 0 ≤ x) (r : ℝ) :
    x ^ r = (Real.sqrt x) ^ (2 * r) := by
  rw [Real.rpow_mul (Real.sqrt_nonneg x), Real.rpow_two, Real.sq_sqrt hx]

private lemma add_sqrt_rpow_le {x r : ℝ} (hx : 2 ≤ x) (hr : 0 ≤ r) (hr' : r ≤ 2) :
    (x + Real.sqrt x) ^ r ≤ 4 * (Real.sqrt x) ^ (2 * r) := by
  have hx0 : 0 ≤ x := by linarith
  have hsx : Real.sqrt x ≤ x := Real.sqrt_le_self_iff.mpr (Or.inr (by linarith))
  have hp : (2 : ℝ) ^ r ≤ 4 := by
    calc
      _ ≤ (2 : ℝ) ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hr'
      _ = _ := by norm_num [Real.rpow_two]
  calc
    _ ≤ (2 * x) ^ r := Real.rpow_le_rpow (by positivity) (by linarith) hr
    _ = (2 : ℝ) ^ r * x ^ r := Real.mul_rpow (by norm_num) hx0
    _ ≤ 4 * x ^ r := mul_le_mul_of_nonneg_right hp (Real.rpow_nonneg hx0 _)
    _ = _ := by rw [rpow_eq_sqrt_rpow_mul_two hx0 r]

/-- Interpolating the linear and quadratic bounds at height square root x
gives a uniform integrable envelope on the line with real part 9/20. -/
theorem norm_left_vertical_kernel_le {x : ℝ} (hx : 2 ≤ x) (t : ℝ) :
    ‖kernel x (Real.sqrt x) (((9 / 20 : ℝ) : ℂ) + (t : ℂ) * I)‖ ≤
      40 * Real.sqrt x * (1 + |t|) ^ (-(11 / 10 : ℝ)) := by
  let h := Real.sqrt x
  let u := 1 + |t|
  let s : ℂ := ((9 / 20 : ℝ) : ℂ) + (t : ℂ) * I
  have hx0 : 0 < x := by linarith
  have hh : 0 < h := Real.sqrt_pos.2 hx0
  have hu : 0 < u := by dsimp [u]; positivity
  have hre : s.re = 9 / 20 := by simp [s]
  have hsim : s.im = t := by simp [s]
  have hn : u / 4 ≤ ‖s‖ := by
    have hr : (9 / 20 : ℝ) ≤ ‖s‖ := hre ▸ re_le_norm s
    have hi : |t| ≤ ‖s‖ := by simpa only [hsim] using abs_im_le_norm s
    dsimp [u]
    linarith
  have hn' : u / 2 ≤ ‖s + 1‖ := by
    have hr : (9 / 20 : ℝ) + 1 ≤ ‖s + 1‖ := by
      simpa only [add_re, hre, one_re] using re_le_norm (s + 1)
    have hi : |t| ≤ ‖s + 1‖ := by
      simpa only [add_im, hsim, one_im, add_zero] using abs_im_le_norm (s + 1)
    dsimp [u]
    linarith
  have hlow : ‖kernel x h s‖ ≤ 16 * h ^ (9 / 10 : ℝ) / u := by
    have hs : 0 < s.re := by rw [hre]; norm_num
    have hnum : (x + h) ^ s.re ≤ 4 * h ^ (9 / 10 : ℝ) := by
      have hl := add_sqrt_rpow_le (r := 9 / 20) hx (by norm_num) (by norm_num)
      rw [hre]
      change (x + Real.sqrt x) ^ (9 / 20 : ℝ) ≤ 4 * (Real.sqrt x) ^ (9 / 10 : ℝ)
      convert hl using 1
      norm_num
    calc
      _ ≤ (x + h) ^ s.re / ‖s‖ := norm_kernel_le hx0 hh hs
      _ ≤ (4 * h ^ (9 / 10 : ℝ)) / (u / 4) :=
        (div_le_div_of_nonneg_right hnum (norm_nonneg _)).trans
          (div_le_div_of_nonneg_left (by positivity) (by positivity) hn)
      _ = _ := by rw [div_div_eq_mul_div]; ring
  have hhigh : ‖kernel x h s‖ ≤ 40 * h ^ (19 / 10 : ℝ) / u ^ 2 := by
    have hr : s.re + 1 = (29 / 20 : ℝ) := by rw [hre]; norm_num
    have hnum : (x + h) ^ (s.re + 1) + x ^ (s.re + 1) ≤ 5 * h ^ (29 / 10 : ℝ) := by
      rw [hr]
      have h₁ := add_sqrt_rpow_le (r := 29 / 20) hx (by norm_num) (by norm_num)
      have h₂ : x ^ (29 / 20 : ℝ) = h ^ (29 / 10 : ℝ) := by
        convert rpow_eq_sqrt_rpow_mul_two hx0.le (29 / 20 : ℝ) using 1
        norm_num [h]
      have hb : (x + h) ^ (29 / 20 : ℝ) ≤ 4 * h ^ (29 / 10 : ℝ) := by
        convert h₁ using 1
        norm_num [h]
      linarith
    have hden : h * (u / 4) * (u / 2) ≤ h * ‖s‖ * ‖s + 1‖ :=
      mul_le_mul (mul_le_mul_of_nonneg_left hn hh.le) hn' (by positivity) (by positivity)
    have hdiv : h ^ (29 / 10 : ℝ) / h = h ^ (19 / 10 : ℝ) := by
      rw [show (19 / 10 : ℝ) = 29 / 10 - 1 by norm_num, Real.rpow_sub hh, Real.rpow_one]
    calc
      _ ≤ ((x + h) ^ (s.re + 1) + x ^ (s.re + 1)) / (h * ‖s‖ * ‖s + 1‖) :=
        norm_kernel_le_tail hx0 hh
      _ ≤ (5 * h ^ (29 / 10 : ℝ)) / (h * (u / 4) * (u / 2)) :=
        (div_le_div_of_nonneg_right hnum (by positivity)).trans
          (div_le_div_of_nonneg_left (by positivity) (by positivity) hden)
      _ = 40 * (h ^ (29 / 10 : ℝ) / h) / u ^ 2 := by
        field_simp [hh.ne', hu.ne']
        ring
      _ = _ := by rw [hdiv]
  change ‖kernel x h s‖ ≤ 40 * h * u ^ (-(11 / 10 : ℝ))
  by_cases ht : u ≤ h
  · have hpowu : u ^ (1 / 10 : ℝ) ≤ h ^ (1 / 10 : ℝ) :=
      Real.rpow_le_rpow hu.le ht (by norm_num)
    have huinv : u⁻¹ = u ^ (1 / 10 : ℝ) * u ^ (-(11 / 10 : ℝ)) := by
      rw [← Real.rpow_add hu]
      norm_num [Real.rpow_neg_one]
    have hpowh : h ^ (9 / 10 : ℝ) * h ^ (1 / 10 : ℝ) = h := by
      rw [← Real.rpow_add hh]
      norm_num
    calc
      _ ≤ 16 * h ^ (9 / 10 : ℝ) / u := hlow
      _ ≤ 40 * h ^ (9 / 10 : ℝ) / u :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (by norm_num) (by positivity)) hu.le
      _ = 40 * h ^ (9 / 10 : ℝ) * u ^ (1 / 10 : ℝ) * u ^ (-(11 / 10 : ℝ)) := by
        rw [div_eq_mul_inv, huinv]
        ring
      _ ≤ 40 * h ^ (9 / 10 : ℝ) * h ^ (1 / 10 : ℝ) * u ^ (-(11 / 10 : ℝ)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpowu (by positivity)) (by positivity)
      _ = _ := by rw [mul_assoc 40, hpowh]
  · have hpowu : h ^ (9 / 10 : ℝ) ≤ u ^ (9 / 10 : ℝ) :=
      Real.rpow_le_rpow hh.le (le_of_not_ge ht) (by norm_num)
    have hpowh : h ^ (19 / 10 : ℝ) = h * h ^ (9 / 10 : ℝ) := by
      rw [show (19 / 10 : ℝ) = 9 / 10 + 1 by norm_num, Real.rpow_add_one hh.ne', mul_comm]
    have huTail : u ^ (9 / 10 : ℝ) / u ^ 2 = u ^ (-(11 / 10 : ℝ)) := by
      rw [show (-(11 / 10 : ℝ)) = 9 / 10 - 2 by norm_num, Real.rpow_sub hu, Real.rpow_two]
    calc
      _ ≤ 40 * h ^ (19 / 10 : ℝ) / u ^ 2 := hhigh
      _ = (40 * h) * h ^ (9 / 10 : ℝ) / u ^ 2 := by rw [hpowh, mul_assoc]
      _ ≤ (40 * h) * u ^ (9 / 10 : ℝ) / u ^ 2 :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hpowu (by positivity)) (by positivity)
      _ = _ := by rw [mul_div_assoc, huTail]

private lemma log_left_vertical_le {x q : ℝ} (hx : 2 ≤ x) (hq : 1 ≤ q) (t : ℝ) :
    Real.log (2 * q * (2 + |t|)) ≤ 21 * Real.log (2 * q * x) ^ 2 *
      (1 + |t|) ^ (1 / 20 : ℝ) := by
  let u := 1 + |t|
  let L := Real.log (2 * q * x)
  have hu1 : 1 ≤ u := by dsimp [u]; linarith [abs_nonneg t]
  have hu : 0 < u := zero_lt_one.trans_le hu1
  have hq2 : 0 < 2 * q := by linarith
  have hx0 : 0 < x := by linarith
  have h4 : (4 : ℝ) ≤ 2 * q * x := by
    have hf : (2 : ℝ) * 2 ≤ (2 * q) * x :=
      mul_le_mul (by linarith) hx (by norm_num) hq2.le
    norm_num at hf
    exact hf
  have hL : 1 ≤ L := by
    have hlog2 := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 2 by norm_num)
    norm_num at hlog2
    have hlog4 : (1 : ℝ) ≤ Real.log 4 := by
      rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
      linarith
    exact hlog4.trans (Real.log_le_log (by norm_num) h4)
  have hLpos : 0 ≤ L := zero_le_one.trans hL
  have hLsq : L ≤ L ^ 2 := by nlinarith [mul_nonneg hLpos (sub_nonneg.mpr hL)]
  have huPow : 1 ≤ u ^ (1 / 20 : ℝ) :=
    Real.one_le_rpow hu1 (by norm_num)
  have harg : 2 + |t| ≤ x * u := by
    calc
      _ ≤ 2 * u := by dsimp [u]; linarith [abs_nonneg t]
      _ ≤ _ := mul_le_mul_of_nonneg_right hx hu.le
  have hlog : Real.log (2 * q * (2 + |t|)) ≤ L + Real.log u := by
    have harg' := mul_le_mul_of_nonneg_left harg hq2.le
    rw [← mul_assoc] at harg'
    have hp := Real.log_le_log (show 0 < 2 * q * (2 + |t|) by positivity) harg'
    rwa [Real.log_mul (mul_ne_zero hq2.ne' hx0.ne') hu.ne'] at hp
  have hlogu : Real.log u ≤ 20 * u ^ (1 / 20 : ℝ) := by
    have h := Real.log_le_rpow_div hu.le (show (0 : ℝ) < 1 / 20 by norm_num)
    convert h using 1
    ring
  have hLu : L ≤ L ^ 2 * u ^ (1 / 20 : ℝ) :=
    hLsq.trans (le_mul_of_one_le_right (sq_nonneg L) huPow)
  have h1L : (1 : ℝ) ≤ L ^ 2 := hL.trans hLsq
  have h20 : 20 * u ^ (1 / 20 : ℝ) ≤ 20 * (L ^ 2 * u ^ (1 / 20 : ℝ)) := by
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    exact le_mul_of_one_le_left (by positivity) h1L
  change _ ≤ 21 * L ^ 2 * u ^ (1 / 20 : ℝ)
  linarith

/-- The left contour integral admits a bound uniform in its endpoint heights,
with an absolute constant and the requested logarithmic dependence. -/
theorem norm_left_vertical_integral_le :
    ∃ D : ℝ, 0 < D ∧
      ∀ (g : ℝ → ℂ) (x q A a b : ℝ), 2 ≤ x → 1 ≤ q → 0 ≤ A → Continuous g →
        (∀ t, ‖g t‖ ≤ A * Real.log (2 * q * (2 + |t|))) →
        ‖∫ t : ℝ in a..b, g t * kernel x (Real.sqrt x) (((9 / 20 : ℝ) : ℂ) + (t : ℂ) * I)‖ ≤
          D * A * Real.sqrt x * Real.log (2 * q * x) ^ 2 := by
  let w : ℝ → ℝ := fun t => (1 + |t|) ^ (-(21 / 20 : ℝ))
  have hwNonneg (t : ℝ) : 0 ≤ w t := by dsimp [w]; positivity
  have hw : Integrable w := by
    have hw' := integrable_one_add_norm (E := ℝ) (μ := volume) (r := 21 / 20) (by norm_num)
    simpa only [w, Real.norm_eq_abs] using hw'
  have hwIntegral : 0 ≤ ∫ t : ℝ, w t := integral_nonneg hwNonneg
  refine ⟨840 * (1 + ∫ t : ℝ, w t), by positivity, ?_⟩
  intro g x q A a b hx hq hA hg hbound
  let h := Real.sqrt x
  let L := Real.log (2 * q * x)
  let C := 840 * A * h * L ^ 2
  let f : ℝ → ℂ := fun t => g t * kernel x h (((9 / 20 : ℝ) : ℂ) + (t : ℂ) * I)
  have hC : 0 ≤ C := by dsimp [C, h]; positivity
  have point (t : ℝ) : ‖f t‖ ≤ C * w t := by
    let u := 1 + |t|
    have hu : 0 < u := by dsimp [u]; positivity
    have hgBound : ‖g t‖ ≤ A * (21 * L ^ 2 * u ^ (1 / 20 : ℝ)) :=
      (hbound t).trans (mul_le_mul_of_nonneg_left (log_left_vertical_le hx hq t) hA)
    change ‖g t * kernel x h (((9 / 20 : ℝ) : ℂ) + (t : ℂ) * I)‖ ≤ _
    rw [norm_mul]
    calc
      _ ≤ (A * (21 * L ^ 2 * u ^ (1 / 20 : ℝ))) * (40 * h * u ^ (-(11 / 10 : ℝ))) :=
        mul_le_mul hgBound (norm_left_vertical_kernel_le hx t) (norm_nonneg _) (by positivity)
      _ = C * (u ^ (1 / 20 : ℝ) * u ^ (-(11 / 10 : ℝ))) := by dsimp [C]; ring
      _ = _ := by rw [← Real.rpow_add hu]; norm_num [w, u]
  have hker : Integrable (fun t : ℝ => kernel x h (((9 / 20 : ℝ) : ℂ) + (t : ℂ) * I)) :=
    kernel_verticalIntegrable (by linarith : 0 < x) (Real.sqrt_pos.2 (by linarith)) (by norm_num)
  have hmajor : Integrable (fun t : ℝ => C * w t) := hw.const_mul C
  have hfi : Integrable f :=
    hmajor.mono' (hg.aestronglyMeasurable.mul hker.aestronglyMeasurable)
      (Eventually.of_forall point)
  change ‖∫ t : ℝ in a..b, f t‖ ≤ _
  calc
    _ ≤ ∫ t in Ι a b, ‖f t‖ := intervalIntegral.norm_integral_le_integral_norm_uIoc
    _ ≤ ∫ t : ℝ, ‖f t‖ := setIntegral_le_integral hfi.norm (ae_of_all _ fun _ => norm_nonneg _)
    _ ≤ ∫ t : ℝ, C * w t := integral_mono hfi.norm hmajor point
    _ = C * ∫ t : ℝ, w t := integral_const_mul C w
    _ ≤ C * (1 + ∫ t : ℝ, w t) := mul_le_mul_of_nonneg_left (by linarith) hC
    _ = _ := by dsimp [C, h, L]; ring

end GoldbachSmoothing

namespace Goldbach

open Filter Set
open scoped Topology

private theorem horizontal_log_sq_le {q t : ℝ} (hq : 1 ≤ q) (ht : 1 ≤ |t|) :
    Real.log (2 * q * (2 + |t|)) ^ 2 ≤ 24 * q * |t| := by
  let v : ℝ := 2 * q * (2 + |t|)
  have hq₀ : 0 < q := by linarith only [hq]
  have hv₁ : 1 ≤ v := one_le_mul_of_one_le_of_one_le (by linarith only [hq])
    (by linarith only [ht])
  have hv₀ := zero_le_one.trans hv₁
  have hsqrt : Real.sqrt v ^ 2 = v := Real.sq_sqrt hv₀
  have hlog : Real.log v ≤ 2 * Real.sqrt v := calc
    _ = Real.log ((Real.sqrt v) ^ 2) := by rw [hsqrt]
    _ = 2 * Real.log (Real.sqrt v) := by rw [Real.log_pow]; norm_num
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.log_le_self (Real.sqrt_nonneg _)) (by norm_num)
  change Real.log v ^ 2 ≤ 24 * q * |t|
  calc
    _ ≤ (2 * Real.sqrt v) ^ 2 :=
      (sq_le_sq₀ (Real.log_nonneg hv₁) (by positivity)).mpr hlog
    _ = 4 * v := by nlinarith only [hsqrt]
    _ = (8 * q) * (2 + |t|) := by dsimp [v]; ring
    _ ≤ (8 * q) * (3 * |t|) := mul_le_mul_of_nonneg_left (by linarith only [ht]) (by positivity)
    _ = _ := by ring

private theorem norm_horizontal_kernel_le {x h σ t : ℝ} (hx : 2 ≤ x) (hh : 0 < h)
    (hσ : σ ≤ 2) (ht : 1 ≤ |t|) :
    ‖GoldbachSmoothing.kernel x h ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      ((x + h) ^ 3 + x ^ 3) / (h * |t| ^ 2) := by
  let z : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I
  have hzRe : z.re = σ := by simp [z]
  have hzIm : z.im = t := by simp [z]
  have hzNextIm : (z + 1).im = t := by simp [hzIm]
  have hAbs₀ : 0 < |t| := zero_lt_one.trans_le ht
  have htZ : |t| ≤ ‖z‖ := by simpa only [hzIm] using Complex.abs_im_le_norm z
  have htZNext : |t| ≤ ‖z + 1‖ := by simpa only [hzNextIm] using Complex.abs_im_le_norm (z + 1)
  have hExp : z.re + 1 ≤ (3 : ℝ) := by linarith only [hzRe, hσ]
  have hXOne : (1 : ℝ) ≤ x := by linarith only [hx]
  have hXHOne : (1 : ℝ) ≤ x + h := by linarith only [hx, hh]
  have hNum : (x + h) ^ (z.re + 1) + x ^ (z.re + 1) ≤ (x + h) ^ 3 + x ^ 3 := by
    have h := add_le_add (Real.rpow_le_rpow_of_exponent_le hXHOne hExp)
      (Real.rpow_le_rpow_of_exponent_le hXOne hExp)
    simpa only [show (3 : ℝ) = (3 : ℕ) by norm_num, Real.rpow_natCast] using h
  have hDen : h * |t| ^ 2 ≤ h * ‖z‖ * ‖z + 1‖ := calc
    _ = h * (|t| * |t|) := by rw [pow_two]
    _ ≤ h * (‖z‖ * ‖z + 1‖) :=
      mul_le_mul_of_nonneg_left (mul_le_mul htZ htZNext (abs_nonneg _) (norm_nonneg _)) hh.le
    _ = _ := by ring
  change ‖GoldbachSmoothing.kernel x h z‖ ≤ ((x + h) ^ 3 + x ^ 3) / (h * |t| ^ 2)
  calc
    _ ≤ ((x + h) ^ (z.re + 1) + x ^ (z.re + 1)) / (h * ‖z‖ * ‖z + 1‖) :=
      GoldbachSmoothing.norm_kernel_le_tail (by linarith only [hx]) hh
    _ ≤ ((x + h) ^ 3 + x ^ 3) / (h * ‖z‖ * ‖z + 1‖) :=
      div_le_div_of_nonneg_right hNum (by positivity)
    _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (by positivity) hDen

/-- On a horizontal segment `[a,2]+it`, a logarithm-square bound on `f` and the quadratic
decay of the Mellin kernel give a bound on the integral proportional to `1/|t|`. -/
theorem norm_horizontal_kernel_integral_le {x h a q A t : ℝ} (hx : 2 ≤ x) (hh : 0 < h)
    (ha : a ≤ 2) (hq : 1 ≤ q) (hA : 0 ≤ A) (ht : 1 ≤ |t|) (f : ℂ → ℂ)
    (hf : ∀ σ ∈ Set.Icc a (2 : ℝ),
      ‖f ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ A * Real.log (2 * q * (2 + |t|)) ^ 2) :
    ‖∫ σ in a..2, f ((σ : ℂ) + (t : ℂ) * Complex.I) *
      GoldbachSmoothing.kernel x h ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      ((2 - a) * (A * (24 * q) * ((x + h) ^ 3 + x ^ 3) / h)) / |t| := by
  let B := (x + h) ^ 3 + x ^ 3
  let C := A * (24 * q) * B / h
  have hx₀ : 0 < x := by linarith only [hx]
  have hAbs₀ : 0 < |t| := zero_lt_one.trans_le ht
  have hBound (σ : ℝ) (hσ : σ ∈ Set.uIoc a (2 : ℝ)) :
      ‖f ((σ : ℂ) + (t : ℂ) * Complex.I) *
        GoldbachSmoothing.kernel x h ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C / |t| := by
    rw [Set.uIoc_of_le ha] at hσ
    let z : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I
    have hK : ‖GoldbachSmoothing.kernel x h z‖ ≤ B / (h * |t| ^ 2) :=
      norm_horizontal_kernel_le hx hh hσ.2 ht
    have hF : ‖f z‖ ≤ A * Real.log (2 * q * (2 + |t|)) ^ 2 := hf σ ⟨hσ.1.le, hσ.2⟩
    have hLog := mul_le_mul_of_nonneg_left (horizontal_log_sq_le hq ht) hA
    change ‖f z * GoldbachSmoothing.kernel x h z‖ ≤ C / |t|
    calc
      _ = ‖f z‖ * ‖GoldbachSmoothing.kernel x h z‖ := norm_mul _ _
      _ ≤ (A * Real.log (2 * q * (2 + |t|)) ^ 2) * (B / (h * |t| ^ 2)) :=
        mul_le_mul hF hK (norm_nonneg _) (by positivity)
      _ ≤ (A * (24 * q * |t|)) * (B / (h * |t| ^ 2)) :=
        mul_le_mul_of_nonneg_right hLog (by dsimp [B]; positivity)
      _ = _ := by
        dsimp [C, B]
        field_simp [hh.ne', hAbs₀.ne']
  change ‖∫ σ in a..2, f ((σ : ℂ) + (t : ℂ) * Complex.I) *
    GoldbachSmoothing.kernel x h ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ ((2 - a) * C) / |t|
  calc
    _ ≤ (C / |t|) * |2 - a| := intervalIntegral.norm_integral_le_of_norm_le_const hBound
    _ = _ := by rw [abs_of_nonneg (sub_nonneg.mpr ha)]; ring

/-- The smoothed horizontal contour contributions tend to zero along any filter of heights
escaping in absolute value and satisfying a uniform logarithm-square bound. -/
theorem tendsto_horizontal_kernel_integral_zero {ι : Type*} {l : Filter ι}
    {x h a q A : ℝ} (hx : 2 ≤ x) (hh : 0 < h) (ha : a ≤ 2) (hq : 1 ≤ q) (hA : 0 ≤ A)
    (f : ℂ → ℂ) (u : ι → ℝ) (hu : Tendsto (fun i ↦ |u i|) l atTop)
    (hf : ∀ᶠ i in l, ∀ σ ∈ Set.Icc a (2 : ℝ),
      ‖f ((σ : ℂ) + (u i : ℂ) * Complex.I)‖ ≤ A * Real.log (2 * q * (2 + |u i|)) ^ 2) :
    Tendsto (fun i ↦ ∫ σ in a..2, f ((σ : ℂ) + (u i : ℂ) * Complex.I) *
      GoldbachSmoothing.kernel x h ((σ : ℂ) + (u i : ℂ) * Complex.I)) l (𝓝 0) := by
  let C := (2 - a) * (A * (24 * q) * ((x + h) ^ 3 + x ^ 3) / h)
  have hInv : Tendsto (fun i ↦ (|u i|)⁻¹) l (𝓝 (0 : ℝ)) := tendsto_inv_atTop_zero.comp hu
  have hLimit : Tendsto (fun i ↦ C / |u i|) l (𝓝 (0 : ℝ)) := by
    simpa only [div_eq_mul_inv, mul_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ι ↦ C) l (𝓝 C)).mul hInv
  refine squeeze_zero_norm' ?_ hLimit
  filter_upwards [hu.eventually_ge_atTop 1, hf] with i hHeight hF
  exact norm_horizontal_kernel_integral_le hx hh ha hq hA hHeight f hF

end Goldbach

namespace Goldbach

open Complex Filter MeasureTheory Set
open scoped BigOperators Interval Topology

theorem uniform_dirichlet_log_control : ∃ C : ℝ, 0 < C ∧ UniformDirichletLogDerivative C := by
  obtain ⟨C, hC, h⟩ := norm_logDeriv_regularizedL_le
  refine ⟨C, hC, ?_⟩
  intro q _ χ σ t d hσ hd hdist
  have hpoint : (⟨σ, t⟩ : ℂ) = (σ : ℂ) + (t : ℂ) * I := by
    apply Complex.ext <;> simp
  rw [← hpoint] at hdist ⊢
  exact h q χ t σ d hσ.1 hσ.2 hd hdist

set_option maxHeartbeats 3000000 in
/-- The smoothed twisted prime sum, with its principal pole term separated. -/
theorem uniform_smoothed_dirichlet_estimate (hGRH : GRH) :
    ∃ D : ℝ, 0 < D ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (X : ℕ), 2 ≤ X →
      ‖(∑' n, GoldbachSmoothing.twistedCoefficient χ n *
          GoldbachSmoothing.cutoff (X : ℝ) (Real.sqrt X) n) -
        principalFlag χ * GoldbachSmoothing.kernel (X : ℝ) (Real.sqrt X) 1‖ ≤
        D * Real.sqrt (X : ℝ) * Real.log (2 * (q : ℝ) * (X : ℝ)) ^ 2 := by
  classical
  obtain ⟨A, B, hA, hB, hBounds⟩ := dirichlet_contour_bounds hGRH uniform_dirichlet_log_control
  obtain ⟨L, hL, hVertical⟩ := GoldbachSmoothing.norm_left_vertical_integral_le
  obtain ⟨Z, hZ, hResidues⟩ := uniform_smoothed_dirichlet_residues hGRH
  let c : ℝ := 1 / (2 * Real.pi)
  refine ⟨c * (L * A) + Z, by dsimp [c]; positivity, ?_⟩
  intro q _ χ X hX
  let x : ℝ := X
  let h : ℝ := Real.sqrt x
  let K := GoldbachSmoothing.kernel x h
  let F := regularizedL χ
  let δ := principalFlag χ
  let G (z : ℂ) : ℂ := contourLog χ z * K z
  let left (t : ℝ) : ℂ := contourLog χ (((9 / 20 : ℝ) : ℂ) + (t : ℂ) * I)
  let right (t : ℝ) : ℂ :=
    (-logDeriv (DirichletCharacter.LFunction χ) (2 + (t : ℂ) * I)) * K (2 + (t : ℂ) * I)
  have hx : 2 ≤ x := by dsimp [x]; exact_mod_cast hX
  have hx0 : 0 < x := by linarith
  have hh : 0 < h := Real.sqrt_pos.2 hx0
  have hq : 1 ≤ (q : ℝ) := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (NeZero.ne q))
  obtain ⟨hbLeft, hbGood⟩ := hBounds q χ
  let good (u : ℝ) : Prop :=
    (∀ ρ : ℂ, 0 < ρ.re → F ρ = 0 → ρ.im ≠ u) ∧
      ∀ σ ∈ Icc (9 / 20 : ℝ) 2,
        ‖contourLog χ ((σ : ℂ) + (u : ℂ) * I)‖ ≤ B * logHeight q u ^ 2
  obtain ⟨lo, up, _, hSign, hGood, hLoLimit, hUpLimit, hLoAbs, hUpAbs⟩ :=
    exists_height_sequences good hbGood
  choose S hZeros hInside hReal using
    fun n : ℕ => exists_regularizedL_contourZeros χ hGRH (lo n) (up n)
      (hGood n).1.1 (hGood n).2.1
  let zeros (n : ℕ) : ℂ := ∑ ρ ∈ S n, (analyticOrderNatAt F ρ : ℂ) * K ρ
  let leftInt (n : ℕ) :=
    ∫ t : ℝ in lo n..up n, G (((9 / 20 : ℝ) : ℂ) + (t : ℂ) * I)
  let horizontal (u : ℝ) := ∫ σ : ℝ in (9 / 20 : ℝ)..2, G ((σ : ℂ) + (u : ℂ) * I)
  let err (n : ℕ) := I * (horizontal (lo n) - horizontal (up n))
  have hRight (t : ℝ) : G (2 + (t : ℂ) * I) = right t := by
    let s : ℂ := 2 + (t : ℂ) * I
    have hsr : s.re = 2 := by simp [s]
    have hne : s ≠ 1 := by
      intro hs
      have e := congrArg Complex.re hs
      rw [hsr, one_re] at e
      norm_num at e
    have hLne := DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inr hne)
      (by rw [hsr]; norm_num)
    change (-logDeriv F s + δ / (s - 1)) * K s =
      (-logDeriv (DirichletCharacter.LFunction χ) s) * K s
    rw [logDeriv_regularizedL_eq χ hne hLne]
    ring
  have hRint : Integrable right := GoldbachSmoothing.integrable_twist_vertical χ hx0 hh
  have hLeftBound (n : ℕ) : ‖leftInt n‖ ≤
      L * A * Real.sqrt x * Real.log (2 * (q : ℝ) * x) ^ 2 :=
    hVertical left x q A (lo n) (up n) hx hq hA.le (contourLog_continuous_left χ hGRH) hbLeft
  have hZeroBound (n : ℕ) : ‖zeros n‖ ≤
      Z * Real.sqrt x * Real.log (2 * (q : ℝ) * x) ^ 2 := hResidues q χ x (S n) hx (hReal n)
  have hHorizLo : Tendsto (fun n => horizontal (lo n)) atTop (𝓝 0) :=
    tendsto_horizontal_kernel_integral_zero hx hh (by norm_num) hq hB.le (contourLog χ) lo
      hLoAbs (Eventually.of_forall fun n => (hGood n).1.2)
  have hHorizUp : Tendsto (fun n => horizontal (up n)) atTop (𝓝 0) :=
    tendsto_horizontal_kernel_integral_zero hx hh (by norm_num) hq hB.le (contourLog χ) up
      hUpAbs (Eventually.of_forall fun n => (hGood n).2.2)
  have hErr : Tendsto err atTop (𝓝 0) := by
    simpa only [err, sub_zero, mul_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => I) atTop (𝓝 I)).mul (hHorizLo.sub hHorizUp)
  have hRect (n : ℕ) : (∫ t : ℝ in lo n..up n, right t) =
      leftInt n + (2 * Real.pi) • (δ * K 1 - zeros n) + err n := by
    have hFanalytic : AnalyticOnNhd ℂ F (Icc (9 / 20 : ℝ) 2 ×ℂ Icc (lo n) (up n)) :=
      (analytic_regularizedL χ).mono (subset_univ _)
    have hKanalytic : AnalyticOnNhd ℂ K (Icc (9 / 20 : ℝ) 2 ×ℂ Icc (lo n) (up n)) := by
      refine (GoldbachSmoothing.kernel_analytic hx0 hh).mono ?_
      intro z hz
      exact (by norm_num : (0 : ℝ) < 9 / 20).trans_le hz.1.1
    have hr := rectBoundaryIntegral_neg_logDeriv_add_pole_mul F K (S n) δ
      (by norm_num) (by norm_num) (hSign n).1 (hSign n).2 hFanalytic hKanalytic
      (fun z hz => ⟨fun h => (hZeros n z).2 ⟨hz, h⟩, fun h => ((hZeros n z).1 h).2⟩)
      (fun z hz => ⟨(hInside n z hz).1.1, (hInside n z hz).1.2,
        (hInside n z hz).2.1, (hInside n z hz).2.2⟩)
      (fun z _ => regularizedL_analyticOrder_ne_top χ z) (regularizedL_ne_zero_at_one χ)
    have hr' := right_vertical_integral_of_rect hr
    change (∫ t : ℝ in lo n..up n, G (((2 : ℝ) : ℂ) + (t : ℂ) * I)) = _ at hr'
    have hIntegral : (∫ t : ℝ in lo n..up n, G (((2 : ℝ) : ℂ) + (t : ℂ) * I)) =
        ∫ t : ℝ in lo n..up n, right t := by
      simp only [ofReal_ofNat, hRight]
    rw [hIntegral] at hr'
    simpa only [Complex.real_smul, ofReal_mul, ofReal_ofNat, leftInt, horizontal, err, zeros,
      G, contourLog] using hr'
  have hf := vertical_contour_error_le hRint hLoLimit hUpLimit hErr
    (Eventually.of_forall hRect) (Eventually.of_forall hLeftBound) (Eventually.of_forall hZeroBound)
  rw [GoldbachSmoothing.smoothed_twist_eq_vertical χ hx0 hh]
  change ‖c • (∫ t : ℝ, right t) - δ * K 1‖ ≤ _
  exact hf.trans_eq (by dsimp [c, x]; ring)

end Goldbach

namespace GoldbachProgression

open GoldbachSmoothing

set_option maxHeartbeats 1000000 in
/-- A uniform smoothed twisted estimate gives the sharp arithmetic-progression estimate. -/
theorem progressionBound_of_smoothedTwistedBound
    (hSmoothed : ∃ D : ℝ, 0 < D ∧ ∀ (q : ℕ) [NeZero q]
      (χ : DirichletCharacter ℂ q) (X : ℕ), 2 ≤ X →
        ‖(∑' n, twistedCoefficient χ n * cutoff (X : ℝ) (Real.sqrt X) n) -
          Goldbach.principalFlag χ * kernel (X : ℝ) (Real.sqrt X) 1‖ ≤
          D * Real.sqrt (X : ℝ) * (Real.log (2 * (q : ℝ) * (X : ℝ))) ^ 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ q a X : ℕ, 0 < q → Nat.Coprime a q → 2 ≤ X →
      |(Finset.sum ((Finset.range (X + 1)).filter (fun k => k % q = a % q))
        (fun k => ArithmeticFunction.vonMangoldt k)) - (X : ℝ) / (Nat.totient q : ℝ)| ≤
        C * Real.sqrt (X : ℝ) * (Real.log (2 * (q : ℝ) * (X : ℝ))) ^ 2 := by
  classical
  apply progressionBound_of_twistedBound
  obtain ⟨D, hD, hEstimate⟩ := hSmoothed
  refine ⟨D + 2, by linarith, ?_⟩
  intro q _ χ X hX
  let h := Real.sqrt (X : ℝ)
  let L := Real.log (2 * (q : ℝ) * (X : ℝ))
  let A : ℂ := ∑' n, twistedCoefficient χ n * cutoff (X : ℝ) h n
  let M : ℂ := Goldbach.principalFlag χ * kernel (X : ℝ) h 1
  let S : ℂ := twistedVonMangoldt χ X
  let P : ℂ := principalMainTerm χ X
  have hXR : 2 ≤ (X : ℝ) := by exact_mod_cast hX
  have hqR : 1 ≤ (q : ℝ) := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (NeZero.ne q))
  have hh : 0 < h := Real.sqrt_pos.2 (by linarith)
  have hArg : 2 * (X : ℝ) ≤ 2 * (q : ℝ) * (X : ℝ) :=
    mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  have hL : 1 ≤ L := by
    have hlog2 := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 2 by norm_num)
    norm_num at hlog2
    have hlog4 : 1 ≤ Real.log 4 := by
      rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
      linarith
    exact hlog4.trans (Real.log_le_log (by norm_num)
      ((by linarith : (4 : ℝ) ≤ 2 * (X : ℝ)).trans hArg))
  have hLsq : L ≤ L ^ 2 := by
    nlinarith [mul_nonneg (zero_le_one.trans hL) (sub_nonneg.mpr hL)]
  have hXS : ‖S - A‖ ≤ h * L ^ 2 := by
    calc
      ‖S - A‖ = ‖A - S‖ := norm_sub_rev _ _
      _ ≤ h * Real.log (2 * (X : ℝ)) := norm_twisted_smoothing_error χ X hX
      _ ≤ h * L ^ 2 := mul_le_mul_of_nonneg_left
        ((Real.log_le_log (by linarith) hArg).trans hLsq) hh.le
  have hAM : ‖A - M‖ ≤ D * h * L ^ 2 := hEstimate q χ X hX
  have hP : P = Goldbach.principalFlag χ * (X : ℂ) := by
    by_cases hχ : χ = 1 <;> simp [P, principalMainTerm, Goldbach.principalFlag, hχ]
  have hFlag : ‖Goldbach.principalFlag χ‖ ≤ 1 := by
    by_cases hχ : χ = 1 <;> simp [Goldbach.principalFlag, hχ]
  have hKernel : kernel (X : ℝ) h 1 - (X : ℂ) = ((h / 2 : ℝ) : ℂ) := by
    simp only [kernel_at_one hh, Complex.ofReal_add, Complex.ofReal_natCast, add_sub_cancel_left]
  have hHalf : 0 ≤ h / 2 := div_nonneg hh.le (by norm_num)
  have hMP : ‖M - P‖ ≤ h * L ^ 2 := by
    change ‖Goldbach.principalFlag χ * kernel (X : ℝ) h 1 - P‖ ≤ _
    rw [hP, ← mul_sub, hKernel, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hHalf]
    calc
      _ ≤ 1 * (h / 2) := mul_le_mul_of_nonneg_right hFlag hHalf
      _ ≤ h := by linarith
      _ = h * 1 := (mul_one _).symm
      _ ≤ h * L ^ 2 := mul_le_mul_of_nonneg_left (hL.trans hLsq) hh.le
  change ‖S - P‖ ≤ (D + 2) * h * L ^ 2
  calc
    ‖S - P‖ ≤ ‖S - A‖ + ‖A - P‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ ‖S - A‖ + (‖A - M‖ + ‖M - P‖) :=
      (add_le_add_right (norm_sub_le_norm_sub_add_norm_sub _ _ _) _)
    _ ≤ h * L ^ 2 + (D * h * L ^ 2 + h * L ^ 2) :=
      (add_le_add hXS (add_le_add hAM hMP))
    _ = _ := by ring

end GoldbachProgression

/-- The von Mangoldt discrepancy in a reduced residue class under the Dirichlet GRH. -/
theorem PEqualNP.Outside.L_goldbach_grh_progression_error :
    (∀ (Q : ℕ) [NeZero Q] (χ : DirichletCharacter ℂ Q) (s : ℂ),
      0 < s.re → s.re < 1 → DirichletCharacter.LFunction χ s = 0 → s.re = 1 / 2) →
    ∃ C : ℝ, 0 < C ∧ ∀ q a X : ℕ, 0 < q → Nat.Coprime a q → 2 ≤ X →
      |(Finset.sum ((Finset.range (X + 1)).filter (fun k => k % q = a % q))
        (fun k => ArithmeticFunction.vonMangoldt k)) - (X : ℝ) / (Nat.totient q : ℝ)| ≤
        C * Real.sqrt (X : ℝ) * (Real.log (2 * (q : ℝ) * (X : ℝ))) ^ 2 := by
  intro hGRH
  exact GoldbachProgression.progressionBound_of_smoothedTwistedBound
    (Goldbach.uniform_smoothed_dirichlet_estimate hGRH)

-- Character-level extraction from the checked analytic proof above.
-- Source: https://github.com/CGandGameEngineLearner/goldbach-proofs/pull/43
-- Authority: https://github.com/CGandGameEngineLearner/goldbach-proofs/actions/runs/45369437743
namespace GoldbachGRHCharacter

open GoldbachSmoothing GoldbachProgression
open scoped BigOperators Classical

set_option maxHeartbeats 1000000 in
theorem twistedMangoldtPrefix_of_smoothedBound
    (hSmoothed : ∃ D : ℝ, 0 < D ∧ ∀ (q : ℕ) [NeZero q]
      (χ : DirichletCharacter ℂ q) (X : ℕ), 2 ≤ X →
        ‖(∑' n, twistedCoefficient χ n * cutoff (X : ℝ) (Real.sqrt X) n) -
          Goldbach.principalFlag χ * kernel (X : ℝ) (Real.sqrt X) 1‖ ≤
          D * Real.sqrt (X : ℝ) * (Real.log (2 * (q : ℝ) * (X : ℝ))) ^ 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q]
      (χ : DirichletCharacter ℂ q) (X : ℕ), 2 ≤ X →
        ‖twistedVonMangoldt χ X - principalMainTerm χ X‖ ≤
          C * Real.sqrt (X : ℝ) * (Real.log (2 * (q : ℝ) * (X : ℝ))) ^ 2 := by
  classical
  obtain ⟨D, hD, hEstimate⟩ := hSmoothed
  refine ⟨D + 2, by linarith, ?_⟩
  intro q _ χ X hX
  let h := Real.sqrt (X : ℝ)
  let L := Real.log (2 * (q : ℝ) * (X : ℝ))
  let A : ℂ := ∑' n, twistedCoefficient χ n * cutoff (X : ℝ) h n
  let M : ℂ := Goldbach.principalFlag χ * kernel (X : ℝ) h 1
  let S : ℂ := twistedVonMangoldt χ X
  let P : ℂ := principalMainTerm χ X
  have hXR : 2 ≤ (X : ℝ) := by exact_mod_cast hX
  have hqR : 1 ≤ (q : ℝ) := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (NeZero.ne q))
  have hh : 0 < h := Real.sqrt_pos.2 (by linarith)
  have hArg : 2 * (X : ℝ) ≤ 2 * (q : ℝ) * (X : ℝ) :=
    mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  have hL : 1 ≤ L := by
    have hlog2 := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 2 by norm_num)
    norm_num at hlog2
    have hlog4 : 1 ≤ Real.log 4 := by
      rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
      linarith
    exact hlog4.trans (Real.log_le_log (by norm_num)
      ((by linarith : (4 : ℝ) ≤ 2 * (X : ℝ)).trans hArg))
  have hLsq : L ≤ L ^ 2 := by
    nlinarith [mul_nonneg (zero_le_one.trans hL) (sub_nonneg.mpr hL)]
  have hXS : ‖S - A‖ ≤ h * L ^ 2 := by
    calc
      ‖S - A‖ = ‖A - S‖ := norm_sub_rev _ _
      _ ≤ h * Real.log (2 * (X : ℝ)) := norm_twisted_smoothing_error χ X hX
      _ ≤ h * L ^ 2 := mul_le_mul_of_nonneg_left
        ((Real.log_le_log (by linarith) hArg).trans hLsq) hh.le
  have hAM : ‖A - M‖ ≤ D * h * L ^ 2 := hEstimate q χ X hX
  have hP : P = Goldbach.principalFlag χ * (X : ℂ) := by
    by_cases hχ : χ = 1 <;> simp [P, principalMainTerm, Goldbach.principalFlag, hχ]
  have hFlag : ‖Goldbach.principalFlag χ‖ ≤ 1 := by
    by_cases hχ : χ = 1 <;> simp [Goldbach.principalFlag, hχ]
  have hKernel : kernel (X : ℝ) h 1 - (X : ℂ) = ((h / 2 : ℝ) : ℂ) := by
    simp only [kernel_at_one hh, Complex.ofReal_add, Complex.ofReal_natCast, add_sub_cancel_left]
  have hHalf : 0 ≤ h / 2 := div_nonneg hh.le (by norm_num)
  have hMP : ‖M - P‖ ≤ h * L ^ 2 := by
    change ‖Goldbach.principalFlag χ * kernel (X : ℝ) h 1 - P‖ ≤ _
    rw [hP, ← mul_sub, hKernel, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hHalf]
    calc
      _ ≤ 1 * (h / 2) := mul_le_mul_of_nonneg_right hFlag hHalf
      _ ≤ h := by linarith
      _ = h * 1 := (mul_one _).symm
      _ ≤ h * L ^ 2 := mul_le_mul_of_nonneg_left (hL.trans hLsq) hh.le
  change ‖S - P‖ ≤ (D + 2) * h * L ^ 2
  calc
    ‖S - P‖ ≤ ‖S - A‖ + ‖A - P‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ ‖S - A‖ + (‖A - M‖ + ‖M - P‖) :=
      (add_le_add_right (norm_sub_le_norm_sub_add_norm_sub _ _ _) _)
    _ ≤ h * L ^ 2 + (D * h * L ^ 2 + h * L ^ 2) :=
      (add_le_add hXS (add_le_add hAM hMP))
    _ = _ := by ring

theorem twistedMangoldtPrefix (hGRH : Goldbach.GRH) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q]
      (χ : DirichletCharacter ℂ q) (X : ℕ), 2 ≤ X →
        ‖(∑ k ∈ Finset.range (X+1),
          (ArithmeticFunction.vonMangoldt k : ℂ) * χ (k : ZMod q)) -
            (if χ = 1 then (X : ℂ) else 0)‖ ≤
          C * Real.sqrt (X : ℝ) * (Real.log (2 * (q : ℝ) * (X : ℝ))) ^ 2 := by
  obtain ⟨C, hC, hBound⟩ :=
    twistedMangoldtPrefix_of_smoothedBound (Goldbach.uniform_smoothed_dirichlet_estimate hGRH)
  refine ⟨C, hC, ?_⟩
  intro q _ χ X hX
  simpa only [twistedVonMangoldt, principalMainTerm, mul_comm] using hBound q χ X hX

theorem twistedMangoldtInterval_of_prefix
    (hPrefix : ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q]
      (χ : DirichletCharacter ℂ q) (X : ℕ), 2 ≤ X →
        ‖(∑ k ∈ Finset.range (X+1),
          (ArithmeticFunction.vonMangoldt k : ℂ) * χ (k : ZMod q)) -
            (if χ = 1 then (X : ℂ) else 0)‖ ≤
          C * Real.sqrt (X : ℝ) * (Real.log (2 * (q : ℝ) * (X : ℝ))) ^ 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
      (n a b : ℕ), 2 ≤ n → a ≤ b → b ≤ n →
        ‖(∑ k ∈ Finset.Icc a b, (ArithmeticFunction.vonMangoldt k : ℂ) * χ (k : ZMod q)) -
            (if χ = 1 then ((Finset.Icc a b).card : ℂ) else 0)‖ ≤
          C * Real.sqrt (n : ℝ) * (Real.log (2 * (q : ℝ) * (n : ℝ))) ^ 2 := by
  obtain ⟨C, hC, hBound⟩ := hPrefix
  refine ⟨2 * (C + 2), by linarith, ?_⟩
  intro q _ χ n a b hn hab hbn
  let terms : ℕ → ℂ := fun k => (ArithmeticFunction.vonMangoldt k : ℂ) * χ (k : ZMod q)
  let prefixSum : ℕ → ℂ := fun m => ∑ k ∈ Finset.range m, terms k
  let main : ℕ → ℂ := fun m => if χ = 1 then (m : ℂ) else 0
  let B : ℝ := Real.sqrt (n : ℝ) * (Real.log (2 * (q : ℝ) * (n : ℝ))) ^ 2
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hLogArg : ∀ (x : ℝ), 2 ≤ x → (4 : ℝ) ≤ 2 * (q : ℝ) * x := by
    intro x hx
    calc
      4 ≤ 2 * x := by linarith
      _ ≤ 2 * (q : ℝ) * x := by
        have h := mul_le_mul_of_nonneg_right hqR (show 0 ≤ x by linarith)
        linarith
  have hLog4 : 1 ≤ Real.log 4 := by
    have hlog2 := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 2 by norm_num)
    norm_num at hlog2
    rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
    linarith
  have hLogN : 1 ≤ Real.log (2 * (q : ℝ) * (n : ℝ)) :=
    hLog4.trans (Real.log_le_log (by norm_num) (hLogArg n hnR))
  have hB : 1 ≤ B :=
    one_le_mul_of_one_le_of_one_le (Real.one_le_sqrt.mpr (by linarith only [hnR]))
      (one_le_pow₀ hLogN)
  have hShift (m : ℕ) : ‖main m - main (m+1)‖ ≤ 1 := by
    by_cases hχ : χ = 1
    · simp [main, hχ, Nat.cast_add]
    · simp [main, hχ]
  have hP (m : ℕ) (hm : m ≤ n+1) : ‖prefixSum m - main m‖ ≤ (C+2) * B := by
    by_cases hmSmall : m ≤ 2
    · have hp : prefixSum m = 0 := by
        rcases (show m = 0 ∨ m = 1 ∨ m = 2 by omega) with rfl | rfl | rfl <;>
          simp [prefixSum, terms, Finset.sum_range_succ]
      have hmain : ‖main m‖ ≤ (m : ℝ) := by
        by_cases hχ : χ = 1 <;> simp [main, hχ]
      have hmR : (m : ℝ) ≤ 2 := by exact_mod_cast hmSmall
      rw [hp, zero_sub, norm_neg]
      exact hmain.trans (hmR.trans (by nlinarith [mul_nonneg hC.le (zero_le_one.trans hB)]))
    · obtain ⟨x, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show m ≠ 0 by omega)
      have hx : 2 ≤ x := by omega
      have hxn : x ≤ n := by omega
      have hxR : (2 : ℝ) ≤ x := by exact_mod_cast hx
      have hxnR : (x : ℝ) ≤ n := by exact_mod_cast hxn
      have hLogX : 0 ≤ Real.log (2 * (q : ℝ) * (x : ℝ)) :=
        zero_le_one.trans (hLog4.trans (Real.log_le_log (by norm_num) (hLogArg x hxR)))
      have hLogLE : Real.log (2 * (q : ℝ) * (x : ℝ)) ≤ Real.log (2 * (q : ℝ) * (n : ℝ)) := by
        exact Real.log_le_log (by linarith only [hLogArg x hxR])
          (mul_le_mul_of_nonneg_left hxnR (by positivity))
      have hRate : Real.sqrt (x : ℝ) * (Real.log (2 * (q : ℝ) * (x : ℝ)))^2 ≤ B :=
        mul_le_mul (Real.sqrt_le_sqrt hxnR) (pow_le_pow_left₀ hLogX hLogLE 2)
          (sq_nonneg _) (Real.sqrt_nonneg _)
      have hs : ‖prefixSum (x+1) - main x‖ ≤ C * B := by
        have hh := hBound q χ x hx
        change ‖prefixSum (x+1) - main x‖ ≤ _ at hh
        rw [mul_assoc] at hh
        exact hh.trans (mul_le_mul_of_nonneg_left hRate hC.le)
      change ‖prefixSum (x+1) - main (x+1)‖ ≤ _
      calc
        _ ≤ ‖prefixSum (x+1) - main x‖ + ‖main x - main (x+1)‖ :=
          norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ C * B + 1 := add_le_add hs (hShift x)
        _ ≤ _ := by nlinarith
  have hSum : (∑ k ∈ Finset.Icc a b, terms k) = prefixSum (b+1) - prefixSum a := by
    rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sub _ (by omega : a ≤ b+1)]
  have hMain : main (b+1) - main a = if χ = 1 then ((Finset.Icc a b).card : ℂ) else 0 := by
    rw [Nat.card_Icc]
    by_cases hχ : χ = 1
    · simp [main, hχ, Nat.cast_sub (by omega : a ≤ b+1)]
    · simp [main, hχ]
  change ‖(∑ k ∈ Finset.Icc a b, terms k) - _‖ ≤ _
  rw [hSum, ← hMain, show prefixSum (b+1) - prefixSum a - (main (b+1) - main a) =
    (prefixSum (b+1) - main (b+1)) - (prefixSum a - main a) by ring]
  calc
    _ ≤ ‖prefixSum (b+1) - main (b+1)‖ + ‖prefixSum a - main a‖ := norm_sub_le _ _
    _ ≤ (C+2)*B + (C+2)*B := add_le_add (hP (b+1) (by omega)) (hP a (by omega))
    _ = _ := by dsimp [B]; ring

theorem twistedMangoldtInterval (hGRH : Goldbach.GRH) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
      (n a b : ℕ), 2 ≤ n → a ≤ b → b ≤ n →
        ‖(∑ k ∈ Finset.Icc a b, (ArithmeticFunction.vonMangoldt k : ℂ) * χ (k : ZMod q)) -
            (if χ = 1 then ((Finset.Icc a b).card : ℂ) else 0)‖ ≤
          C * Real.sqrt (n : ℝ) * (Real.log (2 * (q : ℝ) * (n : ℝ))) ^ 2 :=
  twistedMangoldtInterval_of_prefix (twistedMangoldtPrefix hGRH)

end GoldbachGRHCharacter

end
end

end GoldbachGRHCharacterInput

section GoldbachGRHWindowParseval

open scoped BigOperators ComplexConjugate
open Finset

namespace GoldbachGRHWindow

noncomputable section

private theorem norm_energy_of_columns {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] (K : A → B → ℂ) (D : A → ℝ)
    (hK : ∀ r s : A, (∑ b : B, conj (K r b) * K s b) =
      if r = s then (D r : ℂ) else 0) (f : A → ℂ) :
    (∑ b : B, ‖∑ r : A, f r * K r b‖ ^ 2) =
      ∑ r : A, D r * ‖f r‖ ^ 2 := by
  apply Complex.ofReal_injective
  simp only [Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_pow, ← Complex.conj_mul']
  calc
    _ = ∑ b : B, ∑ r : A, ∑ s : A, conj (f r) * f s * (conj (K r b) * K s b) := by
      refine Finset.sum_congr rfl fun b _ => ?_
      simp only [map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun s _ => ?_
      ring
    _ = ∑ r : A, ∑ s : A, conj (f r) * f s * (∑ b : B, conj (K r b) * K s b) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum]
    _ = _ := by
      refine Finset.sum_congr rfl fun r _ => ?_
      simp only [hK, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
      ring

variable {q : ℕ} [NeZero q]

local instance : DecidableEq (DirichletCharacter ℂ q) := Classical.decEq _

theorem additive_energy (f : ZMod q → ℂ) :
    (∑ a : ZMod q, ‖∑ r : ZMod q, f r * ZMod.stdAddChar (a * r)‖ ^ 2) =
      (q : ℝ) * ∑ r : ZMod q, ‖f r‖ ^ 2 := by
  rw [Finset.mul_sum]
  apply norm_energy_of_columns (fun r a => ZMod.stdAddChar (a * r)) (fun _ => (q : ℝ))
  intro r s
  have hc (z : ZMod q) : conj (ZMod.stdAddChar z) = ZMod.stdAddChar (-z) := by
    rw [AddChar.map_neg_eq_inv]
    exact (Complex.inv_eq_conj (by simp [ZMod.stdAddChar_apply])).symm
  simp only [hc, ← AddChar.map_add_eq_mul, ← mul_neg, ← mul_add]
  by_cases h : r = s
  · simp [h, ZMod.card]
  · rw [ite_eq_right h]
    have hne : -r + s ≠ 0 := by
      simpa only [sub_eq_add_neg, add_comm] using (sub_ne_zero.mpr (fun he : s = r => h he.symm) : s - r ≠ 0)
    calc
      _ = ∑ a : ZMod q, ZMod.stdAddChar ((-r + s) * a) := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [mul_comm]
      _ = 0 := AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar q hne)

omit [NeZero q] in
private theorem char_conj_of_unit (χ : DirichletCharacter ℂ q) {r : ZMod q}
    (hr : IsUnit r) : conj (χ r) = χ r⁻¹ := by
  have hχr : χ r ≠ 0 := (hr.map χ).ne_zero
  have hi : χ r⁻¹ = (χ r)⁻¹ := by
    calc
      _ = χ r⁻¹ * (χ r * (χ r)⁻¹) := by rw [mul_inv_cancel₀ hχr, mul_one]
      _ = _ := by rw [← mul_assoc, ← map_mul, ZMod.inv_mul_of_unit r hr, map_one, one_mul]
  exact (MulChar.star_apply' χ r).trans ((MulChar.inv_apply_eq_inv' χ r).trans hi.symm)

theorem multiplicative_energy (f : ZMod q → ℂ) :
    (∑ χ : DirichletCharacter ℂ q, ‖∑ r : ZMod q, f r * χ r‖ ^ 2) =
      (q.totient : ℝ) * ∑ r ∈ (univ : Finset (ZMod q)).filter IsUnit, ‖f r‖ ^ 2 := by
  rw [Finset.sum_filter, Finset.mul_sum]
  have hParseval := norm_energy_of_columns (fun r (χ : DirichletCharacter ℂ q) => χ r)
    (fun r : ZMod q => if IsUnit r then (q.totient : ℝ) else 0)
    (f := f) (by
      intro r s
      by_cases hr : IsUnit r
      · simp only [char_conj_of_unit _ hr, ite_eq_left hr, Complex.ofReal_natCast]
        exact DirichletCharacter.sum_char_inv_mul_char_eq ℂ hr s
      · simp [hr, MulChar.map_nonunit _ hr])
  rw [hParseval]
  refine Finset.sum_congr rfl fun r _ => ?_
  by_cases hr : IsUnit r <;> simp [hr]

/-- The additive coefficient of the unit-uniform residue distribution. -/
noncomputable def additiveModel (q : ℕ) [NeZero q] (a : ZMod q) : ℂ :=
  (∑ u : (ZMod q)ˣ, ZMod.stdAddChar (a * (u : ZMod q))) / (q.totient : ℂ)

private noncomputable def residueSum (I : Finset ℕ) (w : ℕ → ℂ) (r : ZMod q) : ℂ :=
  ∑ k ∈ I.filter (fun k : ℕ => (k : ZMod q) = r), w k

private noncomputable def residueError (I : Finset ℕ) (w : ℕ → ℂ) (r : ZMod q) : ℂ :=
  residueSum I w r - if IsUnit r then (I.card : ℂ) / (q.totient : ℂ) else 0

private theorem sum_residueSum_mul (I : Finset ℕ) (w : ℕ → ℂ) (K : ZMod q → ℂ) :
    (∑ r : ZMod q, residueSum I w r * K r) =
      ∑ k ∈ I, w k * K (k : ZMod q) := by
  calc
    _ = ∑ r : ZMod q, ∑ k ∈ I.filter (fun k : ℕ => (k : ZMod q) = r),
        w k * K (k : ZMod q) := by
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [residueSum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [(Finset.mem_filter.mp hk).2]
    _ = _ := Finset.sum_fiberwise I (fun k => (k : ZMod q)) _

private theorem sum_if_isUnit (F : ZMod q → ℂ) :
    (∑ r : ZMod q, if IsUnit r then F r else 0) = ∑ u : (ZMod q)ˣ, F (u : ZMod q) := by
  classical
  rw [← Finset.sum_filter]
  have hs : (univ : Finset (ZMod q)).filter IsUnit =
      (univ : Finset (ZMod q)ˣ).map ⟨(↑), Units.val_injective⟩ := by
    ext r
    simp [IsUnit]
  rw [hs, Finset.sum_map]
  rfl

private theorem residueError_character (I : Finset ℕ) (w : ℕ → ℂ)
    (χ : DirichletCharacter ℂ q) :
    (∑ r : ZMod q, residueError I w r * χ r) =
      (∑ k ∈ I, w k * χ (k : ZMod q)) - (if χ = 1 then (I.card : ℂ) else 0) := by
  classical
  unfold residueError
  simp only [sub_mul, Finset.sum_sub_distrib, sum_residueSum_mul]
  congr 1
  have hs : (∑ r : ZMod q, (if IsUnit r then (I.card : ℂ) / (q.totient : ℂ) else 0) * χ r) =
      ((I.card : ℂ) / (q.totient : ℂ)) * (∑ r : ZMod q, χ r) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    by_cases hr : IsUnit r
    · simp [hr]
    · simp [hr, MulChar.map_nonunit χ hr]
  rw [hs]
  by_cases hχ : χ = 1
  · subst χ
    rw [MulChar.sum_one_eq_card_units, ZMod.card_units_eq_totient, ite_eq_left rfl]
    exact div_mul_cancel₀ _ (by exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos q)).ne')
  · rw [MulChar.sum_eq_zero_of_ne_one hχ, mul_zero, ite_eq_right hχ]

private theorem residueError_additive (I : Finset ℕ) (w : ℕ → ℂ) (a : ZMod q) :
    (∑ r : ZMod q, residueError I w r * ZMod.stdAddChar (a * r)) =
      ∑ k ∈ I, (w k * ZMod.stdAddChar (a * (k : ZMod q)) - additiveModel q a) := by
  classical
  simp only [residueError, sub_mul, Finset.sum_sub_distrib, sum_residueSum_mul]
  congr 1
  calc
    _ = ((I.card : ℂ) / (q.totient : ℂ)) *
        (∑ r : ZMod q, if IsUnit r then ZMod.stdAddChar (a * r) else 0) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun r _ => ?_
      by_cases hr : IsUnit r <;> simp [hr]
    _ = _ := by
      rw [sum_if_isUnit, Finset.sum_const, nsmul_eq_mul]
      unfold additiveModel
      simp only [div_eq_mul_inv]
      ring

/-- Squared short-window error at all additive numerators, from uniform
    individual character bounds and an absolute mass bound at nonunits. -/
theorem sum_additive_window_error_sq_le (I : Finset ℕ) (w : ℕ → ℂ)
    (B P : ℝ) (_hB : 0 ≤ B) (_hP : 0 ≤ P)
    (hχ : ∀ χ : DirichletCharacter ℂ q,
      ‖(∑ k ∈ I, w k * χ (k : ZMod q)) - (if χ = 1 then (I.card : ℂ) else 0)‖ ≤ B)
    (hnon : (∑ k ∈ I.filter (fun k : ℕ => ¬ IsUnit (k : ZMod q)), ‖w k‖) ≤ P) :
    (∑ a : ZMod q,
      ‖∑ k ∈ I, (w k * ZMod.stdAddChar (a * (k : ZMod q)) - additiveModel q a)‖ ^ 2) ≤
      (q : ℝ) * (B ^ 2 + P ^ 2) := by
  classical
  have hφ : 0 < (q.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
  have hCard : Fintype.card (DirichletCharacter ℂ q) = q.totient := by
    rw [← Nat.card_eq_fintype_card]
    exact DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q
  have hUnit : (∑ r ∈ (univ : Finset (ZMod q)).filter IsUnit, ‖residueError I w r‖ ^ 2) ≤
      B ^ 2 := by
    apply le_of_mul_le_mul_left _ hφ
    rw [← multiplicative_energy]
    calc
      _ ≤ ∑ χ : DirichletCharacter ℂ q, B ^ 2 := by
        refine Finset.sum_le_sum fun χ _ => ?_
        rw [residueError_character]
        exact pow_le_pow_left₀ (norm_nonneg _) (hχ χ) 2
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, hCard]
  let V : Finset (ZMod q) := univ.filter (fun r => ¬ IsUnit r)
  have hV : (∑ r ∈ V, ‖residueError I w r‖) ≤ P := by
    calc
      _ ≤ ∑ r ∈ V, ∑ k ∈ I.filter (fun k : ℕ => (k : ZMod q) = r), ‖w k‖ := by
        refine Finset.sum_le_sum fun r hr => ?_
        have hr' : ¬ IsUnit r := (Finset.mem_filter.mp hr).2
        simpa [residueError, hr', residueSum] using
          norm_sum_le (I.filter (fun k : ℕ => (k : ZMod q) = r)) w
      _ = ∑ k ∈ I.filter (fun k : ℕ => ¬ IsUnit (k : ZMod q)), ‖w k‖ := by
        rw [Finset.sum_fiberwise_eq_sum_filter]
        simp [V]
      _ ≤ _ := hnon
  have hNonUnit : (∑ r ∈ V, ‖residueError I w r‖ ^ 2) ≤ P ^ 2 :=
    (Finset.sum_sq_le_sq_sum_of_nonneg (fun _ _ => norm_nonneg _)).trans
      (pow_le_pow_left₀ (Finset.sum_nonneg (fun _ _ => norm_nonneg _)) hV 2)
  simp_rw [← residueError_additive]
  rw [additive_energy]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg q)
  rw [← Finset.sum_filter_add_sum_filter_not
    (s := (univ : Finset (ZMod q))) (p := IsUnit)]
  exact add_le_add hUnit hNonUnit

/-- The additive kernel written with the phase convention used in the frozen theorem. -/
theorem stdAddChar_mul_nat (a : ZMod q) (k : ℕ) :
    ZMod.stdAddChar (a * (k : ZMod q)) =
      Complex.exp (((2 * Real.pi * ((k : ℝ) * ((a.val : ℝ) / (q : ℝ))) : ℝ) : ℂ) *
        Complex.I) := by
  have ha : (↑(a.val * k) : ZMod q) = a * (k : ZMod q) := by
    rw [Nat.cast_mul, ZMod.natCast_zmod_val]
  calc
    _ = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (↑(a.val * k) : ℂ) / q) := by
      rw [← ha]
      simpa only [Int.cast_natCast] using ZMod.stdAddChar_coe (N := q) (a.val * k : ℕ)
    _ = _ := by
      congr 1
      push_cast
      ring

/-- Write the character of two natural residues without reducing either natural number. -/
theorem stdAddChar_nat_pair (a k : ℕ) :
    ZMod.stdAddChar ((a : ZMod q) * (k : ZMod q)) =
      Complex.exp (((2 * Real.pi * ((a : ℝ) * (k : ℝ) / (q : ℝ)) : ℝ) : ℂ) *
        Complex.I) := by
  have h := ZMod.stdAddChar_coe (N := q) (a * k : ℕ)
  push_cast at h
  rw [h]
  congr 1
  push_cast
  ring

/-- Express the unit-model coefficient as the exact reduced numerator sum
    occurring in the major-arc statements. -/
theorem additiveModel_eq_reduced_sum (a : ℕ) :
    additiveModel q (a : ZMod q) =
      (∑ r ∈ (Finset.range q).filter (fun r => Nat.Coprime r q),
        Complex.exp (((2 * Real.pi * ((a : ℝ) * (r : ℝ) / (q : ℝ)) : ℝ) : ℂ) *
          Complex.I)) / (q.totient : ℂ) := by
  unfold additiveModel
  congr 1
  apply Finset.sum_bij (fun (u : (ZMod q)ˣ) _ => (u : ZMod q).val)
  · intro u _
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (ZMod.val_lt (u : ZMod q)), ZMod.val_coe_unit_coprime u⟩
  · intro u _ v _ huv
    apply Units.ext
    simpa only [ZMod.natCast_zmod_val] using congrArg (fun x : ℕ => (x : ZMod q)) huv
  · intro r hr
    obtain ⟨hrange, hcop⟩ := Finset.mem_filter.mp hr
    let hrunit : IsUnit (r : ZMod q) := (ZMod.isUnit_iff_coprime r q).mpr hcop
    exact ⟨hrunit.unit, Finset.mem_univ _, by
      rw [IsUnit.unit_spec, ZMod.val_natCast_of_lt (Finset.mem_range.mp hrange)]⟩
  · intro u _
    rw [← stdAddChar_nat_pair (q := q) a ((u : ZMod q).val), ZMod.natCast_zmod_val]

/-- A reduced numerator changes only the order of the same unit residues. -/
theorem additiveModel_of_unit (a : ZMod q) (ha : IsUnit a) :
    additiveModel q a = additiveModel q 1 := by
  unfold additiveModel
  apply congrArg (fun z : ℂ => z / (q.totient : ℂ))
  let e : (ZMod q)ˣ ≃ (ZMod q)ˣ := Equiv.mulLeft ha.unit
  refine Fintype.sum_equiv e (fun u => ZMod.stdAddChar (a * (u : ZMod q)))
    (fun u => ZMod.stdAddChar (1 * (u : ZMod q))) ?_
  intro u
  change ZMod.stdAddChar (a * (u : ZMod q)) =
    ZMod.stdAddChar (1 * (((ha.unit * u) : (ZMod q)ˣ) : ZMod q))
  rw [one_mul, Units.val_mul, IsUnit.unit_spec]

/-- Prime-logarithmic weights, represented in the complex field. -/
noncomputable def primeLog (k : ℕ) : ℂ :=
  ((if Nat.Prime k then Real.log (k : ℝ) else 0 : ℝ) : ℂ)

/-- A prime in a nonunit residue must divide the modulus. Its total
    logarithmic mass in any window is at most the logarithm of the modulus. -/
theorem primeLog_nonunit_mass_le (I : Finset ℕ) :
    (∑ k ∈ I.filter (fun k : ℕ => ¬ IsUnit (k : ZMod q)), ‖primeLog k‖) ≤
      Real.log (q : ℝ) := by
  let J := I.filter (fun k : ℕ => ¬ IsUnit (k : ZMod q))
  change (∑ k ∈ J, ‖primeLog k‖) ≤ _
  have hsub : J.filter Nat.Prime ⊆ q.primeFactors := by
    intro k hk
    obtain ⟨hkJ, hp⟩ := Finset.mem_filter.mp hk
    have hnu := (Finset.mem_filter.mp hkJ).2
    have hd : k ∣ q := by
      by_contra hnd
      exact hnu ((ZMod.isUnit_iff_coprime k q).mpr ((hp.coprime_iff_not_dvd).mpr hnd))
    exact Nat.mem_primeFactors.mpr ⟨hp, hd, NeZero.ne q⟩
  calc
    _ = ∑ k ∈ J.filter Nat.Prime, Real.log (k : ℝ) := by
      conv_rhs => rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun k _ => ?_
      by_cases hp : Nat.Prime k
      · have hk : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (show 1 ≤ k from hp.pos)
        simp only [primeLog, ite_eq_left hp, Complex.norm_real, Real.norm_of_nonneg (Real.log_nonneg hk)]
      · simp [primeLog, hp]
    _ ≤ ∑ p ∈ q.primeFactors, Real.log (p : ℝ) := by
      refine Finset.sum_le_sum_of_subset_of_nonneg hsub fun p hp _ => ?_
      exact Real.log_nonneg (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos)
    _ = Real.log (∏ p ∈ q.primeFactors, (p : ℝ)) := by
      symm
      exact Real.log_prod fun p hp => by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero
    _ ≤ _ := by
      apply Real.log_le_log (Finset.prod_pos fun p hp => by
        exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos)
      rw [← Nat.cast_prod]
      exact_mod_cast Nat.le_of_dvd (NeZero.pos q) (Nat.prod_primeFactors_dvd q)

end

end GoldbachGRHWindow

end GoldbachGRHWindowParseval

section GoldbachGRHBandBase

/- The arithmetic foundation is adapted from muxkin's goldbach-proofs PR #2458,
   commit 25c1ef60495052eb22212b5560f90bbc6a4a0917 (Apache-2.0).
   Its source notes attributing earlier components are retained below. -/

/- The finite Ramanujan identities, kernel identities, CRT and prime-power computations
used below adapt DFQDZZ's goldbach-proofs PR #316, commit
e4ab24712555ae8c2c926adf19d368a9fb392c35 (Apache-2.0). Original credits are
retained with the corresponding sections. The multiplicative averaging, sieve estimates,
convolution bounds and the moving-modulus-window argument are derived below. -/

section

/-!
# An explicit lower bound for the Ramanujan-weighted major-arc model

The arithmetic and kernel estimates below are extracted from DFQDZZ's
goldbach-proofs PR #316 (commit e4ab24712555ae8c2c926adf19d368a9fb392c35,
Apache-2.0). The CRT and prime-power computations are credited below.
The estimate applies to every positive even target.
-/

open Finset Filter MeasureTheory

namespace GoldbachExplicitModeledMajor
noncomputable section

def phase (x : ℝ) : ℂ := Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)

def cutoff (n : ℕ) : ℕ := (Nat.log 2 (n + 2)) ^ 2

def kernel (n : ℕ) (β : ℝ) : ℂ := ∑ k ∈ range (n + 1), phase ((k : ℝ) * β)

def width (n q : ℕ) : ℝ := (cutoff n : ℝ) / ((q : ℝ) * n)

def kernelMass (n : ℕ) (b : ℝ) : ℝ := ∫ β in -b..b, ‖kernel n β‖ ^ 2

private theorem continuous_kernel (n : ℕ) : Continuous (kernel n) := by
  unfold kernel phase
  fun_prop

theorem kernelMass_mono {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) (n : ℕ) :
    kernelMass n u ≤ kernelMass n v :=
  intervalIntegral.integral_mono_interval (neg_le_neg huv) (by linarith) huv
    (Eventually.of_forall fun _ => sq_nonneg _) (((continuous_kernel n).norm.pow 2).intervalIntegrable _ _)

private theorem kernel_on_zero_arc {n : ℕ} (hn : 0 < n) {t : ℝ}
    (ht : t ∈ Set.Icc 0 (1 / (6 * (n : ℝ)))) : (n : ℝ) / 2 ≤ ‖kernel n t‖ := by
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  have hnt := (le_div_iff₀ (show 0 < 6 * (n : ℝ) by positivity)).mp ht.2
  have hc (k : ℕ) (hk : k ∈ range (n + 1)) :
      1 / 2 ≤ (phase ((k : ℝ) * t)).re := by
    rw [phase, Complex.exp_ofReal_mul_I_re, ← Real.cos_pi_div_three]
    apply Real.cos_le_cos_of_nonneg_of_le_pi
    · exact mul_nonneg (by positivity) (mul_nonneg (Nat.cast_nonneg _) ht.1)
    · linarith [Real.pi_pos]
    have hk' : (k : ℝ) ≤ n := by exact_mod_cast Nat.lt_succ_iff.mp (mem_range.mp hk)
    have hkt := mul_le_mul_of_nonneg_right hk' ht.1
    nlinarith only [mul_le_mul_of_nonneg_left hnt Real.pi_pos.le,
      mul_le_mul_of_nonneg_left hkt Real.pi_pos.le]
  calc
    _ ≤ ∑ _k ∈ range (n + 1), (1 / 2 : ℝ) := by simp; linarith
    _ ≤ ∑ k ∈ range (n + 1), (phase ((k : ℝ) * t)).re := sum_le_sum hc
    _ = (kernel n t).re := by rw [kernel, Complex.re_sum]
    _ ≤ _ := Complex.re_le_norm _

/-- Each width at least 1/(6n) captures a positive linear amount of the model's mass. -/
theorem kernelMass_floor {n : ℕ} (hn : 0 < n) {b : ℝ} (hb : 1 / (6 * (n : ℝ)) ≤ b) :
    (n : ℝ) / 24 ≤ kernelMass n b := by
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  let u : ℝ := 1 / (6 * (n : ℝ))
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hb0 : 0 ≤ b := hu.trans hb
  have hc := (continuous_kernel n).norm.pow 2
  calc
    _ = ∫ _t in (0 : ℝ)..u, ((n : ℝ) / 2) ^ 2 := by
      rw [intervalIntegral.integral_const]
      simp only [sub_zero, smul_eq_mul, u]
      field_simp
      ring
    _ ≤ ∫ t in (0 : ℝ)..u, ‖kernel n t‖ ^ 2 :=
      intervalIntegral.integral_mono_on hu (by simp) (hc.intervalIntegrable _ _) fun _ ht =>
        pow_le_pow_left₀ (by positivity) (kernel_on_zero_arc hn ht) 2
    _ ≤ _ := intervalIntegral.integral_mono_interval (neg_nonpos.mpr hb0) hu hb
      (Eventually.of_forall fun _ => sq_nonneg _) (hc.intervalIntegrable _ _)

theorem cutoff_positive (n : ℕ) : 1 ≤ cutoff n :=
  Nat.one_le_iff_ne_zero.mpr (pow_ne_zero 2 (Nat.log_pos (by decide : 1 < 2) (by omega : 2 ≤ n+2)).ne')

theorem width_nonneg (n q : ℕ) : 0 ≤ width n q := by unfold width; positivity

end
end GoldbachExplicitModeledMajor

/- The finite CRT and prime-power calculations below adapt goldbach-proofs PRs #207 (XianWu18) and #203 (wzhxzkk), Apache-2.0. -/
namespace GoldbachExplicitModeledMajor.RamanujanCRT
private def unitsBelow (m : ℕ) := (Finset.range m).filter (fun a => Nat.Coprime a m)

private theorem unitsBelow_card (m : ℕ) : (unitsBelow m).card = m.totient := by
  unfold unitsBelow
  rw [Nat.totient_eq_card_coprime]
  congr 1
  ext a
  simp only [Finset.mem_filter, Finset.mem_range]
  exact and_congr_right (fun _ => Nat.coprime_comm)

private noncomputable def phase (m h a : ℕ) : ℂ :=
  Complex.exp (((2 * Real.pi * ((h : ℝ) * a / m) : ℝ) : ℂ) * Complex.I)

private theorem phase_character (m h a : ℕ) [NeZero m] :
    phase m h a = ZMod.stdAddChar ((h : ZMod m) * (a : ZMod m)) := by
  have ch := ZMod.stdAddChar_coe (N := m) ((h * a : ℕ) : ℤ)
  push_cast at ch
  rw [ch]
  unfold phase
  push_cast
  congr 1
  ring

private theorem phase_modulus (m h a : ℕ) [NeZero m] :
    phase m h (a % m) = phase m h a := by
  simp only [phase_character, ZMod.natCast_mod]

private theorem phase_pair (q r h a b : ℕ) (hq : 0 < q) (hr : 0 < r) :
    phase (q*r) h ((r*a + q*b) % (q*r)) = phase q h a * phase r h b := by
  have : NeZero (q*r) := ⟨Nat.ne_of_gt (Nat.mul_pos hq hr)⟩
  rw [phase_modulus]
  unfold phase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  have qnz : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  have rnz : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  field_simp

theorem crt :
    let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let ram := fun (q h : ℕ) => Finset.sum ((Finset.range q).filter (fun a => Nat.Coprime a q)) (fun a => E ((h:ℝ)*(a:ℝ)/(q:ℝ))); ∀ q r h, 0<q → 0<r → Nat.Coprime q r → ram (q*r) h=ram q h*ram r h := by
  dsimp only
  intro q r h hq hr cop
  let combine (x : ℕ × ℕ) := (r*x.1 + q*x.2) % (q*r)
  let pairs := unitsBelow q ×ˢ unitsBelow r
  have member {m a : ℕ} : a ∈ unitsBelow m ↔ a < m ∧ Nat.Coprime a m := by
    simp only [unitsBelow, Finset.mem_filter, Finset.mem_range]
  have maps : pairs.image combine ⊆ unitsBelow (q*r) := by
    intro z hz
    obtain ⟨⟨a,b⟩, hab, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨ha,hb⟩ := Finset.mem_product.mp hab
    apply member.mpr
    refine ⟨Nat.mod_lt _ (Nat.mul_pos hq hr), ?_⟩
    change Nat.gcd ((r*a + q*b) % (q*r)) (q*r) = 1
    rw [← Nat.gcd_rec]
    change Nat.Coprime (q*r) (r*a + q*b)
    apply Nat.coprime_mul_iff_left.mpr
    constructor
    · rw [Nat.coprime_add_mul_left_right]
      exact cop.mul_right (member.mp ha).2.symm
    · rw [add_comm, Nat.coprime_add_mul_left_right]
      exact cop.symm.mul_right (member.mp hb).2.symm
  have injective : Set.InjOn combine (↑pairs) := by
    rintro ⟨a,b⟩ hab ⟨c,d⟩ hcd he
    obtain ⟨ha,hb⟩ := Finset.mem_product.mp hab
    obtain ⟨hc,hd⟩ := Finset.mem_product.mp hcd
    have congruence : r*a + q*b ≡ r*c + q*d [MOD q*r] := he
    apply Prod.ext
    · have hmod := congruence.of_dvd (dvd_mul_right q r)
      have reduced : r*a ≡ r*c [MOD q] := by
        simpa only [Nat.ModEq, Nat.add_mod, Nat.mul_mod_right, add_zero, Nat.mod_mod] using hmod
      exact (Nat.ModEq.cancel_left_of_coprime cop reduced).eq_of_lt_of_lt
        (member.mp ha).1 (member.mp hc).1
    · have hmod := congruence.of_dvd (dvd_mul_left r q)
      have reduced : q*b ≡ q*d [MOD r] := by
        simpa only [Nat.ModEq, Nat.add_mod, Nat.mul_mod_right, zero_add, Nat.mod_mod] using hmod
      exact (Nat.ModEq.cancel_left_of_coprime cop.symm reduced).eq_of_lt_of_lt
        (member.mp hb).1 (member.mp hd).1
  have covers : pairs.image combine = unitsBelow (q*r) := by
    apply Finset.eq_of_subset_of_card_le maps
    rw [Finset.card_image_of_injOn injective, unitsBelow_card, Nat.totient_mul cop]
    simp only [pairs, Finset.card_product, unitsBelow_card]
    exact le_rfl
  change (∑ z ∈ unitsBelow (q*r), phase (q*r) h z) =
    (∑ a ∈ unitsBelow q, phase q h a) * ∑ b ∈ unitsBelow r, phase r h b
  rw [← covers, Finset.sum_image injective, Finset.sum_mul_sum]
  rw [← Finset.sum_product']
  exact Finset.sum_congr rfl (fun x _ => phase_pair q r h x.1 x.2 hq hr)

end GoldbachExplicitModeledMajor.RamanujanCRT
namespace GoldbachExplicitModeledMajor.RamanujanPower
open Finset

theorem primePower :
    let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let ram := fun (q h : ℕ) => Finset.sum ((Finset.range q).filter (fun a => Nat.Coprime a q)) (fun a => E ((h:ℝ)*(a:ℝ)/(q:ℝ))); ∀ p j h, Nat.Prime p → ram (p^(j+1)) h = (if p^(j+1) ∣ h then ((p^(j+1):ℕ):ℂ) else 0) - (if p^j ∣ h then ((p^j:ℕ):ℂ) else 0) := by
  intro E ram p j h hp
  have full (q : ℕ) (hq : 0 < q) :
      ∑ a ∈ range q, E ((h:ℝ) * a / q) = if q ∣ h then (q:ℂ) else 0 := by
    let : NeZero q := ⟨hq.ne'⟩
    calc
      _ = ∑ x : ZMod q, ZMod.stdAddChar ((h : ZMod q) * x) := by
        apply Finset.sum_bij (fun (a : ℕ) _ => (a : ZMod q))
        · intro a ha
          exact mem_univ _
        · intro a ha b hb hab
          simpa only [ZMod.val_natCast_of_lt (mem_range.mp ha),
            ZMod.val_natCast_of_lt (mem_range.mp hb)] using congrArg ZMod.val hab
        · intro x _
          exact ⟨x.val, mem_range.mpr x.val_lt, ZMod.natCast_zmod_val x⟩
        · intro a _
          have cast_eq : (h : ZMod q) * a = ((h * a : ℕ) : ℤ) := by push_cast; rfl
          rw [cast_eq, ZMod.stdAddChar_coe]
          dsimp [E]
          congr 1
          push_cast
          ring
      _ = _ := by
        by_cases hd : q ∣ h
        · have hz : (h : ZMod q) = 0 := (ZMod.natCast_eq_zero_iff h q).mpr hd
          simp [hd, hz, ZMod.card]
        · have hz : (h : ZMod q) ≠ 0 := fun hz => hd ((ZMod.natCast_eq_zero_iff h q).mp hz)
          rw [ite_eq_right hd]
          exact AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar q hz)
  let m := p ^ j
  have hm : 0 < m := pow_pos hp.pos _
  let mult := (range m).image (fun b => p * b)
  have hsub : mult ⊆ range (p^(j+1)) := by
    intro a ha
    obtain ⟨b, hb, rfl⟩ := mem_image.mp ha
    rw [mem_range, pow_succ']
    exact Nat.mul_lt_mul_of_pos_left (mem_range.mp hb) hp.pos
  have hfilter : (range (p^(j+1))).filter (fun a => Nat.Coprime a (p^(j+1))) =
      range (p^(j+1)) \ mult := by
    rw [sdiff_eq_filter]
    apply filter_congr
    intro a ha
    rw [Nat.coprime_pow_right_iff (Nat.succ_pos j), Nat.coprime_comm, hp.coprime_iff_not_dvd]
    apply not_congr
    constructor
    · rintro ⟨b, rfl⟩
      apply mem_image.mpr
      refine ⟨b, mem_range.mpr ?_, rfl⟩
      rw [mem_range, pow_succ'] at ha
      exact (Nat.mul_lt_mul_left hp.pos).mp ha
    · intro ha'
      obtain ⟨b, _, rfl⟩ := mem_image.mp ha'
      exact dvd_mul_right _ _
  have removed : ∑ a ∈ mult, E ((h:ℝ)*a/(p^(j+1):ℕ)) =
      ∑ b ∈ range m, E ((h:ℝ)*b/m) := by
    rw [show mult = (range m).image (fun b => p * b) from rfl,
      sum_image (mul_right_injective₀ hp.ne_zero).injOn]
    apply sum_congr rfl
    intro b _
    congr 1
    rw [pow_succ']
    push_cast
    dsimp [m]
    push_cast
    field_simp [show (p : ℝ) ≠ 0 by exact_mod_cast hp.ne_zero]
  change ∑ a ∈ (range (p^(j+1))).filter _, E ((h:ℝ)*a/(p^(j+1):ℕ)) = _
  rw [hfilter, ← full _ (pow_pos hp.pos (j+1)), ← full _ hm, ← removed]
  exact eq_sub_of_add_eq (sum_sdiff hsub)

end GoldbachExplicitModeledMajor.RamanujanPower

namespace GoldbachExplicitModeledMajor

open Finset
open scoped ComplexConjugate
noncomputable section

def ram (q h : ℕ) : ℂ :=
  ∑ a ∈ (range q).filter (fun a => a.Coprime q), phase ((h : ℝ) * a / q)

theorem ram_mul {q r : ℕ} (hq : 0 < q) (hr : 0 < r) (hc : q.Coprime r) (h : ℕ) :
    ram (q * r) h = ram q h * ram r h := RamanujanCRT.crt q r h hq hr hc

theorem ram_primePower (p j h : ℕ) (hp : p.Prime) :
    ram (p ^ (j + 1)) h = (if p ^ (j + 1) ∣ h then ((p ^ (j + 1) : ℕ) : ℂ) else 0) -
      (if p ^ j ∣ h then ((p ^ j : ℕ) : ℂ) else 0) := RamanujanPower.primePower p j h hp

theorem ram_one (h : ℕ) : ram 1 h = 1 := by simp [ram, phase]

theorem ram_prime {p : ℕ} (hp : p.Prime) (h : ℕ) :
    ram p h = (if p ∣ h then (p : ℂ) else 0) - 1 := by
  simpa using ram_primePower p 0 h hp

private theorem ram_unit_power {p : ℕ} (hp : p.Prime) (j h : ℕ) (hc : h.Coprime p) :
    ram (p ^ (j + 1)) h = if j = 0 then -1 else 0 := by
  have hd := hp.coprime_iff_not_dvd.mp hc.symm
  have hpow (k : ℕ) : ¬ p ^ (k + 1) ∣ h :=
    fun hh => hd ((dvd_pow_self p (Nat.succ_ne_zero k)).trans hh)
  rw [ram_primePower p j h hp, ite_eq_right (hpow j)]
  cases j with
  | zero => simp
  | succ k => simp [hpow k]

def localCoefficient (p n : ℕ) : ℝ :=
  if p ∣ n then 1 / ((p : ℝ) - 1) else -(1 / ((p : ℝ) - 1) ^ 2)

def coefficient (q n : ℕ) : ℂ := (ram q 1 / (q.totient : ℂ)) ^ 2 * conj (ram q n)

theorem coefficient_one (n : ℕ) : coefficient 1 n = 1 := by simp [coefficient, ram_one]

theorem coefficient_mul {q r : ℕ} (hq : 0 < q) (hr : 0 < r) (hc : q.Coprime r) (n : ℕ) :
    coefficient (q * r) n = coefficient q n * coefficient r n := by
  unfold coefficient
  rw [ram_mul hq hr hc, ram_mul hq hr hc, Nat.totient_mul hc, Nat.cast_mul, map_mul]
  ring

theorem coefficient_prime {p : ℕ} (hp : p.Prime) (n : ℕ) :
    coefficient p n = (localCoefficient p n : ℂ) := by
  have hone : ¬ p ∣ 1 := fun h => hp.ne_one (Nat.dvd_one.mp h)
  have hne : (p : ℂ) - 1 ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hp.ne_one)
  rw [coefficient, ram_prime hp, ram_prime hp, ite_eq_right hone, Nat.totient_prime hp,
    Nat.cast_sub hp.one_le, Nat.cast_one]
  by_cases hd : p ∣ n <;> simp [localCoefficient, hd] <;> field_simp

theorem coefficient_higher_power {p : ℕ} (hp : p.Prime) (k n : ℕ) :
    coefficient (p ^ (k + 2)) n = 0 := by
  have h := ram_unit_power hp (k + 1) 1 (by simp)
  simp only [Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ite_false] at h
  simp [coefficient, h]

end
end GoldbachExplicitModeledMajor

namespace GoldbachExplicitModeledMajor

open Finset

noncomputable section
theorem coefficient_not_squarefree {q : ℕ} (n : ℕ) (hq : 0 < q)
    (hs : ¬ Squarefree q) : coefficient q n = 0 := by
  induction q using Nat.recOnPosPrimePosCoprime with
  | zero => omega
  | one => exact (hs squarefree_one).elim
  | prime_pow p k hp hk =>
    cases k with
    | zero => omega
    | succ k =>
      cases k with
      | zero => exact (hs (by simpa using hp.squarefree)).elim
      | succ j => exact coefficient_higher_power hp j n
  | coprime a b ha hb hab ia ib =>
    rw [coefficient_mul (by omega) (by omega) hab]
    by_cases h : Squarefree a
    · rw [ib (by omega) (fun h' => hs ((Nat.squarefree_mul hab).mpr ⟨h,h'⟩)), mul_zero]
    · rw [ia (by omega) h, zero_mul]

theorem coefficient_prime_product (n : ℕ) (s : Finset ℕ)
    (hs : ∀ p ∈ s, p.Prime) :
    coefficient (∏ p ∈ s, p) n = ((∏ p ∈ s, localCoefficient p n : ℝ) : ℂ) := by
  induction s using Finset.induction_on with
  | empty => simp [coefficient_one]
  | @insert p s hp ih =>
    have hprime := hs p (mem_insert_self _ _)
    have hs' : ∀ r ∈ s, r.Prime := fun r hr => hs r (mem_insert_of_mem hr)
    have hcop : p.Coprime (∏ r ∈ s, r) := Nat.coprime_prod_right_iff.mpr fun r hr =>
      (Nat.coprime_primes hprime (hs' r hr)).mpr fun he => hp (he ▸ hr)
    rw [prod_insert hp, prod_insert hp, coefficient_mul hprime.pos (prod_pos fun r hr => (hs' r hr).pos) hcop,
      coefficient_prime hprime, ih hs', Complex.ofReal_mul]


end
end GoldbachExplicitModeledMajor

end

section

namespace BandTail
open Finset GoldbachExplicitModeledMajor
noncomputable section

private theorem coprime_prod_factors {p : ℕ} {s : Finset ℕ} (hp : p.Prime)
    (hs : ∀ r∈s, r.Prime) (hps : p∉s) : p.Coprime (∏ r∈s, r) :=
  Nat.coprime_prod_right_iff.mpr (fun r hr => (Nat.coprime_primes hp (hs r hr)).mpr (fun e => hps (e ▸ hr)))

theorem coeff_norm_le (q n : ℕ) (hq : 0<q) :
    ‖coefficient q n‖ ≤ 1/(q.totient:ℝ) := by
  by_cases hsf : Squarefree q
  · suffices H : ∀ s : Finset ℕ, (∀ p∈s, p.Prime) →
        ‖coefficient (∏ p∈s, p) n‖ ≤ 1/((∏ p∈s, p).totient:ℝ) by
      simpa only [Nat.prod_primeFactors_of_squarefree hsf] using H q.primeFactors
        (fun _ h => Nat.prime_of_mem_primeFactors h)
    intro s
    induction s using Finset.induction_on with
    | empty => simp [coefficient_one]
    | @insert p s hp ih =>
      intro hs
      have hprime := hs p (mem_insert_self ..)
      have hs' (r : ℕ) (hr : r∈s) := hs r (mem_insert_of_mem hr)
      have hc := coprime_prod_factors hprime hs' hp
      have hpos : 0<∏ r∈s, r := prod_pos fun i hi => (hs' i hi).pos
      rw [prod_insert hp,coefficient_mul hprime.pos hpos hc,Nat.totient_mul hc,Nat.cast_mul,norm_mul,
        coefficient_prime hprime, Complex.norm_real,Real.norm_eq_abs]
      have hR : (2:ℝ)≤p := by exact_mod_cast hprime.two_le
      have hp1 : 0≤(p:ℝ)-1 := by linarith
      have hf : |localCoefficient p n| ≤ 1/(p.totient:ℝ) := by
        rw [Nat.totient_prime hprime,Nat.cast_sub hprime.one_le,Nat.cast_one]
        dsimp [localCoefficient]
        split_ifs
        · rw [abs_of_nonneg (by positivity)]
        · rw [abs_neg,abs_of_nonneg (by positivity)]
          apply one_div_le_one_div_of_le (by linarith)
          nlinarith [mul_nonneg (show 0≤(p:ℝ)-1 by linarith) (show 0≤(p:ℝ)-2 by linarith)]
      exact (mul_le_mul hf (ih hs') (norm_nonneg _) (by positivity)).trans_eq (by ring)
  · rw [coefficient_not_squarefree n hq hsf, norm_zero]; positivity

theorem coeff_bad_prime (p r n : ℕ) (hp : p.Prime) (hpn : ¬p∣n) (hr : 0<r) :
    ‖coefficient (p*r) n‖ ≤ 1/((p:ℝ)-1)^2 * (1/(r.totient:ℝ)) := by
  by_cases hc : p.Coprime r
  · rw [coefficient_mul hp.pos hr hc,norm_mul,coefficient_prime hp,Complex.norm_real,Real.norm_eq_abs,
      localCoefficient,if_neg hpn,abs_neg,abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left (coeff_norm_le r n hr) (by positivity)
  · have hpr : p∣r := by simpa [hp.coprime_iff_not_dvd] using hc
    have hsf : ¬Squarefree (p*r) := fun h =>
      Nat.squarefree_iff_prime_squarefree.mp h p hp (Nat.mul_dvd_mul_left _ hpr)
    rw [coefficient_not_squarefree n (Nat.mul_pos hp.pos hr) hsf,norm_zero]
    positivity

theorem good_product {s : Finset ℕ} {n : ℕ} (hs : ∀ p∈s, p.Prime ∧ p∣n) :
    coefficient (∏ p∈s, p) n = ((1/((∏ p∈s, p).totient:ℝ):ℝ):ℂ) := by
  induction s using Finset.induction_on with
  | empty => simp [coefficient_one]
  | @insert p s hp ih =>
    have hprime := (hs p (mem_insert_self ..)).1
    have hpn := (hs p (mem_insert_self ..)).2
    have hs' (r : ℕ) (hr : r∈s) := hs r (mem_insert_of_mem hr)
    have hc := coprime_prod_factors hprime (fun r hr => (hs' r hr).1) hp
    have hpos : 0<∏ r∈s, r := prod_pos fun i hi => (hs' i hi).1.pos
    rw [prod_insert hp,coefficient_mul hprime.pos hpos hc,Nat.totient_mul hc,ih hs',coefficient_prime hprime,
      localCoefficient,if_pos hpn,Nat.totient_prime hprime,Nat.cast_mul,Nat.cast_sub hprime.one_le,Nat.cast_one,←Complex.ofReal_mul]
    congr 1
    simp only [div_eq_mul_inv, mul_inv, mul_pow, inv_pow]; ring

theorem bad_product {s : Finset ℕ} {n : ℕ} (hs : ∀ p∈s, p.Prime ∧ ¬p∣n) :
    coefficient (∏ p∈s, p) n =
      (((ArithmeticFunction.moebius (∏ p∈s, p):ℝ)/((∏ p∈s, p).totient:ℝ)^2:ℝ):ℂ) := by
  induction s using Finset.induction_on with
  | empty => simp [coefficient_one]
  | @insert p s hp ih =>
    have hprime := (hs p (mem_insert_self ..)).1
    have hpn := (hs p (mem_insert_self ..)).2
    have hs' (r : ℕ) (hr : r∈s) := hs r (mem_insert_of_mem hr)
    have hc := coprime_prod_factors hprime (fun r hr => (hs' r hr).1) hp
    have hpos : 0<∏ r∈s, r := prod_pos fun i hi => (hs' i hi).1.pos
    rw [prod_insert hp,coefficient_mul hprime.pos hpos hc,Nat.totient_mul hc,ih hs',coefficient_prime hprime,
      localCoefficient,if_neg hpn,Nat.totient_prime hprime,Nat.cast_mul,Nat.cast_sub hprime.one_le,Nat.cast_one,
      ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hc,ArithmeticFunction.moebius_apply_prime hprime,←Complex.ofReal_mul]
    push_cast
    simp only [div_eq_mul_inv, mul_inv, mul_pow, inv_pow]; ring

theorem coefficient_factorization (q n : ℕ) (hsq : Squarefree q) (hn : 0<n) :
    ∃ d m : ℕ, q=d*m ∧ d∣n ∧ m.Coprime n ∧
      coefficient q n = (((ArithmeticFunction.moebius m:ℝ)/((d.totient:ℝ)*(m.totient:ℝ)^2):ℝ):ℂ) := by
  classical
  let G := q.primeFactors.filter (fun p => p∣n)
  let B := q.primeFactors \ G
  let d := ∏ p∈G, p
  let m := ∏ p∈B, p
  have hG (p : ℕ) (hp : p∈G) : p.Prime ∧ p∣n := by
    obtain ⟨h1,h2⟩ := mem_filter.mp hp
    exact ⟨Nat.prime_of_mem_primeFactors h1,h2⟩
  have hB (p : ℕ) (hp : p∈B) : p.Prime ∧ ¬p∣n := by
    obtain ⟨h1,h2⟩ := mem_sdiff.mp hp
    exact ⟨Nat.prime_of_mem_primeFactors h1,fun hd => h2 (mem_filter.mpr ⟨h1,hd⟩)⟩
  have hqm : q=d*m := by
    have h := Finset.prod_sdiff (f:=id) (s₁:=G) (s₂:=q.primeFactors) (Finset.filter_subset ..)
    simpa [d,m,B,Nat.prod_primeFactors_of_squarefree hsq,mul_comm] using h.symm
  have hdn : d∣n := by
    have hsub : G ⊆ n.primeFactors := fun p hp => Nat.mem_primeFactors.mpr ⟨(hG p hp).1,(hG p hp).2,hn.ne'⟩
    exact dvd_trans (Finset.prod_dvd_prod_of_subset G n.primeFactors id hsub) (Nat.prod_primeFactors_dvd n)
  have hmn : m.Coprime n := Nat.coprime_prod_left_iff.mpr fun p hp => (hB p hp).1.coprime_iff_not_dvd.mpr (hB p hp).2
  refine ⟨d,m,hqm,hdn,hmn,?_⟩
  rw [hqm,coefficient_mul (prod_pos (fun p hp => (hG p hp).1.pos)) (prod_pos (fun p hp => (hB p hp).1.pos))
    (hmn.of_dvd_right hdn).symm, show coefficient d n = _ from good_product hG,
    show coefficient m n = _ from bad_product hB,←Complex.ofReal_mul]
  congr 1
  simp only [div_eq_mul_inv, mul_inv, mul_pow, inv_pow]; ring
end
end BandTail

end

section

namespace BandTail
open Finset ArithmeticFunction GoldbachExplicitModeledMajor
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta
noncomputable section

def smooth (n k : ℕ) : Prop := ∀ p ∈ k.primeFactors, p∣n
instance smoothDec (n k : ℕ) : Decidable (smooth n k) := by unfold smooth; infer_instance

def g (n : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun k => if k=0 then 0 else if smooth n k then 1 else 0,by simp⟩

@[simp] theorem g_one (n : ℕ) : g n 1=1 := by simp [g,smooth]
theorem g_mul (n a b : ℕ) : g n (a*b)=g n a*g n b := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  rcases eq_or_ne b 0 with rfl | hb
  · simp
  have hs : smooth n (a*b) ↔ smooth n a ∧ smooth n b := by
    simp only [smooth,Nat.primeFactors_mul ha hb,mem_union]
    constructor
    · intro h; exact ⟨fun p hp => h p (Or.inl hp),fun p hp => h p (Or.inr hp)⟩
    · rintro ⟨x,y⟩ p (h|h)
      · exact x p h
      · exact y p h
  simp only [g,coe_mk, mul_ne_zero ha hb,ha,hb,ite_false]
  by_cases h1 : smooth n a <;> by_cases h2 : smooth n b <;> simp [hs,h1,h2]
theorem g_mult (n : ℕ) : IsMultiplicative (g n) := ⟨g_one n, fun {_ _} _ => g_mul n _ _⟩
theorem g_prime (n p : ℕ) (hp : p.Prime) : g n p=if p∣n then 1 else 0 := by
  simp [g,smooth,hp.ne_zero,hp.primeFactors]

def F (n : ℕ) : ArithmeticFunction ℝ := ⟨fun q => (q:ℝ)*(coefficient q n).re,by simp⟩

theorem coeff_real {q : ℕ} (hq : 0<q) (n : ℕ) : coefficient q n = (((coefficient q n).re:ℝ):ℂ) := by
  by_cases hsf : Squarefree q
  · have he := coefficient_prime_product n q.primeFactors (fun _ hp => Nat.prime_of_mem_primeFactors hp)
    rw [Nat.prod_primeFactors_of_squarefree hsf] at he
    rw [he]; rfl
  · rw [coefficient_not_squarefree n hq hsf]; simp
theorem F_mult (n : ℕ) : IsMultiplicative (F n) := by
  refine ⟨by simp [F,coefficient_one],fun {a b} hab => ?_⟩
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  rcases eq_or_ne b 0 with rfl | hb
  · simp
  have hzero : (coefficient a n).im=0 := by rw [coeff_real ha.bot_lt n]; rfl
  simp [F,coefficient_mul ha.bot_lt hb.bot_lt hab,Complex.mul_re,hzero]
  ring
theorem F_prime (n p : ℕ) (hp : p.Prime) : F n p=(p:ℝ)*localCoefficient p n := by simp [F,coefficient_prime hp]
theorem F_higher (n p j : ℕ) (hp : p.Prime) : F n (p^(j+2))=0 := by simp [F,coefficient_higher_power hp j n]

def invG (n : ℕ) : ArithmeticFunction ℝ := pmul (μ : ArithmeticFunction ℝ) (g n)
def h (n : ℕ) : ArithmeticFunction ℝ := invG n * F n

theorem h_mult (n : ℕ) : IsMultiplicative (h n) :=
  (isMultiplicative_moebius.intCast.pmul (g_mult n)).mul (F_mult n)

theorem inverse_id (n : ℕ) : g n * invG n = 1 := by
  ext k
  have heq : (g n*invG n) k = g n k * (((ζ : ArithmeticFunction ℝ)*μ) k) := by
    simp only [ArithmeticFunction.mul_apply,Finset.mul_sum,invG,pmul_apply]
    apply Finset.sum_congr rfl
    intro ab hab
    have h0 : 0<ab.1 := Nat.pos_of_mem_divisors (Nat.fst_mem_divisors_of_mem_antidiagonal hab)
    have hG : g n k=g n ab.1*g n ab.2 := (Nat.mem_divisorsAntidiagonal.mp hab).1 ▸ g_mul n ab.1 ab.2
    rw [hG]
    simp [zeta_apply,h0.ne']; ring
  rw [heq,coe_zeta_mul_coe_moebius]
  by_cases hk : k=1 <;> simp [ArithmeticFunction.one_apply,hk]
theorem convolution (n : ℕ) : F n = g n*h n := by rw [h,←mul_assoc,inverse_id,one_mul]

theorem h_prime_recurrence (n p j : ℕ) (hp : p.Prime) :
    h n (p^(j+1))=F n (p^(j+1))-g n p*F n (p^j) := by
  let q := p^(j+1)
  have hq : q≠0 := pow_ne_zero _ hp.ne_zero
  let v := fun d : ℕ => invG n d * F n (q/d)
  have hv : h n q = ∑ d ∈ q.divisors, v d := by
    rw [h,ArithmeticFunction.mul_apply,Nat.sum_divisorsAntidiagonal (fun a b : ℕ => invG n a * F n b)]
  have h1 : ({1,p}:Finset ℕ) ⊆ q.divisors := by
    intro a ha
    simp only [mem_insert,mem_singleton] at ha
    rcases ha with rfl | rfl
    · exact Nat.mem_divisors.mpr ⟨one_dvd _,hq⟩
    · exact Nat.mem_divisors.mpr ⟨dvd_pow_self _ (by omega),hq⟩
  have hsum : ∑ d ∈ q.divisors,v d = ∑ d ∈ ({1,p}:Finset ℕ),v d := by
    symm; apply sum_subset h1
    intro d hd hn
    obtain ⟨i,hi,he⟩ := (Nat.dvd_prime_pow hp).mp (Nat.dvd_of_mem_divisors hd)
    by_cases hi0 : i=0
    · exfalso; apply hn; simp [he,hi0]
    by_cases hi1 : i=1
    · exfalso; apply hn; simp [he,hi1]
    have hm : μ d=0 := by rw [he, moebius_apply_prime_pow hp hi0,if_neg hi1]
    simp [v,invG,pmul_apply,intCoe_apply,hm]
  have hdiv : q/p=p^j := by dsimp [q]; rw [pow_succ,Nat.mul_div_cancel _ hp.pos]
  change h n q = _
  rw [hv,hsum,Finset.sum_insert (by simpa using hp.ne_one.symm : (1:ℕ)∉({p}:Finset ℕ)),Finset.sum_singleton]
  simp [v,invG,pmul_apply,intCoe_apply,moebius_apply_prime hp,hdiv,q]
  ring

theorem h_prime (n p : ℕ) (hp : p.Prime) : h n p =
    if p∣n then 1/((p:ℝ)-1) else -(p:ℝ)/((p:ℝ)-1)^2 := by
  have he := h_prime_recurrence n p 0 hp
  have he1 : F n 1=1 := (F_mult n).map_one
  simp only [Nat.zero_add,pow_one,pow_zero,he1,F_prime n p hp,g_prime n p hp,mul_one] at he
  rw [he]; dsimp [localCoefficient]
  have hr1 : (p:ℝ)-1≠0 := by
    have ht : (2:ℝ)≤p := by exact_mod_cast hp.two_le
    linarith
  split_ifs <;> field_simp <;> ring
theorem h_square (n p : ℕ) (hp : p.Prime) : h n (p^2) =
    if p∣n then -(p:ℝ)/((p:ℝ)-1) else 0 := by
  have he := h_prime_recurrence n p 1 hp
  rw [F_higher n p 0 hp,pow_one,g_prime n p hp,F_prime n p hp] at he
  rw [he]; dsimp [localCoefficient]; split_ifs <;> ring
theorem h_cube (n p j : ℕ) (hp : p.Prime) : h n (p^(j+3))=0 := by
  have he := h_prime_recurrence n p (j+2) hp
  rw [F_higher n p j hp,show j+2+1=(j+1)+2 by omega,F_higher n p (j+1) hp] at he
  simpa [show j+2+1=j+3 by omega] using he

end
end BandTail

end

section

namespace BandTail
open Finset
noncomputable section

private theorem pairPos {q : ℕ} {v : ℕ × ℕ} (hv : v ∈ q.divisorsAntidiagonal) : 0<v.1 ∧ 0<v.2 :=
  ⟨Nat.pos_of_mem_divisors (Nat.fst_mem_divisors_of_mem_antidiagonal hv),
   Nat.pos_of_mem_divisors (Nat.snd_mem_divisors_of_mem_antidiagonal hv)⟩

theorem unpair (U : ℕ) (F : ℕ×ℕ → ℝ) (hF : ∀ x, 0 ≤ F x) :
    (∑ q ∈ Icc 1 U, ∑ v ∈ q.divisorsAntidiagonal, F v) ≤
      ∑ a ∈ Icc 1 U, ∑ b ∈ Icc 1 U, F (a,b) := by
  classical
  let S := Icc 1 U
  have hf (q : ℕ) (hq : q ∈ S) :
      q.divisorsAntidiagonal = (S ×ˢ S).filter (fun ab : ℕ × ℕ => ab.1*ab.2=q) := by
    obtain ⟨hq0,hqQ⟩ := mem_Icc.mp hq
    ext ab
    constructor
    · intro hab
      have hm (a : ℕ) (ha : a ∈ q.divisors) : a ∈ S :=
        mem_Icc.mpr ⟨Nat.pos_of_mem_divisors ha,(Nat.le_of_dvd hq0 (Nat.dvd_of_mem_divisors ha)).trans hqQ⟩
      exact mem_filter.mpr ⟨mem_product.mpr ⟨hm _ (Nat.fst_mem_divisors_of_mem_antidiagonal hab),
        hm _ (Nat.snd_mem_divisors_of_mem_antidiagonal hab)⟩,(Nat.mem_divisorsAntidiagonal.mp hab).1⟩
    · intro h; exact Nat.mem_divisorsAntidiagonal.mpr ⟨(mem_filter.mp h).2,by omega⟩
  calc
    _ = ∑ q ∈ S, ∑ v ∈ (S ×ˢ S).filter (fun ab : ℕ × ℕ => ab.1*ab.2=q), F v :=
      sum_congr rfl (fun q hq => by rw [hf q hq])
    _ = ∑ v ∈ (S ×ˢ S).filter (fun ab : ℕ × ℕ => ab.1*ab.2 ∈ S), F v :=
      sum_fiberwise_eq_sum_filter _ _ _ _
    _ ≤ ∑ v ∈ S ×ˢ S, F v := sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun v _ _ => hF v)
    _ = _ := Finset.sum_product _ _ _

theorem invSquares (U : ℕ) : (∑ k ∈ Icc 1 U, ((k:ℝ)^2)⁻¹) ≤ 2 := by
  rcases U with _ | u
  · simp
  · have hUU : 1≤u+1 := by omega
    have H := sum_Ioc_inv_sq_le_sub (α:=ℝ) (by decide : 1 ≠ 0) hUU
    rw [← Finset.sum_Ioc_add_eq_sum_Icc hUU]
    norm_num at H ⊢
    linarith [show 0 ≤ ((u:ℝ)+1)⁻¹ by positivity]

theorem scaledInvSquares (X v U : ℕ) (hv : 0<v) :
    (X:ℝ) * (∑ k ∈ Icc 1 U, if X<v*k then ((k:ℝ)^2)⁻¹ else 0) ≤ 2*v := by
  by_cases h : X<v
  · have hc : (∑ k ∈ Icc 1 U, if X<v*k then ((k:ℝ)^2)⁻¹ else 0) ≤ 2 :=
      (sum_le_sum fun k _ => by split_ifs <;> first | rfl | positivity).trans (invSquares U)
    exact (mul_le_mul_of_nonneg_left hc (by positivity)).trans (by exact_mod_cast (by omega : X*2 ≤ 2*v))
  have hm : 0<X/v := Nat.div_pos (by omega) hv
  have he : ∑ k ∈ Icc 1 U, (if X<v*k then ((k:ℝ)^2)⁻¹ else 0) =
      ∑ k ∈ Ioc (X/v) U, ((k:ℝ)^2)⁻¹ := by
    rw [← sum_filter]
    congr 1
    ext k
    simp only [mem_filter,mem_Icc,mem_Ioc,Nat.div_lt_iff_lt_mul hv]
    constructor <;> rintro h
    · exact ⟨by simpa [mul_comm] using h.2,h.1.2⟩
    · exact ⟨⟨by cases k <;> simp_all, h.2⟩,by simpa [mul_comm] using h.1⟩
  rw [he]
  by_cases hU : X/v≤U
  · have H := sum_Ioc_inv_sq_le_sub (α:=ℝ) hm.ne' hU
    have hc := H.trans (sub_le_self _ (by positivity))
    have hlim := Nat.div_add_mod X v
    have hmod := Nat.mod_lt X hv
    have hle : X ≤ 2*v*(X/v) := by nlinarith only [hlim,hmod,Nat.mul_le_mul_left v hm]
    have hr : 0<((X/v:ℕ):ℝ) := by exact_mod_cast hm
    refine (mul_le_mul_of_nonneg_left hc (by positivity : 0≤(X:ℝ))).trans ?_
    rw [←div_eq_mul_inv,div_le_iff₀ hr]
    exact_mod_cast hle
  · simp [Finset.Ioc_eq_empty_of_le (by omega : U≤X/v)]

theorem totient_series (U : ℕ) : (∑ q ∈ Icc 1 U, 1/((q:ℝ)*q.totient)) ≤ 4 := by
  let F := fun ab : ℕ×ℕ => ((ab.1:ℝ)^2)⁻¹ * ((ab.2:ℝ)^2)⁻¹
  calc
    _ ≤ ∑ q ∈ Icc 1 U, ∑ ab ∈ q.divisorsAntidiagonal, F ab := by
      apply sum_le_sum
      intro q hq
      have hq0 := (mem_Icc.mp hq).1
      have hφ := Nat.totient_pos.mpr hq0
      have hcount : q ≤ q.divisors.card*q.totient := calc
        _ = ∑ d ∈ q.divisors, d.totient := (Nat.sum_totient q).symm
        _ ≤ ∑ _ ∈ q.divisors, q.totient := sum_le_sum fun d hd => Nat.le_of_dvd hφ (Nat.totient_dvd_of_dvd (Nat.dvd_of_mem_divisors hd))
        _ = _ := by simp
      calc
        _ ≤ (q.divisors.card:ℝ)/(q:ℝ)^2 := by
          have hr : (0:ℝ)<q := by exact_mod_cast hq0
          have hφr : (0:ℝ)<q.totient := by exact_mod_cast hφ
          apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
          have hc : (q:ℝ)≤q.divisors.card*q.totient := by exact_mod_cast hcount
          nlinarith only [mul_le_mul_of_nonneg_left hc hr.le]
        _ = ∑ ab ∈ q.divisorsAntidiagonal, ((q:ℝ)^2)⁻¹ := by
          rw [Nat.sum_divisorsAntidiagonal (fun _ _ => ((q:ℝ)^2)⁻¹)]; simp [div_eq_mul_inv]
        _ = _ := by
          apply sum_congr rfl; intro ab hab
          dsimp [F]
          rw [←(Nat.mem_divisorsAntidiagonal.mp hab).1,Nat.cast_mul,mul_pow,mul_inv]
    _ ≤ ∑ a ∈ Icc 1 U, ∑ b ∈ Icc 1 U, F (a,b) := unpair U F (by intro x; dsimp [F]; positivity)
    _ = (∑ a ∈ Icc 1 U, ((a:ℝ)^2)⁻¹)^2 := by dsimp [F]; rw [sq,Finset.sum_mul_sum]
    _ ≤ 4 := by
      have h := pow_le_pow_left₀ (by exact sum_nonneg (fun _ _ => by positivity)) (invSquares U) 2
      norm_num at h ⊢; exact h

theorem totient_tail (X v U : ℕ) (hv : 0<v) :
    (X:ℝ)*(∑ q ∈ Icc 1 U, if X<v*q then 1/((q:ℝ)*q.totient) else 0) ≤ 8*v := by
  let F := fun ab : ℕ×ℕ => (1 / ((ab.1:ℝ)^2*ab.1.totient)) *
      (if X<v*ab.1*ab.2 then ((ab.2:ℝ)^2)⁻¹ else 0)
  have hF (x : ℕ×ℕ) : 0≤F x := by dsimp [F]; split_ifs <;> positivity
  have hh (q : ℕ) (hq : q ∈ Icc 1 U) :
      (if X<v*q then 1/((q:ℝ)*q.totient) else 0) ≤ ∑ ab ∈ q.divisorsAntidiagonal, F ab := by
    by_cases h : X<v*q
    · rw [if_pos h]
      have hq0 := (mem_Icc.mp hq).1
      have hqR : (0:ℝ)<q := by exact_mod_cast hq0
      have hφR : (0:ℝ)<q.totient := by exact_mod_cast Nat.totient_pos.mpr hq0
      have he : ∑ ab ∈ q.divisorsAntidiagonal, (ab.2.totient:ℝ) = (q:ℝ) := by
        exact_mod_cast (by rw [Nat.sum_divisorsAntidiagonal (fun (_ : ℕ) (b : ℕ) => b.totient), Nat.sum_div_divisors]; exact Nat.sum_totient q : ∑ ab ∈ q.divisorsAntidiagonal, ab.2.totient=q)
      calc
        _ = (∑ ab ∈ q.divisorsAntidiagonal, (ab.2.totient:ℝ))/((q:ℝ)^2*q.totient) := by rw [he]; field_simp
        _ = ∑ ab ∈ q.divisorsAntidiagonal, (ab.2.totient:ℝ)/((q:ℝ)^2*q.totient) := Finset.sum_div _ _ _
        _ ≤ _ := by
          apply sum_le_sum
          intro ab hab
          obtain ⟨ha,hb⟩ := pairPos hab
          have hprod := (Nat.mem_divisorsAntidiagonal.mp hab).1
          have habR : (ab.1:ℝ)*ab.2=q := by exact_mod_cast hprod
          have hφa : (0:ℝ)<ab.1.totient := by exact_mod_cast Nat.totient_pos.mpr ha
          have hbR : (0:ℝ)<ab.2 := by exact_mod_cast hb
          have haR : (0:ℝ)<ab.1 := by exact_mod_cast ha
          have hs := Nat.totient_super_multiplicative ab.1 ab.2
          rw [hprod] at hs
          have hs' : (ab.1.totient:ℝ)*ab.2.totient≤q.totient := by exact_mod_cast hs
          dsimp [F]
          rw [mul_assoc,hprod,if_pos h]
          rw [←habR,mul_pow]
          field_simp
          nlinarith only [hs']
    · rw [if_neg h]; exact sum_nonneg fun ab _ => hF ab
  calc
    _ ≤ (X:ℝ)*(∑ a ∈ Icc 1 U, ∑ b ∈ Icc 1 U, F (a,b)) :=
      mul_le_mul_of_nonneg_left ((sum_le_sum hh).trans (unpair U F hF)) (by positivity)
    _ = ∑ a ∈ Icc 1 U, (1 / ((a:ℝ)^2*a.totient)) *
        ((X:ℝ) * ∑ b ∈ Icc 1 U, if X<(v*a)*b then ((b:ℝ)^2)⁻¹ else 0) := by
      rw [Finset.mul_sum]
      apply sum_congr rfl; intro a _
      dsimp [F]
      rw [←Finset.mul_sum]; ring
    _ ≤ ∑ a ∈ Icc 1 U, 2*(v:ℝ)*(1/((a:ℝ)*a.totient)) := by
      apply sum_le_sum; intro a ha
      have ha0 := (Finset.mem_Icc.mp ha).1
      have hs := scaledInvSquares X (v*a) U (Nat.mul_pos hv ha0)
      refine (mul_le_mul_of_nonneg_left hs (by positivity : 0≤1/((a:ℝ)^2*a.totient))).trans_eq ?_
      push_cast
      have haR : (0:ℝ)<a := by exact_mod_cast ha0
      have hφR : (0:ℝ)<a.totient := by exact_mod_cast Nat.totient_pos.mpr ha0
      field_simp
    _ = 2*(v:ℝ)*(∑ a ∈ Icc 1 U, 1/((a:ℝ)*a.totient)) := (Finset.mul_sum ..).symm
    _ ≤ 8*v := by nlinarith only [mul_le_mul_of_nonneg_left (totient_series U) (show 0≤(v:ℝ) by positivity)]

end
end BandTail

end

section

/- The finite phase and Ramanujan identities in this section are adapted from
DFQDZZ's Apache-2.0 proof in goldbach-proofs PR #316,
commit e4ab24712555ae8c2c926adf19d368a9fb392c35. -/
namespace GoldbachExplicitModeledMajor
open Finset MeasureTheory
open scoped ComplexConjugate
noncomputable section

private theorem windowPhaseAdd (x y : ℝ) : phase (x + y) = phase x * phase y := by
  unfold phase
  rw [← Complex.exp_add]
  push_cast
  congr 1
  ring

private theorem windowConjPhase (x : ℝ) : conj (phase x) = phase (-x) := by
  unfold phase
  rw [← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I]
  congr 1
  push_cast
  ring

/-- Centering the square of the geometric sum makes its phase cancel exactly. -/
theorem windowKernelSquare (n : ℕ) (β : ℝ) :
    kernel n β ^ 2 * phase (-(n : ℝ) * β) = ((‖kernel n β‖ ^ 2 : ℝ) : ℂ) := by
  have hsym : kernel n β * phase (-(n : ℝ) * β) = conj (kernel n β) := by
    unfold kernel
    rw [sum_mul, map_sum]
    calc
      _ = ∑ k ∈ range (n + 1), conj (phase (((n - k : ℕ) : ℝ) * β)) := by
        refine sum_congr rfl fun k hk => ?_
        rw [windowConjPhase, ← windowPhaseAdd, Nat.cast_sub (Nat.lt_succ_iff.mp (mem_range.mp hk))]
        congr 1
        ring
      _ = _ := by
        simpa only [Nat.add_sub_cancel] using
          (Finset.sum_range_reflect (fun k => conj (phase ((k : ℝ) * β))) (n + 1))
  calc
    _ = kernel n β * (kernel n β * phase (-(n : ℝ) * β)) := by ring
    _ = _ := by rw [hsym, Complex.mul_conj, Complex.normSq_eq_norm_sq]

private theorem windowRamPower {p : ℕ} (hp : p.Prime) (j h : ℕ) (hc : h.Coprime p) :
    ram (p ^ (j + 1)) h = if j = 0 then -1 else 0 := by
  have hd := hp.coprime_iff_not_dvd.mp hc.symm
  have hpow (k : ℕ) : ¬ p ^ (k + 1) ∣ h :=
    fun hh => hd ((dvd_pow_self p (Nat.succ_ne_zero k)).trans hh)
  rw [ram_primePower p j h hp, ite_eq_right (hpow j)]
  cases j with
  | zero => simp
  | succ k => simp [hpow k]

theorem windowRamUnit (q h : ℕ) (hc : h.Coprime q) : ram q h = ram q 1 := by
  induction q using Nat.recOnPrimeCoprime with
  | zero => simp [ram]
  | prime_pow p j hp =>
    cases j with
    | zero => simp [ram_one]
    | succ k =>
      have hc' := (Nat.coprime_pow_right_iff (Nat.succ_pos k) h p).mp hc
      rw [windowRamPower hp k h hc', windowRamPower hp k 1 (by simp)]
  | coprime q r hq hr hqr iq ir =>
    obtain ⟨h₁,h₂⟩ := Nat.coprime_mul_iff_right.mp hc
    rw [ram_mul (by omega) (by omega) hqr, ram_mul (by omega) (by omega) hqr, iq h₁, ir h₂]

def windowAvg (q a : ℕ) : ℂ := (∑ r ∈ (range q).filter (fun r => r.Coprime q),
  phase ((r:ℝ)*a/q))/(q.totient:ℂ)

private theorem avg_const (q a : ℕ) (ha : a.Coprime q) :
    windowAvg q a = ram q 1/(q.totient:ℂ) := by
  have hm : (∑ r ∈ (range q).filter (fun r => r.Coprime q), phase ((r:ℝ)*a/q)) = ram q a := by
    unfold ram; apply sum_congr rfl; intro r _; congr 1; ring
  rw [windowAvg,hm,windowRamUnit q a ha]

def windowModel (n A B : ℕ) : ℂ :=
  ∑ q ∈ Ioc A B, ∑ a ∈ (range (q+1)).filter (fun a => a.Coprime q),
    ∫ t in (a:ℝ)/q-width n q..(a:ℝ)/q+width n q,
      (windowAvg q a * kernel n (t-(a:ℝ)/q))^2 * phase (-(n:ℝ)*t)

private theorem windowIntegral (n : ℕ) (c b : ℝ) (z : ℂ) :
    (∫ t in c-b..c+b, (z*kernel n (t-c))^2*phase (-(n:ℝ)*t)) =
      z^2*phase (-(n:ℝ)*c)*(kernelMass n b:ℂ) := by
  have ht := intervalIntegral.integral_comp_add_left
    (fun t => (z*kernel n (t-c))^2*phase (-(n:ℝ)*t)) (a := -b) (b := b) c
  rw [sub_eq_add_neg,← ht]
  calc
    _ = ∫ x in -b..b, (z^2*phase (-(n:ℝ)*c))*((‖kernel n x‖^2:ℝ):ℂ) := by
      apply intervalIntegral.integral_congr
      intro x _
      dsimp only
      rw [add_sub_cancel_left,mul_add,windowPhaseAdd,← windowKernelSquare]
      ring
    _ = _ := by rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_ofReal]; rfl

theorem windowModel_re (n A B : ℕ) (hA : 1≤A) :
    (windowModel n A B).re = ∑ q ∈ Ioc A B, (coefficient q n).re * kernelMass n (width n q) := by
  unfold windowModel
  simp_rw [windowIntegral]
  rw [Complex.re_sum]
  apply sum_congr rfl
  intro q hq
  have hq' : 1<q := lt_of_le_of_lt hA (mem_Ioc.mp hq).1
  have hrange : (range (q+1)).filter (fun a => a.Coprime q) = (range q).filter (fun a => a.Coprime q) := by
    ext a
    simp only [mem_filter,mem_range]
    constructor
    · rintro ⟨ha,hc⟩
      have hne : a ≠ q := by
        rintro rfl
        simp [Nat.Coprime] at hc
        omega
      exact ⟨by omega,hc⟩
    · rintro ⟨ha,hc⟩; exact ⟨by omega,hc⟩
  rw [hrange,← sum_mul]
  have hc : (∑ a ∈ (range q).filter (fun a => a.Coprime q),
      windowAvg q a ^ 2 * phase (-(n:ℝ)*((a:ℝ)/q))) = coefficient q n := by
    unfold coefficient ram
    rw [map_sum,mul_sum]
    apply sum_congr rfl
    intro a ha
    rw [avg_const _ _ (mem_filter.mp ha).2,windowConjPhase]
    congr 2
    ring
  rw [hc,Complex.mul_re]; simp

end
end GoldbachExplicitModeledMajor

end

section

namespace BandTail
open Finset GoldbachExplicitModeledMajor MeasureTheory Filter Topology
noncomputable section

private theorem mass_nonneg (n q : ℕ) : 0 ≤ kernelMass n (width n q) := by
  apply intervalIntegral.integral_nonneg
  · linarith only [width_nonneg n q]
  · intro t _; positivity

theorem mass_upper (n q : ℕ) (hn : 1 ≤ n) (hq : 1 ≤ q) :
    kernelMass n (width n q) ≤ 8*(n:ℝ)*(cutoff n:ℝ)/q := by
  have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hq' : (0:ℝ) < q := by exact_mod_cast hq
  have hK (x : ℝ) : ‖kernel n x‖ ≤ (n:ℝ)+1 := by
    unfold kernel
    exact (norm_sum_le ..).trans (by simp [phase,Complex.norm_exp])
  have hnn := mass_nonneg n q
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := -(width n q)) (b := width n q)
    (f := fun x : ℝ => ‖kernel n x‖^2) (C := ((n:ℝ)+1)^2) (fun t _ => by
      rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (norm_nonneg _) (hK t) 2)
  change |kernelMass n (width n q)| ≤ _ at h
  rw [abs_of_nonneg hnn,abs_of_nonneg (by linarith only [width_nonneg n q])] at h
  refine h.trans ?_
  unfold width
  have hnpos : (0:ℝ) < n := by linarith
  have hQ : 0 ≤ (cutoff n:ℝ) := by positivity
  have hsq : ((n:ℝ)+1)^2 ≤ 4*(n:ℝ)^2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hn') (show 0 ≤ 3*(n:ℝ)+1 by positivity)]
  field_simp
  nlinarith only [mul_le_mul_of_nonneg_right hsq hQ]

private def bandWeight (n q : ℕ) : ℝ := kernelMass n (width n q)/(q:ℝ)

private theorem weight_mono (n i j : ℕ) (hi : 1 ≤ i) (hij : i ≤ j) : bandWeight n j ≤ bandWeight n i := by
  have hi' : (0:ℝ) < i := by exact_mod_cast hi
  have hj' : (0:ℝ) < j := by exact_mod_cast hi.trans hij
  have hr : (i:ℝ) ≤ j := by exact_mod_cast hij
  have hw : width n j ≤ width n i := by
    by_cases hn : n=0
    · simp [width,hn]
    · unfold width
      gcongr
  unfold bandWeight
  apply div_le_div₀ (mass_nonneg n i) (kernelMass_mono (width_nonneg n j) hw n) hi' hr

theorem weighted_prefix_lower (A B : ℕ) (f w : ℕ → ℝ) (k : ℝ)
    (hab : A ≤ B) (hk : 0 ≤ k) (hw : ∀ i ≥ A,0 ≤ w i) (hm : ∀ i ≥ A,w (i+1) ≤ w i)
    (hp : ∀ i ≥ A,i ≤ B → -k ≤ ∑ j ∈ Ioc A i,f j) :
    -(k*w A) ≤ ∑ j ∈ Ioc A B,f j*w j := by
  have strong (i : ℕ) (hi : A ≤ i) (hiB : i ≤ B) :
      w i*((∑ j ∈ Ioc A i,f j)+k) ≤ (∑ j ∈ Ioc A i,f j*w j)+k*w A := by
    induction i,hi using Nat.le_induction with
    | base => simp [mul_comm]
    | succ i hi ih =>
      have h := ih (by omega)
      have hmono := hm i hi
      have hx := hp i hi (by omega)
      rw [sum_Ioc_succ_top hi,sum_Ioc_succ_top hi]
      nlinarith only [h,mul_nonneg (sub_nonneg.mpr hmono) (show 0 ≤ (∑ j ∈ Ioc A i,f j)+k by linarith)]
  have h := strong B hab le_rfl
  have v := hp B hab le_rfl
  nlinarith only [h,mul_nonneg (hw B hab) (show 0 ≤ (∑ j ∈ Ioc A B, f j)+k by linarith)]

theorem model_from_prefix (n B R : ℕ) (δ : ℝ) (hn : 1 ≤ n) (hR : 1 ≤ R) (hδ : 0 ≤ δ)
    (hprefix : ∀ i ≥ cutoff n,i ≤ R*cutoff n → -(δ*(cutoff n:ℝ)) ≤ ∑ q ∈ Ioc (cutoff n) i, F n q) :
    -((8*δ + 64/(R:ℝ))*(n:ℝ)) ≤ (windowModel n (cutoff n) B).re := by
  let A := cutoff n
  have ha : 1 ≤ A := cutoff_positive n
  have ha' : (0:ℝ) < A := by exact_mod_cast ha
  have hr' : (0:ℝ) < R := by exact_mod_cast hR
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  rw [windowModel_re _ _ _ ha]
  change _ ≤ ∑ q ∈ Ioc A B, _
  by_cases hab : A ≤ B
  · let T := min B (R*A)
    have hT : A ≤ T := le_min hab (by dsimp [A]; nlinarith [Nat.mul_le_mul_right (cutoff n) hR])
    have hind := weighted_prefix_lower A T (F n) (bandWeight n) (δ*(A:ℝ)) hT (by positivity)
      (fun i _ => div_nonneg (mass_nonneg n i) (by positivity)) (fun i hi => weight_mono n _ _ (ha.trans hi) (by omega))
      (fun i hi hmax => hprefix i hi (hmax.trans (min_le_right _ _)))
    have hweight : bandWeight n A ≤ 8*(n:ℝ)/A := by
      have h := mass_upper n A hn ha
      change kernelMass n (width n A) ≤ 8*(n:ℝ)*A/A at h
      rw [mul_div_cancel_right₀ _ ha'.ne'] at h
      exact div_le_div_of_nonneg_right h ha'.le
    have hs : -(8*δ*(n:ℝ)) ≤ ∑ q ∈ Ioc A T, (coefficient q n).re * kernelMass n (width n q) := by
      calc
        _ ≤ -(δ*(A:ℝ)*bandWeight n A) := by
          have h := mul_le_mul_of_nonneg_left hweight (show 0 ≤ δ*(A:ℝ) by positivity)
          field_simp at h
          nlinarith only [h]
        _ ≤ _ := hind
        _ = _ := sum_congr rfl (fun q hq => by
          have hq' : (q:ℝ)≠0 := by exact_mod_cast (show q≠0 by have := (mem_Ioc.mp hq).1; omega)
          change (q:ℝ)*_ * (_/(q:ℝ)) = _
          field_simp)
    have ht : -(64*(n:ℝ)/R) ≤ ∑ q ∈ Ioc T B, (coefficient q n).re * kernelMass n (width n q) := by
      by_cases hB : B ≤ R*A
      · simp [T,min_eq_left hB]; positivity
      · rw [show T = R*A from min_eq_right (by omega)]
        have hsum := totient_tail (R*A) 1 B (by decide)
        let S := Ioc (R*A) B
        have he : ∑ q ∈ S, 1/((q:ℝ)*q.totient) ≤
          ∑ q ∈ Icc 1 B, if R*A < 1*q then 1/((q:ℝ)*q.totient) else 0 := by
          rw [← sum_filter]
          apply le_of_eq
          congr 1
          ext q; simp only [S,mem_Ioc,mem_filter,mem_Icc,one_mul]
          constructor <;> rintro h <;> omega
        have hsz : ((R:ℝ)*A)*(∑ q ∈ S,1/((q:ℝ)*q.totient)) ≤ 8 := by
          push_cast at hsum
          exact (mul_le_mul_of_nonneg_left he (by positivity)).trans (by simpa only [Nat.cast_one,mul_one] using hsum)
        have hterm (q : ℕ) (hq : q∈S) : -((8*(n:ℝ)*A)*(1/((q:ℝ)*q.totient))) ≤
            (coefficient q n).re * kernelMass n (width n q) := by
          have hq0 : 1 ≤ q := by have := (mem_Ioc.mp hq).1; omega
          have hq' : (0:ℝ) < q := by exact_mod_cast hq0
          have hφ : (0:ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr hq0
          have hc := (Complex.abs_re_le_norm (coefficient q n)).trans (coeff_norm_le q n hq0)
          have hmass := mass_upper n q hn hq0
          have hprod := mul_le_mul hc hmass (mass_nonneg n q) (by positivity)
          have habs : |(coefficient q n).re * kernelMass n (width n q)| ≤ (1/(q.totient:ℝ))*(8*(n:ℝ)*(cutoff n:ℝ)/q) := by
            simpa only [abs_mul,abs_of_nonneg (mass_nonneg n q)] using hprod
          have hneg := (neg_le_of_abs_le habs)
          convert hneg using 1 <;> dsimp [A] <;> ring
        have hsum' := sum_le_sum hterm
        rw [sum_neg_distrib,← mul_sum] at hsum'
        refine le_trans ?_ hsum'
        apply neg_le_neg
        apply (le_div_iff₀ hr').mpr
        nlinarith only [mul_le_mul_of_nonneg_left hsz (show 0 ≤ 8*(n:ℝ) by positivity)]
    rw [← sum_Ioc_consecutive _ hT (min_le_left _ _)]
    have hid : 64*(n:ℝ)/R = (64/(R:ℝ))*(n:ℝ) := by ring
    linarith
  · simp [Ioc_eq_empty (by omega : ¬ A < B)]
    positivity

end
end BandTail

end

section

namespace BandTail
open Finset GoldbachExplicitModeledMajor Filter Topology
noncomputable section

theorem floor_from_uniform
    (uniform : ∀ R : ℕ, 1 ≤ R → ∀ δ : ℝ, 0 < δ → ∃ A₀ : ℕ,
      ∀ A ≥ A₀, ∀ n i : ℕ, A ≤ i → i ≤ R*A → -(δ*(A:ℝ)) ≤ ∑ q ∈ Ioc A i, F n q) :
    ∀ e : ℝ, 0 < e → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ B : ℕ,
      -(e*(n:ℝ)) ≤ (windowModel n (cutoff n) B).re := by
  intro e he
  let R : ℕ := ⌈128/e⌉₊+1
  have hR : 1 ≤ R := by dsimp [R]; omega
  have hR' : (0:ℝ) < R := by exact_mod_cast hR
  have hlarge : 128 / e ≤ (R:ℝ) := by
    dsimp [R]; push_cast; linarith only [Nat.le_ceil (128/e)]
  have hratio : 64/(R:ℝ) ≤ e/2 := (div_le_iff₀ hR').mpr (by
    have h := (div_le_iff₀ he).mp hlarge
    linarith)
  obtain ⟨A₀,hA⟩ := uniform R hR (e/16) (by positivity)
  refine ⟨2^A₀+1,?_⟩
  intro n hn B
  have hn' : 1 ≤ n := (Nat.succ_le_succ (Nat.zero_le (2^A₀))).trans hn
  have hlog : A₀ ≤ Nat.log 2 (n+2) := (Nat.le_log_iff_pow_le (by decide) (by omega)).mpr (by omega)
  have hl : 1 ≤ Nat.log 2 (n+2) := Nat.log_pos (by decide) (by omega)
  have hc : A₀ ≤ cutoff n := hlog.trans (by
    dsimp [cutoff]; nlinarith [Nat.mul_le_mul_left (Nat.log 2 (n+2)) hl])
  apply le_trans _ (model_from_prefix n B R (e/16) hn' hR (by positivity) (hA _ hc n))
  have hk : 8*(e/16)+64/(R:ℝ) ≤ e := by linarith
  exact neg_le_neg (mul_le_mul_of_nonneg_right hk (by positivity))

end
end BandTail

end

section

namespace BandTail
open Finset ArithmeticFunction
open scoped ArithmeticFunction.zeta
noncomputable section
def w (n : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun d => |h n d|/(d:ℝ)^(3/4:ℝ),by simp⟩
def z (n : ℕ) : ArithmeticFunction ℝ := ⟨fun d => h n d/(d:ℝ),by simp⟩
theorem w_mult (n : ℕ) : IsMultiplicative (w n) := by
  refine ⟨by simp [w,(h_mult n).map_one],fun {a b} hab => ?_⟩
  simp only [w,coe_mk,(h_mult n).map_mul_of_coprime hab,Nat.cast_mul,abs_mul,Real.mul_rpow (Nat.cast_nonneg a) (Nat.cast_nonneg b)]
  ring
theorem z_mult (n : ℕ) : IsMultiplicative (z n) := by
  refine ⟨by simp [z,(h_mult n).map_one],fun {a b} hab => ?_⟩
  simp [z,(h_mult n).map_mul_of_coprime hab]; ring
theorem w_nonneg (n d : ℕ) : 0≤w n d := by dsimp [w]; positivity

theorem localReduce (f : ℕ → ℝ) (hf : ∀ j, f (j+3)=0) (k : ℕ) :
    (∑ i ∈ range (k+1), f i)=f 0 + (if k≥1 then f 1 else 0) + (if k≥2 then f 2 else 0) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [sum_range_succ,ih]
    rcases k with _ | _ | j
    · simp
    · simp
    · simp [hf,show 2≤j+1+1 by omega,show 2≤j+1+1+1 by omega]

theorem wLocal (p n k : ℕ) (hp : p.Prime) :
    (∑ d ∈ (p^k).divisors, w n d) ≤ 1+6/((p:ℝ)^(3/2:ℝ)) := by
  have hp2 : (2:ℝ)≤p := by exact_mod_cast hp.two_le
  have hp1 : 0<(p:ℝ)-1 := by linarith
  have hpr : 0<(p:ℝ) := by linarith
  have hW1 : w n p ≤ 4/((p:ℝ)^(3/2:ℝ)) := by
    have h₁ : |h n p| ≤ 4/(p:ℝ) := by
      rw [h_prime n p hp]
      split_ifs
      · rw [abs_of_nonneg (by positivity)]; field_simp; linarith
      · rw [abs_div,abs_neg,abs_of_nonneg hpr.le,abs_of_nonneg (sq_nonneg _)]
        field_simp
        nlinarith [mul_nonneg (show 0≤(p:ℝ)-2 by linarith) (show 0≤3*(p:ℝ)-2 by linarith)]
    dsimp [w]
    calc
      _ ≤ (4/(p:ℝ))/((p:ℝ)^(3/4:ℝ)) := div_le_div_of_nonneg_right h₁ (by positivity)
      _ = 4/(p:ℝ)^(1+(3/4):ℝ) := by rw [Real.rpow_add hpr,Real.rpow_one,div_div]
      _ ≤ _ := by apply div_le_div_of_nonneg_left (by norm_num) (by positivity); exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  have hW2 : w n (p^2) ≤ 2/(p:ℝ)^(3/2:ℝ) := by
    have he : |h n (p^2)| ≤ 2 := by
      rw [h_square n p hp]; split_ifs
      · rw [abs_div,abs_neg,abs_of_nonneg hpr.le,abs_of_nonneg hp1.le]; apply (div_le_iff₀ hp1).mpr; linarith
      · norm_num
    change |h n (p^2)| / ((p^2:ℕ):ℝ)^(3/4:ℝ) ≤ _
    rw [Nat.cast_pow,←Real.rpow_natCast_mul hpr.le,show (↑(2:ℕ):ℝ)*(3/4)=3/2 by norm_num]
    exact div_le_div_of_nonneg_right he (by positivity)
  rw [Nat.sum_divisors_prime_pow hp,localReduce (fun j => w n (p^j)) (fun j => by simp [w,h_cube n p j hp])]
  simp only [pow_zero,pow_one,(w_mult n).map_one]
  simp only [div_eq_mul_inv] at hW1 hW2 ⊢
  split_ifs <;> linarith [w_nonneg n p,w_nonneg n (p^2)]

theorem zLocal (p n k : ℕ) (hp : p.Prime) : 0≤∑ d ∈ (p^k).divisors,z n d := by
  rw [Nat.sum_divisors_prime_pow hp,localReduce (fun j => z n (p^j)) (fun j => by simp [z,h_cube n p j hp])]
  simp only [pow_zero,pow_one,(z_mult n).map_one]
  have h2 : (2:ℝ)≤p := by exact_mod_cast hp.two_le
  have hp1 : 0<(p:ℝ)-1 := by linarith
  have hpr : 0<(p:ℝ) := by linarith
  have hsq : 1≤((p:ℝ)-1)^2 := by nlinarith [mul_nonneg (show 0≤(p:ℝ)-2 by linarith) (show 0≤(p:ℝ) by linarith)]
  simp only [z,coe_mk,h_prime n p hp,h_square n p hp,Nat.cast_pow]
  by_cases hpn : p∣n
  · simp only [hpn,ite_true]
    split_ifs with hk hk2
    · field_simp; nlinarith [mul_pos hpr hp1]
    · positivity
    · omega
    · norm_num
  · simp only [hpn,ite_false,zero_div,ite_self,add_zero]
    split_ifs
    · field_simp; nlinarith [mul_le_mul_of_nonneg_right hsq hpr.le]
    · norm_num

def universal : ℝ := Real.exp (6*∑' j : ℕ, ((j:ℝ)^(3/2:ℝ))⁻¹)

theorem uniformDivisors (n M : ℕ) (hM : 0<M) :
    (∑ d ∈ M.divisors, w n d) ≤ universal := by
  let A : ArithmeticFunction ℝ := w n * (ζ : ArithmeticFunction ℝ)
  have hA : IsMultiplicative A := (w_mult n).mul isMultiplicative_zeta.natCast
  have he (m : ℕ) : A m = ∑ d ∈ m.divisors,w n d := coe_mul_zeta_apply
  have hprod := hA.multiplicative_factorization A hM.ne'
  rw [he] at hprod
  rw [hprod,Finsupp.prod]
  calc
    _ ≤ ∏ p ∈ M.factorization.support, Real.exp (6/((p:ℝ)^(3/2:ℝ))) := by
      refine Finset.prod_le_prod₀ (fun p hp => ?_) (fun p hp => ?_)
      · rw [he]; exact sum_nonneg fun d _ => w_nonneg n d
      · rw [he]
        have hh : p ∈ M.primeFactors := M.support_factorization ▸ hp
        exact (wLocal p n _ (Nat.prime_of_mem_primeFactors hh)).trans (by linarith [Real.add_one_le_exp (6/((p:ℝ)^(3/2:ℝ)))])
    _ ≤ universal := by
      rw [←Real.exp_sum,universal]
      apply Real.exp_le_exp.mpr
      simp_rw [div_eq_mul_inv,←mul_sum]
      apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ)≤6)
      exact (Real.summable_nat_rpow_inv.mpr (by norm_num : (1:ℝ)<3/2)).sum_le_tsum _ (by intro _ _; positivity)

theorem signedDivisors (n M : ℕ) (hM : 0<M) :
    0 ≤ ∑ d ∈ M.divisors, z n d := by
  let A : ArithmeticFunction ℝ := z n * (ζ : ArithmeticFunction ℝ)
  have hA : IsMultiplicative A := (z_mult n).mul isMultiplicative_zeta.natCast
  have he (m : ℕ) : A m = ∑ d ∈ m.divisors,z n d := coe_mul_zeta_apply
  have hh := hA.multiplicative_factorization A hM.ne'
  rw [he] at hh
  rw [hh,Finsupp.prod]
  apply Finset.prod_nonneg
  intro p hp
  rw [he]
  exact zLocal p n _ (Nat.prime_of_mem_primeFactors (M.support_factorization ▸ hp))

theorem prefixDiv (J : ℕ) : Icc 1 J ⊆ J.factorial.divisors := by
  intro d hd
  obtain ⟨hd1, hdJ⟩ := mem_Icc.mp hd
  exact Nat.mem_divisors.mpr ⟨Nat.dvd_factorial hd1 hdJ,J.factorial_pos.ne'⟩

theorem uniformPrefix (n J : ℕ) : (∑ d ∈ Icc 1 J, w n d)≤universal :=
  (sum_le_sum_of_subset_of_nonneg (prefixDiv J) (fun d _ _ => w_nonneg n d)).trans
    (uniformDivisors n _ J.factorial_pos)

theorem tailTerm (n J d : ℕ) (hJ : 0<J) (hJd : J≤d) :
    |z n d| ≤ w n d / ((J:ℝ)^(1/4:ℝ)) := by
  have hd : 0<(d:ℝ) := by exact_mod_cast hJ.trans_le hJd
  have hJr : 0<(J:ℝ) := by exact_mod_cast hJ
  have he : (d:ℝ)^(3/4:ℝ)*(d:ℝ)^(1/4:ℝ)=d := by
    rw [←Real.rpow_add hd,show (3/4:ℝ)+1/4=1 by norm_num,Real.rpow_one]
  change |h n d / (d:ℝ)| ≤ |h n d| / _ / _
  rw [abs_div,abs_of_pos hd,div_div]
  apply div_le_div_of_nonneg_left (abs_nonneg _) (mul_pos (Real.rpow_pos_of_pos hd _) (Real.rpow_pos_of_pos hJr _))
  apply le_trans _ he.le
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) (by exact_mod_cast hJd) (by norm_num)) (by positivity)

theorem uniformTail (n J : ℕ) (s : Finset ℕ) (hJ : 0<J) (hs : ∀ d ∈ s,J≤d) :
    (∑ d ∈ s, |z n d|) ≤ universal / (J:ℝ)^(1/4:ℝ) := by
  have hb : s⊆Icc 1 (s.sup id) := by
    intro d hd
    exact mem_Icc.mpr ⟨by have := hs d hd; omega, le_sup (f:=id) hd⟩
  calc
    _ ≤ ∑ d ∈ s, w n d / (J:ℝ)^(1/4:ℝ) := sum_le_sum fun d hd => tailTerm n J d hJ (hs d hd)
    _ = _ := (sum_div _ _ _).symm
    _ ≤ _ := div_le_div_of_nonneg_right ((sum_le_sum_of_subset_of_nonneg hb (fun d _ _ => w_nonneg n d)).trans (uniformPrefix n _)) (by positivity)

theorem signedPrefix (n J : ℕ) (hJ : 0<J) :
    -(universal / (J:ℝ)^(1/4:ℝ)) ≤ ∑ d ∈ Icc 1 J, z n d := by
  have hu := uniformTail n J (J.factorial.divisors \ Icc 1 J) hJ (by
    intro d hd
    obtain ⟨hd,hd'⟩ := mem_sdiff.mp hd
    have hpos := Nat.pos_of_mem_divisors hd
    simp only [mem_Icc,not_and] at hd'
    omega)
  have hh := signedDivisors n J.factorial J.factorial_pos
  rw [←sum_sdiff (s₁:=Icc 1 J) (s₂:=J.factorial.divisors) (prefixDiv J)] at hh
  have ht := sum_le_sum (s:=J.factorial.divisors \ Icc 1 J) (fun d _ => le_abs_self (z n d))
  linarith

end
end BandTail

end

section

namespace BandTail
open Finset ArithmeticFunction
noncomputable section

def gSum (n X : ℕ) : ℝ := ∑ k ∈ Icc 1 X, g n k
def gAvg (n X : ℕ) : ℝ := gSum n X / X
def fSum (n X : ℕ) : ℝ := ∑ k ∈ Icc 1 X, F n k

theorem g_sum_bounds (n X : ℕ) : 0≤gSum n X ∧ gSum n X≤X := by
  constructor
  · apply sum_nonneg
    intro k hk
    simp [g]; split_ifs <;> norm_num
  · calc
      _ ≤ ∑ k ∈ Icc 1 X,(1:ℝ) := by
        apply sum_le_sum
        intro k hk
        simp [g]; split_ifs <;> norm_num
      _ = _ := by simp

theorem g_avg_bounds (n X : ℕ) : 0≤gAvg n X ∧ gAvg n X≤1 := by
  have hb := g_sum_bounds n X
  exact ⟨div_nonneg hb.1 (Nat.cast_nonneg _),div_le_one_of_le₀ hb.2 (Nat.cast_nonneg _)⟩

theorem fSum_convolution (n X : ℕ) :
    fSum n X = ∑ d ∈ Icc 1 X,h n d * gSum n (X/d) := by
  classical
  let S := Icc 1 X
  let f := fun v : ℕ × ℕ => h n v.1 * g n v.2
  have hf (q : ℕ) (hq : q ∈ S) :
      q.divisorsAntidiagonal = (S ×ˢ S).filter (fun ab : ℕ × ℕ => ab.1*ab.2=q) := by
    obtain ⟨hq0,hqQ⟩ := mem_Icc.mp hq
    ext ab
    constructor
    · intro hab
      have hm (a : ℕ) (ha : a ∈ q.divisors) : a ∈ S :=
        mem_Icc.mpr ⟨Nat.pos_of_mem_divisors ha,(Nat.le_of_dvd hq0 (Nat.dvd_of_mem_divisors ha)).trans hqQ⟩
      exact mem_filter.mpr ⟨mem_product.mpr ⟨hm _ (Nat.fst_mem_divisors_of_mem_antidiagonal hab),
        hm _ (Nat.snd_mem_divisors_of_mem_antidiagonal hab)⟩,(Nat.mem_divisorsAntidiagonal.mp hab).1⟩
    · intro hh; exact Nat.mem_divisorsAntidiagonal.mpr ⟨(mem_filter.mp hh).2,by omega⟩
  calc
    _ = ∑ q ∈ S,∑ v ∈ q.divisorsAntidiagonal,f v := by
      simp [fSum,S,convolution n,mul_comm (g n) (h n),ArithmeticFunction.mul_apply,f]
    _ = ∑ q ∈ S, ∑ v ∈ (S ×ˢ S).filter (fun ab : ℕ × ℕ => ab.1*ab.2=q), f v :=
      sum_congr rfl (fun q hq => by rw [hf q hq])
    _ = ∑ v ∈ (S ×ˢ S).filter (fun ab : ℕ × ℕ => ab.1*ab.2 ∈ S), f v :=
      sum_fiberwise_eq_sum_filter _ _ _ _
    _ = _ := by
      rw [sum_filter,sum_product]
      apply sum_congr rfl
      intro d hd
      have hd0 := (mem_Icc.mp hd).1
      have hkd : (S.filter fun k => d*k∈S)=Icc 1 (X/d) := by
        ext k
        simp only [S,mem_filter,mem_Icc]
        constructor
        · rintro ⟨⟨hk,_⟩,_,hdk⟩
          exact ⟨hk,(Nat.le_div_iff_mul_le hd0).mpr (by simpa [mul_comm] using hdk)⟩
        · rintro ⟨hk,hkx⟩
          exact ⟨⟨hk,hkx.trans (Nat.div_le_self _ _)⟩,Nat.mul_pos hd0 hk, by simpa [mul_comm] using (Nat.le_div_iff_mul_le hd0).mp hkx⟩
      simp only [f,gSum,mul_sum]
      rw [←sum_filter,hkd]

theorem prefix_split (f : ℕ→ℝ) {J X : ℕ} (hJX : J≤X) :
    (∑ d ∈ Icc 1 X,f d)=(∑ d ∈ Icc 1 J,f d)+(∑ d ∈ Ioc J X,f d) := by
  have he : Icc 1 X=Icc 1 J ∪ Ioc J X := by ext k; simp only [mem_union,mem_Icc,mem_Ioc]; omega
  rw [he,sum_union (by rw [Finset.disjoint_left]; intro k hk hj; have := (mem_Icc.mp hk).2; have := (mem_Ioc.mp hj).1; omega)]

def scaleFactor (X d : ℕ) : ℝ := (d:ℝ)*(X/d:ℕ)/X

theorem scale_bounds (X d : ℕ) (hX : 0<X) (hd : 0<d) :
    0≤ scaleFactor X d ∧ scaleFactor X d ≤ 1 ∧ 1-scaleFactor X d ≤ (d:ℝ)/X := by
  have hx : 0<(X:ℝ) := by exact_mod_cast hX
  have hx0 : (d:ℝ)*(X/d:ℕ) ≤ X := by exact_mod_cast Nat.mul_div_le X d
  have hx1 : (X:ℝ) < (d:ℝ)*((X/d:ℕ)+1:ℝ) := by exact_mod_cast Nat.lt_mul_div_succ X hd
  unfold scaleFactor
  refine ⟨by positivity,(div_le_iff₀ hx).mpr (by linarith),?_⟩
  rw [sub_div' hx.ne',div_le_div_iff_of_pos_right hx]
  linarith

theorem scaled_piece (n X d : ℕ) (hd : 0<d) :
    h n d * gSum n (X/d) / X = z n d * (scaleFactor X d * gAvg n (X/d)) := by
  have hdr : (d:ℝ)≠0 := by exact_mod_cast hd.ne'
  by_cases hy : X/d=0
  · simp [gSum,gAvg,scaleFactor,hy]
  · have hyr : ((X/d:ℕ):ℝ)≠0 := by exact_mod_cast hy
    simp only [z,coe_mk,scaleFactor,gAvg]
    field_simp

theorem piece_approx (n X d : ℕ) (hX : 0<X) (hd : 0<d) (t e : ℝ)
    (he : |gAvg n (X/d)-t|≤e) (hdX : (d:ℝ)/X≤e) :
    |h n d * gSum n (X/d) / X - z n d * t| ≤ |z n d| *(2*e) := by
  obtain ⟨_,hs,hs'⟩ := scale_bounds X d hX hd
  have hg := g_avg_bounds n (X/d)
  have hc : |scaleFactor X d * gAvg n (X/d)-gAvg n (X/d)| ≤ e := by
    rw [←sub_one_mul,abs_mul,abs_of_nonpos (sub_nonpos.mpr hs),abs_of_nonneg hg.1]
    calc
      _ ≤ -(scaleFactor X d-1)*1 := mul_le_mul_of_nonneg_left hg.2 (by linarith)
      _ ≤ e := by linarith
  rw [scaled_piece n X d hd,←mul_sub,abs_mul]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  exact (abs_sub_le _ (gAvg n (X/d)) _).trans (by linarith)

theorem dyadic_approx (n X J : ℕ) (hX : 0<X) (hJ : 0<J) (hJX : J≤X) (t e : ℝ) (he : 0≤e)
    (hne : ∀ d ∈ Icc 1 J,|gAvg n (X/d)-t|≤e) (hJr : (J:ℝ)/X ≤ e) :
    |fSum n X / X - (∑ d ∈ Icc 1 J,z n d)*t| ≤
      universal*(2*e)+universal/(J:ℝ)^(1/4:ℝ) := by
  let a := fun d => h n d * gSum n (X/d) / X
  have hsmall : |∑ d ∈ Icc 1 J,(a d-z n d*t)|≤universal*(2*e) := by
    apply (abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑ d ∈ Icc 1 J, |z n d| *(2*e) := by
        refine sum_le_sum fun d hd => piece_approx n X d hX (mem_Icc.mp hd).1 t e (hne _ hd) ?_
        exact (div_le_div_of_nonneg_right (by exact_mod_cast (mem_Icc.mp hd).2) (Nat.cast_nonneg _)).trans hJr
      _ = _ := (sum_mul _ _ _).symm
      _ ≤ _ := by
        have hu := uniformTail n 1 (Icc 1 J) (by decide) (fun d hd => (mem_Icc.mp hd).1)
        norm_num at hu
        exact mul_le_mul_of_nonneg_right hu (by positivity)
  have hlarge : |∑ d ∈ Ioc J X,a d| ≤ universal/(J:ℝ)^(1/4:ℝ) := by
    apply (abs_sum_le_sum_abs _ _).trans
    apply le_trans _ (uniformTail n J (Ioc J X) hJ (fun d hd => (mem_Ioc.mp hd).1.le))
    apply sum_le_sum
    intro d hd
    have hd0 : 0<d := hJ.trans (mem_Ioc.mp hd).1
    obtain ⟨hs,hs',_⟩ := scale_bounds X d hX hd0
    have hg := g_avg_bounds n (X/d)
    dsimp only [a]; rw [scaled_piece n X d hd0,abs_mul,abs_of_nonneg (mul_nonneg hs hg.1)]
    exact mul_le_of_le_one_right (abs_nonneg _) (mul_le_one₀ hs' hg.1 hg.2)
  have htotal : fSum n X / X = (∑ d ∈ Icc 1 J,a d)+(∑ d ∈ Ioc J X,a d) := by
    rw [fSum_convolution,sum_div]
    exact prefix_split a hJX
  rw [htotal,sum_mul]
  rw [show (∑ d ∈ Icc 1 J,a d)+(∑ d ∈ Ioc J X,a d)-(∑ d ∈ Icc 1 J,z n d*t)=
      (∑ d ∈ Icc 1 J,(a d-z n d*t))+(∑ d ∈ Ioc J X,a d) by rw [sum_sub_distrib]; ring]
  exact (abs_add_le _ _).trans (add_le_add hsmall hlarge)

end
end BandTail

end

section

namespace GoldbachModelMean

open Finset Filter Topology

private def modProd (s : Finset Nat.Primes) : ℕ := ∏ p ∈ s, (p:ℕ)

private theorem modProd_pos (s : Finset Nat.Primes) : 0 < modProd s :=
  Finset.prod_pos (fun p _ => p.property.pos)

private theorem totientProd (s : Finset Nat.Primes) :
    ((modProd s).totient:ℝ)*(1+∑ p ∈ s, 1/(p:ℝ)) ≤ modProd s := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [modProd]
  | @insert p s hps ih =>
    have hcop : (p:ℕ).Coprime (modProd s) := by
      apply Nat.coprime_prod_right_iff.mpr
      intro q hq
      apply (Nat.coprime_primes p.property q.property).mpr
      intro h
      exact hps ((Subtype.ext h : p=q) ▸ hq)
    have heq : modProd (insert p s) = (p:ℕ)*modProd s := Finset.prod_insert hps
    have hp : (1:ℕ)≤p.val := p.property.one_lt.le
    have hp' : (0:ℝ)<p := by exact_mod_cast p.property.pos
    have hsum : 0 ≤ ∑ q ∈ s, (1:ℝ)/(q:ℝ) := sum_nonneg fun q _ => by positivity
    rw [heq,Nat.totient_mul hcop,Nat.totient_prime p.property,Finset.sum_insert hps]
    push_cast [Nat.cast_sub hp]
    calc
      _ ≤ (p:ℝ)*(((modProd s).totient:ℝ)*(1+∑ q ∈ s, 1/(q:ℝ))) := by
        have : ((p:ℝ)-1)*(1+(1/(p:ℝ)+∑ q ∈ s, 1/(q:ℝ))) ≤ (p:ℝ)*(1+∑ q ∈ s, 1/(q:ℝ)) := by
          field_simp
          nlinarith [mul_nonneg hp'.le hsum]
        nlinarith only [mul_le_mul_of_nonneg_right this (Nat.cast_nonneg (modProd s).totient (α:=ℝ))]
      _ ≤ _ := mul_le_mul_of_nonneg_left ih hp'.le

theorem exists_thin_modulus (e : ℝ) (he : 0<e) :
    ∃ D : ℕ, 0<D ∧ (D.totient:ℝ)/(D:ℝ)<e := by
  classical
  have hs : ∃ s : Finset Nat.Primes, (1/e:ℝ) < ∑ p ∈ s, 1/(p:ℝ) := by
    by_contra! h
    exact Nat.Primes.not_summable_one_div (summable_of_sum_le (fun p => by positivity) h)
  obtain ⟨s,hs⟩ := hs
  refine ⟨modProd s,modProd_pos s,(div_lt_iff₀ (by exact_mod_cast modProd_pos s)).mpr ?_⟩
  have h := totientProd s
  have ht : (0:ℝ) < (modProd s).totient := by exact_mod_cast Nat.totient_pos.mpr (modProd_pos s)
  have h1 := (div_lt_iff₀ he).mp hs
  nlinarith only [mul_le_mul_of_nonneg_right h he.le,
    mul_lt_mul_of_pos_right h1 ht,mul_pos he ht]

def fewFactors (k X : ℕ) : Finset ℕ :=
  (range X).filter fun n => 0 < n ∧ n.primeFactorsList.length ≤ k

private theorem few_step (k X D : ℕ) (hD : 0<D) :
    (fewFactors (k+1) X).card ≤ D.totient*(X/D+1)+(D+1)*(fewFactors k X).card := by
  classical
  let R := (range X).filter fun n => D.Coprime n
  let cover := (range (D+1)).biUnion fun p => (fewFactors k X).image fun y => p*y
  have hsub : fewFactors (k+1) X ⊆ R ∪ cover := by
    intro x hx
    obtain ⟨hxX,hxp,hxk⟩ := mem_filter.mp hx
    by_cases hc : D.Coprime x
    · exact mem_union_left _ (mem_filter.mpr ⟨hxX,hc⟩)
    obtain ⟨p,hp,hpd,hpx⟩ := Nat.Prime.not_coprime_iff_dvd.mp hc
    obtain ⟨y,rfl⟩ := hpx
    have hy : y ≠ 0 := by intro hz; simp [hz] at hxp
    have hlen := (Nat.perm_primeFactorsList_mul hp.ne_zero hy).length_eq
    simp [Nat.primeFactorsList_prime hp] at hlen
    have hyX : y < X := lt_of_le_of_lt (by simpa [Nat.mul_comm] using Nat.le_mul_of_pos_left y hp.pos) (mem_range.mp hxX)
    exact mem_union_right _ (mem_biUnion.mpr ⟨p,mem_range.mpr (by have := Nat.le_of_dvd hD hpd; omega),
      mem_image.mpr ⟨y,mem_filter.mpr ⟨mem_range.mpr hyX,by omega,by omega⟩,rfl⟩⟩)
  have hR : R.card ≤ D.totient*(X/D+1) := by
    simpa only [R,zero_add,← range_eq_Ico] using Nat.Ico_filter_coprime_le 0 X hD.ne'
  have hc : cover.card ≤ (D+1)*(fewFactors k X).card := calc
    _ ≤ ∑ p ∈ range (D+1), ((fewFactors k X).image fun y => p*y).card := card_biUnion_le
    _ ≤ ∑ _ ∈ range (D+1), (fewFactors k X).card := by exact Finset.sum_le_sum (fun p _ => card_image_le)
    _ = _ := by simp
  exact (card_le_card hsub).trans ((card_union_le _ _).trans (Nat.add_le_add hR hc))

theorem fewFactors_eventually (k : ℕ) (e : ℝ) (he : 0<e) :
    ∀ᶠ X : ℕ in atTop, ((fewFactors k X).card:ℝ) ≤ e*X := by
  induction k generalizing e with
  | zero =>
    filter_upwards [(tendsto_natCast_atTop_atTop (R:=ℝ)).eventually_ge_atTop (1/e)] with X hX
    have hsub : fewFactors 0 X ⊆ {1} := by
      intro x hx
      obtain ⟨_,hp,hl⟩ := mem_filter.mp hx
      have hn := (Nat.primeFactorsList_eq_nil x).mp (List.length_eq_zero_iff.mp (by omega))
      simp only [mem_singleton]
      omega
    have hc : (fewFactors 0 X).card ≤ 1 := by simpa using card_le_card hsub
    change 1/e ≤ (X:ℝ) at hX
    have hh := (div_le_iff₀ he).mp hX
    exact (by exact_mod_cast hc : ((fewFactors 0 X).card:ℝ) ≤ 1) |>.trans (by linarith)
  | succ k ih =>
    obtain ⟨D,hD,hphi⟩ := exists_thin_modulus (e/4) (by positivity)
    have hD' : (0:ℝ)<D := by exact_mod_cast hD
    filter_upwards [ih (e/(4*(D+1))) (by positivity),
      (tendsto_natCast_atTop_atTop (R:=ℝ)).eventually_ge_atTop (4*(D.totient:ℝ)/e)] with X hprev hlarge
    change 4*(D.totient:ℝ)/e ≤ X at hlarge
    have hr := (div_le_iff₀ he).mp hlarge
    have hp := (div_lt_iff₀ hD').mp hphi
    have hquot : ((X/D:ℕ):ℝ) ≤ (X:ℝ)/D := by
      apply (le_div_iff₀ hD').mpr
      exact_mod_cast Nat.div_mul_le_self X D
    have h := few_step k X D hD
    have h' : ((fewFactors (k+1) X).card:ℝ) ≤ D.totient*(((X/D:ℕ):ℝ)+1)+((D:ℝ)+1)*(fewFactors k X).card := by exact_mod_cast h
    have hf : ((D:ℝ)+1)*((fewFactors k X).card:ℝ) ≤ (e/4)*X := by
      calc
        _ ≤ ((D:ℝ)+1)*(e/(4*(D+1))*X) := mul_le_mul_of_nonneg_left hprev (by positivity)
        _ = _ := by field_simp
    have hg : (D.totient:ℝ)*((X/D:ℕ):ℝ) ≤ (e/4)*X := calc
      _ ≤ (D.totient:ℝ)*((X:ℝ)/D) := mul_le_mul_of_nonneg_left hquot (by positivity)
      _ = ((D.totient:ℝ)/D)*X := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hphi.le (by positivity)
    nlinarith only [h',hf,hg,hr,mul_nonneg he.le (Nat.cast_nonneg X (α:=ℝ))]

end GoldbachModelMean

end

section

noncomputable section
namespace GoldbachModelMean.Brun
open Finset Filter

def product (s : Finset ℕ) := ∏ p ∈ s, p
def hits (P : Finset ℕ) (m : ℕ) := P.filter (fun p => p ∣ m)
def count (P : Finset ℕ) (X : ℕ) : ℝ := ∑ m ∈ Ioc 0 X, if (hits P m).card=0 then 1 else 0
def harmonic (P : Finset ℕ) : ℝ := ∑ p ∈ P, 1/(p:ℝ)
def divisCount (P : Finset ℕ) (j X : ℕ) : ℝ :=
  ∑ s ∈ P.powersetCard j, ((X / product s : ℕ):ℝ)
def trunc (P : Finset ℕ) (r X : ℕ) : ℝ :=
  ∑ j ∈ range (r+1), (-1:ℝ)^j*divisCount P j X

lemma prodPos (s : Finset ℕ) (hp : ∀ p ∈ s, p.Prime) : 0<product s :=
  prod_pos (fun p h => (hp p h).pos)

lemma prodDvd (s : Finset ℕ) (hp : ∀ p ∈ s, p.Prime) (m : ℕ) :
    product s ∣ m ↔ ∀ p ∈ s, p ∣ m := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [product]
  | @insert p s hps ih =>
    have hp' := hp p (mem_insert_self _ _)
    have hs := fun q (hq : q∈s) => hp q (mem_insert_of_mem hq)
    have hc : p.Coprime (product s) := Nat.coprime_prod_right_iff.mpr (fun q hq =>
      (Nat.coprime_primes hp' (hs q hq)).mpr fun he => hps (he ▸ hq))
    rw [product,prod_insert hps,forall_mem_insert]
    change p*product s ∣ m ↔ _
    exact ⟨fun h => ⟨(dvd_mul_right p _).trans h,(ih hs).mp ((dvd_mul_left (product s) p).trans h)⟩,
      fun h => hc.mul_dvd_of_dvd_of_dvd h.1 ((ih hs).mpr h.2)⟩

lemma omegaProd (s : Finset ℕ) (hp : ∀ p ∈ s, p.Prime) : (product s).primeFactorsList.length=s.card := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [product]
  | @insert p s hps ih =>
    have hp' := hp p (mem_insert_self _ _)
    have hs := fun q (hq : q∈s) => hp q (mem_insert_of_mem hq)
    have he := (Nat.perm_primeFactorsList_mul hp'.ne_zero (prodPos s hs).ne').length_eq
    change (∏ q ∈ insert p s,q).primeFactorsList.length=_
    rw [prod_insert hps,card_insert_of_notMem hps]
    change (p*product s).primeFactorsList.length=_
    simpa [Nat.primeFactorsList_prime hp',ih hs,Nat.add_comm] using he

theorem divisAsChoose (P : Finset ℕ) (hp : ∀ p∈P, p.Prime) (j X : ℕ) :
    divisCount P j X = ∑ m ∈ Ioc 0 X, (((hits P m).card.choose j:ℕ):ℝ) := by
  classical
  have hs (m : ℕ) :
      (P.powersetCard j).filter (fun s => product s ∣ m) = (hits P m).powersetCard j := by
    ext s
    simp only [mem_filter,mem_powersetCard]
    constructor
    · rintro ⟨⟨hsub,hj⟩,hd⟩
      exact ⟨fun q hq => mem_filter.mpr ⟨hsub hq,(prodDvd s (fun p h => hp p (hsub h)) m).mp hd q hq⟩,hj⟩
    · rintro ⟨hsub,hj⟩
      have hP (q) (hq:q∈s) := (mem_filter.mp (hsub hq)).1
      exact ⟨⟨fun q hq => hP q hq,hj⟩,(prodDvd s (fun p h => hp p (hP p h)) m).mpr
        (fun q hq => (mem_filter.mp (hsub hq)).2)⟩
  unfold divisCount
  simp_rw [←Nat.Ioc_filter_dvd_card_eq_div, ←Finset.sum_boole]
  rw [Finset.sum_comm]
  apply sum_congr rfl
  intro m _
  rw [Finset.sum_boole,hs,card_powersetCard]

private theorem localTrunc (k r : ℕ) :
    |(if k=0 then (1:ℝ) else 0) - ∑ j ∈ range (r+1), (-1:ℝ)^j*(k.choose j:ℕ)| ≤ k.choose r := by
  cases k with
  | zero =>
    have hy : (∑ j ∈ range (r+1), (-1:ℝ)^j*(((0:ℕ).choose j):ℕ))=1 := by
      rw [sum_eq_single 0]
      · simp
      · intro j _ hj
        have hh : (0:ℕ).choose j=0 := Nat.choose_eq_zero_of_lt (by omega)
        rw [hh];simp
      · simp
    simp [hy]
  | succ k =>
    have hi := @Int.alternating_sum_range_choose_eq_choose k r
    have hr : (∑ j ∈ range (r+1), (-1:ℝ)^j*(((k+1).choose j):ℕ))=(-1:ℝ)^r*(k.choose r:ℕ) := by exact_mod_cast hi
    rw [if_neg (by omega),zero_sub,abs_neg,hr,abs_mul,abs_pow]
    simpa using (show ((k.choose r:ℕ):ℝ) ≤ ((k+1).choose r:ℕ) by exact_mod_cast Nat.choose_le_succ k r)

theorem truncateError (P : Finset ℕ) (hp : ∀ p∈P, p.Prime) (r X : ℕ) :
    |count P X-trunc P r X| ≤ divisCount P r X := by
  unfold count trunc
  simp_rw [divisAsChoose P hp,Finset.mul_sum]
  rw [Finset.sum_comm (s:=range (r+1)),←sum_sub_distrib]
  exact (Finset.abs_sum_le_sum_abs _ _).trans (sum_le_sum (fun m _ => localTrunc (hits P m).card r))

theorem reciprocalLayer (P : Finset ℕ) (hp : ∀ p∈P, p.Prime) (r : ℕ) :
    (∑ s ∈ P.powersetCard r, 1/(product s:ℝ)) ≤ Real.exp (2*harmonic P)/(2:ℝ)^r := by
  apply (le_div_iff₀ (by positivity)).mpr
  rw [Finset.sum_mul]
  calc
    _ = ∑ s ∈ P.powersetCard r, ∏ p ∈ s, (2/(p:ℝ)) := by
      apply sum_congr rfl
      intro s hs
      rw [prod_div_distrib,prod_const,(mem_powersetCard.mp hs).2]
      simp [product,div_eq_mul_inv,mul_comm]
    _ ≤ ∑ s ∈ P.powerset, ∏ p ∈ s, (2/(p:ℝ)) :=
      sum_le_sum_of_subset_of_nonneg (fun s hs => mem_powerset.mpr (mem_powersetCard.mp hs).1)
        (fun s _ _ => prod_nonneg (fun _ _ => by positivity))
    _ = ∏ p ∈ P, (1+2/(p:ℝ)) := (prod_one_add ..).symm
    _ ≤ ∏ p ∈ P, Real.exp (2/(p:ℝ)) := by
      apply Finset.prod_le_prod₀ (fun p _ => by positivity)
      intro p hp
      simpa [add_comm] using (Real.add_one_le_exp (2/(p:ℝ)))
    _ = _ := by rw [←Real.exp_sum]; congr 1;unfold harmonic;rw [mul_sum];apply sum_congr rfl;intros;ring

theorem errorEnvelope (P : Finset ℕ) (hp : ∀ p∈P, p.Prime) (r X : ℕ) :
    |count P X-trunc P r X| ≤ (X:ℝ)*Real.exp (2*harmonic P)/(2:ℝ)^r := by
  apply (truncateError P hp r X).trans
  calc
    divisCount P r X ≤ (X:ℝ)*(∑ s ∈ P.powersetCard r, 1/(product s:ℝ)) := by
      unfold divisCount
      rw [mul_sum]
      apply sum_le_sum
      intro s _
      simpa only [mul_one_div] using (Nat.cast_div_le (m:=X) (n:=product s) : ((X/product s:ℕ):ℝ)≤X/(product s:ℝ))
    _ ≤ (X:ℝ)*(Real.exp (2*harmonic P)/(2:ℝ)^r) :=
      mul_le_mul_of_nonneg_left (reciprocalLayer P hp r) (Nat.cast_nonneg _)
    _ = _ := by ring
end GoldbachModelMean.Brun

end

section

noncomputable section
namespace GoldbachModelMean.Brun
open Finset Filter

private lemma floorIneq (m d : ℕ) (hd : 0<d) :
    (m:ℝ)/d-1 ≤ ((m/d:ℕ):ℝ) ∧ ((m/d:ℕ):ℝ) ≤ m/(d:ℝ) := by
  refine ⟨?_,Nat.cast_div_le⟩
  have h : (m:ℝ) < d * (((m/d:ℕ):ℝ)+1) := by exact_mod_cast Nat.lt_mul_div_succ m hd
  have hh : (m:ℝ)/d < ((m/d:ℕ):ℝ)+1 := (div_lt_iff₀ (by exact_mod_cast hd)).mpr (by linarith)
  linarith

private lemma floorDiff (X Y d : ℕ) (hd : 0<d) (hY : 0<Y) :
    |((X/d:ℕ):ℝ)-(X:ℝ)/Y*((Y/d:ℕ):ℝ)| ≤ 1+(X:ℝ)/Y := by
  have hY' : (0:ℝ)<Y := by exact_mod_cast hY
  have hpos : 0≤(X:ℝ)/Y := by positivity
  obtain ⟨a,b⟩ := floorIneq X d hd
  obtain ⟨c,e⟩ := floorIneq Y d hd
  have h : (X:ℝ)/Y*(Y/(d:ℝ))=X/(d:ℝ) := by field_simp
  have h1 := mul_le_mul_of_nonneg_left c hpos
  have h2 := mul_le_mul_of_nonneg_left e hpos
  rw [h] at h2
  rw [mul_sub,h,mul_one] at h1
  rw [abs_le]
  constructor <;> linarith

private lemma layerCard (P : Finset ℕ) (hp : ∀ p∈P,p.Prime) (r j X : ℕ) (hj : j≤r) :
    ((P.powersetCard j).filter (fun s => product s ≤ X)).card ≤
      (GoldbachModelMean.fewFactors r (X+1)).card := by
  apply Finset.card_le_card_of_injOn product
  · intro s hs
    obtain ⟨hP,hX⟩ := mem_filter.mp hs
    obtain ⟨hsub,hcard⟩ := mem_powersetCard.mp hP
    have hPrime (q) (hq:q∈s) := hp q (hsub hq)
    exact mem_filter.mpr ⟨mem_range.mpr (by omega),prodPos s hPrime,(omegaProd s hPrime).trans_le (hcard.trans_le hj)⟩
  · intro s hs t ht e
    have h1 := (mem_powersetCard.mp (mem_filter.mp hs).1).1
    have h2 := (mem_powersetCard.mp (mem_filter.mp ht).1).1
    have hs' : (product s).primeFactors=s := Nat.primeFactors_prod (fun q hq => hp q (h1 hq))
    have ht' : (product t).primeFactors=t := Nat.primeFactors_prod (fun q hq => hp q (h2 hq))
    rw [←hs',e,ht']

private lemma layerDiff (P : Finset ℕ) (hp : ∀ p∈P,p.Prime) (r j X Y : ℕ)
    (hj : j≤r) (hY : 0<Y) (hYX : Y≤X) :
    |divisCount P j X-(X:ℝ)/Y*divisCount P j Y| ≤
      ((GoldbachModelMean.fewFactors r (X+1)).card:ℝ)*(1+(X:ℝ)/Y) := by
  classical
  unfold divisCount
  rw [mul_sum,←sum_sub_distrib]
  apply (abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ s ∈ P.powersetCard j, if product s≤X then 1+(X:ℝ)/Y else 0 := by
      apply sum_le_sum
      intro s hs
      split_ifs with h
      · exact floorDiff X Y (product s) (prodPos s (fun q hq => hp q ((mem_powersetCard.mp hs).1 hq))) hY
      · have hx : X<product s := by omega
        simp [Nat.div_eq_of_lt hx,Nat.div_eq_of_lt (hYX.trans_lt hx)]
    _ = (((P.powersetCard j).filter (fun s => product s ≤ X)).card:ℝ)*(1+(X:ℝ)/Y) := by
      rw [←sum_filter];simp;ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast layerCard P hp r j X hj) (by positivity)

theorem truncDiff (P : Finset ℕ) (hp : ∀ p∈P,p.Prime) (r X Y : ℕ)
    (hY : 0<Y) (hYX : Y≤X) :
    |trunc P r X-(X:ℝ)/Y*trunc P r Y| ≤
      ((r:ℝ)+1)*((GoldbachModelMean.fewFactors r (X+1)).card:ℝ)*(1+(X:ℝ)/Y) := by
  unfold trunc
  rw [mul_sum,←sum_sub_distrib]
  apply (abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ j ∈ range (r+1), ((GoldbachModelMean.fewFactors r (X+1)).card:ℝ)*(1+(X:ℝ)/Y) := by
      apply sum_le_sum
      intro j hj
      have hh := layerDiff P hp r j X Y (by have := mem_range.mp hj;omega) hY hYX
      rw [show (X:ℝ)/Y*((-1:ℝ)^j*divisCount P j Y)=(-1:ℝ)^j*((X:ℝ)/Y*divisCount P j Y) by ring,
        ←mul_sub,abs_mul,abs_pow]
      simpa using hh
    _ = _ := by simp [mul_assoc]

end GoldbachModelMean.Brun

end

section

noncomputable section
namespace GoldbachModelMean.Brun
open Finset Filter

theorem uniform_lowH (H C e : ℝ) (hC : 1≤C) (he : 0<e) :
    ∀ᶠ X : ℕ in atTop, ∀ Y : ℕ, 0<Y → Y≤X → (X:ℝ)≤C*Y →
    ∀ P : Finset ℕ, (∀ p∈P,p.Prime) → harmonic P≤H →
    |count P X/X - count P Y/Y| ≤ e := by
  obtain ⟨r,hr⟩ := pow_unbounded_of_one_lt (4*Real.exp (2*H)/e) (show (1:ℝ)<2 by norm_num)
  let A : ℝ := ((r:ℝ)+1)*(1+C)
  have hA : 0<A := by dsimp [A];positivity
  have heps : 0<e/(4*A) := by positivity
  obtain ⟨x₀,hx⟩ := eventually_atTop.mp (GoldbachModelMean.fewFactors_eventually r (e/(4*A)) heps)
  filter_upwards [eventually_ge_atTop x₀,eventually_ge_atTop 1] with X hX hX1
  intro Y hY hYX hscale P hp hH
  have hY' : (0:ℝ)<Y := by exact_mod_cast hY
  have hX' : (0:ℝ)<X := by exact_mod_cast hX1
  have hx1 : (1:ℝ)≤X := by exact_mod_cast hX1
  have hRatio : (X:ℝ)/Y≤C := (div_le_iff₀ hY').mpr hscale
  have hR : 0≤(X:ℝ)/Y := by positivity
  have hExp := Real.exp_le_exp.mpr (show 2*harmonic P≤2*H by linarith)
  have hcoeff : Real.exp (2*harmonic P)/(2:ℝ)^r ≤ e/4 := by
    apply (div_le_iff₀ (by positivity)).mpr
    have := (div_lt_iff₀ he).mp hr
    nlinarith
  have err (W : ℕ) : |count P W-trunc P r W| ≤ (W:ℝ)*(e/4) := by
    refine (errorEnvelope P hp r W).trans ?_
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left hcoeff (Nat.cast_nonneg _)
  have hf := hx (X+1) (by omega)
  push_cast at hf
  have hL : ((r:ℝ)+1)*((GoldbachModelMean.fewFactors r (X+1)).card:ℝ)*(1+(X:ℝ)/Y) ≤ (X:ℝ)*(e/2) := by
    calc
      _ ≤ ((r:ℝ)+1)*((GoldbachModelMean.fewFactors r (X+1)).card:ℝ)*(1+C) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = A*((GoldbachModelMean.fewFactors r (X+1)).card:ℝ) := by dsimp [A];ring
      _ ≤ A*(e/(4*A)*((X:ℝ)+1)) := mul_le_mul_of_nonneg_left hf hA.le
      _ = e/4*((X:ℝ)+1) := by field_simp
      _ ≤ _ := by nlinarith [mul_nonneg he.le (sub_nonneg.mpr hx1)]
  have ht := (truncDiff P hp r X Y hY hYX).trans hL
  have hE : |(X:ℝ)/Y*trunc P r Y-(X:ℝ)/Y*count P Y| ≤ (X:ℝ)*(e/4) := by
    rw [←mul_sub,abs_mul,abs_of_nonneg hR,abs_sub_comm]
    calc
      _ ≤ ((X:ℝ)/Y)*(Y*(e/4)) := mul_le_mul_of_nonneg_left (err _) hR
      _ = _ := by field_simp
  have hT := abs_sub_le (count P X) (trunc P r X) ((X:ℝ)/Y*count P Y)
  have hU := abs_sub_le (trunc P r X) ((X:ℝ)/Y*trunc P r Y) ((X:ℝ)/Y*count P Y)
  have hab : |count P X-(X:ℝ)/Y*count P Y|≤e*X := by linarith [err X]
  rw [show count P X/(X:ℝ)-count P Y/Y=(count P X-(X:ℝ)/Y*count P Y)/X by field_simp,
    abs_div,abs_of_pos hX']
  exact (div_le_iff₀ hX').mpr hab

end GoldbachModelMean.Brun

end

section

noncomputable section
namespace BandTail
open Finset Filter GoldbachModelMean.Brun

def exceptionalPrimes (n X : ℕ) : Finset ℕ := (Icc 1 X).filter (fun p => p.Prime ∧ ¬p∣n)
def meanG (n X : ℕ) : ℝ := (∑ k ∈ Icc 1 X,g n k)/X

theorem count_eq_g (n X T : ℕ) (hT : T≤X) :
    count (exceptionalPrimes n X) T = ∑ k ∈ Icc 1 T,g n k := by
  unfold count
  have hset : Ioc 0 T=Icc 1 T := by ext k;simp;omega
  rw [hset]
  apply sum_congr rfl
  intro k hk
  obtain ⟨hk1,hkT⟩ := mem_Icc.mp hk
  have h0 : k≠0 := by omega
  have he : (hits (exceptionalPrimes n X) k).card=0 ↔ smooth n k := by
    rw [Finset.card_eq_zero]
    constructor
    · intro h p hp
      by_contra hn
      obtain ⟨hp',hpk,_⟩ := Nat.mem_primeFactors.mp hp
      have hpX := (Nat.le_of_dvd (by omega : 0<k) hpk).trans (hkT.trans hT)
      have hmem : p ∈ hits (exceptionalPrimes n X) k := mem_filter.mpr
        ⟨mem_filter.mpr ⟨mem_Icc.mpr ⟨hp'.one_lt.le,hpX⟩,hp',hn⟩,hpk⟩
      simp [h] at hmem
    · intro hs
      apply eq_empty_iff_forall_notMem.mpr
      intro p hpm
      obtain ⟨hP,hpk⟩ := mem_filter.mp hpm
      obtain ⟨_,hp,hn⟩ := mem_filter.mp hP
      exact hn (hs p (Nat.mem_primeFactors.mpr ⟨hp,hpk,h0⟩))
  simp [g,h0,he]

theorem meanG_nonneg (n X : ℕ) : 0≤ meanG n X := by
  apply div_nonneg _ (Nat.cast_nonneg _)
  apply sum_nonneg
  intro k _
  simp only [g,ArithmeticFunction.coe_mk];split_ifs <;> norm_num

theorem meanG_le_one (n X : ℕ) : meanG n X≤1 := by
  rcases eq_or_ne X 0 with rfl|hx
  · simp [meanG]
  · apply (div_le_iff₀ (by exact_mod_cast Nat.pos_of_ne_zero hx)).mpr
    calc
      _ ≤ ∑ k ∈ Icc 1 X, (1:ℝ) := by
        apply sum_le_sum
        intro k _
        simp only [g,ArithmeticFunction.coe_mk];split_ifs <;> norm_num
      _ = _ := by simp

end BandTail

end

section

namespace BandTail
open Finset
noncomputable section

def frequency (P : Finset ℕ) : ℝ := ∑ p ∈ P, (p:ℝ)⁻¹
def hit (p k : ℕ) : ℝ := if p ∣ k then 1 else 0
def hitCount (P : Finset ℕ) (k : ℕ) : ℝ := ∑ p ∈ P, hit p k

theorem hit_sum (p X : ℕ) : (∑ k ∈ Icc 1 X, hit p k) = (X/p : ℕ) := by
  have he : Icc 1 X=Ioc 0 X := by ext k; simp only [mem_Icc,mem_Ioc]; omega
  unfold hit
  rw [he,Finset.sum_boole,Nat.Ioc_filter_dvd_card_eq_div]

theorem firstMoment (P : Finset ℕ) (X : ℕ) (hP : ∀ p ∈ P, 0<p) :
    (X:ℝ)*frequency P-P.card ≤ ∑ k ∈ Icc 1 X,hitCount P k := by
  simp only [hitCount,Finset.sum_comm (s:=Icc 1 X) (t:=P),hit_sum]
  calc
    _ = ∑ p ∈ P, ((X:ℝ)*(p:ℝ)⁻¹-1) := by simp [frequency,mul_sum,sum_sub_distrib]
    _ ≤ _ := by
      apply sum_le_sum
      intro p hp
      have hpr : 0<(p:ℝ) := by exact_mod_cast hP p hp
      have hc : (X:ℝ) < (p:ℝ)*((X/p:ℕ)+1:ℝ) := by exact_mod_cast Nat.lt_mul_div_succ X (hP p hp)
      have hh : (X:ℝ)/(p:ℝ) ≤ ((X/p:ℕ):ℝ)+1 := (div_le_iff₀ hpr).mpr (by linarith)
      linarith [show (X:ℝ)*(p:ℝ)⁻¹ = X/p by rw [div_eq_mul_inv]]

theorem hitPair (X p r : ℕ) (hp : p.Prime) (hr : r.Prime) :
    (∑ k ∈ Icc 1 X,hit p k * hit r k) ≤
      (X:ℝ)*((p:ℝ)⁻¹*(r:ℝ)⁻¹) + (if p=r then (X:ℝ)*(p:ℝ)⁻¹ else 0) := by
  by_cases he : p=r
  · subst r
    have hh (k : ℕ) : hit p k*hit p k=hit p k := by by_cases hk : p∣k <;> simp [hit,hk]
    simp only [hh,hit_sum,ite_true]
    exact (Nat.cast_div_le (α:=ℝ)).trans (by rw [div_eq_mul_inv]; exact le_add_of_nonneg_left (by positivity))
  · have hh (k : ℕ) : hit p k*hit r k=hit (p*r) k := by
      have hc := (Nat.coprime_primes hp hr).mpr he
      have eqv : p*r∣k ↔ p∣k ∧ r∣k := ⟨fun hk => ⟨(dvd_mul_right p r).trans hk,(dvd_mul_left r p).trans hk⟩,fun hk => hc.mul_dvd_of_dvd_of_dvd hk.1 hk.2⟩
      by_cases ha : p∣k <;> by_cases hb : r∣k <;> simp [hit,eqv,ha,hb]
    simp only [hh,hit_sum,if_neg he,add_zero]
    exact (Nat.cast_div_le (α:=ℝ)).trans_eq (by simp [div_eq_mul_inv,mul_comm])

theorem secondMoment (P : Finset ℕ) (X : ℕ) (hP : ∀ p ∈ P, p.Prime) :
    (∑ k ∈ Icc 1 X,(hitCount P k)^2) ≤ (X:ℝ)*(frequency P)^2+X*frequency P := by
  have hswap (f : ℕ → ℕ → ℕ → ℝ) :
      (∑ k ∈ Icc 1 X,∑ p ∈ P,∑ r ∈ P,f k p r)=∑ p ∈ P,∑ r ∈ P,∑ k ∈ Icc 1 X,f k p r := by
    rw [sum_comm]
    exact sum_congr rfl fun _ _ => sum_comm
  simp only [hitCount,sq,sum_mul_sum,hswap]
  calc
    _ ≤ ∑ p ∈ P,∑ r ∈ P, ((X:ℝ)*((p:ℝ)⁻¹*(r:ℝ)⁻¹)+(if p=r then (X:ℝ)*(p:ℝ)⁻¹ else 0)) :=
      sum_le_sum fun p hp => sum_le_sum fun r hr => hitPair X p r (hP p hp) (hP r hr)
    _ = _ := by
      simp only [sum_add_distrib,←mul_sum,sum_ite_eq]
      unfold frequency
      congr 1
      · rw [←Finset.sum_mul]
      · rw [mul_sum]
        exact sum_congr rfl fun p hp => by simp [hp]

theorem highH (n X : ℕ) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime ∧ ¬p∣n) :
    frequency P * (∑ k ∈ Icc 1 X, g n k) ≤ (X:ℝ) + 2*P.card := by
  let H := frequency P
  have hH : 0≤H := sum_nonneg fun p _ => inv_nonneg.mpr (Nat.cast_nonneg p)
  rcases hH.eq_or_lt with hz | hpos
  · change H*_ ≤ _
    rw [←hz,zero_mul]; positivity
  have h1 := firstMoment P X (fun p hp => (hP p hp).1.pos)
  have h2 := secondMoment P X (fun p hp => (hP p hp).1)
  have hdom : (∑ k ∈ Icc 1 X, g n k * H^2) ≤ ∑ k ∈ Icc 1 X, (hitCount P k-H)^2 := by
    apply sum_le_sum
    intro k hk
    have hk0 : k≠0 := by have := (mem_Icc.mp hk).1; omega
    by_cases hsm : smooth n k
    · have h0 : hitCount P k=0 := by
        apply sum_eq_zero
        intro p hp
        have hn := (hP p hp).2
        have hpk : ¬p∣k := fun hpk => hn (hsm p (Nat.mem_primeFactors.mpr ⟨(hP p hp).1,hpk,hk0⟩))
        simp [hit,hpk]
      simp [g,hk0,hsm,h0]
    · simp [g,hk0,hsm,sq_nonneg]
  have he (k : ℕ) : (hitCount P k-H)^2=(hitCount P k)^2 - hitCount P k*(2*H)+ H^2 := by ring
  simp only [he,sum_add_distrib,sum_sub_distrib,←sum_mul,sum_const,nsmul_eq_mul,Nat.card_Icc,Nat.add_sub_cancel] at hdom
  change (X:ℝ)*H-_≤_ at h1
  change _≤(X:ℝ)*H^2+X*H at h2
  have h3 := mul_le_mul_of_nonneg_right h1 (mul_nonneg (by norm_num : (0:ℝ)≤2) hpos.le)
  apply le_of_mul_le_mul_right (a:=H) _ hpos
  nlinarith only [hdom,h3,h2]
end
end BandTail

end

section

noncomputable section
namespace BandTail
open Finset Filter GoldbachModelMean.Brun

theorem mean_slow (C e : ℝ) (hC : 1≤C) (he : 0<e) :
    ∀ᶠ X : ℕ in atTop, ∀ Y : ℕ, 0<Y → Y≤X → (X:ℝ)≤C*Y →
    ∀ n, |meanG n X-meanG n Y|≤e := by
  let H : ℝ := (1+2*C)/e
  have hHpos : 0<H := by dsimp [H];positivity
  filter_upwards [uniform_lowH H C e hC he] with X hlow
  intro Y hY hYX hscale n
  let P := exceptionalPrimes n X
  have hprime (p) (hp : p∈P) : p.Prime ∧ ¬p∣n := (mem_filter.mp hp).2
  have hh : harmonic P=frequency P := by simp [GoldbachModelMean.Brun.harmonic,frequency,one_div]
  by_cases hc : harmonic P≤H
  · have hh := hlow Y hY hYX hscale P (fun p h => (hprime p h).1) hc
    rwa [count_eq_g n X X le_rfl,count_eq_g n X Y hYX] at hh
  · have hPH := lt_of_not_ge hc
    rw [hh] at hPH
    have hPcard : P.card≤X := (card_filter_le ..).trans_eq (by simp)
    have hX' : (0:ℝ)<X := by exact_mod_cast hY.trans_le hYX
    have hyp : (0:ℝ)<Y := by exact_mod_cast hY
    have hscaleX : (X:ℝ)≤C*X := by simpa using (mul_le_mul_of_nonneg_right hC hX'.le)
    have hb (T : ℕ) (ht : (0:ℝ)<T) (hscaleT : (X:ℝ)≤C*T) : meanG n T≤e := by
      have hcard' : (P.card:ℝ) ≤ C*T := (show (P.card:ℝ)≤X by exact_mod_cast hPcard).trans hscaleT
      have hbound := highH n T P hprime
      have hp : 0≤∑ k ∈ Icc 1 T,g n k := by
        have hh := meanG_nonneg n T
        unfold meanG at hh
        simpa [ht.ne'] using mul_nonneg hh ht.le
      have hlo := mul_le_mul_of_nonneg_right hPH.le hp
      have hHS : H*(∑ k ∈ Icc 1 T,g n k) ≤ (1+2*C)*T := by linarith
      have hid : (1+2*C)*T=H*(e*T) := by dsimp [H];field_simp
      rw [hid] at hHS
      exact (div_le_iff₀ ht).mpr ((mul_le_mul_iff_right₀ hHpos).mp hHS)
    have hx := hb X hX' hscaleX
    have hy := hb Y hyp hscale
    rw [abs_le]
    constructor <;> linarith [meanG_nonneg n X, meanG_nonneg n Y]

end BandTail

end

section

namespace BandTail
open Finset Filter
noncomputable section

theorem uniform_prefix_floor (R : ℕ) (hR : 1 ≤ R) (δ : ℝ) (hδ : 0<δ) :
    ∃ A₀ : ℕ, ∀ A ≥ A₀, ∀ n i : ℕ, A ≤ i → i ≤ R*A →
      -(δ*(A:ℝ))  ≤  ∑ q ∈ Finset.Ioc A i,F n q := by
  have hr : (1:ℝ) ≤ R := by exact_mod_cast hR
  have hu : 0<universal := Real.exp_pos _
  let τ : ℝ := δ/(8*((R:ℝ)+1))
  have hτ : 0<τ := by dsimp [τ]; positivity
  let e : ℝ := τ/(universal+1)
  have he : 0<e := by dsimp [e]; positivity
  have heu : universal*e  ≤  τ := by
    have heq : e*(universal+1)=τ := by dsimp [e]; field_simp
    nlinarith
  obtain ⟨N,hN⟩ := exists_nat_ge (universal/τ)
  let J := (N+1)^4
  have hJ : 0<J := by dsimp [J]; positivity
  have hj : (J:ℝ)^(1/4:ℝ)=(N:ℝ)+1 := by
    dsimp [J]; push_cast
    rw [←Real.rpow_natCast_mul (by positivity),show (↑(4:ℕ):ℝ)*(1/4)=1 by norm_num,Real.rpow_one]
  have ht : universal/(J:ℝ)^(1/4:ℝ)  ≤  τ := by
    rw [hj]
    apply (div_le_iff₀ (by positivity)).mpr
    have := (div_le_iff₀ hτ).mp hN
    nlinarith
  let C : ℝ := 2*(R:ℝ)*J
  have hjr : (1:ℝ) ≤ J := by exact_mod_cast hJ
  have hC : 1 ≤ C := by dsimp [C]; nlinarith [mul_le_mul hr hjr (by norm_num) (by positivity)]
  obtain ⟨M,hM⟩ := eventually_atTop.mp (mean_slow C e hC he)
  obtain ⟨L,hL⟩ := exists_nat_ge ((J:ℝ)/e)
  refine ⟨max J (max M L),?_⟩
  intro A hA n i hAi hiA
  have hJA : J ≤ A := by omega
  have hA0 : 0<A := hJ.trans_le hJA
  have hAr : (0:ℝ)<A := by exact_mod_cast hA0
  have hi0 : 0 < i := hA0.trans_le hAi
  have hir : (0:ℝ) < i := by exact_mod_cast hi0
  have hscale : (i:ℝ) ≤ R*(A:ℝ) := by exact_mod_cast hiA
  let t := gAvg n i
  let Z := ∑ d ∈ Icc 1 J,z n d
  have ht01 : 0 ≤ t ∧ t ≤ 1 := g_avg_bounds n i
  have hz : -τ ≤ Z := by have hz' := signedPrefix n J hJ; dsimp [Z]; linarith
  have hlin (X : ℕ) (hAX : A ≤ X) (hXi : X ≤ i) :
      |fSum n X-(X:ℝ)*(Z*t)|  ≤  X*(3*τ) := by
    have hX : 0<X := hA0.trans_le hAX
    have hxr : (0:ℝ)<X := by exact_mod_cast hX
    have hjx : (J:ℝ)/X ≤ e := by
      apply (div_le_iff₀ hxr).mpr
      have hLX : (L:ℝ) ≤ X := by exact_mod_cast (show L ≤ X by omega)
      have := (div_le_iff₀ he).mp (hL.trans hLX)
      linarith
    have hnear (d : ℕ) (hd : d∈Icc 1 J) : |gAvg n (X/d)-t| ≤ e := by
      obtain ⟨hd0,hdJ⟩ := mem_Icc.mp hd
      have hdX : d ≤ X := by omega
      have hy : 0<X/d := Nat.div_pos hdX hd0
      have hii : i ≤ R*X := hiA.trans (Nat.mul_le_mul_left R hAX)
      have hratio : X ≤ (2*J)*(X/d) := by
        calc
          X  ≤  d*(X/d+1) := (Nat.lt_mul_div_succ X hd0).le
          _  ≤  J*(2*(X/d)) := Nat.mul_le_mul hdJ (by omega)
          _ = _ := by ring
      have hcxy : (i:ℝ) ≤ C*(X/d:ℕ) := by
        dsimp [C]
        exact_mod_cast (show i ≤ 2*R*J*(X/d) from hii.trans (by calc
          R*X  ≤  R*((2*J)*(X/d)) := Nat.mul_le_mul_left R hratio
          _ = _ := by ring))
      rw [abs_sub_comm]
      exact hM i (by omega) (X/d) hy ((Nat.div_le_self X d).trans hXi) hcxy n
    have h := dyadic_approx n X J hX hJ (by omega) t e he.le hnear hjx
    have ha : |fSum n X / X - Z*t| ≤ 3*τ := h.trans (by linarith)
    have eqv : fSum n X-(X:ℝ)*(Z*t)=(X:ℝ)*(fSum n X/X-Z*t) := by field_simp
    rw [eqv,abs_mul,abs_of_pos hxr]
    exact mul_le_mul_of_nonneg_left ha hxr.le
  have ha := abs_le.mp (hlin A le_rfl hAi)
  have hb := abs_le.mp (hlin i hAi le_rfl)
  have htZ : -τ  ≤  Z*t := by
    calc
      -τ  ≤  -τ*t := by nlinarith [mul_nonneg hτ.le (sub_nonneg.mpr ht01.2)]
      _  ≤  _ := mul_le_mul_of_nonneg_right hz ht01.1
  have hia : (A:ℝ) ≤ i := by exact_mod_cast hAi
  have hdiff := mul_le_mul_of_nonneg_left htZ (sub_nonneg.mpr hia)
  have heqτ : (8*((R:ℝ)+1))*τ=δ := by dsimp [τ]; field_simp
  have htot : (i:ℝ)*τ  ≤  R*A*τ := mul_le_mul_of_nonneg_right hscale hτ.le
  have hgood : -(δ*(A:ℝ)) ≤ fSum n i-fSum n A := by
    have δeq : δ*(A:ℝ)=(8*((R:ℝ)+1))*τ*A := by rw [heqτ]
    nlinarith only [ha.1,ha.2,hb.1,hb.2,hdiff,htot,δeq,
      mul_nonneg (Nat.cast_nonneg R) (mul_nonneg hAr.le hτ.le),mul_nonneg hAr.le hτ.le]
  have hsplit := prefix_split (fun q => F n q) hAi
  change fSum n i=fSum n A+_ at hsplit
  linarith

end
end BandTail

end

end
end
end
end
end

end GoldbachGRHBandBase

section GoldbachGRHRamanujanMobius

open scoped BigOperators

namespace GoldbachExplicitModeledMajor

/-- The reduced-residue exponential sum at numerator one is the Möbius value. -/
theorem ram_one_eq_moebius (q : ℕ) :
    ram q 1 = (ArithmeticFunction.moebius q : ℂ) := by
  induction q using Nat.recOnPrimeCoprime with
  | zero => simp [ram]
  | prime_pow p j hp =>
    cases j with
    | zero => simp [ram_one]
    | succ k =>
      have hd (a : ℕ) : ¬ p ^ (a + 1) ∣ 1 := by
        intro ha
        exact (Nat.one_lt_pow (Nat.succ_ne_zero a) hp.one_lt).ne' (Nat.dvd_one.mp ha)
      rw [ram_primePower p k 1 hp,
        ArithmeticFunction.moebius_apply_prime_pow hp (Nat.succ_ne_zero k), ite_eq_right (hd k)]
      cases k with
      | zero => norm_num
      | succ k => simp [hd k]
  | coprime q r hq hr hqr iq ir =>
    rw [ram_mul (by omega) (by omega) hqr, iq, ir,
      ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hqr, Int.cast_mul]

end GoldbachExplicitModeledMajor


namespace GoldbachGRHWindow

/-- A reduced additive numerator has the exact Möbius/totient model. -/
theorem additiveModel_eq_moebius {q : ℕ} [NeZero q] (a : ZMod q) (ha : IsUnit a) :
    additiveModel q a = (ArithmeticFunction.moebius q : ℂ) / (q.totient : ℂ) := by
  rw [additiveModel_of_unit a ha]
  have h := additiveModel_eq_reduced_sum (q := q) 1
  have hr : additiveModel q 1 =
      GoldbachExplicitModeledMajor.ram q 1 / (q.totient : ℂ) := by
    simpa only [Nat.cast_one, GoldbachExplicitModeledMajor.ram,
      GoldbachExplicitModeledMajor.phase] using h
  rw [hr, GoldbachExplicitModeledMajor.ram_one_eq_moebius]

end GoldbachGRHWindow

end GoldbachGRHRamanujanMobius

section GoldbachGRHKernel

open MeasureTheory Set Finset
open scoped Interval

namespace GoldbachGRHKernel

open GoldbachFourthMoment (phase phase_add)

noncomputable def kernel (n : ℕ) : ℝ → ℂ :=
  GoldbachWindow.poly (n + 1) fun _ => 1

noncomputable def mass (n : ℕ) (r : ℝ) : ℝ :=
  ∫ t in (-r)..r, ‖kernel n t‖ ^ 2

theorem kernel_eq_sum (n : ℕ) (t : ℝ) :
    kernel n t = ∑ k ∈ range (n + 1), phase ((k : ℝ) * t) := by
  simp [kernel, GoldbachWindow.poly]

theorem phase_nat (k : ℕ) : phase (k : ℝ) = 1 := by
  unfold phase
  have h : (((2 * Real.pi * (k : ℝ) : ℝ) : ℂ) * Complex.I) =
      (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    push_cast
    ring
  rw [h]
  exact_mod_cast Complex.exp_int_mul_two_pi_mul_I (k : ℤ)

theorem kernel_periodic (n : ℕ) : Function.Periodic (kernel n) 1 := by
  intro t
  simp only [kernel_eq_sum, mul_add, mul_one, phase_add, phase_nat, mul_one]

theorem kernel_continuous (n : ℕ) : Continuous (kernel n) := by
  rw [show kernel n = fun t => ∑ k ∈ range (n + 1), phase ((k : ℝ) * t) from
    funext (kernel_eq_sum n)]
  unfold phase
  fun_prop

theorem reflect (n : ℕ) (t : ℝ) :
    kernel n t ^ 2 * phase (-(n : ℝ) * t) = (↑(‖kernel n t‖ ^ 2) : ℂ) := by
  simp only [kernel_eq_sum, ← Complex.normSq_eq_norm_sq]
  exact frontierMedcoreKernelReflection n t

theorem full_parseval (n : ℕ) :
    (∫ t in (0 : ℝ)..1, ‖kernel n t‖ ^ 2) = (n : ℝ) + 1 := by
  simpa [kernel] using GoldbachWindow.parseval (n + 1) (fun _ => (1 : ℂ))

theorem mass_nonneg (n : ℕ) {r : ℝ} (hr : 0 ≤ r) : 0 ≤ mass n r :=
  intervalIntegral.integral_nonneg_of_forall (by linarith) fun _ => sq_nonneg _

theorem mass_mono (n : ℕ) {r s : ℝ} (hr : 0 ≤ r) (hrs : r ≤ s) :
    mass n r ≤ mass n s := by
  apply intervalIntegral.integral_mono_interval (by linarith) (by linarith) hrs
  · exact Filter.Eventually.of_forall fun _ => sq_nonneg _
  · exact ((kernel_continuous n).norm.pow 2).intervalIntegrable _ _

theorem mass_loss (n : ℕ) {r : ℝ} (hr : 0 < r) (hh : r ≤ 1 / 2) :
    0 ≤ (n : ℝ) + 1 - mass n r ∧
      (n : ℝ) + 1 - mass n r ≤ 1 / (2 * r) := by
  let F : ℝ → ℝ := fun t => ‖kernel n t‖ ^ 2
  have hF : Continuous F := (kernel_continuous n).norm.pow 2
  have hp : Function.Periodic F 1 := by
    intro t
    simp only [F, kernel_periodic n t]
  have hfull : (∫ t in (-r)..(1 - r), F t) = (n : ℝ) + 1 := by
    have h := hp.intervalIntegral_add_eq (-r) 0
    rw [show -r + 1 = 1 - r by ring, zero_add] at h
    exact h.trans (full_parseval n)
  have hsplit :
      mass n r + (∫ t in r..(1 - r), F t) = (n : ℝ) + 1 := by
    have h := intervalIntegral.integral_add_adjacent_intervals
      (hF.intervalIntegrable (μ := volume) (-r) r) (hF.intervalIntegrable r (1 - r))
    exact h.trans hfull
  have htail : (n : ℝ) + 1 - mass n r = ∫ t in r..(1 - r), F t := by
    linarith only [hsplit]
  have hordered : r ≤ 1 - r := by linarith only [hh]
  have hrepr : (∫ t in (0 : ℝ)..1, (Ioc r (1 - r)).indicator F t) =
      ∫ t in r..(1 - r), F t := by
    rw [intervalIntegral.integral_of_le zero_le_one, intervalIntegral.integral_of_le hordered,
      MeasureTheory.integral_indicator measurableSet_Ioc,
      Measure.restrict_restrict measurableSet_Ioc]
    rw [inter_eq_left.mpr (Ioc_subset_Ioc hr.le (by linarith only [hr]))]
  have hcut : ∀ t ∈ Icc (0 : ℝ) 1, t ∈ Ioc r (1 - r) →
      r ≤ |(1 : ℝ) * t - (round ((1 : ℝ) * t) : ℝ)| := by
    intro t ht hz
    rw [one_mul]
    by_cases hhalf : t < 1 / 2
    · have hround : round t = 0 :=
        round_eq_zero_iff.mpr ⟨by linarith only [ht.1], hhalf⟩
      simp only [hround, Int.cast_zero, sub_zero, abs_of_nonneg ht.1]
      exact hz.1.le
    · have hround : round t = 1 := round_eq_iff.mpr (by
        change ((1 : ℤ) : ℝ) - 1 / 2 ≤ t ∧ t < ((1 : ℤ) : ℝ) + 1 / 2
        push_cast
        constructor <;> linarith only [hhalf, ht.2])
      simp only [hround, Int.cast_one, abs_of_nonpos (sub_nonpos.mpr ht.2)]
      linarith only [hz.2]
  have hbound := goldbach_geometric_tail_l2 (n + 1) 1 Nat.one_pos r hr hh
    (Ioc r (1 - r)) measurableSet_Ioc hcut
  simp only [Nat.cast_one, one_mul] at hbound
  have hboundF : (∫ t in (0 : ℝ)..1, (Ioc r (1 - r)).indicator F t) ≤ 1 / (2 * r) := by
    simpa only [F, kernel_eq_sum, phase, mul_assoc] using hbound
  rw [hrepr] at hboundF
  rw [htail]
  exact ⟨intervalIntegral.integral_nonneg_of_forall hordered (fun _ => sq_nonneg _), hboundF⟩

end GoldbachGRHKernel

end GoldbachGRHKernel

section GoldbachGRHArcs

open Finset MeasureTheory Set
open scoped Interval

namespace GoldbachGRHArcs

noncomputable abbrev cap := GoldbachFourthGeometry.wide

/-- Indices of reduced fractions in the closed unit interval. The two endpoints are both
present when the denominator is one. -/
def centers (U : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.Icc 1 U) ×ˢ (Finset.range (U+1))).filter
    (fun i => i.2 ≤ i.1 ∧ Nat.Coprime i.2 i.1)

theorem mem_centers {U : ℕ} {i : ℕ × ℕ} :
    i ∈ centers U ↔ 1 ≤ i.1 ∧ i.1 ≤ U ∧ i.2 ≤ i.1 ∧ Nat.Coprime i.2 i.1 := by
  simp only [centers, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_range]
  constructor
  · rintro ⟨⟨⟨h₁, h₂⟩, _⟩, h₃, h₄⟩
    exact ⟨h₁,h₂,h₃,h₄⟩
  · rintro ⟨h₁,h₂,h₃,h₄⟩
    exact ⟨⟨⟨h₁,h₂⟩, by omega⟩,h₃,h₄⟩

theorem centers_mono {Q U : ℕ} (h : Q ≤ U) : centers Q ⊆ centers U := by
  intro i hi
  obtain ⟨h₁,h₂,h₃,h₄⟩ := mem_centers.mp hi
  exact mem_centers.mpr ⟨h₁,h₂.trans h,h₃,h₄⟩

noncomputable def radius (n H q : ℕ) : ℝ := (H : ℝ) / ((q : ℝ) * (n : ℝ))

noncomputable def center (i : ℕ × ℕ) : ℝ := (i.2 : ℝ) / (i.1 : ℝ)

noncomputable def arc (n H : ℕ) (i : ℕ × ℕ) : Set ℝ :=
  {t | |t - center i| ≤ radius n H i.1}

theorem measurable_arc (n H : ℕ) (i : ℕ × ℕ) : MeasurableSet (arc n H i) := by
  unfold arc
  exact measurableSet_le (show Continuous (fun t : ℝ => |t - center i|) by fun_prop).measurable
    measurable_const

theorem arc_eq_Icc (n H : ℕ) (i : ℕ × ℕ) :
    arc n H i = Set.Icc (center i - radius n H i.1) (center i + radius n H i.1) := by
  ext t
  change |t - center i| ≤ radius n H i.1 ↔ _
  rw [abs_le, Set.mem_Icc]
  constructor <;> rintro ⟨h₁,h₂⟩ <;> constructor <;> linarith

theorem mem_cap {n U H : ℕ} {t : ℝ} :
    t ∈ cap n U H ↔ ∃ i ∈ centers U, t ∈ arc n H i := by
  constructor
  · rintro ⟨q,a,h₁,h₂,h₃,h₄,h₅⟩
    exact ⟨(q,a),mem_centers.mpr ⟨h₁,h₂,h₃,h₄⟩,h₅⟩
  · rintro ⟨⟨q,a⟩,hi,ht⟩
    obtain ⟨h₁,h₂,h₃,h₄⟩ := mem_centers.mp hi
    exact ⟨q,a,h₁,h₂,h₃,h₄,ht⟩

theorem measurable_cap (n U H : ℕ) : MeasurableSet (cap n U H) := by
  have h : cap n U H = ⋃ i ∈ centers U, arc n H i := by
    ext t
    rw [mem_cap]
    simp only [Set.mem_iUnion]
    constructor <;> rintro ⟨i,hi,ht⟩ <;> exact ⟨i,hi,ht⟩
  rw [h]
  exact MeasurableSet.iUnion fun i => MeasurableSet.iUnion fun _ => measurable_arc n H i

theorem arc_mono {n R H : ℕ} (h : R ≤ H) (i : ℕ × ℕ) : arc n R i ⊆ arc n H i := by
  intro t ht
  change |t - center i| ≤ radius n R i.1 at ht
  change |t - center i| ≤ radius n H i.1
  exact ht.trans (div_le_div_of_nonneg_right (by exact_mod_cast h) (by positivity))

theorem cap_mono {n Q U R H : ℕ} (hQ : Q ≤ U) (hH : R ≤ H) :
    cap n Q R ⊆ cap n U H := by
  intro t ht
  obtain ⟨i,hi,hit⟩ := mem_cap.mp ht
  exact mem_cap.mpr ⟨i,centers_mono hQ hi,arc_mono hH i hit⟩

theorem common_arc_unique {n U H : ℕ} (hbudget : 2 * H * U < n)
    {i j : ℕ × ℕ} (hi : i ∈ centers U) (hj : j ∈ centers U) {t : ℝ}
    (hti : t ∈ arc n H i) (htj : t ∈ arc n H j) : i = j := by
  obtain ⟨hi₁,hi₂,_,hi₄⟩ := mem_centers.mp hi
  obtain ⟨hj₁,hj₂,_,hj₄⟩ := mem_centers.mp hj
  obtain ⟨h₁,h₂⟩ := GoldbachWideArcs.reduced_centers_eq_of_common_point
    hbudget hi₁ hj₁ hi₂ hj₂ hi₄ hj₄ hti htj
  exact Prod.ext h₁ h₂

/-- A wide arc clipped to the unit interval, with its narrow interval removed when appropriate. -/
noncomputable def cell (n Q H : ℕ) (i : ℕ × ℕ) : Set ℝ :=
  (arc n H i \ (if i.1 ≤ Q then arc n Q i else ∅)) ∩ Set.Ioc 0 1

theorem measurable_cell (n Q H : ℕ) (i : ℕ × ℕ) : MeasurableSet (cell n Q H i) := by
  unfold cell
  apply MeasurableSet.inter _ measurableSet_Ioc
  apply (measurable_arc n H i).diff
  split
  · exact measurable_arc n Q i
  · exact MeasurableSet.empty

theorem cell_disjoint {n Q U H : ℕ} (hbudget : 2 * H * U < n) :
    (↑(centers U) : Set (ℕ × ℕ)).PairwiseDisjoint (cell n Q H) := by
  intro i hi j hj hij
  apply Set.disjoint_left.mpr
  intro t hti htj
  exact hij (common_arc_unique hbudget hi hj hti.1.1 htj.1.1)

theorem cells_eq {n Q U H : ℕ} (hQ : Q ≤ U) (hH : Q ≤ H) (hbudget : 2 * H * U < n) :
    (⋃ i ∈ centers U, cell n Q H i) = (cap n U H \ cap n Q Q) ∩ Set.Ioc 0 1 := by
  ext t
  simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_sdiff]
  constructor
  · rintro ⟨i,hi,ht⟩
    refine ⟨⟨mem_cap.mpr ⟨i,hi,ht.1.1⟩,?_⟩, ht.2⟩
    intro hN
    obtain ⟨j,hj,htj⟩ := mem_cap.mp hN
    have he := common_arc_unique hbudget hi (centers_mono hQ hj) ht.1.1 (arc_mono hH j htj)
    subst j
    apply ht.1.2
    rw [ite_eq_left (mem_centers.mp hj).2.1]
    exact htj
  · rintro ⟨⟨ht,hnot⟩,hunit⟩
    obtain ⟨i,hi,hti⟩ := mem_cap.mp ht
    refine ⟨i,hi,⟨⟨hti,?_⟩,hunit⟩⟩
    by_cases hic : i.1 ≤ Q
    · rw [ite_eq_left hic]
      intro hnarrow
      apply hnot
      obtain ⟨h₁,_,h₃,h₄⟩ := mem_centers.mp hi
      exact mem_cap.mpr ⟨i,mem_centers.mpr ⟨h₁,hic,h₃,h₄⟩,hnarrow⟩
    · simp [hic]

theorem integrate_difference_eq_sum {n Q U H : ℕ}
    (hQ : Q ≤ U) (hH : Q ≤ H) (hbudget : 2 * H * U < n) (F : ℝ → ℂ) (hF : Continuous F) :
    (∫ t in (0 : ℝ)..1, (cap n U H \ cap n Q Q).indicator F t) =
      ∑ i ∈ centers U, ∫ t in cell n Q H i, F t := by
  have hm := (measurable_cap n U H).diff (measurable_cap n Q Q)
  have hint : IntegrableOn F (Set.Ioc (0 : ℝ) 1) volume :=
    (hF.intervalIntegrable (0 : ℝ) 1).1
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1), setIntegral_indicator hm,
    inter_comm, ← cells_eq hQ hH hbudget]
  exact integral_biUnion_finset (centers U) (fun i _ => measurable_cell n Q H i)
    (cell_disjoint hbudget) (fun i _ => hint.mono_set inter_subset_right)

theorem integrate_middle_split {n Q U H : ℕ}
    (hQ : Q ≤ U) (hH : Q ≤ H) (F : ℝ → ℂ) (hF : Continuous F) :
    (∫ t in (0 : ℝ)..1, (cap n U Q \ cap n Q Q).indicator F t) +
      (∫ t in (0 : ℝ)..1, (cap n U H \ cap n U Q).indicator F t) =
        ∫ t in (0 : ℝ)..1, (cap n U H \ cap n Q Q).indicator F t := by
  let L := cap n Q Q
  let M := cap n U Q
  let W := cap n U H
  have hLM : L ⊆ M := cap_mono hQ le_rfl
  have hMW : M ⊆ W := cap_mono le_rfl hH
  have hm := (measurable_cap n U Q).diff (measurable_cap n Q Q)
  have hw := (measurable_cap n U H).diff (measurable_cap n U Q)
  have hint : IntegrableOn F (Set.Ioc (0 : ℝ) 1) volume :=
    (hF.intervalIntegrable (0 : ℝ) 1).1
  have hmi : IntervalIntegrable ((M \ L).indicator F) volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).2 (hint.indicator hm)
  have hwi : IntervalIntegrable ((W \ M).indicator F) volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).2 (hint.indicator hw)
  change (∫ t in (0 : ℝ)..1, (M \ L).indicator F t) +
    (∫ t in (0 : ℝ)..1, (W \ M).indicator F t) =
    ∫ t in (0 : ℝ)..1, (W \ L).indicator F t
  rw [← intervalIntegral.integral_add hmi hwi]
  apply intervalIntegral.integral_congr
  intro t _
  by_cases hl : t ∈ L
  · have hmt := hLM hl
    simp [hl, hmt]
  · by_cases hmt : t ∈ M
    · have hwt := hMW hmt
      simp [hl, hmt, hwt]
    · by_cases hwt : t ∈ W <;> simp [hl, hmt, hwt]

end GoldbachGRHArcs

end GoldbachGRHArcs

section GoldbachGRHCenterSums

open scoped BigOperators

namespace GoldbachGRHArcs

/-- Group the reduced arc centers by denominator. -/
theorem sum_centers_eq (U : ℕ) {A : Type*} [AddCommMonoid A] (F : ℕ × ℕ → A) :
    (∑ i ∈ centers U, F i) =
      ∑ q ∈ Finset.Icc 1 U, ∑ a ∈ (Finset.range (q + 1)).filter (fun a => a.Coprime q),
        F (q, a) := by
  rw [centers, Finset.sum_filter, Finset.sum_product]
  refine Finset.sum_congr rfl fun q hq => ?_
  change (∑ a ∈ Finset.range (U + 1), if a ≤ q ∧ a.Coprime q then F (q, a) else 0) = _
  rw [← Finset.sum_filter]
  have hqU := (Finset.mem_Icc.mp hq).2
  have hs : (Finset.range (U + 1)).filter (fun a => a ≤ q ∧ a.Coprime q) =
      (Finset.range (q + 1)).filter (fun a => a.Coprime q) := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨_, ha, hcop⟩
      exact ⟨Nat.lt_succ_of_le ha, hcop⟩
    · rintro ⟨ha, hcop⟩
      exact ⟨by omega, by omega, hcop⟩
  rw [hs]

/-- The least nonnegative representatives enumerate all residues once. -/
theorem sum_range_natCast_zmod (q : ℕ) [NeZero q] {A : Type*} [AddCommMonoid A]
    (f : ZMod q → A) :
    (∑ a ∈ Finset.range q, f (a : ZMod q)) = ∑ a : ZMod q, f a := by
  apply Finset.sum_bij (fun (a : ℕ) _ => (a : ZMod q))
  · intro a _
    exact Finset.mem_univ _
  · intro a ha b hb hab
    simpa only [ZMod.val_natCast_of_lt (Finset.mem_range.mp ha),
      ZMod.val_natCast_of_lt (Finset.mem_range.mp hb)] using congrArg ZMod.val hab
  · intro a _
    exact ⟨a.val, Finset.mem_range.mpr a.val_lt, ZMod.natCast_zmod_val a⟩
  · intro a _
    rfl

/-- Restrict to the reduced numerators of the closed unit interval. The factor
    two allows the endpoints \(0/1\) and \(1/1\) to share their residue. -/
theorem sum_numerators_le_real (q : ℕ) [NeZero q] (f : ZMod q → ℝ)
    (hf : ∀ a, 0 ≤ f a) :
    (∑ a ∈ (Finset.range (q + 1)).filter (fun a => a.Coprime q), f (a : ZMod q)) ≤
      2 * (∑ a : ZMod q, f a) := by
  calc
    _ ≤ ∑ a ∈ Finset.range (q + 1), f (a : ZMod q) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun a _ _ => hf a)
    _ = (∑ a ∈ Finset.range q, f (a : ZMod q)) + f (q : ZMod q) :=
      Finset.sum_range_succ _ _
    _ = (∑ a : ZMod q, f a) + f 0 := by
      rw [sum_range_natCast_zmod, ZMod.natCast_self]
    _ ≤ _ := by
      have hzero : f 0 ≤ ∑ a : ZMod q, f a :=
        Finset.single_le_sum (fun a _ => hf a) (Finset.mem_univ 0)
      linarith

end GoldbachGRHArcs

end GoldbachGRHCenterSums

section GoldbachGRHArcTransport

open MeasureTheory
open Set hiding center
open scoped Interval

namespace GoldbachGRHArcTransport

open GoldbachGRHArcs

private theorem radius_nonnegative (n H q : ℕ) : 0 ≤ radius n H q := by
  unfold radius
  positivity

private theorem continuous_translate {E : Type*} [TopologicalSpace E]
    {G : ℝ → E} (hG : Continuous G) (c : ℝ) : Continuous (fun t => G (t - c)) :=
  hG.comp (continuous_id.sub continuous_const)

section Integral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem arc_integral (n H : ℕ) (i : ℕ × ℕ) (G : ℝ → E) :
    (∫ t in arc n H i, G (t - center i)) =
      ∫ t in (-(radius n H i.1))..(radius n H i.1), G t := by
  have hr := radius_nonnegative n H i.1
  rw [arc_eq_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith only [hr] :
      center i - radius n H i.1 ≤ center i + radius n H i.1),
    intervalIntegral.integral_comp_sub_right]
  congr 2 <;> ring

private theorem clipped_arc_integral_closed (n H : ℕ) (i : ℕ × ℕ) (G : ℝ → E) :
    (∫ t in arc n H i ∩ Ioc 0 1, G (t - center i)) =
      ∫ t in arc n H i ∩ Icc 0 1, G (t - center i) := by
  apply setIntegral_congr_set
  have h : Ioc (0 : ℝ) 1 =ᵐ[volume] Icc (0 : ℝ) 1 := Ioc_ae_eq_Icc
  filter_upwards [h] with t ht
  simp only [mem_inter_iff, ht]

theorem clipped_arc_integral_of_interior (n H : ℕ) (i : ℕ × ℕ) (G : ℝ → E)
    (hleft : radius n H i.1 ≤ center i) (hright : center i + radius n H i.1 ≤ 1) :
    (∫ t in arc n H i ∩ Ioc 0 1, G (t - center i)) =
      ∫ t in (-(radius n H i.1))..(radius n H i.1), G t := by
  rw [clipped_arc_integral_closed, inter_eq_left.mpr, arc_integral]
  rw [arc_eq_Icc]
  exact Icc_subset_Icc (sub_nonneg.mpr hleft) hright

theorem clipped_arc_integral_zero (n H : ℕ) (G : ℝ → E)
    (hr : radius n H 1 ≤ 1) :
    (∫ t in arc n H (1, 0) ∩ Ioc 0 1, G (t - center (1, 0))) =
      ∫ t in (0 : ℝ)..(radius n H 1), G t := by
  have hnonneg := radius_nonnegative n H 1
  rw [clipped_arc_integral_closed, arc_eq_Icc]
  simp only [show center (1, 0) = 0 by norm_num [center], zero_sub, zero_add, sub_zero]
  rw [Icc_inter_Icc, sup_eq_right.mpr (neg_nonpos.mpr hnonneg), inf_eq_left.mpr hr,
    integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le hnonneg]

theorem clipped_arc_integral_one (n H : ℕ) (G : ℝ → E)
    (hr : radius n H 1 ≤ 1) :
    (∫ t in arc n H (1, 1) ∩ Ioc 0 1, G (t - center (1, 1))) =
      ∫ t in (-(radius n H 1))..(0 : ℝ), G t := by
  have hnonneg := radius_nonnegative n H 1
  rw [clipped_arc_integral_closed, arc_eq_Icc]
  simp only [show center (1, 1) = 1 by norm_num [center] ]
  rw [Icc_inter_Icc, sup_eq_left.mpr (sub_nonneg.mpr hr),
    inf_eq_right.mpr (by linarith only [hnonneg] : (1 : ℝ) ≤ 1 + radius n H 1),
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith only [hnonneg] :
      1 - radius n H 1 ≤ 1), intervalIntegral.integral_comp_sub_right]
  congr 2 <;> ring

theorem cell_integral_eq_clipped_sub {n Q H : ℕ} (hQH : Q ≤ H) (i : ℕ × ℕ)
    (G : ℝ → E) (hG : Continuous G) :
    (∫ t in cell n Q H i, G (t - center i)) =
      (∫ t in arc n H i ∩ Ioc 0 1, G (t - center i)) -
        if i.1 ≤ Q then (∫ t in arc n Q i ∩ Ioc 0 1, G (t - center i)) else 0 := by
  by_cases hq : i.1 ≤ Q
  · simp only [cell, ite_eq_left hq]
    rw [show (arc n H i \ arc n Q i) ∩ Ioc (0 : ℝ) 1 =
        (arc n H i ∩ Ioc 0 1) \ (arc n Q i ∩ Ioc 0 1) by
      ext t
      simp only [mem_inter_iff, mem_sdiff]
      tauto]
    apply setIntegral_sdiff ((measurable_arc n Q i).inter measurableSet_Ioc)
    · exact ((continuous_translate hG (center i)).intervalIntegrable 0 1).1.mono_set inter_subset_right
    · exact inter_subset_inter_left _ (arc_mono hQH i)
  · simp [cell, hq]

end Integral

/-- A nonnegative translated integrand on the clipped cell is bounded by its full window. -/
theorem cell_l2_le (n Q H : ℕ) (i : ℕ × ℕ) (G : ℝ → ℝ) (hG : Continuous G)
    (hG0 : ∀ t, 0 ≤ G t) :
    (∫ t in cell n Q H i, G (t - center i)) ≤
      ∫ t in (-(radius n H i.1))..(radius n H i.1), G t := by
  rw [← arc_integral]
  apply setIntegral_mono_set
  · rw [arc_eq_Icc, integrableOn_Icc_iff_integrableOn_Ioc]
    exact ((continuous_translate hG (center i)).intervalIntegrable _ _).1
  · exact Filter.Eventually.of_forall fun t => hG0 (t - center i)
  · exact (show cell n Q H i ⊆ arc n H i from fun _ ht => ht.1.1).eventuallySubset

theorem arc_interior_bounds {n H q a : ℕ} (hH : H ≤ n) (hq : 2 ≤ q) (ha : a ≤ q)
    (hcop : Nat.Coprime a q) :
    radius n H q ≤ center (q, a) ∧ center (q, a) + radius n H q ≤ 1 := by
  have ha0 : 1 ≤ a := by
    by_contra! hn
    have ha' : a = 0 := by omega
    subst a
    have h := (Nat.coprime_zero_left q).mp hcop
    omega
  have haq : a + 1 ≤ q := by
    by_contra! hn
    have ha' : a = q := by omega
    subst a
    have h : q = 1 := by simpa [Nat.Coprime] using hcop
    omega
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (show 0 < q by omega)
  have hr : radius n H q ≤ 1 / (q : ℝ) := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [radius]
    have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hHn : (H : ℝ) ≤ (n : ℝ) := by exact_mod_cast hH
    unfold radius
    apply (div_le_iff₀ (mul_pos hqR hnR)).mpr
    rw [← mul_assoc, one_div_mul_cancel hqR.ne', one_mul]
    exact hHn
  refine ⟨hr.trans ?_, (add_le_add_right hr (center (q, a))).trans ?_⟩
  · unfold center
    exact div_le_div_of_nonneg_right (by exact_mod_cast ha0) hqR.le
  · unfold center
    rw [← add_div]
    apply (div_le_iff₀ hqR).mpr
    simpa only [one_mul, Nat.cast_add, Nat.cast_one] using (show ((a + 1 : ℕ) : ℝ) ≤ q by
      exact_mod_cast haq)

theorem radius_one_le {n H : ℕ} (hH : H ≤ n) : radius n H 1 ≤ 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [radius]
  · simpa [radius] using (div_le_one (by exact_mod_cast hn : (0:ℝ) < n)).mpr
      (show (H : ℝ) ≤ n by exact_mod_cast hH)


theorem cell_integral_interior {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n Q H q a : ℕ} (hQH : Q ≤ H) (hHn : H ≤ n) (hq : 2 ≤ q) (ha : a ≤ q)
    (hcop : Nat.Coprime a q) (G : ℝ → E) (hG : Continuous G) :
    (∫ t in cell n Q H (q, a), G (t - center (q, a))) =
      (∫ t in (-(radius n H q))..(radius n H q), G t) -
        if q ≤ Q then (∫ t in (-(radius n Q q))..(radius n Q q), G t) else 0 := by
  obtain ⟨hHl, hHr⟩ := arc_interior_bounds hHn hq ha hcop
  obtain ⟨hQl, hQr⟩ := arc_interior_bounds (hQH.trans hHn) hq ha hcop
  rw [cell_integral_eq_clipped_sub hQH (q, a) G hG,
    clipped_arc_integral_of_interior n H (q, a) G hHl hHr,
    clipped_arc_integral_of_interior n Q (q, a) G hQl hQr]

/-- The two denominator-one cells assemble to a full translated window. -/
theorem cell_integral_endpoints {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n Q H : ℕ} (hQH : Q ≤ H) (hHn : H ≤ n) (G : ℝ → E) (hG : Continuous G) :
    (∫ t in cell n Q H (1, 0), G (t - center (1, 0))) +
      (∫ t in cell n Q H (1, 1), G (t - center (1, 1))) =
      (∫ t in (-(radius n H 1))..(radius n H 1), G t) -
        if 1 ≤ Q then (∫ t in (-(radius n Q 1))..(radius n Q 1), G t) else 0 := by
  have hQn := hQH.trans hHn
  have hfull (R : ℕ) :
      (∫ t in (0 : ℝ)..(radius n R 1), G t) +
        (∫ t in (-(radius n R 1))..(0 : ℝ), G t) =
          ∫ t in (-(radius n R 1))..(radius n R 1), G t := by
    rw [add_comm]
    exact intervalIntegral.integral_add_adjacent_intervals (hG.intervalIntegrable _ _)
      (hG.intervalIntegrable _ _)
  simp only [cell_integral_eq_clipped_sub hQH _ G hG,
    clipped_arc_integral_zero n H G (radius_one_le hHn),
    clipped_arc_integral_zero n Q G (radius_one_le hQn),
    clipped_arc_integral_one n H G (radius_one_le hHn),
    clipped_arc_integral_one n Q G (radius_one_le hQn)]
  by_cases h : 1 ≤ Q
  · simp only [ite_eq_left h]
    rw [← hfull H, ← hfull Q]
    abel
  · simpa only [ite_eq_right h, sub_zero] using hfull H

theorem cell_kernel_interior {n Q H q a : ℕ} (hQH : Q ≤ H) (hHn : H ≤ n)
    (hq : 2 ≤ q) (ha : a ≤ q) (hcop : Nat.Coprime a q) :
    (∫ t in cell n Q H (q, a), ‖GoldbachGRHKernel.kernel n (t - center (q, a))‖ ^ 2) =
      GoldbachGRHKernel.mass n (radius n H q) -
        if q ≤ Q then GoldbachGRHKernel.mass n (radius n Q q) else 0 :=
  cell_integral_interior hQH hHn hq ha hcop _
    ((GoldbachGRHKernel.kernel_continuous n).norm.pow 2)

theorem cell_kernel_endpoints {n Q H : ℕ} (hQH : Q ≤ H) (hHn : H ≤ n) :
    (∫ t in cell n Q H (1, 0), ‖GoldbachGRHKernel.kernel n (t - center (1, 0))‖ ^ 2) +
      (∫ t in cell n Q H (1, 1), ‖GoldbachGRHKernel.kernel n (t - center (1, 1))‖ ^ 2) =
      GoldbachGRHKernel.mass n (radius n H 1) -
        if 1 ≤ Q then GoldbachGRHKernel.mass n (radius n Q 1) else 0 :=
  cell_integral_endpoints hQH hHn _ ((GoldbachGRHKernel.kernel_continuous n).norm.pow 2)

end GoldbachGRHArcTransport

end GoldbachGRHArcTransport

section GoldbachGRHModelDef

namespace GoldbachGRHModel

/-- The principal model on a single reduced rational arc. -/
noncomputable def model (n : ℕ) (i : ℕ × ℕ) (t : ℝ) : ℂ :=
  ((ArithmeticFunction.moebius i.1 : ℂ) / (i.1.totient : ℂ)) *
    GoldbachGRHKernel.kernel n (t - GoldbachGRHArcs.center i)

theorem model_continuous (n : ℕ) (i : ℕ × ℕ) : Continuous (model n i) :=
  continuous_const.mul ((GoldbachGRHKernel.kernel_continuous n).comp
    (continuous_id.sub continuous_const))

end GoldbachGRHModel

end GoldbachGRHModelDef

section GoldbachGRHModelAssembly

open Finset MeasureTheory
open scoped ComplexConjugate

namespace GoldbachGRHModelAssembly

open GoldbachGRHArcs (cell centers center radius)
open GoldbachGRHKernel (kernel mass)
open GoldbachFourthMoment (phase phase_add)
open GoldbachGRHModel (model)
open GoldbachExplicitModeledMajor (coefficient ram ram_one_eq_moebius)

noncomputable def massDifference (n Q H q : ℕ) : ℝ :=
  mass n (radius n H q) - if q ≤ Q then mass n (radius n Q q) else 0

private noncomputable def signedFactor (n q a : ℕ) : ℂ :=
  ((ArithmeticFunction.moebius q : ℂ) / (q.totient : ℂ)) ^ 2 *
    phase (-(n : ℝ) * center (q, a))

private theorem phase_neg (x : ℝ) : phase (-x) = conj (phase x) := by
  symm
  unfold phase
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

private theorem signedFactor_zero (n : ℕ) : signedFactor n 1 0 = 1 := by
  simp [signedFactor, center, phase]

private theorem signedFactor_one (n : ℕ) : signedFactor n 1 1 = 1 := by
  simp [signedFactor, center, phase_neg, GoldbachGRHKernel.phase_nat]

private theorem model_square_eq (n q a : ℕ) (t : ℝ) :
    model n (q, a) t ^ 2 * phase (-(n : ℝ) * t) =
      signedFactor n q a * (↑(‖kernel n (t - center (q, a))‖ ^ 2) : ℂ) := by
  have hphase : -(n : ℝ) * t =
      -(n : ℝ) * center (q, a) + -(n : ℝ) * (t - center (q, a)) := by ring
  rw [← GoldbachGRHKernel.reflect n (t - center (q, a)), model, hphase, phase_add]
  unfold signedFactor
  ring

private theorem cell_model_integral (n Q H q a : ℕ) :
    (∫ t in cell n Q H (q, a), model n (q, a) t ^ 2 * phase (-(n : ℝ) * t)) =
      signedFactor n q a *
        (↑(∫ t in cell n Q H (q, a), ‖kernel n (t - center (q, a))‖ ^ 2) : ℂ) := by
  simp_rw [model_square_eq]
  rw [MeasureTheory.integral_const_mul, integral_complex_ofReal]

private theorem sum_signedFactor (n q : ℕ) :
    (∑ a ∈ (range q).filter (fun a => Nat.Coprime a q), signedFactor n q a) =
      coefficient q n := by
  rw [coefficient, ram_one_eq_moebius, ram, map_sum, Finset.mul_sum]
  refine sum_congr rfl fun a _ => ?_
  unfold signedFactor
  congr 1
  have h : -(n : ℝ) * center (q, a) = -((n : ℝ) * a / q) := by
    simp only [center, ← mul_div_assoc, neg_mul, neg_div]
  rw [h, phase_neg]
  rfl

/-- Grouping the centered kernels by denominator recovers the exact Ramanujan model. -/
theorem sum_cell_model {n Q H U : ℕ} (_hU : 1 ≤ U) (hQH : Q ≤ H) (hHn : H ≤ n) :
    (∑ i ∈ centers U, ∫ t in cell n Q H i, model n i t ^ 2 * phase (-(n : ℝ) * t)) =
      ∑ q ∈ Icc 1 U, coefficient q n * (massDifference n Q H q : ℂ) := by
  classical
  rw [GoldbachGRHArcs.sum_centers_eq]
  refine sum_congr rfl fun q hq => ?_
  have hq1 := (mem_Icc.mp hq).1
  by_cases hqOne : q = 1
  · subst q
    have hf : ((range (1 + 1)).filter (fun a : ℕ => Nat.Coprime a 1)) =
        ({0, 1} : Finset ℕ) := by
      ext a
      simp only [mem_filter, mem_range, Nat.coprime_one_right_iff, and_true,
        mem_insert, mem_singleton]
      omega
    rw [hf, sum_pair (by decide : (0 : ℕ) ≠ 1)]
    simp only [cell_model_integral, signedFactor_zero, signedFactor_one, one_mul,
      ← Complex.ofReal_add, GoldbachGRHArcTransport.cell_kernel_endpoints hQH hHn,
      GoldbachExplicitModeledMajor.coefficient_one, massDifference]
  · have hq2 : 2 ≤ q := by omega
    have hf : ((range (q + 1)).filter (fun a => Nat.Coprime a q)) =
        (range q).filter (fun a => Nat.Coprime a q) := by
      ext a
      simp only [mem_filter, mem_range]
      constructor
      · rintro ⟨haq, hcop⟩
        have hne : a ≠ q := by
          intro heq
          subst a
          have h : q = 1 := by simpa [Nat.Coprime] using hcop
          exact hqOne h
        exact ⟨lt_of_le_of_ne (Nat.lt_succ_iff.mp haq) hne, hcop⟩
      · rintro ⟨haq, hcop⟩
        exact ⟨haq.trans (Nat.lt_succ_self q), hcop⟩
    rw [hf, ← sum_signedFactor, Finset.sum_mul]
    refine sum_congr rfl fun a ha => ?_
    obtain ⟨haq, hcop⟩ := mem_filter.mp ha
    rw [cell_model_integral, GoldbachGRHArcTransport.cell_kernel_interior hQH hHn hq2
      (mem_range.mp haq).le hcop, massDifference]

theorem sum_cell_model_re {n Q H U : ℕ} (hU : 1 ≤ U) (hQH : Q ≤ H) (hHn : H ≤ n) :
    (∑ i ∈ centers U, ∫ t in cell n Q H i, model n i t ^ 2 * phase (-(n : ℝ) * t)).re =
      ∑ q ∈ Icc 1 U, (coefficient q n).re * massDifference n Q H q := by
  rw [sum_cell_model hU hQH hHn, Complex.re_sum]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]

end GoldbachGRHModelAssembly

end GoldbachGRHModelAssembly

section GoldbachGRHPrimeError

open Finset
open scoped Classical

namespace GoldbachGRHPrimeError

open GoldbachFourthMoment (primeWeight theta_eq_prime_log_sum)
open ArithmeticFunction

private noncomputable def gap (k : ℕ) : ℝ := vonMangoldt k - primeWeight k

private theorem gap_nonneg (k : ℕ) : 0 ≤ gap k := by
  unfold gap primeWeight
  by_cases hk : Nat.Prime k
  · simp [hk, vonMangoldt_apply_prime hk]
  · simp [hk]

private theorem sum_gap_le (n : ℕ) (hn : 1 ≤ n) (I : Finset ℕ) (hI : I ⊆ range (n+1)) :
    (∑ k ∈ I, gap k) ≤ 2 * Real.sqrt (n : ℝ) * Real.log (n : ℝ) := by
  have hp : Chebyshev.psi (n:ℝ) = ∑ k ∈ range (n+1), vonMangoldt k := by
    rw [Chebyshev.psi_eq_sum_Icc, Nat.floor_natCast, Nat.range_succ_eq_Icc_zero]
  have ht : Chebyshev.theta (n:ℝ) = ∑ k ∈ range (n+1), primeWeight k :=
    theta_eq_prime_log_sum n
  calc
    _ ≤ ∑ k ∈ range (n+1), gap k :=
      sum_le_sum_of_subset_of_nonneg hI (fun k _ _ => gap_nonneg k)
    _ = Chebyshev.psi (n:ℝ) - Chebyshev.theta (n:ℝ) := by
      simp only [hp, ht, gap, Finset.sum_sub_distrib]
    _ ≤ _ := Chebyshev.psi_sub_theta_le (by exact_mod_cast hn)

private theorem twist_gap_le (q n : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (I : Finset ℕ) (hI : I ⊆ range (n+1)) (hn : 1 ≤ n) :
    ‖∑ k ∈ I, (gap k : ℂ) * χ (k : ZMod q)‖ ≤ 2 * Real.sqrt (n : ℝ) * Real.log (n : ℝ) := by
  calc
    _ ≤ ∑ k ∈ I, ‖(gap k : ℂ) * χ (k : ZMod q)‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ I, gap k := by
      apply Finset.sum_le_sum
      intro k _
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (gap_nonneg k)]
      exact mul_le_of_le_one_right (gap_nonneg k) (χ.norm_le_one _)
    _ ≤ _ := sum_gap_le n hn I hI

theorem twisted_prime_interval (hGRH : Goldbach.GRH) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (n a b : ℕ),
      2 ≤ n → q ≤ n → b ≤ n →
      ‖(∑ k ∈ Icc a b, (primeWeight k : ℂ) * χ (k : ZMod q)) -
        (if χ = 1 then ((Icc a b).card : ℂ) else 0)‖ ≤
        C * Real.sqrt (n : ℝ) * (Real.log (n : ℝ))^2 := by
  classical
  obtain ⟨C,hC,hbound⟩ := GoldbachGRHCharacter.twistedMangoldtInterval hGRH
  refine ⟨9*C+4, by positivity, ?_⟩
  intro q hq χ n a b hn hqn hbn
  let P : ℂ := if χ = 1 then ((Icc a b).card : ℂ) else 0
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hpN : 0 ≤ (n : ℝ) := by positivity
  have hqR : (q : ℝ) ≤ (n : ℝ) := by exact_mod_cast hqn
  have hq₀ : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast (NeZero.pos q)
  have hlog : (1/2 : ℝ) ≤ Real.log (n : ℝ) := by
    have hh := Real.log_le_log (by norm_num : 0 < (2 : ℝ)) hnR
    linarith [Real.log_two_gt_d9]
  by_cases hab : a ≤ b
  · have hI : Icc a b ⊆ range (n+1) := by
      intro k hk
      exact mem_range.mpr ((mem_Icc.mp hk).2.trans_lt (by omega))
    have hGRHBound := hbound q χ n a b hn hab hbn
    have hGap := twist_gap_le q n χ (Icc a b) hI (by omega)
    have hsplit :
        (∑ k ∈ Icc a b, (primeWeight k : ℂ) * χ (k : ZMod q)) - P =
        ((∑ k ∈ Icc a b, (vonMangoldt k : ℂ) * χ (k : ZMod q)) - P) -
          (∑ k ∈ Icc a b, (gap k : ℂ) * χ (k : ZMod q)) := by
      suffices h :
          (∑ k ∈ Icc a b, (gap k : ℂ) * χ (k : ZMod q)) =
          (∑ k ∈ Icc a b, (vonMangoldt k : ℂ) * χ (k : ZMod q)) -
            (∑ k ∈ Icc a b, (primeWeight k : ℂ) * χ (k : ZMod q)) by
        rw [h]
        ring
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro k _
      rw [← sub_mul]
      simp only [gap, Complex.ofReal_sub]
    have hlog₀ : 0 ≤ Real.log (2 * (q : ℝ) * (n : ℝ)) := Real.log_nonneg (by
      have h := mul_le_mul (by linarith : (1:ℝ) ≤ 2*(q:ℝ)) (by linarith : (1:ℝ)≤(n:ℝ))
        (by norm_num : (0:ℝ)≤1) (by positivity : 0≤2*(q:ℝ))
      linarith)
    have hlogBound : Real.log (2 * (q : ℝ) * (n : ℝ)) ≤ 3 * Real.log (n : ℝ) := by
      calc
        _ ≤ Real.log ((n : ℝ)^3) := Real.log_le_log (by positivity) (by
          have h := mul_le_mul hnR hqR (by positivity : 0≤(q:ℝ)) hpN
          have h := mul_le_mul_of_nonneg_right h hpN
          nlinarith only [h])
        _ = _ := by rw [Real.log_pow]; norm_num
    have hs := pow_le_pow_left₀ hlog₀ hlogBound 2
    have hmul := mul_le_mul_of_nonneg_left hs
      (show 0 ≤ C * Real.sqrt (n:ℝ) by positivity)
    have hlog2 : 2 * Real.log (n:ℝ) ≤ 4 * (Real.log (n:ℝ))^2 := by
      have hs := mul_le_mul_of_nonneg_right hlog (show 0≤Real.log (n:ℝ) by linarith)
      nlinarith only [hs]
    have hmul2 := mul_le_mul_of_nonneg_right hlog2 (Real.sqrt_nonneg (n:ℝ))
    change ‖(∑ k ∈ Icc a b, (primeWeight k : ℂ) * χ (k : ZMod q)) - P‖ ≤ _
    rw [hsplit]
    apply (norm_sub_le _ _).trans
    exact (add_le_add hGRHBound hGap).trans (by nlinarith only [hmul, hmul2])
  · have he : Icc a b = ∅ := Finset.Icc_eq_empty_of_lt (lt_of_not_ge hab)
    rw [he]
    simp [show (0 : ℝ) ≤ (9*C+4) * Real.sqrt (n:ℝ) * Real.log (n:ℝ)^2 by positivity]

end GoldbachGRHPrimeError

end GoldbachGRHPrimeError

section GoldbachGRHWindowEnergy

open Finset MeasureTheory
open scoped Interval

namespace GoldbachGRHWindowEnergy

open GoldbachWindow

/-- The low-frequency estimate summed over a finite family with a common window length. -/
theorem sum_low_frequency_le {ι : Type*} (s : Finset ι) (N h : ℕ)
    (b : ι → ℕ → ℂ) (δ C : ℝ) (hh : 0 < h) (hδ : 0 ≤ δ)
    (hwidth : 6 * (h : ℝ) * δ ≤ 1)
    (hwindow : ∀ m ∈ range (N + h), ∑ i ∈ s, ‖moving N h (b i) m‖^2 ≤ C) :
    (h : ℝ)^2 / 4 * (∑ i ∈ s, ∫ t in (-δ)..δ, ‖poly N (b i) t‖^2) ≤
      ((N + h : ℕ) : ℝ) * C := by
  rw [Finset.mul_sum]
  calc
    _ ≤ ∑ i ∈ s, ∑ m ∈ range (N + h), ‖moving N h (b i) m‖^2 :=
      Finset.sum_le_sum fun i _ => low_frequency_le N h (b i) δ hh hδ hwidth
    _ = ∑ m ∈ range (N + h), ∑ i ∈ s, ‖moving N h (b i) m‖^2 := Finset.sum_comm
    _ ≤ ∑ _ ∈ range (N + h), C := Finset.sum_le_sum hwindow
    _ = _ := by rw [Finset.sum_const, card_range, nsmul_eq_mul]

/-- Choose the integer window by rounding down the reciprocal of the frequency width. -/
theorem sum_low_frequency_width_le {ι : Type*} (s : Finset ι) (N : ℕ)
    (b : ι → ℕ → ℂ) (δ C : ℝ) (hδ : 0 < δ) (hsmall : δ ≤ 1/24)
    (hlarge : 1 ≤ (N : ℝ) * δ) (hC : 0 ≤ C)
    (hwindow : ∀ m : ℕ, ∑ i ∈ s,
      ‖moving N ⌊1 / (12 * δ)⌋₊ (b i) m‖^2 ≤ C) :
    (∑ i ∈ s, ∫ t in (-δ)..δ, ‖poly N (b i) t‖^2) ≤ 4608 * (N : ℝ) * δ^2 * C := by
  let h := ⌊1 / (12 * δ)⌋₊
  have hz : 0 < 12 * δ := by positivity
  have hrec : 2 ≤ 1 / (12 * δ) := (le_div_iff₀ hz).2 (by linarith)
  have hh : 0 < h := lt_of_lt_of_le (by decide : 0 < 2) (Nat.le_floor (by simpa using hrec))
  have hhlo : 1 / (24 * δ) ≤ (h : ℝ) := by
    have hfloor := Nat.lt_floor_add_one (1 / (12 * δ))
    change 1 / (12 * δ) < (h : ℝ) + 1 at hfloor
    have heq : 1 / (24 * δ) = (1 / (12 * δ)) / 2 := by ring
    rw [heq]
    linarith
  have hhhi : (h : ℝ) ≤ 1 / (12 * δ) := Nat.floor_le (by positivity)
  have hwidth : 6 * (h : ℝ) * δ ≤ 1 := by
    have h := (le_div_iff₀ hz).1 hhhi
    nlinarith only [h]
  have hhN : (h : ℝ) ≤ (N : ℝ) := hhhi.trans <|
    (div_le_iff₀ hz).2 (by nlinarith only [hlarge])
  have hb := sum_low_frequency_le s N h b δ C hh hδ.le hwidth (fun m _ => hwindow m)
  let E := ∑ i ∈ s, ∫ t in (-δ)..δ, ‖poly N (b i) t‖^2
  have hE : 0 ≤ E := by
    apply Finset.sum_nonneg
    intro i hi
    exact intervalIntegral.integral_nonneg (by linarith) (fun _ _ => by positivity)
  have hhscale : 1 ≤ (24 * δ) * (h : ℝ) := by
    have h := (div_le_iff₀ (by positivity : 0 < 24 * δ)).1 hhlo
    simpa [mul_comm] using h
  have hEbound : (h : ℝ)^2 / 4 * E ≤ 2 * (N : ℝ) * C := by
    exact hb.trans (mul_le_mul_of_nonneg_right (by push_cast; linarith) hC)
  have hsq := pow_le_pow_left₀ (by norm_num : 0 ≤ (1 : ℝ)) hhscale 2
  calc
    E ≤ ((24 * δ) * (h : ℝ))^2 * E := by
      simpa only [one_pow, one_mul] using (mul_le_mul_of_nonneg_right hsq hE)
    _ = (4 * (24 * δ)^2) * ((h : ℝ)^2 / 4 * E) := by ring
    _ ≤ (4 * (24 * δ)^2) * (2 * (N : ℝ) * C) :=
      mul_le_mul_of_nonneg_left hEbound (by positivity)
    _ = _ := by ring

/-- Young's inequality written with the energy of the original sum. -/
private theorem norm_square_sub_square_le (z w : ℂ) {η : ℝ} (hη : 0 < η) :
    ‖z^2 - w^2‖ ≤ (1 + 1/η) * ‖z-w‖^2 + η * ‖z‖^2 := by
  have hfactor : z^2 - w^2 = (2 : ℂ) * z * (z-w) - (z-w)^2 := by ring
  have hmain :
      2 * ‖z‖ * ‖z - w‖ ≤ (1 / η) * ‖z - w‖^2 + η * ‖z‖^2 := by
    apply (le_of_mul_le_mul_right ?_ hη)
    have hsq := sq_nonneg (η * ‖z‖ - ‖z-w‖)
    field_simp
    nlinarith only [hsq]
  calc
    _ ≤ ‖(2 : ℂ) * z * (z-w)‖ + ‖(z-w)^2‖ := hfactor ▸ norm_sub_le _ _
    _ = 2 * ‖z‖ * ‖z-w‖ + ‖z-w‖^2 := by simp [norm_pow]
    _ ≤ _ := by linarith [hmain]

set_option maxHeartbeats 1500000 in
/-- On disjoint sets, compare the squared model with the original squared sum using its
global energy. The factors of modulus at most one can encode any target frequency. -/
theorem sum_setIntegral_square_difference_le {ι : Type*} (s : Finset ι)
    (D : ι → Set ℝ) (hD : ∀ i ∈ s, MeasurableSet (D i))
    (hsub : ∀ i ∈ s, D i ⊆ Set.Ioc 0 1)
    (hdisj : (↑s : Set ι).PairwiseDisjoint D) (S : ℝ → ℂ) (M : ι → ℝ → ℂ)
    (osc : ℝ → ℂ) (hS : Continuous S) (hM : ∀ i ∈ s, Continuous (M i))
    (hosc : Continuous osc) (hnorm : ∀ t, ‖osc t‖ ≤ 1) {η : ℝ} (hη : 0 < η) :
    (∑ i ∈ s, ‖∫ t in D i, (S t ^ 2 - M i t ^ 2) * osc t‖) ≤
      (1 + 1/η) * (∑ i ∈ s, ∫ t in D i, ‖S t - M i t‖^2) +
      η * (∫ t in (0 : ℝ)..1, ‖S t‖^2) := by
  let A (t : ℝ) := ‖S t‖^2
  let C (i : ι) (t : ℝ) := ‖S t - M i t‖^2
  have hA : Continuous A := hS.norm.pow 2
  have hAI : IntegrableOn A (Set.Ioc 0 1) volume := (hA.intervalIntegrable 0 1).1
  have hAi (i : ι) (hi : i ∈ s) : IntegrableOn A (D i) volume := hAI.mono_set (hsub i hi)
  have hUsed : (⋃ i ∈ s, D i) ⊆ Set.Ioc 0 1 := by
    intro t ht
    simp only [Set.mem_iUnion] at ht
    obtain ⟨i, hi, ht⟩ := ht
    exact hsub i hi ht
  have htotal : (∑ i ∈ s, ∫ t in D i, A t) ≤ ∫ t in (0 : ℝ)..1, A t := by
    rw [← integral_biUnion_finset s hD hdisj hAi,
      intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
    exact setIntegral_mono_set hAI (Filter.Eventually.of_forall (fun _ => by positivity))
      hUsed.eventuallySubset
  have hlocal (i : ι) (hi : i ∈ s) :
      ‖∫ t in D i, (S t ^ 2 - M i t ^ 2) * osc t‖ ≤
        (1+1/η) * (∫ t in D i, C i t) + η * (∫ t in D i, A t) := by
    have hCt : Continuous (C i) := ((hS.sub (hM i hi)).norm.pow 2)
    have hCi : IntegrableOn (C i) (D i) volume :=
      (hCt.intervalIntegrable 0 1).1.mono_set (hsub i hi)
    have hF : Continuous fun t => (S t ^ 2 - M i t ^ 2) * osc t :=
      ((hS.pow 2).sub ((hM i hi).pow 2)).mul hosc
    have hFi : IntegrableOn (fun t => ‖(S t ^ 2 - M i t ^ 2) * osc t‖) (D i) volume :=
      (hF.norm.intervalIntegrable 0 1).1.mono_set (hsub i hi)
    calc
      _ ≤ ∫ t in D i, ‖(S t ^ 2 - M i t ^ 2) * osc t‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ t in D i, (1+1/η) * C i t + η * A t := by
        apply integral_mono hFi ((hCi.const_mul _).add ((hAi i hi).const_mul _))
        intro t
        change ‖(S t ^ 2 - M i t ^ 2) * osc t‖ ≤
          (1+1/η) * ‖S t - M i t‖^2 + η * ‖S t‖^2
        rw [norm_mul]
        exact (mul_le_of_le_one_right (norm_nonneg _) (hnorm t)).trans
          (norm_square_sub_square_le (S t) (M i t) hη)
      _ = _ := by rw [integral_add (hCi.const_mul _) ((hAi i hi).const_mul _),
        integral_const_mul, integral_const_mul]
  calc
    _ ≤ ∑ i ∈ s, ((1+1/η) * (∫ t in D i, C i t) + η * (∫ t in D i, A t)) :=
      Finset.sum_le_sum hlocal
    _ = (1+1/η) * (∑ i ∈ s, ∫ t in D i, C i t) + η * (∑ i ∈ s, ∫ t in D i, A t) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_left htotal hη.le)

end GoldbachGRHWindowEnergy

end GoldbachGRHWindowEnergy

section GoldbachGRHAnalytic

open Finset
open scoped Interval Classical

namespace GoldbachGRHAnalytic

open GoldbachFourthMoment (phase phase_add primeSum primeWeight)
open GoldbachWindow (poly moving)
open GoldbachGRHWindow (additiveModel primeLog)
open GoldbachGRHKernel (kernel)

/-- Fourier coefficients of the deviation from the principal local model. -/
noncomputable def errorCoeff {q : ℕ} [NeZero q] (a : ZMod q) (k : ℕ) : ℂ :=
  primeLog k * ZMod.stdAddChar (a * (k : ZMod q)) - additiveModel q a

theorem shifted_error_eq {q : ℕ} [NeZero q] (n a : ℕ) (β : ℝ) :
    poly (n+1) (errorCoeff (a : ZMod q)) β =
      primeSum n ((a : ℝ) / (q:ℝ) + β) -
        additiveModel q (a : ZMod q) * kernel n β := by
  unfold kernel poly errorCoeff primeSum
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _
  rw [sub_mul, one_mul, GoldbachGRHWindow.stdAddChar_nat_pair]
  change (primeWeight k : ℂ) * phase ((a:ℝ)*(k:ℝ)/(q:ℝ)) * phase ((k:ℝ)*β) -
    additiveModel q (a : ZMod q) * phase ((k:ℝ)*β) =
      (primeWeight k : ℂ) * phase ((k:ℝ)*((a:ℝ)/(q:ℝ)+β)) -
        additiveModel q (a : ZMod q) * phase ((k:ℝ)*β)
  rw [mul_assoc, ← phase_add]
  congr 3
  ring

theorem prime_sum_energy_le (n : ℕ) (hn : 2 ≤ n) :
    (∫ t in (0:ℝ)..1, ‖primeSum n t‖^2) ≤ ((n:ℝ)+1)*(Real.log (n:ℝ))^2 := by
  change (∫ t in (0:ℝ)..1, ‖poly (n+1) (fun k => (primeWeight k:ℂ)) t‖^2) ≤ _
  rw [GoldbachWindow.parseval]
  have hnR : (1:ℝ) ≤ n := by exact_mod_cast (show 1≤n by omega)
  calc
    _ ≤ ∑ k ∈ range (n+1), (Real.log (n:ℝ))^2 := by
      apply Finset.sum_le_sum
      intro k hk
      unfold primeWeight
      by_cases hp : k.Prime
      · rw [ite_eq_left hp, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg
          (Real.log_nonneg (by exact_mod_cast hp.one_lt.le))]
        exact pow_le_pow_left₀ (Real.log_nonneg (by exact_mod_cast hp.one_lt.le))
          (Real.log_le_log (by exact_mod_cast hp.pos)
            (by exact_mod_cast Nat.le_of_lt_succ (mem_range.mp hk))) _
      · simpa [hp] using (sq_nonneg (Real.log (n:ℝ)))
    _ = _ := by simp [Finset.sum_const, nsmul_eq_mul]

private theorem window_eq_Icc (n h m : ℕ) :
    (range (n+1)).filter (fun k => m+1-h≤k ∧ k≤m) = Icc (m+1-h) (min m n) := by
  ext k
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc, le_min_iff]
  omega

theorem per_denominator_energy (hGRH : Goldbach.GRH) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n q H : ℕ) [NeZero q], 2 ≤ n → q ≤ n →
      let δ := (H : ℝ) / ((q : ℝ)*(n:ℝ))
      0 < δ → δ ≤ 1/24 → 1 ≤ ((n+1:ℕ):ℝ)*δ →
      (∑ a : ZMod q, ∫ β in (-δ)..δ, ‖poly (n+1) (errorCoeff a) β‖^2) ≤
        C*(H:ℝ)^2/(q:ℝ)*(Real.log (n:ℝ))^4 := by
  obtain ⟨C,hC,hprime⟩ := GoldbachGRHPrimeError.twisted_prime_interval hGRH
  refine ⟨9216*(C^2+4),by positivity,?_⟩
  intro n q H hq hn hqn δ hδ hsmall hlarge
  have hnR : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : 0 < (n:ℝ) := by linarith
  have hqR : (1:ℝ) ≤ q := by exact_mod_cast (NeZero.pos q)
  have hqpos : 0 < (q:ℝ) := by linarith
  have hlog : (1/2:ℝ) ≤ Real.log (n:ℝ) := by
    have ht := Real.log_le_log (by norm_num : 0<(2:ℝ)) hnR
    linarith [Real.log_two_gt_d9]
  have hlogq : 0 ≤ Real.log (q:ℝ) := Real.log_nonneg hqR
  have hlogq_le : Real.log (q:ℝ) ≤ Real.log (n:ℝ) :=
    Real.log_le_log hqpos (by exact_mod_cast hqn)
  let L := Real.log (n:ℝ)
  let B := C * Real.sqrt (n:ℝ) * L^2
  let U := (q:ℝ)*((C^2+4)*(n:ℝ)*L^4)
  have hU : 0 ≤ U := by unfold U L; positivity
  have hB : 0 ≤ B := by unfold B L; positivity
  have hsq : B^2+(Real.log (q:ℝ))^2 ≤ (C^2+4)*(n:ℝ)*L^4 := by
    have hl := pow_le_pow_left₀ hlogq hlogq_le 2
    have hlog' : (1/2:ℝ) ≤ L := hlog
    have hs := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤1/2) hlog' 2
    have hl' := mul_le_mul_of_nonneg_right hs (sq_nonneg L)
    have hm := mul_le_mul_of_nonneg_right (show (1:ℝ)≤n by linarith) (pow_nonneg (show 0≤L by linarith) 4)
    change (Real.log (q:ℝ))^2 ≤ L^2 at hl
    have hBp : B^2 = C^2*(n:ℝ)*L^4 := by
      unfold B
      rw [mul_pow, mul_pow, Real.sq_sqrt hnpos.le]
      ring
    rw [hBp]
    nlinarith only [hl,hl',hm]
  have hwindow (m : ℕ) : ∑ a : ZMod q,
      ‖moving (n+1) ⌊1/(12*δ)⌋₊ (errorCoeff a) m‖^2 ≤ U := by
    let h := ⌊1/(12*δ)⌋₊
    let I := Icc (m+1-h) (min m n)
    change (∑ a : ZMod q, ‖moving (n+1) h (errorCoeff a) m‖^2) ≤ U
    simp_rw [GoldbachWindow.moving_eq_sum, window_eq_Icc, errorCoeff]
    have ht := GoldbachGRHWindow.sum_additive_window_error_sq_le (q:=q) I primeLog B
      (Real.log (q:ℝ)) hB hlogq (by
        intro χ
        exact hprime q χ n (m+1-h) (min m n) hn hqn (min_le_right _ _))
      (GoldbachGRHWindow.primeLog_nonunit_mass_le (q:=q) I)
    exact ht.trans (mul_le_mul_of_nonneg_left hsq (Nat.cast_nonneg q))
  have hfreq := GoldbachGRHWindowEnergy.sum_low_frequency_width_le univ (n+1)
    (fun a : ZMod q => errorCoeff a) δ U hδ hsmall hlarge hU hwindow
  calc
    _ ≤ 4608 * ((n+1:ℕ):ℝ) * δ^2 * U := hfreq
    _ ≤ 4608 * (2*(n:ℝ)) * δ^2 * U := by
      gcongr
      push_cast
      linarith
    _ = _ := by
      dsimp [δ, U, L]
      field_simp [hnpos.ne', hqpos.ne']
      ring

end GoldbachGRHAnalytic

end GoldbachGRHAnalytic

section GoldbachGRHBudget

open Filter Finset
open scoped Topology

namespace GoldbachGRHBudget

def narrow (n : ℕ) : ℕ := (Nat.log 2 (n+2))^2
noncomputable def cutoff (n : ℕ) : ℕ := ⌊(n:ℝ)^(1/3:ℝ)⌋₊
noncomputable def width (n : ℕ) : ℕ := 256 * cutoff n * narrow n

private theorem log_nat_le (n : ℕ) (hn : 2 ≤ n) : (Nat.log 2 (n+2) : ℝ) ≤ 4 * Real.log (n:ℝ) := by
  have hnR : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hnon : 0 ≤ Real.log (n:ℝ) := Real.log_nonneg (by linarith)
  have hpow : (2:ℝ)^(Nat.log 2 (n+2)) ≤ ((n+2 : ℕ):ℝ) := by
    exact_mod_cast Nat.pow_log_le_self 2 (by omega : n+2 ≠ 0)
  have hraw := Real.log_le_log (by positivity) hpow
  have hin : ((n+2 : ℕ) : ℝ) ≤ (n:ℝ)^2 := by
    push_cast
    nlinarith only [hnR, sq_nonneg ((n:ℝ)-2)]
  have hlog := Real.log_le_log (by positivity) hin
  rw [Real.log_pow] at hraw hlog
  have hl2 : (1/2:ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hm := mul_le_mul_of_nonneg_left hl2 (Nat.cast_nonneg (Nat.log 2 (n+2)) : 0≤(_ : ℝ))
  push_cast at hlog hraw
  linarith only [hm, hraw, hlog]

theorem eventually_log_pow_le (k : ℕ) (a c : ℝ) (ha : 0 < a) (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop, (Real.log (n:ℝ))^k ≤ c * (n:ℝ)^a := by
  have h := (isLittleO_log_rpow_rpow_atTop (s:=a) k ha).def hc
  filter_upwards [h.natCast_atTop] with n hn
  simpa only [Real.rpow_natCast, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) a)]
    using (le_abs_self ((Real.log (n:ℝ))^(k:ℝ))).trans hn

theorem eventual_geometry :
    ∀ᶠ n : ℕ in atTop, 2 ≤ n ∧ 1 ≤ narrow n ∧ narrow n ≤ cutoff n ∧ cutoff n ≤ n ∧
      24 * width n ≤ n ∧ 2 * width n * cutoff n < n := by
  obtain ⟨N,hN⟩ := GoldbachFourthGeometry.eventually_strip_budget
  have hroot : ∀ᶠ n : ℕ in atTop, (3:ℝ) ≤ (n:ℝ)^(1/3:ℝ) :=
    ((tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/3)).comp
      (tendsto_natCast_atTop_atTop (R:=ℝ))).eventually (eventually_ge_atTop (3:ℝ))
  filter_upwards [eventually_ge_atTop N, eventually_ge_atTop (2:ℕ), hroot,
    eventually_log_pow_le 2 (1/3) (1/32) (by norm_num) (by norm_num)] with n hnN hn h3 hlog
  obtain ⟨hU,hH,hNn⟩ := hN n hnN
  change 2 * width n * (4 * cutoff n) < n at hU
  have hQ₀ : 1 ≤ narrow n := by
    unfold narrow
    exact Nat.pow_pos (Nat.log_pos (by decide) (by omega))
  have hQ : narrow n ≤ cutoff n := by
    apply Nat.le_floor
    calc
      (narrow n : ℝ) ≤ (4 * Real.log (n:ℝ))^2 := by
        unfold narrow
        push_cast
        exact pow_le_pow_left₀ (by positivity) (log_nat_le n hn) _
      _ = 16 * Real.log (n:ℝ)^2 := by ring
      _ ≤ (n:ℝ)^(1/3:ℝ) := by
        have ht := mul_le_mul_of_nonneg_left hlog (show (0:ℝ)≤16 by norm_num)
        nlinarith only [ht, Real.rpow_nonneg (Nat.cast_nonneg n) (1/3:ℝ)]
  have hU3 : 3 ≤ cutoff n := Nat.le_floor (by exact h3)
  have hW : 24 * width n ≤ n := by
    have ht := Nat.mul_le_mul_left (2*width n) (show 12 ≤ 4*cutoff n by omega)
    omega
  have hBudget : 2 * width n * cutoff n < n := by
    have ht := Nat.mul_le_mul_left (2*width n) (show cutoff n ≤ 4*cutoff n by omega)
    exact ht.trans_lt hU
  exact ⟨hn,hQ₀,hQ,(by change 4 * cutoff n ≤ n at hNn; omega),hW,hBudget⟩

theorem width_ge_cutoff (n : ℕ) (h : 1 ≤ narrow n) : cutoff n ≤ width n := by
  unfold width
  have hh := Nat.mul_le_mul_left (256 * cutoff n) h
  omega

theorem harmonic_le (U : ℕ) : (∑ q ∈ Icc 1 U, 1 / (q : ℝ)) ≤ 1 + Real.log U := by
  have hh := harmonic_le_one_add_log U
  apply le_trans _ hh
  unfold harmonic
  rw [Rat.cast_sum]
  -- Compare the shifted positive range with the sum defining the harmonic number.
  have he : Icc 1 U = (range U).map ⟨Nat.succ, Nat.succ_injective⟩ := by
    ext j
    simp only [Finset.mem_Icc, Finset.mem_map, Function.Embedding.coeFn_mk, Finset.mem_range]
    constructor
    · rintro ⟨hj,hU⟩
      exact ⟨j-1,by omega,by omega⟩
    · rintro ⟨k,hk,rfl⟩
      omega
  rw [he, Finset.sum_map]
  simp [one_div, Nat.succ_eq_add_one, Nat.cast_add]

theorem eventually_wide_energy (C : ℝ) (hC : 0 < C) :
    ∀ᶠ n : ℕ in atTop, C * (width n : ℝ)^2 * (Real.log (n:ℝ))^5 ≤ (n:ℝ)^(5/6:ℝ) := by
  have hC' : 0 < 1 / (C * (4096:ℝ)^2) := by positivity
  filter_upwards [eventually_ge_atTop (2:ℕ), eventually_log_pow_le 9 (1/6)
    (1/(C*(4096:ℝ)^2)) (by norm_num) hC'] with n hn hlog
  have hnR : (0:ℝ) < n := Nat.cast_pos.mpr (by omega)
  let x := (n:ℝ)^(1/3:ℝ)
  have hU : (cutoff n:ℝ) ≤ x := Nat.floor_le (Real.rpow_nonneg hnR.le _)
  have hN : (narrow n:ℝ) ≤ (4*Real.log (n:ℝ))^2 := by
    unfold narrow
    push_cast
    exact pow_le_pow_left₀ (by positivity) (log_nat_le n hn) _
  have hw : (width n:ℝ) ≤ 4096 * x * (Real.log (n:ℝ))^2 := by
    unfold width
    push_cast
    calc
      _ ≤ 256 * x * (4*Real.log (n:ℝ))^2 :=
        mul_le_mul (mul_le_mul_of_nonneg_left hU (by norm_num)) hN (by positivity) (by positivity)
      _ = _ := by ring
  have hlog₀ : 0 ≤ Real.log (n:ℝ) := Real.log_nonneg (by exact_mod_cast (show 1≤n by omega))
  have hx : x^2 = (n:ℝ)^(2/3:ℝ) := by
    dsimp [x]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hnR.le]
    norm_num
  calc
    _ ≤ C * (4096*x*(Real.log (n:ℝ))^2)^2*(Real.log (n:ℝ))^5 :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hw _) hC.le)
        (pow_nonneg hlog₀ _)
    _ = x^2*(C*4096^2*(Real.log (n:ℝ))^9) := by ring
    _ ≤ x^2*(n:ℝ)^(1/6:ℝ) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have ht := mul_le_mul_of_nonneg_left hlog (show 0≤C*(4096:ℝ)^2 by positivity)
      convert ht using 1
      field_simp
    _ = _ := by rw [hx, ← Real.rpow_add hnR]; norm_num

end GoldbachGRHBudget

end GoldbachGRHBudget

section GoldbachGRHYoungBudget

open Filter Asymptotics
open scoped Topology

namespace GoldbachGRHYoungBudget

/-- The two errors from Young's inequality use a sublinear budget with
    the common parameter \(n^{-1/12}\). -/
theorem eventually_young_budget (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      let η := (n : ℝ) ^ (-1 / 12 : ℝ)
      0 < η ∧ (1 + 1 / η) * (n : ℝ) ^ (5 / 6 : ℝ) +
        η * ((n : ℝ) + 1) * (Real.log (n : ℝ)) ^ 2 ≤ ε * (n : ℝ) := by
  have hlogLimit : Tendsto (fun n : ℕ => Real.log (n : ℝ) ^ 2 / (n : ℝ) ^ (1 / 24 : ℝ))
      atTop (𝓝 0) := by
    have h := (isLittleO_log_rpow_rpow_atTop ((2 : ℕ) : ℝ)
      (by norm_num : (0 : ℝ) < 1 / 24)).tendsto_div_nhds_zero
    simpa only [Function.comp_def, Real.rpow_natCast] using
      h.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hpowerLimit : Tendsto (fun n : ℕ => (n : ℝ) ^ (1 / 24 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 24)).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
  filter_upwards [eventually_ge_atTop 1, hlogLimit.eventually_lt_const zero_lt_one,
    (tendsto_atTop.1 hpowerLimit) (4 / ε)] with n hn hlog hlarge
  let x : ℝ := n
  let η := x ^ (-1 / 12 : ℝ)
  change 0 < η ∧ (1 + 1 / η) * x ^ (5 / 6 : ℝ) + η * (x + 1) * (Real.log x) ^ 2 ≤ ε * x
  have hx1 : 1 ≤ x := by
    change (1 : ℝ) ≤ (n : ℝ)
    exact_mod_cast hn
  have hx : 0 < x := zero_lt_one.trans_le hx1
  have hη : 0 < η := Real.rpow_pos_of_pos hx _
  have hlog' : Real.log x ^ 2 ≤ x ^ (1 / 24 : ℝ) := by
    change Real.log x ^ 2 / x ^ (1 / 24 : ℝ) < 1 at hlog
    simpa using (div_le_iff₀ (Real.rpow_pos_of_pos hx (1 / 24 : ℝ))).mp hlog.le
  have hinv : 1 / η = x ^ (1 / 12 : ℝ) := by
    dsimp [η]
    rw [show (-1 / 12 : ℝ) = -(1 / 12 : ℝ) by norm_num, Real.rpow_neg hx.le, one_div, inv_inv]
  have hfirst : (1 + 1 / η) * x ^ (5 / 6 : ℝ) ≤ 2 * x ^ (23 / 24 : ℝ) := by
    calc
      _ = x ^ (5 / 6 : ℝ) + x ^ (11 / 12 : ℝ) := by
        rw [hinv, add_mul, one_mul, ← Real.rpow_add hx]
        norm_num
      _ ≤ 2 * x ^ (23 / 24 : ℝ) := by
        have ha := Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num : (5 / 6 : ℝ) ≤ 23 / 24)
        have hb := Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num : (11 / 12 : ℝ) ≤ 23 / 24)
        linarith
  have hsecond : η * (x + 1) * (Real.log x) ^ 2 ≤ 2 * x ^ (23 / 24 : ℝ) := by
    have hsize : x + 1 ≤ 2 * x := by linarith
    calc
      _ ≤ η * (2 * x) * x ^ (1 / 24 : ℝ) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hsize hη.le) hlog' (sq_nonneg _) (by positivity)
      _ = 2 * (η * x ^ (1 : ℝ) * x ^ (1 / 24 : ℝ)) := by rw [Real.rpow_one]; ring
      _ = _ := by
        dsimp [η]
        rw [← Real.rpow_add hx, ← Real.rpow_add hx]
        norm_num
  refine ⟨hη, ?_⟩
  have hlarge' : 4 ≤ ε * x ^ (1 / 24 : ℝ) := by
    change 4 / ε ≤ x ^ (1 / 24 : ℝ) at hlarge
    simpa only [mul_comm] using (div_le_iff₀ hε).mp hlarge
  calc
    _ ≤ 4 * x ^ (23 / 24 : ℝ) := by linarith
    _ ≤ (ε * x ^ (1 / 24 : ℝ)) * x ^ (23 / 24 : ℝ) :=
      mul_le_mul_of_nonneg_right hlarge' (Real.rpow_nonneg hx.le _)
    _ = ε * x := by rw [mul_assoc, ← Real.rpow_add hx]; norm_num

end GoldbachGRHYoungBudget

end GoldbachGRHYoungBudget

section GoldbachGRHSignedModel

open Filter
open scoped Topology BigOperators ComplexConjugate

namespace GoldbachGRHSignedModel

open Finset

theorem weighted_suffix_lower (f : ℕ → ℝ) (ε : ℝ) (hε : 0 ≤ ε) :
    ∀ (m A : ℕ) (w : ℕ → ℝ), Monotone w → (∀ q ≥ A, 0 ≤ w q) →
      (∀ k, A ≤ k → k ≤ A+m → -ε ≤ ∑ q ∈ Ioc k (A+m), f q) →
      -(ε * w (A+m)) ≤ ∑ q ∈ Ioc A (A+m), f q * w q := by
  intro m
  induction m with
  | zero =>
    intro A w _ hw _
    simpa using neg_nonpos.mpr (mul_nonneg hε (hw A le_rfl))
  | succ m ih =>
    intro A w hw hw₀ hfloor
    let B := A + (m+1)
    let v : ℕ → ℝ := fun q => w q-w (A+1)
    have hB : A+1+m=B := by dsimp [B]; omega
    have hv : Monotone v := by
      intro i j hij
      exact sub_le_sub_right (hw hij) _
    have hv₀ (q : ℕ) (hq : A+1 ≤ q) : 0 ≤ v q := sub_nonneg.mpr (hw hq)
    have hsub : -(ε * v B) ≤ ∑ q ∈ Ioc (A+1) B, f q * v q := by
      rw [← hB]
      apply ih (A+1) v hv hv₀
      intro k hk hkB
      simpa only [hB] using hfloor k (by omega) (show k ≤ B from hB ▸ hkB)
    have hs : Ioc A B = insert (A+1) (Ioc (A+1) B) := by
      ext k
      have hAB : A+1 ≤ B := by dsimp [B]; omega
      simp only [mem_Ioc, mem_insert]
      omega
    have hnin : A+1 ∉ Ioc (A+1) B := by simp
    have hsum :
        (∑ q ∈ Ioc A B, f q * w q) =
          w (A+1) * (∑ q ∈ Ioc A B, f q) +
            ∑ q ∈ Ioc (A+1) B, f q * v q := by
      rw [hs]
      simp only [sum_insert hnin, v, mul_sub, sum_sub_distrib, ← sum_mul]
      ring
    have hf := hfloor A le_rfl (by omega)
    have hfirst : -(ε * w (A+1)) ≤ w (A+1) * (∑ q ∈ Ioc A B, f q) := by
      simpa [B, mul_comm] using mul_le_mul_of_nonneg_left hf (hw₀ (A+1) (by omega))
    change -(ε * w B) ≤ ∑ q ∈ Ioc A B, f q * w q
    rw [hsum]
    dsimp [v] at hsub
    calc
      _ = -(ε*w (A+1)) + -(ε*(w B-w (A+1))) := by ring
      _ ≤ _ := add_le_add hfirst hsub

theorem weighted_suffix_lower_of_le_one (f w : ℕ → ℝ) (ε : ℝ) (hε : 0 ≤ ε)
    {A B : ℕ} (hAB : A ≤ B) (hw : Monotone w) (hw₀ : ∀ q ≥ A, 0 ≤ w q) (hwend : w B ≤ 1)
    (hfloor : ∀ k, A ≤ k → k ≤ B → -ε ≤ ∑ q ∈ Ioc k B, f q) :
    -ε ≤ ∑ q ∈ Ioc A B, f q * w q := by
  have hlen : A+(B-A)=B := Nat.add_sub_of_le hAB
  have hh := weighted_suffix_lower f ε hε (B-A) A w hw hw₀
  rw [hlen] at hh
  exact (by nlinarith [mul_le_mul_of_nonneg_left hwend hε] : -ε ≤ -(ε * w B)).trans (hh hfloor)

end GoldbachGRHSignedModel

namespace GoldbachGRHSignedModel

open Finset Filter ArithmeticFunction
open scoped Topology ArithmeticFunction.zeta

private theorem inverse_squares_ge_two_le (X : ℕ) :
    (∑ j ∈ Icc 2 X, ((j : ℝ)^2)⁻¹) ≤ 3/4 := by
  by_cases hX : 2 ≤ X
  · rw [← sum_Ioc_add_eq_sum_Icc hX]
    have hh := sum_Ioc_inv_sq_le_sub (α := ℝ) (by decide : (2 : ℕ) ≠ 0) hX
    norm_num at hh ⊢
    linarith [show 0 ≤ ((X : ℝ))⁻¹ by positivity]
  · norm_num [Icc_eq_empty_of_lt (lt_of_not_ge hX)]

private theorem product_one_sub_ge {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    (hf : ∀ i ∈ s, 0 ≤ f i ∧ f i ≤ 1) :
    1 - (∑ i ∈ s, f i) ≤ ∏ i ∈ s, (1-f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have haF := hf a (mem_insert_self _ _)
    have hs : ∀ i ∈ s, 0 ≤ f i ∧ f i ≤ 1 := fun i hi => hf i (mem_insert_of_mem hi)
    rw [sum_insert ha, prod_insert ha]
    have hsum : 0 ≤ ∑ i ∈ s, f i := sum_nonneg fun i hi => (hs i hi).1
    have hh := mul_le_mul_of_nonneg_left (ih hs) (sub_nonneg.mpr haF.2)
    nlinarith only [hh, mul_nonneg haF.1 hsum]

private noncomputable def correctionLoss (n p : ℕ) : ℝ :=
  if p ∣ n then 0 else (((p : ℝ)-1)^2)⁻¹

private theorem odd_prime_ge_three {n p : ℕ} (hn : Even n) (hp : p.Prime)
    (hpn : ¬ p ∣ n) : 3 ≤ p := by
  have hp2 := hp.two_le
  by_contra! hh
  have hp₂ : p = 2 := by omega
  apply hpn
  rw [hp₂]
  obtain ⟨k, hk⟩ := hn
  exact ⟨k, by omega⟩

private theorem correctionLoss_bounds {n p : ℕ} (hn : Even n) (hp : p.Prime) :
    0 ≤ correctionLoss n p ∧ correctionLoss n p ≤ 1 := by
  unfold correctionLoss
  by_cases hpN : p ∣ n
  · simp [hpN]
  · have h3 : (3 : ℝ) ≤ p := by exact_mod_cast odd_prime_ge_three hn hp hpN
    rw [ite_eq_right hpN]
    exact ⟨by positivity, inv_le_one_of_one_le₀ (by nlinarith [sq_nonneg ((p:ℝ)-2)])⟩

private theorem local_correction_floor (n p k : ℕ) (hp : p.Prime) :
    1 - correctionLoss n p ≤ ∑ d ∈ (p^k).divisors, BandTail.z n d := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp1 : 0 < (p : ℝ) - 1 := by linarith
  rw [Nat.sum_divisors_prime_pow hp,
    BandTail.localReduce (fun j => BandTail.z n (p^j))
      (fun j => by simp [BandTail.z,BandTail.h_cube n p j hp])]
  simp only [pow_zero,pow_one,(BandTail.z_mult n).map_one]
  simp only [correctionLoss,BandTail.z,ArithmeticFunction.coe_mk,
    BandTail.h_prime n p hp,BandTail.h_square n p hp,Nat.cast_pow]
  by_cases hpn : p ∣ n
  · simp only [hpn, ite_true, sub_zero]
    have hpos : 0 ≤ (1 / ((p : ℝ)-1)) / (p : ℝ) := by positivity
    have hcancel : (1 / ((p : ℝ)-1)) / (p : ℝ) +
        (-(p : ℝ) / ((p : ℝ)-1)) / (p : ℝ)^2 = 0 := by
      field_simp; ring
    split_ifs <;> first | omega | linarith only [hpos,hcancel]
  · simp only [hpn, ite_false, zero_div, ite_self, add_zero]
    have hneg : (-(p : ℝ) / ((p : ℝ)-1)^2) / (p : ℝ) = -(((p : ℝ)-1)^2)⁻¹ := by
      field_simp
    rw [hneg]
    split_ifs <;> linarith [show 0 ≤ (((p : ℝ)-1)^2)⁻¹ by positivity]

theorem signed_divisors_quarter (n M : ℕ) (hn : Even n) (hM : 0 < M) :
    (1/4 : ℝ) ≤ ∑ d ∈ M.divisors, BandTail.z n d := by
  classical
  let s := M.factorization.support
  let P := s.filter (fun p => ¬ p ∣ n)
  have hprime (p : ℕ) (hp : p ∈ s) : p.Prime :=
    Nat.prime_of_mem_primeFactors (M.support_factorization ▸
      (show p ∈ M.factorization.support from hp))
  have hle (p : ℕ) (hp : p ∈ s) : p ≤ M :=
    Nat.le_of_dvd hM (Nat.dvd_of_mem_primeFactors (M.support_factorization ▸
      (show p ∈ M.factorization.support from hp)))
  have hM' (p : ℕ) (hp : p ∈ P) : 3 ≤ p :=
    odd_prime_ge_three hn (hprime p (mem_filter.mp hp).1) (mem_filter.mp hp).2
  have hinj : Set.InjOn (fun p : ℕ => p-1) (↑P : Set ℕ) := by
    intro p hp q hq he
    have h1 := hM' p hp
    have h2 := hM' q hq
    change p - 1 = q - 1 at he
    omega
  have himage : P.image (fun p => p-1) ⊆ Icc 2 M := by
    intro j hj
    obtain ⟨p, hp, rfl⟩ := mem_image.mp hj
    have h1 := hM' p hp
    have h2 := hle p (mem_filter.mp hp).1
    exact mem_Icc.mpr ⟨by omega, by omega⟩
  have hsum : (∑ p ∈ s, correctionLoss n p) ≤ 3/4 := by
    calc
      _ = ∑ p ∈ P, (((p : ℝ)-1)^2)⁻¹ := by
        rw [sum_filter]
        apply sum_congr rfl
        intro p hp
        by_cases hpN : p ∣ n <;> simp [correctionLoss,hpN]
      _ = ∑ p ∈ P, ((((p-1 : ℕ) : ℝ)^2))⁻¹ := by
        apply sum_congr rfl
        intro p hp
        rw [Nat.cast_sub (by have := hM' p hp; omega)]
        norm_cast
      _ = ∑ j ∈ P.image (fun p : ℕ => p-1), ((j : ℝ)^2)⁻¹ := by rw [sum_image hinj]
      _ ≤ ∑ j ∈ Icc 2 M, ((j : ℝ)^2)⁻¹ :=
        sum_le_sum_of_subset_of_nonneg himage (fun _ _ _ => by positivity)
      _ ≤ _ := inverse_squares_ge_two_le M
  let A : ArithmeticFunction ℝ := BandTail.z n * (ζ : ArithmeticFunction ℝ)
  have hA : IsMultiplicative A := (BandTail.z_mult n).mul isMultiplicative_zeta.natCast
  have he (m : ℕ) : A m = ∑ d ∈ m.divisors,BandTail.z n d := coe_mul_zeta_apply
  have hprod := hA.multiplicative_factorization A hM.ne'
  rw [he] at hprod
  rw [hprod,Finsupp.prod]
  change _ ≤ ∏ p ∈ s, A (p^M.factorization p)
  calc
    _ ≤ 1 - ∑ p ∈ s, correctionLoss n p := by linarith
    _ ≤ ∏ p ∈ s, (1 - correctionLoss n p) :=
      product_one_sub_ge s _ (fun p hp => correctionLoss_bounds hn (hprime p hp))
    _ ≤ _ := by
      apply prod_le_prod₀
      · exact fun p hp => sub_nonneg.mpr (correctionLoss_bounds hn (hprime p hp)).2
      · intro p hp
        rw [he]
        exact local_correction_floor n p _ (hprime p hp)

theorem correction_prefix_eighth :
    ∀ᶠ J : ℕ in atTop, 0 < J ∧ ∀ n : ℕ, Even n →
      (1/8 : ℝ) ≤ ∑ d ∈ Icc 1 J, BandTail.z n d := by
  have ht := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1/4)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  filter_upwards [eventually_ge_atTop (1 : ℕ), ht.eventually_ge_atTop (8 * BandTail.universal)]
    with J hJ hlarge
  refine ⟨hJ, ?_⟩
  intro n hn
  have hJ' : 0 < J := hJ
  have hu := BandTail.uniformTail n J (J.factorial.divisors \ Icc 1 J) hJ' (by
    intro d hd
    obtain ⟨hd, hd'⟩ := mem_sdiff.mp hd
    have hpos := Nat.pos_of_mem_divisors hd
    simp only [mem_Icc, not_and] at hd'
    omega)
  have hh := signed_divisors_quarter n J.factorial hn J.factorial_pos
  rw [← sum_sdiff (s₁ := Icc 1 J) (s₂ := J.factorial.divisors) (BandTail.prefixDiv J)] at hh
  have ht := sum_le_sum (s := J.factorial.divisors \ Icc 1 J) (fun d _ => le_abs_self (BandTail.z n d))
  have hsmall : BandTail.universal / (J : ℝ)^(1/4 : ℝ) ≤ 1/8 := by
    apply (div_le_iff₀ (by positivity)).mpr
    change 8 * BandTail.universal ≤ (J : ℝ)^(1/4 : ℝ) at hlarge
    linarith
  linarith

end GoldbachGRHSignedModel

namespace GoldbachGRHSignedModel

open Finset Filter ArithmeticFunction
open scoped Topology

noncomputable def harmonicG (n X : ℕ) : ℝ :=
  ∑ k ∈ Icc 1 X, BandTail.g n k / (k : ℝ)

noncomputable def harmonicF (n X : ℕ) : ℝ :=
  ∑ q ∈ Icc 1 X, BandTail.F n q / (q : ℝ)

theorem g_unit_interval (n k : ℕ) : 0 ≤ BandTail.g n k ∧ BandTail.g n k ≤ 1 := by
  simp [BandTail.g]
  split_ifs <;> norm_num

private theorem harmonicG_sub (n : ℕ) {A B : ℕ} (hAB : A ≤ B) :
    harmonicG n B - harmonicG n A =
      ∑ k ∈ Ioc A B, BandTail.g n k / (k : ℝ) := by
  have h := BandTail.prefix_split (fun k => BandTail.g n k / (k : ℝ)) hAB
  unfold harmonicG
  linarith

theorem harmonicG_mono (n : ℕ) : Monotone (harmonicG n) := by
  intro A B hAB
  have h := harmonicG_sub n hAB
  have hn : 0 ≤ ∑ k ∈ Ioc A B, BandTail.g n k / (k : ℝ) :=
    sum_nonneg fun k _ => div_nonneg (g_unit_interval n k).1 (Nat.cast_nonneg _)
  linarith

theorem g_boundary_le_mean (n X d : ℕ) (hX : 0 < X) (hd : 0 < d) :
    harmonicG n X - harmonicG n (X/d) ≤ (d : ℝ) * BandTail.gAvg n X := by
  have hXR : (0 : ℝ) < X := by exact_mod_cast hX
  have hsub : Ioc (X/d) X ⊆ Icc 1 X := by
    intro k hk
    exact mem_Icc.mpr ⟨Nat.succ_le_of_lt ((Nat.zero_le (X/d)).trans_lt (mem_Ioc.mp hk).1), (mem_Ioc.mp hk).2⟩
  rw [harmonicG_sub n (Nat.div_le_self X d)]
  calc
    _ ≤ ∑ k ∈ Ioc (X/d) X, BandTail.g n k * ((d : ℝ)/X) := by
      apply sum_le_sum
      intro k hk
      have hkR : (0 : ℝ) < k := by exact_mod_cast Nat.zero_lt_of_lt (mem_Ioc.mp hk).1
      have hxk := (Nat.div_lt_iff_lt_mul hd).mp (mem_Ioc.mp hk).1
      have hxkR : (X : ℝ) ≤ k * d := by exact_mod_cast hxk.le
      have hcoeff : (1 : ℝ)/(k : ℝ) ≤ (d : ℝ)/X :=
        (div_le_div_iff₀ hkR hXR).mpr (by nlinarith)
      simpa only [div_eq_mul_inv, one_mul] using
        mul_le_mul_of_nonneg_left hcoeff (g_unit_interval n k).1
    _ ≤ ∑ k ∈ Icc 1 X, BandTail.g n k * ((d : ℝ)/X) :=
      sum_le_sum_of_subset_of_nonneg hsub (fun k _ _ => mul_nonneg (g_unit_interval n k).1 (by positivity))
    _ = _ := by
      rw [← sum_mul]
      unfold BandTail.gAvg BandTail.gSum
      ring

theorem g_boundary_le_log (n X d : ℕ) (hd : 0 < d) :
    harmonicG n X - harmonicG n (X/d) ≤ 1 + Real.log d := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hlogd : 0 ≤ Real.log (d : ℝ) := Real.log_nonneg (by exact_mod_cast hd)
  by_cases hX : X = 0
  · simp [hX, harmonicG]
    positivity
  have hXR : (0 : ℝ) < X := by exact_mod_cast Nat.pos_of_ne_zero hX
  have hfloor := Nat.div_le_self X d
  have hQ : (0 : ℝ) < ((X / d : ℕ) : ℝ) + 1 := by positivity
  have hdiv : (X : ℝ) / (((X / d : ℕ) : ℝ) + 1) ≤ d := by
    apply (div_le_iff₀ hQ).mpr
    exact_mod_cast (Nat.lt_mul_div_succ X hd).le
  have hlogs : Real.log (X : ℝ) - Real.log (((X / d : ℕ) : ℝ) + 1) ≤ Real.log d := by
    rw [← Real.log_div hXR.ne' hQ.ne']
    exact Real.log_le_log (div_pos hXR hQ) hdiv
  have hH := harmonic_le_one_add_log X
  have hL := log_add_one_le_harmonic (X/d)
  have hsum : (∑ k ∈ Ioc (X/d) X, (k : ℝ)⁻¹) =
      (harmonic X:ℝ) - (harmonic (X/d):ℝ) := by
    simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
    have hp := BandTail.prefix_split (fun k : ℕ => (k : ℝ)⁻¹) hfloor
    linarith
  rw [harmonicG_sub n hfloor]
  calc
    _ ≤ ∑ k ∈ Ioc (X/d) X, (k : ℝ)⁻¹ := by
      apply sum_le_sum
      intro k _
      rw [div_eq_mul_inv]
      exact mul_le_of_le_one_left (inv_nonneg.mpr (Nat.cast_nonneg k)) (g_unit_interval n k).2
    _ = _ := hsum
    _ ≤ _ := by
      rw [Nat.cast_add, Nat.cast_one] at hL
      linarith

theorem harmonic_doubling_lower (n A : ℕ) (hA : 0 < A) (t η : ℝ)
    (hlo : |BandTail.gAvg n A - t| ≤ η)
    (hhi : |BandTail.gAvg n (2*A) - t| ≤ η) :
    t/2 - (3/2)*η ≤ harmonicG n (2*A) - harmonicG n A := by
  have hAB : A ≤ 2*A := by omega
  have hAR : (0 : ℝ) < A := by exact_mod_cast hA
  have hBA := BandTail.prefix_split (BandTail.g n) hAB
  change BandTail.gSum n (2*A) = BandTail.gSum n A + _ at hBA
  have hweak : BandTail.gAvg n (2*A) - BandTail.gAvg n A / 2 ≤
      harmonicG n (2*A) - harmonicG n A := by
    rw [harmonicG_sub n hAB]
    calc
      _ = (∑ j ∈ Ioc A (2*A), BandTail.g n j) / ((2*A : ℕ) : ℝ) := by
        unfold BandTail.gAvg
        rw [← sub_eq_of_eq_add hBA]
        push_cast
        field_simp; ring
      _ ≤ _ := by
        rw [sum_div]
        apply sum_le_sum
        intro k hk
        apply div_le_div_of_nonneg_left (g_unit_interval n k).1
        · exact_mod_cast hA.trans (mem_Ioc.mp hk).1
        · exact_mod_cast (mem_Ioc.mp hk).2
  linarith [(abs_le.mp hlo).2, (abs_le.mp hhi).1]

theorem harmonic_dyadic_lower (n : ℕ) (t η : ℝ) :
    ∀ (L A : ℕ), 0 < A →
      (∀ j ≤ L, |BandTail.gAvg n (2^j*A) - t| ≤ η) →
      (L : ℝ) * (t/2 - (3/2)*η) ≤ harmonicG n (2^L*A) - harmonicG n A := by
  intro L
  induction L with
  | zero => simp
  | succ L ih =>
    intro A hA hnear
    have hm := ih A hA (fun j hj => hnear j (by omega))
    have ht : 0 < 2^L*A := Nat.mul_pos (pow_pos (by decide) _) hA
    have hh := harmonic_doubling_lower n (2^L*A) ht t η (hnear L (by omega)) (by
      simpa only [pow_succ', mul_assoc] using hnear (L+1) le_rfl)
    push_cast
    rw [pow_succ', mul_assoc]
    linarith

end GoldbachGRHSignedModel

namespace GoldbachGRHSignedModel

open Finset Filter ArithmeticFunction
open scoped Topology

private theorem sum_divisors_reindex (X : ℕ) (f : ℕ × ℕ → ℝ) :
    (∑ q ∈ Icc 1 X, ∑ v ∈ q.divisorsAntidiagonal, f v) =
      ∑ d ∈ Icc 1 X, ∑ k ∈ Icc 1 (X/d), f (d,k) := by
  classical
  let S := Icc 1 X
  have hf (q : ℕ) (hq : q ∈ S) :
      q.divisorsAntidiagonal = (S ×ˢ S).filter (fun ab : ℕ × ℕ => ab.1*ab.2=q) := by
    obtain ⟨hq0,hqQ⟩ := mem_Icc.mp hq
    ext ab
    constructor
    · intro hab
      have hm (a : ℕ) (ha : a ∈ q.divisors) : a ∈ S :=
        mem_Icc.mpr ⟨Nat.pos_of_mem_divisors ha,(Nat.le_of_dvd hq0 (Nat.dvd_of_mem_divisors ha)).trans hqQ⟩
      exact mem_filter.mpr ⟨mem_product.mpr ⟨hm _ (Nat.fst_mem_divisors_of_mem_antidiagonal hab),
        hm _ (Nat.snd_mem_divisors_of_mem_antidiagonal hab)⟩,(Nat.mem_divisorsAntidiagonal.mp hab).1⟩
    · intro hh; exact Nat.mem_divisorsAntidiagonal.mpr ⟨(mem_filter.mp hh).2,by omega⟩
  calc
    _ = ∑ q ∈ S, ∑ v ∈ (S ×ˢ S).filter (fun ab : ℕ × ℕ => ab.1*ab.2=q), f v :=
      sum_congr rfl (fun q hq => by rw [hf q hq])
    _ = ∑ v ∈ (S ×ˢ S).filter (fun ab : ℕ × ℕ => ab.1*ab.2 ∈ S), f v :=
      sum_fiberwise_eq_sum_filter _ _ _ _
    _ = _ := by
      rw [sum_filter,sum_product]
      apply sum_congr rfl
      intro d hd
      have hd0 := (mem_Icc.mp hd).1
      have hkd : (S.filter fun k => d*k∈S)=Icc 1 (X/d) := by
        ext k
        simp only [S,mem_filter,mem_Icc]
        constructor
        · rintro ⟨⟨hk,_⟩,_,hdk⟩
          exact ⟨hk,(Nat.le_div_iff_mul_le hd0).mpr (by simpa [mul_comm] using hdk)⟩
        · rintro ⟨hk,hkx⟩
          exact ⟨⟨hk,hkx.trans (Nat.div_le_self _ _)⟩,Nat.mul_pos hd0 hk,by simpa [mul_comm] using (Nat.le_div_iff_mul_le hd0).mp hkx⟩
      rw [←sum_filter,hkd]

theorem harmonicF_convolution (n X : ℕ) :
    harmonicF n X = ∑ d ∈ Icc 1 X, BandTail.z n d * harmonicG n (X/d) := by
  let f := fun v : ℕ × ℕ => BandTail.z n v.1 * (BandTail.g n v.2 / (v.2 : ℝ))
  calc
    _ = ∑ q ∈ Icc 1 X, ∑ v ∈ q.divisorsAntidiagonal, f v := by
      apply sum_congr rfl
      intro q _
      rw [BandTail.convolution n,mul_comm (BandTail.g n) (BandTail.h n),ArithmeticFunction.mul_apply,sum_div]
      apply sum_congr rfl
      intro v hv
      change BandTail.h n v.1*BandTail.g n v.2/(q:ℝ) =
        (BandTail.h n v.1/(v.1:ℝ))*(BandTail.g n v.2/(v.2:ℝ))
      rw [←(Nat.mem_divisorsAntidiagonal.mp hv).1, Nat.cast_mul,div_eq_mul_inv,mul_inv]
      simp only [div_eq_mul_inv]
      ring
    _ = ∑ d ∈ Icc 1 X, ∑ k ∈ Icc 1 (X/d), f (d,k) := sum_divisors_reindex X f
    _ = _ := by simp [f,harmonicG,mul_sum]

theorem absolute_prefix_le (n X : ℕ) :
    (∑ q ∈ Icc 1 X, |BandTail.F n q|) ≤ BandTail.universal * (X:ℝ) := by
  classical
  let f : ℕ × ℕ → ℝ := fun v => |BandTail.h n v.1|
  calc
    _ ≤ ∑ q ∈ Icc 1 X, ∑ v ∈ q.divisorsAntidiagonal, f v := by
      apply sum_le_sum
      intro q _
      rw [BandTail.convolution n,mul_comm (BandTail.g n) (BandTail.h n),ArithmeticFunction.mul_apply]
      refine (abs_sum_le_sum_abs _ _).trans ?_
      apply sum_le_sum
      intro v _
      rw [abs_mul,abs_of_nonneg (g_unit_interval n v.2).1]
      exact mul_le_of_le_one_right (abs_nonneg _) (g_unit_interval n v.2).2
    _ = ∑ d ∈ Icc 1 X, ∑ k ∈ Icc 1 (X/d), f (d,k) := sum_divisors_reindex X f
    _ ≤ ∑ d ∈ Icc 1 X, |BandTail.z n d| * (X:ℝ) := by
      apply sum_le_sum
      intro d hd
      have hd0 := (mem_Icc.mp hd).1
      have hdR : (0:ℝ)<d := by exact_mod_cast hd0
      have hdiv : ((X/d:ℕ):ℝ) ≤ (X:ℝ)/(d:ℝ) := by
        apply (le_div_iff₀ hdR).2
        exact_mod_cast Nat.div_mul_le_self X d
      calc
        _ = ((X/d:ℕ):ℝ)*|BandTail.h n d| := by
          simp [f,Nat.card_Icc,nsmul_eq_mul]
        _ ≤ ((X:ℝ)/(d:ℝ))*|BandTail.h n d| := mul_le_mul_of_nonneg_right hdiv (abs_nonneg _)
        _ = _ := by
          rw [BandTail.z,ArithmeticFunction.coe_mk,abs_div,abs_of_pos hdR]
          ring
    _ = (∑ d ∈ Icc 1 X, |BandTail.z n d|) * (X:ℝ) := (sum_mul ..).symm
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      simpa using BandTail.uniformTail n 1 (Icc 1 X) (by decide) (fun d hd => (mem_Icc.mp hd).1)

theorem harmonic_convolution_interval (n K X : ℕ) (hKX : K ≤ X) :
    (∑ q ∈ Ioc K X, BandTail.F n q / (q:ℝ)) =
      ∑ d ∈ Icc 1 X, BandTail.z n d * (harmonicG n (X/d)-harmonicG n (K/d)) := by
  have hsub := BandTail.prefix_split (fun q => BandTail.F n q / (q:ℝ)) hKX
  have hsub' : (∑ q ∈ Ioc K X, BandTail.F n q / (q:ℝ)) = harmonicF n X-harmonicF n K := by
    unfold harmonicF
    linarith
  have hK :
      ∑ d ∈ Icc 1 K, BandTail.z n d * harmonicG n (K/d) =
        ∑ d ∈ Icc 1 X, BandTail.z n d * harmonicG n (K/d) := by
    apply sum_subset (Icc_subset_Icc_right hKX)
    intro d hd hnot
    have hdK : K<d := by
      simp only [mem_Icc,not_and] at hnot
      have hd' := mem_Icc.mp hd
      omega
    simp [Nat.div_eq_of_lt hdK,harmonicG]
  rw [hsub',harmonicF_convolution n X,harmonicF_convolution n K,hK,←sum_sub_distrib]
  apply sum_congr rfl
  intro d _
  ring

theorem uniform_log_tail (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ J : ℕ in atTop, 0 < J ∧ ∀ n : ℕ, ∀ s : Finset ℕ, (∀ d ∈ s, J ≤ d) →
      (∑ d ∈ s, |BandTail.z n d| *(1+Real.log d)) ≤ ε := by
  have hC : 0 < BandTail.universal := Real.exp_pos _
  let τ := ε/(2*BandTail.universal)
  have hτ : 0<τ := by dsimp [τ]; positivity
  have hc := tendsto_natCast_atTop_atTop (R:=ℝ)
  have hm := ((isLittleO_log_rpow_rpow_atTop (1:ℝ) (by norm_num : (0:ℝ)<1/4)).comp_tendsto hc).bound hτ
  have hlog := (Real.tendsto_log_atTop.comp hc).eventually_ge_atTop (1:ℝ)
  obtain ⟨N,hN⟩ := eventually_atTop.mp (hm.and hlog)
  filter_upwards [eventually_ge_atTop (max N 1)] with J hJ
  have hJ' : 0<J := lt_of_lt_of_le (by decide : 0<1) ((le_max_right N 1).trans hJ)
  refine ⟨hJ',?_⟩
  intro n s hs
  have hbound (d : ℕ) (hd : d ∈ s) : |BandTail.z n d| *(1+Real.log d) ≤
      (ε/BandTail.universal)*BandTail.w n d := by
    have hdJ := hs d hd
    have hd0 := hJ'.trans_le hdJ
    have hz : (0:ℝ)<(d:ℝ)^(1/4:ℝ) := Real.rpow_pos_of_pos (by exact_mod_cast hd0) _
    obtain ⟨ha,hb⟩ := hN d ((le_max_left N 1).trans (hJ.trans hdJ))
    change ‖(Real.log (d:ℝ))^(1:ℝ)‖ ≤ τ*‖(d:ℝ)^(1/4:ℝ)‖ at ha
    change 1 ≤ Real.log (d:ℝ) at hb
    rw [Real.rpow_one,Real.norm_eq_abs,abs_of_nonneg (by linarith : 0≤Real.log (d:ℝ)),
      Real.norm_eq_abs,abs_of_pos hz] at ha
    have hh : 1+Real.log (d:ℝ) ≤ (ε/BandTail.universal)*(d:ℝ)^(1/4:ℝ) := by
      have hτ' : 2*τ=ε/BandTail.universal := by dsimp [τ]; ring
      rw [←hτ',mul_assoc]
      linarith
    calc
      _ ≤ (BandTail.w n d/(d:ℝ)^(1/4:ℝ))*(1+Real.log d) :=
        mul_le_mul_of_nonneg_right (BandTail.tailTerm n d d hd0 le_rfl) (by linarith)
      _ ≤ (BandTail.w n d/(d:ℝ)^(1/4:ℝ))*((ε/BandTail.universal)*(d:ℝ)^(1/4:ℝ)) :=
        mul_le_mul_of_nonneg_left hh (div_nonneg (BandTail.w_nonneg n d) hz.le)
      _ = _ := by field_simp
  have hu : ∑ d ∈ s, BandTail.w n d ≤ BandTail.universal := by
    apply le_trans _ (BandTail.uniformPrefix n (s.sup id))
    apply sum_le_sum_of_subset_of_nonneg
    · intro d hd
      exact mem_Icc.mpr ⟨hJ'.trans_le (hs d hd),le_sup (f:=id) hd⟩
    · intro d _ _
      exact BandTail.w_nonneg n d
  calc
    _ ≤ ∑ d ∈ s, (ε/BandTail.universal)*BandTail.w n d := sum_le_sum hbound
    _ = (ε/BandTail.universal)*(∑ d ∈ s,BandTail.w n d) := (mul_sum ..).symm
    _ ≤ (ε/BandTail.universal)*BandTail.universal := mul_le_mul_of_nonneg_left hu (by positivity)
    _ = _ := by field_simp

end GoldbachGRHSignedModel

namespace GoldbachGRHSignedModel

open Finset Filter
open scoped Topology

private theorem harmonic_diff_boundary (n K X d : ℕ) :
    harmonicG n (X/d) - harmonicG n (K/d) -
      (harmonicG n X - harmonicG n K) =
      (harmonicG n K - harmonicG n (K/d)) -
      (harmonicG n X - harmonicG n (X/d)) := by ring

private theorem harmonic_diff_abs (n K X d : ℕ) :
    |harmonicG n (X/d) - harmonicG n (K/d) -
      (harmonicG n X - harmonicG n K)| ≤
      (harmonicG n K - harmonicG n (K/d)) +
      (harmonicG n X - harmonicG n (X/d)) := by
  rw [harmonic_diff_boundary]
  have hK := sub_nonneg.mpr (harmonicG_mono n (Nat.div_le_self K d))
  have hX := sub_nonneg.mpr (harmonicG_mono n (Nat.div_le_self X d))
  exact abs_le.mpr ⟨by linarith, by linarith⟩

private theorem gAvg_nonneg (n X : ℕ) : 0 ≤ BandTail.gAvg n X := by
  unfold BandTail.gAvg BandTail.gSum
  exact div_nonneg (sum_nonneg fun k _ => (g_unit_interval n k).1) (by positivity)

theorem harmonic_convolution_lower (n K X J : ℕ) (hK : 0 < K) (hKX : K ≤ X)
    (hJX : J ≤ X) (e : ℝ)
    (hZ : (1/8 : ℝ) ≤ ∑ d ∈ Icc 1 X, BandTail.z n d)
    (hlog : (∑ d ∈ Ioc J X, |BandTail.z n d| * (1 + Real.log d)) ≤ e) :
    (1/8 : ℝ) * (harmonicG n X - harmonicG n K) -
      (J : ℝ) * BandTail.universal * (BandTail.gAvg n K + BandTail.gAvg n X) - 2*e ≤
      ∑ q ∈ Ioc K X, BandTail.F n q / (q:ℝ) := by
  let A := harmonicG n X - harmonicG n K
  let D (d : ℕ) := harmonicG n (X/d) - harmonicG n (K/d) - A
  let t := BandTail.gAvg n K + BandTail.gAvg n X
  have ht := add_nonneg (gAvg_nonneg n K) (gAvg_nonneg n X)
  have hpos := sub_nonneg.mpr (harmonicG_mono n hKX)
  have hlow (d : ℕ) : -(abs (BandTail.z n d) * abs (D d)) ≤ BandTail.z n d * D d := by
    rw [← abs_mul]
    exact neg_abs_le _
  have hsmall : -((J : ℝ) * BandTail.universal * t) ≤ ∑ d ∈ Icc 1 J, BandTail.z n d * D d := by
    have habs (d : ℕ) (hd : d ∈ Icc 1 J) : |D d| ≤ (J : ℝ) * t := by
      have hd0 := (mem_Icc.mp hd).1
      calc
        _ ≤ _ := harmonic_diff_abs n K X d
        _ ≤ (d : ℝ) * t := by
          dsimp [t]
          rw [mul_add]
          exact add_le_add (g_boundary_le_mean n K d hK hd0)
            (g_boundary_le_mean n X d (hK.trans_le hKX) hd0)
        _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast (mem_Icc.mp hd).2) ht
    have hU : (∑ d ∈ Icc 1 J, |BandTail.z n d|) ≤ BandTail.universal := by
      simpa using BandTail.uniformTail n 1 (Icc 1 J) (by decide) (fun d hd => (mem_Icc.mp hd).1)
    calc
      _ = -(BandTail.universal * ((J : ℝ) * t)) := by ring
      _ ≤ -((∑ d ∈ Icc 1 J, |BandTail.z n d|) * ((J : ℝ) * t)) :=
        neg_le_neg (mul_le_mul_of_nonneg_right hU (mul_nonneg (Nat.cast_nonneg J) ht))
      _ = ∑ d ∈ Icc 1 J, -(|BandTail.z n d| * ((J : ℝ) * t)) := by rw [sum_neg_distrib, sum_mul]
      _ ≤ _ := sum_le_sum fun d hd =>
        (neg_le_neg (mul_le_mul_of_nonneg_left (habs d hd) (abs_nonneg _))).trans (hlow d)
  have hlarge : -(2*e) ≤ ∑ d ∈ Ioc J X, BandTail.z n d * D d := by
    have habs (d : ℕ) (hd : d ∈ Ioc J X) : |D d| ≤ 2 * (1 + Real.log d) := by
      have hd0 := (Nat.zero_le J).trans_lt (mem_Ioc.mp hd).1
      calc
        _ ≤ _ := harmonic_diff_abs n K X d
        _ ≤ (1 + Real.log d) + (1 + Real.log d) := by
          exact add_le_add (g_boundary_le_log n K d hd0) (g_boundary_le_log n X d hd0)
        _ = _ := by ring
    calc
      _ ≤ -(2*(∑ d ∈ Ioc J X, |BandTail.z n d| * (1 + Real.log d))) :=
        neg_le_neg (mul_le_mul_of_nonneg_left hlog (by norm_num))
      _ = ∑ d ∈ Ioc J X, -(|BandTail.z n d| * (2 * (1 + Real.log d))) := by
        rw [sum_neg_distrib, mul_sum]
        congr 1
        apply sum_congr rfl
        intro d _
        ring
      _ ≤ _ := sum_le_sum fun d hd =>
        (neg_le_neg (mul_le_mul_of_nonneg_left (habs d hd) (abs_nonneg _))).trans (hlow d)
  have hsplit := BandTail.prefix_split (fun d => BandTail.z n d * D d) hJX
  rw [harmonic_convolution_interval n K X hKX]
  have hrewrite : (∑ d ∈ Icc 1 X, BandTail.z n d *
      (harmonicG n (X/d) - harmonicG n (K/d))) =
      (∑ d ∈ Icc 1 X, BandTail.z n d) * A + ∑ d ∈ Icc 1 X, BandTail.z n d * D d := by
    rw [sum_mul, ←sum_add_distrib]
    apply sum_congr rfl
    intro d _
    dsimp [D]
    ring
  rw [hrewrite, hsplit]
  change (1/8 : ℝ) * A - (J : ℝ)*BandTail.universal*t - 2*e ≤ _
  linarith [mul_le_mul_of_nonneg_right hZ hpos]

end GoldbachGRHSignedModel

namespace GoldbachGRHSignedModel

open Finset Filter
open scoped Topology

theorem harmonic_suffix_floor (ε : ℝ) (hε : 0 < ε) :
    ∃ K₀ : ℕ, ∀ K ≥ K₀, ∀ n X : ℕ, Even n → K ≤ X →
      -ε ≤ ∑ q ∈ Ioc K X, BandTail.F n q / (q:ℝ) := by
  obtain ⟨J,hJ⟩ := eventually_atTop.mp
    (correction_prefix_eighth.and (uniform_log_tail (ε/4) (by positivity)))
  obtain ⟨hJ₀,_⟩ := (hJ J le_rfl).1
  obtain ⟨m,hm⟩ := exists_nat_ge (16 * ((J:ℝ) * BandTail.universal))
  let L := m+1
  let T : ℕ := 2^L
  have hT : 0 < T := pow_pos (by decide) _
  have hC : (1:ℝ) ≤ 2*(T:ℝ) := by
    have ht' : (1:ℝ) ≤ T := by exact_mod_cast hT
    linarith
  have hL : (0:ℝ) < L := by exact_mod_cast (Nat.zero_lt_succ m)
  have hLJ : (J:ℝ)*BandTail.universal ≤ (L:ℝ)/16 := by
    change (J:ℝ)*BandTail.universal ≤ ((m+1:ℕ):ℝ)/16
    push_cast
    linarith
  let η := ε/(L:ℝ)
  have hη : 0 < η := div_pos hε hL
  have hLη : (L:ℝ)*η=ε := by dsimp [η]; field_simp
  obtain ⟨M,hM⟩ := eventually_atTop.mp (BandTail.mean_slow (2*(T:ℝ)) η hC hη)
  have hR : 1 ≤ T*T := Nat.mul_pos hT hT
  obtain ⟨N,hN⟩ := BandTail.uniform_prefix_floor (T*T) hR ε hε
  refine ⟨max J (max M N),?_⟩
  intro K hK₀ n X hn hKX
  have hJK : J ≤ K := (le_max_left J (max M N)).trans hK₀
  have hMK : M ≤ K := ((le_max_left M N).trans (le_max_right J (max M N))).trans hK₀
  have hNK : N ≤ K := ((le_max_right M N).trans (le_max_right J (max M N))).trans hK₀
  have hK : 0 < K := hJ₀.trans_le hJK
  have hKR : (0:ℝ)<K := by exact_mod_cast hK
  by_cases hnear : X ≤ (T*T)*K
  · have hh := BandTail.weighted_prefix_lower K X (BandTail.F n)
      (fun q => (q:ℝ)⁻¹) (ε*(K:ℝ)) hKX (by positivity)
      (fun i _ => by positivity)
      (fun i hi => by
        apply inv_anti₀
        · exact_mod_cast hK.trans_le hi
        · exact_mod_cast Nat.le_succ i)
      (fun i hi hiX => hN K hNK n i hi (hiX.trans hnear))
    have hEq : -(ε*(K:ℝ)*(K:ℝ)⁻¹) = -ε := by field_simp
    rw [hEq] at hh
    simpa [div_eq_mul_inv] using hh
  · let B := X/T
    have hfar : (T*T)*K ≤ X := le_of_lt (lt_of_not_ge hnear)
    have hKB : T*K ≤ B := by
      apply (Nat.le_div_iff_mul_le hT).2
      calc
        T*K*T = (T*T)*K := by ring
        _ ≤ X := hfar
    have hB : 0<B := (Nat.mul_pos hT hK).trans_le hKB
    have hBX : T*B ≤ X := Nat.mul_div_le X T
    have hXT : X ≤ 2*T*B := by
      have hmod := Nat.mod_lt X hT
      have hdiv : X % T + T * B = X := Nat.mod_add_div X T
      have hTB : T ≤ T*B := by
        simpa using Nat.mul_le_mul_left T (show 1≤B from hB)
      have he : 2*T*B=T*B+T*B := by ring
      rw [he]
      omega
    have hdT (j : ℕ) (hj : j≤L) : (2:ℕ)^j≤T := Nat.pow_le_pow_right (by decide) hj
    have hd1 (j : ℕ) : 1≤(2:ℕ)^j := pow_pos (by decide : 0<(2:ℕ)) j
    have hKm (j : ℕ) : K ≤ 2^j*K := by simpa using Nat.mul_le_mul_right K (hd1 j)
    have hBm (j : ℕ) : B ≤ 2^j*B := by simpa using Nat.mul_le_mul_right B (hd1 j)
    have hslowK (j : ℕ) (hj : j≤L) : |BandTail.gAvg n (2^j*K)-BandTail.gAvg n K| ≤ η := by
      apply hM (2^j*K) (hMK.trans (hKm j)) K hK (hKm j) _ n
      have hx : (2:ℕ)^j*K≤T*K := Nat.mul_le_mul_right K (hdT j hj)
      have hx' : (((2:ℕ)^j*K : ℕ):ℝ) ≤ (T:ℝ)*(K:ℝ) := by exact_mod_cast hx
      nlinarith [show (0:ℝ)≤(T:ℝ)*(K:ℝ) by positivity]
    have hslowX (j : ℕ) (hj : j≤L) : |BandTail.gAvg n (2^j*B)-BandTail.gAvg n X| ≤ η := by
      rw [abs_sub_comm]
      apply hM X (hMK.trans hKX) (2^j*B) (hB.trans_le (hBm j))
        ((Nat.mul_le_mul_right B (hdT j hj)).trans hBX) _ n
      have hXj : X ≤ 2*T*(2^j*B) := hXT.trans (Nat.mul_le_mul_left (2*T) (hBm j))
      exact_mod_cast hXj
    have hnearK := harmonic_dyadic_lower n (BandTail.gAvg n K) η L K hK hslowK
    have hnearX := harmonic_dyadic_lower n (BandTail.gAvg n X) η L B hB hslowX
    have hmid := harmonicG_mono n hKB
    have hlast := harmonicG_mono n hBX
    change (L:ℝ)*(BandTail.gAvg n K/2 - (3/2)*η) ≤ harmonicG n (T*K)-harmonicG n K at hnearK
    change (L:ℝ)*(BandTail.gAvg n X/2 - (3/2)*η) ≤ harmonicG n (T*B)-harmonicG n B at hnearX
    have hlong : ((L:ℝ)/2)*(BandTail.gAvg n K+BandTail.gAvg n X)-3*ε ≤
      harmonicG n X-harmonicG n K := by linarith
    have hJX := hJK.trans hKX
    have hZ := (hJ X hJX).1.2 n hn
    have hlog := (hJ J le_rfl).2.2 n (Ioc J X) (fun d hd => (mem_Ioc.mp hd).1.le)
    have hlower := harmonic_convolution_lower n K X J hK hKX hJX (ε/4) hZ hlog
    have hdom := mul_le_mul_of_nonneg_right hLJ
      (add_nonneg (gAvg_nonneg n K) (gAvg_nonneg n X))
    linarith

end GoldbachGRHSignedModel

namespace GoldbachGRHSignedModel

open Finset

theorem coefficient_re_eq (n q : ℕ) (hq : 0 < q) :
    (GoldbachExplicitModeledMajor.coefficient q n).re = BandTail.F n q / (q:ℝ) := by
  have hqR : (q:ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  simp [BandTail.F,hqR]

/-- A monotone weight that is at most q/Q near the origin preserves the asymptotic
lower floor of the full initial Ramanujan sum. -/
theorem harmonic_tapered_prefix_floor (ε : ℝ) (hε : 0 < ε) :
    ∃ Q₀ : ℕ, ∀ Q ≥ Q₀, ∀ n : ℕ, Even n → ∀ w : ℕ → ℝ, Monotone w →
      (∀ q, 0 ≤ w q) → w Q ≤ 2 →
      (∀ q ∈ Icc 1 Q, w q ≤ (q:ℝ)/(Q:ℝ)) →
      -ε ≤ ∑ q ∈ Icc 1 Q, (BandTail.F n q / (q:ℝ)) * w q := by
  have hδ : 0 < ε/4 := by positivity
  obtain ⟨K₀,hK₀⟩ := harmonic_suffix_floor (ε/4) hδ
  let K := max K₀ 1
  have hK₁ : 1 ≤ K := le_max_right _ _
  obtain ⟨M,hM⟩ := exists_nat_ge (2 * (BandTail.universal * (K:ℝ)) / ε)
  refine ⟨max K M, ?_⟩
  intro Q hQ n hn w hw hw₀ hwQ hweight
  have hKQ : K ≤ Q := (le_max_left _ _).trans hQ
  have hMQ : M ≤ Q := (le_max_right _ _).trans hQ
  have hQR : (0:ℝ) < Q := by exact_mod_cast hK₁.trans hKQ
  have hQM : 2 * (BandTail.universal * (K:ℝ)) / ε ≤ (Q:ℝ) :=
    hM.trans (by exact_mod_cast hMQ)
  have hcut : BandTail.universal * (K:ℝ) / (Q:ℝ) ≤ ε/2 := by
    have hs := (div_le_iff₀ hε).1 hQM
    apply (div_le_iff₀ hQR).2
    linarith
  have hterm (q : ℕ) (hq : q ∈ Icc 1 K) :
      -(|BandTail.F n q| / (Q:ℝ)) ≤ (BandTail.F n q / (q:ℝ)) * w q := by
    have hqR : (0:ℝ) < q := by exact_mod_cast (mem_Icc.mp hq).1
    have hh := hweight q ((Icc_subset_Icc_right hKQ) hq)
    calc
      _ = -((|BandTail.F n q| / (q:ℝ)) * ((q:ℝ)/(Q:ℝ))) := by field_simp
      _ ≤ -((|BandTail.F n q| / (q:ℝ)) * w q) :=
        neg_le_neg (mul_le_mul_of_nonneg_left hh (div_nonneg (abs_nonneg _) hqR.le))
      _ ≤ _ := by
        have he : |(BandTail.F n q / (q:ℝ)) * w q| =
            (|BandTail.F n q| / (q:ℝ)) * w q := by
          rw [abs_mul, abs_div, abs_of_pos hqR, abs_of_nonneg (hw₀ q)]
        rw [←he]
        exact neg_abs_le _
  have hsmall :
      -(ε/2) ≤ ∑ q ∈ Icc 1 K, (BandTail.F n q / (q:ℝ)) * w q := by
    calc
      _ ≤ -(BandTail.universal * (K:ℝ) / (Q:ℝ)) := neg_le_neg hcut
      _ ≤ -((∑ q ∈ Icc 1 K, |BandTail.F n q|) / (Q:ℝ)) :=
        neg_le_neg (div_le_div_of_nonneg_right (absolute_prefix_le n K) hQR.le)
      _ = ∑ q ∈ Icc 1 K, -(|BandTail.F n q| / (Q:ℝ)) := by
        rw [sum_neg_distrib, sum_div]
      _ ≤ _ := sum_le_sum hterm
  have hlen : K+(Q-K)=Q := Nat.add_sub_of_le hKQ
  have htail := weighted_suffix_lower (fun q => BandTail.F n q/(q:ℝ)) (ε/4) hδ.le
    (Q-K) K w hw (fun q _ => hw₀ q)
  rw [hlen] at htail
  have hrest := htail (fun k hk hkQ => hK₀ k ((le_max_left _ _).trans hk) n Q hn hkQ)
  have hrest' : -(ε/2) ≤ ∑ q ∈ Ioc K Q, (BandTail.F n q/(q:ℝ))*w q := by
    exact (by linarith [mul_le_mul_of_nonneg_left hwQ hδ.le] : -(ε/2) ≤ -(ε/4 * w Q)).trans hrest
  rw [BandTail.prefix_split (fun q => (BandTail.F n q/(q:ℝ))*w q) hKQ]
  linarith

end GoldbachGRHSignedModel

namespace GoldbachGRHSignedModel

open Finset

/-- Uniform lower floor for the two model sums after separating the common kernel
mass, the low-denominator taper, and a uniformly small truncation error. -/
theorem medium_model_floor (ε : ℝ) (hε : 0 < ε) :
    ∃ Q₀ : ℕ, ∀ Q ≥ Q₀, ∀ n U : ℕ, Even n → Q ≤ U →
      ∀ mass defect : ℝ, mass ∈ Set.Icc 0 2 → 0 ≤ defect →
      defect * (BandTail.universal * (U:ℝ)) ≤ ε/4 →
      ∀ wide taper : ℕ → ℝ, Monotone taper → (∀ q, 0 ≤ taper q) → taper Q ≤ 2 →
      (∀ q ∈ Icc 1 Q, taper q ≤ (q:ℝ)/(Q:ℝ)) →
      (∀ q ∈ Icc 1 U, |wide q-mass| ≤ defect*(q:ℝ)) →
      -ε ≤ (∑ q ∈ Ioc Q U, (GoldbachExplicitModeledMajor.coefficient q n).re * wide q) +
        ∑ q ∈ Icc 1 Q, (GoldbachExplicitModeledMajor.coefficient q n).re *
          (wide q-mass+taper q) := by
  have hδ : 0 < ε/4 := by positivity
  obtain ⟨Q₁,hQ₁⟩ := harmonic_suffix_floor (ε/4) hδ
  obtain ⟨Q₂,hQ₂⟩ := harmonic_tapered_prefix_floor (ε/4) hδ
  refine ⟨max Q₁ Q₂,?_⟩
  intro Q hQ n U hn hQU mass defect hmass hdefect hcost wide taper hmono hnonneg
    hcap hscale hwide
  let a (q : ℕ) := (GoldbachExplicitModeledMajor.coefficient q n).re
  have hite (q : ℕ) (hq : q ∈ Ioc Q U) : 0 < q := (Nat.zero_le Q).trans_lt (mem_Ioc.mp hq).1
  have hlarge : -(ε/4) ≤ ∑ q ∈ Ioc Q U, a q := by
    have hh := hQ₁ Q ((le_max_left _ _).trans hQ) n U hn hQU
    refine hh.trans (le_of_eq (sum_congr rfl ?_))
    intro q hq
    exact (coefficient_re_eq n q (hite q hq)).symm
  have hmain : -(ε/2) ≤ (∑ q ∈ Ioc Q U, a q)*mass := by
    exact (by linarith [mul_le_mul_of_nonneg_left hmass.2 hδ.le] :
      -(ε/2) ≤ -(ε/4)*mass).trans (mul_le_mul_of_nonneg_right hlarge hmass.1)
  have hsmall : -(ε/4) ≤ ∑ q ∈ Icc 1 Q, a q*taper q := by
    have hh := hQ₂ Q ((le_max_right _ _).trans hQ) n hn taper hmono hnonneg hcap hscale
    refine hh.trans (le_of_eq (sum_congr rfl ?_))
    intro q hq
    exact congrArg (fun x : ℝ => x*taper q) (coefficient_re_eq n q (mem_Icc.mp hq).1).symm
  have herror : -(ε/4) ≤ ∑ q ∈ Icc 1 U, a q*(wide q-mass) := by
    have hterm (q : ℕ) (hq : q ∈ Icc 1 U) :
        -(defect*|BandTail.F n q|) ≤ a q*(wide q-mass) := by
      have hq0 := (mem_Icc.mp hq).1
      have hqR : (0:ℝ)<q := by exact_mod_cast hq0
      have hAbs : |a q*(wide q-mass)| ≤ defect*|BandTail.F n q| := by
        dsimp [a]
        rw [abs_mul, coefficient_re_eq n q hq0, abs_div, abs_of_pos hqR]
        calc
          _ ≤ (|BandTail.F n q|/(q:ℝ))*(defect*(q:ℝ)) :=
            mul_le_mul_of_nonneg_left (hwide q hq) (div_nonneg (abs_nonneg _) hqR.le)
          _ = _ := by field_simp
      exact (neg_le_neg hAbs).trans (neg_abs_le _)
    calc
      _ ≤ -(defect*(BandTail.universal*(U:ℝ))) := neg_le_neg hcost
      _ ≤ -(defect*(∑ q ∈ Icc 1 U, |BandTail.F n q|)) :=
        neg_le_neg (mul_le_mul_of_nonneg_left (absolute_prefix_le n U) hdefect)
      _ = ∑ q ∈ Icc 1 U, -(defect*|BandTail.F n q|) := by rw [sum_neg_distrib,mul_sum]
      _ ≤ _ := sum_le_sum hterm
  change -ε ≤ (∑ q ∈ Ioc Q U, a q * wide q) +
    ∑ q ∈ Icc 1 Q, a q * (wide q-mass+taper q)
  have H :
      (∑ q ∈ Ioc Q U, a q * wide q) =
        (∑ q ∈ Ioc Q U, a q)*mass + ∑ q ∈ Ioc Q U, a q*(wide q-mass) := by
    rw [sum_mul,←sum_add_distrib]
    apply sum_congr rfl
    intro q _
    ring
  have E := BandTail.prefix_split (fun q => a q*(wide q-mass)) hQU
  rw [H]
  simp only [mul_add,sum_add_distrib]
  linarith

end GoldbachGRHSignedModel

end GoldbachGRHSignedModel

section GoldbachGRHConcreteFloor

open Filter Finset MeasureTheory
open scoped Topology Interval Classical

namespace GoldbachGRHConcreteFloor

open GoldbachGRHBudget (narrow cutoff width)
open GoldbachGRHArcs (radius centers cell)
open GoldbachGRHKernel (mass)
open GoldbachExplicitModeledMajor (coefficient)

private theorem eventually_narrow_ge (m : ℕ) : ∀ᶠ n : ℕ in atTop, m ≤ narrow n := by
  filter_upwards [eventually_ge_atTop (2^m : ℕ)] with n hn
  have h := Nat.le_log_of_pow_le (by decide : 1 < 2) (hn.trans (by omega : n≤n+2))
  have h₁ : 1 ≤ Nat.log 2 (n+2) := Nat.log_pos (by decide) (by omega)
  have h₂ := Nat.mul_le_mul_left (Nat.log 2 (n+2)) h₁
  exact h.trans (by simpa [narrow,pow_two] using h₂)

noncomputable def normalized (n T q : ℕ) : ℝ :=
  mass n (radius n T (max 1 q)) / (n:ℝ)

private theorem normalized_loss (n T q : ℕ) (hn : 0 < n) (hT : 0 < T) (hbudget : 24*T≤n) :
    0 ≤ ((n:ℝ)+1)/(n:ℝ)-normalized n T q ∧
     ((n:ℝ)+1)/(n:ℝ)-normalized n T q ≤ (max 1 q:ℕ)/(2*(T:ℝ)) := by
  let r := radius n T (max 1 q)
  have hnR : 0 < (n:ℝ) := by exact_mod_cast hn
  have hTR : 0 < (T:ℝ) := by exact_mod_cast hT
  have hqR : (1:ℝ) ≤ (max 1 q:ℕ) := by exact_mod_cast le_max_left 1 q
  have hqpos : (0:ℝ) < ((max 1 q:ℕ):ℝ) := by linarith
  have hbn : 24*(T:ℝ) ≤ (n:ℝ) := by exact_mod_cast hbudget
  have hqp := mul_le_mul_of_nonneg_right hqR hnR.le
  have hr : 0 < r := by unfold r radius; positivity
  have hr' : r ≤ 1/2 := by
    apply (div_le_iff₀ (mul_pos hqpos hnR)).2
    nlinarith only [hqp,hbn,hTR]
  have hmass := GoldbachGRHKernel.mass_loss n hr hr'
  change 0 ≤ ((n:ℝ)+1)/(n:ℝ) - mass n r/(n:ℝ) ∧
    ((n:ℝ)+1)/(n:ℝ) - mass n r/(n:ℝ) ≤ _
  rw [← sub_div]
  constructor
  · exact div_nonneg hmass.1 hnR.le
  · calc
      _ ≤ (1/(2*r))/(n:ℝ) := div_le_div_of_nonneg_right hmass.2 hnR.le
      _ = _ := by
        unfold r radius
        field_simp [hnR.ne',hqpos.ne',hTR.ne']

theorem eventually_model_floor (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, Even n →
      -ε * (n:ℝ) ≤
      (∑ i ∈ centers (cutoff n), ∫ t in cell n (narrow n) (width n) i,
        GoldbachGRHModel.model n i t^2 * GoldbachFourthMoment.phase (-(n:ℝ)*t)).re := by
  obtain ⟨Q₀,hfloor⟩ := GoldbachGRHSignedModel.medium_model_floor ε hε
  obtain ⟨P,hP⟩ := exists_nat_ge (4*(|BandTail.universal|+1)/ε)
  filter_upwards [GoldbachGRHBudget.eventual_geometry, eventually_narrow_ge Q₀,
    eventually_narrow_ge P] with n hgeo hQ₀ hQP
  intro hEven
  obtain ⟨hn,hQ,hQU,_,hbudget,_⟩ := hgeo
  let Q := narrow n
  let U := cutoff n
  let H := width n
  let full := ((n:ℝ)+1)/(n:ℝ)
  let d := 1/(2*(H:ℝ))
  let wide := normalized n H
  let taper (q : ℕ) := full - normalized n Q q
  have hn₀ : 0 < n := by omega
  have hnR : 0 < (n:ℝ) := by exact_mod_cast hn₀
  have hn1 : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast (show 1≤n by omega)
  have hU₀ : 1≤U := hQ.trans hQU
  have hUH : U≤H := GoldbachGRHBudget.width_ge_cutoff n hQ
  have hQH : Q≤H := hQU.trans hUH
  have hH₀ : 0<H := hU₀.trans hUH
  have hHn : H≤n := by change 24*H≤n at hbudget; omega
  have hH' : 0 < (H:ℝ) := by exact_mod_cast hH₀
  have hQ' : 0 < (Q:ℝ) := by exact_mod_cast hQ
  have hU' : 0 < (U:ℝ) := by exact_mod_cast hU₀
  have hQbudget : 24*Q≤n := (Nat.mul_le_mul_left 24 hQH).trans hbudget
  have hfull : full ∈ Set.Icc 0 2 := ⟨by unfold full; positivity,
    (div_le_iff₀ hnR).2 (by linarith)⟩
  have hcost : d*(BandTail.universal*(U:ℝ)) ≤ ε/4 := by
    have hhQ : (4*(|BandTail.universal|+1)/ε : ℝ) ≤ (Q:ℝ) :=
      hP.trans (by exact_mod_cast hQP)
    have hv := (div_le_iff₀ hε).1 hhQ
    have hconst : BandTail.universal ≤ (ε/4)*(512*(Q:ℝ)) := by
      have hnon := mul_nonneg hε.le hQ'.le
      nlinarith [le_abs_self BandTail.universal]
    have hval : d*(BandTail.universal*(U:ℝ)) = BandTail.universal/(512*(Q:ℝ)) := by
      unfold d H width
      push_cast
      change 1/(2*(256*(U:ℝ)*(Q:ℝ)))*(BandTail.universal*(U:ℝ)) = _
      field_simp [hU'.ne', hQ'.ne']
      ring
    rw [hval]
    exact (div_le_iff₀ (show 0 < 512*(Q:ℝ) by positivity)).2 hconst
  have htaper : ∀ q, 0≤taper q := fun q =>
    (normalized_loss n Q q hn₀ hQ hQbudget).1
  have hmono : Monotone taper := by
    intro q r hqr
    apply sub_le_sub_left
    unfold normalized
    apply div_le_div_of_nonneg_right _ hnR.le
    apply GoldbachGRHKernel.mass_mono
    · unfold radius
      positivity
    · unfold radius
      apply div_le_div_of_nonneg_left (by positivity)
        (mul_pos (by exact_mod_cast (show 0 < max 1 q by omega)) hnR)
      exact mul_le_mul_of_nonneg_right
        (by exact_mod_cast max_le_max (le_refl 1) hqr) hnR.le
  have htcap : taper Q≤2 := by
    have hnon : 0≤normalized n Q Q := by
      unfold normalized
      apply div_nonneg _ hnR.le
      exact GoldbachGRHKernel.mass_nonneg _ (by unfold radius; positivity)
    unfold taper
    linarith [hfull.2]
  have htbound : ∀ q∈Icc 1 Q, taper q ≤ (q:ℝ)/(Q:ℝ) := by
    intro q hq
    have hh := (normalized_loss n Q q hn₀ hQ hQbudget).2
    rw [max_eq_right (Finset.mem_Icc.mp hq).1] at hh
    exact hh.trans (div_le_div_of_nonneg_left (by positivity) hQ' (by linarith))
  have hwbound : ∀ q∈Icc 1 U, |wide q-full|≤d*(q:ℝ) := by
    intro q hq
    obtain ⟨h₁,h₂⟩ := normalized_loss n H q hn₀ hH₀ hbudget
    rw [max_eq_right (Finset.mem_Icc.mp hq).1] at h₂
    change 0≤full-wide q at h₁
    change full-wide q ≤ _ at h₂
    rw [abs_sub_comm, abs_of_nonneg h₁]
    unfold d
    exact h₂.trans_eq (by ring)
  have hm := hfloor Q hQ₀ n U hEven hQU full d hfull (by unfold d; positivity)
    hcost wide taper hmono htaper htcap htbound hwbound
  rw [GoldbachGRHModelAssembly.sum_cell_model_re hU₀ hQH hHn]
  have hrew :
      (∑ q ∈ Icc 1 U, (coefficient q n).re * GoldbachGRHModelAssembly.massDifference n Q H q)
      = (((∑ q ∈ Ioc Q U, (coefficient q n).re * wide q) +
        ∑ q ∈ Icc 1 Q, (coefficient q n).re * (wide q-full+taper q)) * (n:ℝ)) := by
    let f (q : ℕ) := (coefficient q n).re * GoldbachGRHModelAssembly.massDifference n Q H q
    have hI (Y : ℕ) : Finset.Ioc 0 Y = Finset.Icc 1 Y := by
      ext j
      simp only [Finset.mem_Ioc, Finset.mem_Icc]
      omega
    have hsplit : (∑ q ∈ Icc 1 Q, f q) + (∑ q ∈ Ioc Q U, f q) =
        ∑ q ∈ Icc 1 U, f q := by
      simpa only [hI] using Finset.sum_Ioc_consecutive f (Nat.zero_le Q) hQU
    have hlo : (∑ q ∈ Icc 1 Q, f q) =
        (∑ q ∈ Icc 1 Q, (coefficient q n).re * (wide q-full+taper q))*(n:ℝ) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro q hq
      obtain ⟨hqL,hqU⟩ := Finset.mem_Icc.mp hq
      simp only [f, GoldbachGRHModelAssembly.massDifference, ite_eq_left hqU, taper, wide, normalized,
        max_eq_right hqL]
      field_simp [hnR.ne']
      ring
    have hhi : (∑ q ∈ Ioc Q U, f q) =
        (∑ q ∈ Ioc Q U, (coefficient q n).re * wide q)*(n:ℝ) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro q hq
      have hqL : 1≤q := by have := (Finset.mem_Ioc.mp hq).1; omega
      simp only [f, GoldbachGRHModelAssembly.massDifference,
        ite_eq_right (not_le.mpr (Finset.mem_Ioc.mp hq).1), sub_zero, wide, normalized, max_eq_right hqL]
      field_simp [hnR.ne']
    change (∑ q ∈ Icc 1 U, f q) = _
    rw [← hsplit, hlo, hhi, add_mul, add_comm]
  rw [hrew]
  exact mul_le_mul_of_nonneg_right hm hnR.le

end GoldbachGRHConcreteFloor

end GoldbachGRHConcreteFloor

section GoldbachGRHApproximation

open Filter Finset MeasureTheory
open scoped Interval Topology Classical

namespace GoldbachGRHApproximation

open GoldbachFourthMoment (phase primeSum primeWeight)
open GoldbachGRHBudget (narrow cutoff width)
open GoldbachGRHArcs (cap center centers cell radius)
open GoldbachGRHModel (model model_continuous)
open GoldbachGRHWindow (additiveModel)
open GoldbachGRHAnalytic (errorCoeff shifted_error_eq)
open GoldbachWindow (poly)

noncomputable def integrand (n : ℕ) (t : ℝ) : ℂ := primeSum n t ^ 2 * phase (-(n:ℝ)*t)

noncomputable def signedModel (n : ℕ) : ℂ :=
  ∑ i ∈ centers (cutoff n), ∫ t in cell n (narrow n) (width n) i,
    model n i t ^ 2 * phase (-(n:ℝ)*t)

private theorem eventual_cell_l2 (hGRH : Goldbach.GRH) :
    ∀ᶠ n : ℕ in atTop,
      (∑ i ∈ centers (cutoff n), ∫ t in cell n (narrow n) (width n) i,
        ‖primeSum n t - model n i t‖^2) ≤ (n:ℝ)^(5/6:ℝ) := by
  obtain ⟨C,hC,hfreq⟩ := GoldbachGRHAnalytic.per_denominator_energy hGRH
  have hC₁ : 0 < 6*C := by positivity
  filter_upwards [GoldbachGRHBudget.eventual_geometry,
    GoldbachGRHBudget.eventually_wide_energy (6*C) hC₁] with n hgeo hlarge
  obtain ⟨hn,hQ,hQU,hUn,hHn,_⟩ := hgeo
  have hUH := GoldbachGRHBudget.width_ge_cutoff n hQ
  have hU₀ : 1 ≤ cutoff n := hQ.trans hQU
  have hnR : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : 0 < (n:ℝ) := by linarith
  have hH : 0 < width n := hU₀.trans hUH
  have hHnR : 24 * (width n:ℝ) ≤ (n:ℝ) := by exact_mod_cast hHn
  have hlog : (1/2:ℝ) ≤ Real.log (n:ℝ) := by
    have ht := Real.log_le_log (by norm_num : 0<(2:ℝ)) hnR
    linarith [Real.log_two_gt_d9]
  let L := Real.log (n:ℝ)
  let D (i : ℕ × ℕ) := ∫ t in cell n (narrow n) (width n) i, ‖primeSum n t - model n i t‖^2
  have hq (q : ℕ) (hq : q ∈ Icc 1 (cutoff n)) :
      (∑ a ∈ (range (q+1)).filter (fun a => a.Coprime q), D (q,a)) ≤
        2*C*(width n:ℝ)^2/(q:ℝ)*L^4 := by
    obtain ⟨hq1,hqU⟩ := Finset.mem_Icc.mp hq
    let : NeZero q := ⟨(show 0<q by omega).ne'⟩
    have hqR : (1:ℝ) ≤ q := by exact_mod_cast hq1
    have hqpos : 0 < (q:ℝ) := by linarith
    let r := radius n (width n) q
    have hr : 0 < r := by unfold r radius; positivity
    have hr₁ : r ≤ 1/24 := by
      apply (div_le_iff₀ (by positivity : 0<(q:ℝ)*(n:ℝ))).2
      have hqn := mul_le_mul_of_nonneg_right hqR hnpos.le
      nlinarith only [hqn,hHnR]
    have hr₂ : 1 ≤ ((n+1:ℕ):ℝ)*r := by
      have hqH : (q:ℝ) ≤ (width n:ℝ) := by exact_mod_cast hqU.trans hUH
      have hprod := mul_le_mul_of_nonneg_right hqH hnpos.le
      have hnon : 0 ≤ (width n:ℝ) := by positivity
      dsimp only [r, radius]
      rw [← mul_div_assoc]
      apply (le_div_iff₀ (by positivity : 0<(q:ℝ)*(n:ℝ))).2
      push_cast
      nlinarith only [hprod,hnon]
    let E (a : ZMod q) := ∫ β in (-r)..r, ‖poly (n+1) (errorCoeff a) β‖^2
    have hE (a : ZMod q) : 0 ≤ E a :=
      intervalIntegral.integral_nonneg (by linarith) (fun _ _ => by positivity)
    have hcell (a : ℕ) (ha : a ∈ (range (q+1)).filter (fun a => a.Coprime q)) :
        D (q,a) ≤ E (a : ZMod q) := by
      have hunit := (ZMod.isUnit_iff_coprime a q).2 (Finset.mem_filter.mp ha).2
      let G (β : ℝ) := ‖poly (n+1) (errorCoeff (a : ZMod q)) β‖^2
      have hGc : Continuous G := by unfold G poly phase; fun_prop
      have hG₀ (t : ℝ) : 0 ≤ G t := by unfold G; positivity
      have ht (t : ℝ) : G (t - center (q,a)) = ‖primeSum n t - model n (q,a) t‖^2 := by
        unfold G
        rw [shifted_error_eq]
        rw [GoldbachGRHWindow.additiveModel_eq_moebius _ hunit]
        unfold model
        change ‖primeSum n ((a:ℝ)/q + (t-center (q,a))) -
          (ArithmeticFunction.moebius q:ℂ)/(q.totient:ℂ) *
             GoldbachGRHKernel.kernel n (t-center (q,a))‖^2 =
          ‖primeSum n t -
          (ArithmeticFunction.moebius q:ℂ)/(q.totient:ℂ) *
             GoldbachGRHKernel.kernel n (t-center (q,a))‖^2
        have ha' : ((a:ℝ)/q) + (t-center (q,a)) = t := by unfold center; ring
        rw [ha']
      have hc := GoldbachGRHArcTransport.cell_l2_le n (narrow n) (width n) (q,a) G hGc hG₀
      simpa only [ht, D, G, E, r] using hc
    calc
      _ ≤ ∑ a ∈ (range (q+1)).filter (fun a => a.Coprime q), E (a : ZMod q) :=
        Finset.sum_le_sum hcell
      _ ≤ 2*(∑ a : ZMod q, E a) := GoldbachGRHArcs.sum_numerators_le_real q E hE
      _ ≤ 2*(C*(width n:ℝ)^2/(q:ℝ)*L^4) :=
        mul_le_mul_of_nonneg_left (hfreq n q (width n) hn (hqU.trans hUn) hr hr₁ hr₂)
          (by norm_num)
      _ = _ := by ring
  have hlogU : Real.log (cutoff n:ℝ) ≤ L := Real.log_le_log
    (by exact_mod_cast (show 0 < cutoff n by omega)) (by exact_mod_cast hUn)
  have hhar : (∑ q ∈ Icc 1 (cutoff n), 1/(q:ℝ)) ≤ 3*L := by
    have ht := GoldbachGRHBudget.harmonic_le (cutoff n)
    change (1/2:ℝ) ≤ L at hlog
    linarith
  have hscale : 0 ≤ 2*C*(width n:ℝ)^2*L^4 := by dsimp [L]; positivity
  calc
    (∑ i ∈ centers (cutoff n), D i) =
       ∑ q ∈ Icc 1 (cutoff n), ∑ a ∈ (range (q+1)).filter (fun a => a.Coprime q), D (q,a) :=
      GoldbachGRHArcs.sum_centers_eq (cutoff n) D
    _ ≤ ∑ q ∈ Icc 1 (cutoff n), 2*C*(width n:ℝ)^2/(q:ℝ)*L^4 :=
      Finset.sum_le_sum hq
    _ = (2*C*(width n:ℝ)^2*L^4)*(∑ q ∈ Icc 1 (cutoff n), 1/(q:ℝ)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q _
      ring
    _ ≤ (2*C*(width n:ℝ)^2*L^4)*(3*L) := mul_le_mul_of_nonneg_left hhar hscale
    _ = (6*C)*(width n:ℝ)^2*L^5 := by ring
    _ ≤ _ := hlarge

theorem eventual_signed_model_error (hGRH : Goldbach.GRH) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      ‖((∫ t in (0:ℝ)..1, (cap n (cutoff n) (narrow n) \ cap n (narrow n) (narrow n)).indicator
            (integrand n) t) +
        (∫ t in (0:ℝ)..1, (cap n (cutoff n) (width n) \ cap n (cutoff n) (narrow n)).indicator
            (integrand n) t)) - signedModel n‖ ≤ ε*(n:ℝ) := by
  filter_upwards [GoldbachGRHBudget.eventual_geometry, eventual_cell_l2 hGRH,
    GoldbachGRHYoungBudget.eventually_young_budget ε hε] with n hgeo hErr hYoung
  obtain ⟨hn,hQ,hQU,_,_,hbudget⟩ := hgeo
  obtain ⟨hη,hYoung⟩ := hYoung
  have hQH : narrow n ≤ width n := hQU.trans (GoldbachGRHBudget.width_ge_cutoff n hQ)
  let η := (n:ℝ)^(-1/12:ℝ)
  let osc (t : ℝ) := phase (-(n:ℝ)*t)
  have hOsc : Continuous osc := by unfold osc phase; fun_prop
  have hS : Continuous (primeSum n) := by unfold primeSum phase; fun_prop
  have hF : Continuous (integrand n) := (hS.pow 2).mul hOsc
  rw [GoldbachGRHArcs.integrate_middle_split hQU hQH _ hF,
    GoldbachGRHArcs.integrate_difference_eq_sum hQU hQH hbudget _ hF,
    signedModel, ← Finset.sum_sub_distrib]
  have hsplit (i : ℕ × ℕ) :
      (∫ t in cell n (narrow n) (width n) i, integrand n t) -
        (∫ t in cell n (narrow n) (width n) i, model n i t ^ 2 * osc t) =
      ∫ t in cell n (narrow n) (width n) i, (primeSum n t ^ 2 - model n i t ^ 2) * osc t := by
    have hpart : cell n (narrow n) (width n) i ⊆ Set.Ioc (0:ℝ) 1 :=
      Set.inter_subset_right
    have h₁ : IntegrableOn (integrand n) (cell n (narrow n) (width n) i) volume :=
      (hF.intervalIntegrable 0 1).1.mono_set hpart
    have hm : Continuous (fun t => model n i t ^ 2 * osc t) :=
      ((model_continuous n i).pow 2).mul hOsc
    have h₂ : IntegrableOn (fun t => model n i t ^ 2 * osc t)
        (cell n (narrow n) (width n) i) volume :=
      (hm.intervalIntegrable 0 1).1.mono_set hpart
    rw [← integral_sub h₁ h₂]
    simp [integrand, osc, sub_mul]
  dsimp only [osc] at hsplit
  simp_rw [hsplit]
  apply (norm_sum_le _ _).trans
  apply (GoldbachGRHWindowEnergy.sum_setIntegral_square_difference_le
    (centers (cutoff n)) (cell n (narrow n) (width n))
    (fun i _ => GoldbachGRHArcs.measurable_cell _ _ _ i)
    (fun _ _ => Set.inter_subset_right) (GoldbachGRHArcs.cell_disjoint hbudget)
    (primeSum n) (model n) osc hS (fun i _ => model_continuous n i) hOsc
    (fun t => le_of_eq (Complex.norm_exp_ofReal_mul_I (2 * Real.pi * (-(n:ℝ)*t)))) hη).trans
  apply (add_le_add (mul_le_mul_of_nonneg_left hErr (by positivity : 0≤1+1/η))
    (mul_le_mul_of_nonneg_left (GoldbachGRHAnalytic.prime_sum_energy_le n hn) hη.le)).trans
  simpa only [η, mul_assoc] using hYoung

end GoldbachGRHApproximation

end GoldbachGRHApproximation


section GoldbachMediumModulusSkirt

open Filter Finset MeasureTheory
open scoped Interval Topology

namespace GoldbachMediumModulusSkirt

open GoldbachGRHArcs
open GoldbachGRHBudget (narrow cutoff width)
open GoldbachFourthMoment (phase primeSum)
open GoldbachGRHModel (model model_continuous)
open GoldbachGRHKernel (mass kernel)
open GoldbachExplicitModeledMajor (coefficient)
open GoldbachGRHApproximation (integrand)
open GoldbachGRHSignedModel (harmonic_suffix_floor)

def indices (Q U : ℕ) := (centers U).filter fun i => Q < i.1

noncomputable def skirt (n Q H : ℕ) (i : ℕ × ℕ) : Set ℝ :=
  (arc n H i \ arc n Q i) ∩ Set.Ioc 0 1

noncomputable def remaining (n Q U H : ℕ) : Set ℝ :=
  (cap n U H \ cap n U Q) \ (cap n Q H \ cap n Q Q)

theorem skirt_subset_cell (n Q H : ℕ) (i : ℕ × ℕ) :
    skirt n Q H i ⊆ cell n Q H i := by
  intro t ht
  change (t ∈ arc n H i ∧ t ∉ arc n Q i) ∧ t ∈ Set.Ioc (0 : ℝ) 1 at ht
  by_cases hi : i.1 ≤ Q
  · simpa only [cell, ite_eq_left hi, Set.mem_inter_iff, Set.mem_sdiff] using ht
  · simpa [cell, hi] using And.intro ht.1.1 ht.2

theorem measurable_skirt (n Q H : ℕ) (i : ℕ × ℕ) : MeasurableSet (skirt n Q H i) :=
  ((measurable_arc n H i).diff (measurable_arc n Q i)).inter measurableSet_Ioc

theorem skirt_disjoint {n Q U H : ℕ} (hB : 2 * H * U < n) :
    (↑(indices Q U) : Set (ℕ × ℕ)).PairwiseDisjoint (skirt n Q H) := by
  intro i hi j hj hne
  exact (cell_disjoint (Q := Q) hB (mem_filter.mp hi).1 (mem_filter.mp hj).1 hne).mono
    (skirt_subset_cell n Q H i) (skirt_subset_cell n Q H j)

theorem skirt_union {n Q U H : ℕ} (hQU : Q ≤ U) (hQH : Q ≤ H)
    (hB : 2 * H * U < n) :
    (⋃ i ∈ indices Q U, skirt n Q H i) = remaining n Q U H ∩ Set.Ioc 0 1 := by
  ext t
  simp only [Set.mem_iUnion, remaining, skirt, Set.mem_inter_iff, Set.mem_sdiff,
    indices, mem_filter]
  constructor
  · rintro ⟨i, ⟨hi, hiQ⟩, ⟨⟨hwide, hnarrow⟩, hunit⟩⟩
    refine ⟨⟨⟨mem_cap.mpr ⟨i, hi, hwide⟩, ?_⟩, ?_⟩, hunit⟩
    · intro ht
      obtain ⟨j, hj, ht'⟩ := mem_cap.mp ht
      have he := common_arc_unique hB hi hj hwide (arc_mono hQH j ht')
      subst j
      exact hnarrow ht'
    · intro hl
      obtain ⟨j, hj, ht⟩ := mem_cap.mp hl.1
      have he := common_arc_unique hB hi (centers_mono hQU hj) hwide ht
      subst j
      exact (not_le_of_gt hiQ) (mem_centers.mp hj).2.1
  · rintro ⟨⟨⟨hwide, hnarrow⟩, hlow⟩, hunit⟩
    obtain ⟨i, hi, ht⟩ := mem_cap.mp hwide
    have hiQ : Q < i.1 := by
      by_contra! hq
      obtain ⟨h₁, _, h₂, h₃⟩ := mem_centers.mp hi
      apply hlow
      exact ⟨mem_cap.mpr ⟨i, mem_centers.mpr ⟨h₁, hq, h₂, h₃⟩, ht⟩,
        fun hl => hnarrow (cap_mono hQU le_rfl hl)⟩
    exact ⟨i, ⟨hi, hiQ⟩, ⟨⟨ht, fun hh => hnarrow (mem_cap.mpr ⟨i, hi, hh⟩)⟩, hunit⟩⟩

theorem integral_remaining_eq_sum {n Q U H : ℕ} (hQU : Q ≤ U) (hQH : Q ≤ H)
    (hB : 2 * H * U < n) (F : ℝ → ℂ) (hF : Continuous F) :
    (∫ t in (0 : ℝ)..1, (remaining n Q U H).indicator F t) =
      ∑ i ∈ indices Q U, ∫ t in skirt n Q H i, F t := by
  have hm : MeasurableSet (remaining n Q U H) :=
    ((measurable_cap n U H).diff (measurable_cap n U Q)).diff
      ((measurable_cap n Q H).diff (measurable_cap n Q Q))
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1), setIntegral_indicator hm,
    Set.inter_comm (Set.Ioc (0 : ℝ) 1), ← skirt_union hQU hQH hB]
  exact integral_biUnion_finset _ (fun i _ => measurable_skirt n Q H i) (skirt_disjoint hB)
    (fun _ _ => (hF.intervalIntegrable 0 1).1.mono_set Set.inter_subset_right)

theorem model_sum_re {n Q U H : ℕ} (hQ : 1 ≤ Q) (hQH : Q ≤ H) (hHn : H ≤ n) :
    (∑ i ∈ indices Q U, ∫ t in skirt n Q H i,
      model n i t ^ 2 * phase (-(n : ℝ) * t)).re =
      ∑ q ∈ Ioc Q U, (coefficient q n).re * (mass n (radius n H q) - mass n (radius n Q q)) := by
  classical
  let F (i : ℕ × ℕ) := ∫ t in skirt n Q H i, model n i t ^ 2 * phase (-(n : ℝ) * t)
  change (∑ i ∈ indices Q U, F i).re = _
  rw [indices, sum_filter, sum_centers_eq]
  dsimp only
  have hsplit (q : ℕ) :
      (∑ a ∈ (range (q + 1)).filter (fun a => a.Coprime q), if Q < q then F (q, a) else 0) =
        if Q < q then (∑ a ∈ (range (q + 1)).filter (fun a => a.Coprime q), F (q, a)) else 0 := by
    split <;> simp_all
  simp_rw [hsplit]
  rw [← sum_filter, Complex.re_sum]
  have hindex : (Icc 1 U).filter (fun q => Q < q) = Ioc Q U := by
    ext q
    simp only [mem_filter, mem_Ioc, mem_Icc]
    omega
  rw [hindex]
  apply sum_congr rfl
  intro q hq
  have hq2 : 2 ≤ q := by have := (mem_Ioc.mp hq).1; omega
  have haSet : (range (q + 1)).filter (fun a => a.Coprime q) =
      (range q).filter (fun a => a.Coprime q) := by
    ext a
    simp only [mem_filter, mem_range]
    constructor
    · rintro ⟨h, hc⟩
      have hne : a ≠ q := by
        intro he
        subst a
        have : q = 1 := by simpa [Nat.Coprime] using hc
        omega
      exact ⟨by omega, hc⟩
    · exact fun ⟨ha, hc⟩ => ⟨by omega, hc⟩
  rw [haSet]
  have hcell : ∀ a ∈ (range q).filter (fun a => a.Coprime q),
      F (q, a) = GoldbachGRHModelAssembly.signedFactor n q a *
        (↑(mass n (radius n H q) - mass n (radius n Q q)) : ℂ) := by
    intro a ha
    obtain ⟨ha, hc⟩ := mem_filter.mp ha
    have hmeq : skirt n Q H (q, a) = (arc n H (q, a) ∩ Set.Ioc (0 : ℝ) 1) \
        (arc n Q (q, a) ∩ Set.Ioc (0 : ℝ) 1) := by
      ext t
      simp only [skirt, Set.mem_inter_iff, Set.mem_sdiff]
      tauto
    have hG : Continuous (fun t : ℝ => ‖kernel n t‖ ^ 2) := (GoldbachGRHKernel.kernel_continuous n).norm.pow 2
    have hArc (T : ℕ) (hTn : T ≤ n) :
        (∫ t in arc n T (q, a) ∩ Set.Ioc (0 : ℝ) 1, ‖kernel n (t - center (q, a))‖ ^ 2) =
          mass n (radius n T q) := by
      have h := GoldbachGRHArcTransport.arc_interior_bounds hTn hq2 (mem_range.mp ha).le hc
      exact GoldbachGRHArcTransport.clipped_arc_integral_of_interior n T (q, a)
        (fun t => ‖kernel n t‖ ^ 2) h.1 h.2
    have hContinuous : Continuous (fun t : ℝ => ‖kernel n (t - center (q, a))‖ ^ 2) :=
      hG.comp (continuous_id.sub continuous_const)
    have hInt : IntegrableOn (fun t => ‖kernel n (t - center (q, a))‖ ^ 2)
        (arc n H (q, a) ∩ Set.Ioc (0 : ℝ) 1) volume :=
      ((hContinuous.intervalIntegrable (0 : ℝ) 1).1).mono_set Set.inter_subset_right
    have hSub : arc n Q (q, a) ∩ Set.Ioc (0 : ℝ) 1 ⊆ arc n H (q, a) ∩ Set.Ioc 0 1 :=
      Set.inter_subset_inter_left _ (arc_mono hQH (q, a))
    dsimp [F]
    simp_rw [GoldbachGRHModelAssembly.model_square_eq]
    rw [MeasureTheory.integral_const_mul, integral_complex_ofReal, hmeq,
      setIntegral_sdiff ((measurable_arc n Q (q, a)).inter measurableSet_Ioc) hInt hSub,
      hArc H hHn, hArc Q (hQH.trans hHn)]
  rw [sum_congr rfl hcell, ← sum_mul, GoldbachGRHModelAssembly.sum_signedFactor]
  simp [Complex.mul_re]

private noncomputable def signedModel (n : ℕ) : ℂ :=
  ∑ i ∈ indices (narrow n) (cutoff n), ∫ t in skirt n (narrow n) (width n) i,
    model n i t ^ 2 * phase (-(n : ℝ) * t)

theorem model_floor (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, Even n → -ε * (n : ℝ) ≤ (signedModel n).re := by
  obtain ⟨Q₀, hTail⟩ := harmonic_suffix_floor (ε / 4) (by positivity)
  obtain ⟨P, hP⟩ := exists_nat_ge (2 * (|BandTail.universal| + 1) / ε)
  filter_upwards [GoldbachGRHBudget.eventual_geometry,
    GoldbachGRHConcreteFloor.eventually_narrow_ge Q₀,
    GoldbachGRHConcreteFloor.eventually_narrow_ge P] with n hg hQ₀ hPQ
  intro hEven
  obtain ⟨hn, hQ, hQU, _, hBudget, _⟩ := hg
  let Q := narrow n
  let U := cutoff n
  let H := width n
  let full := ((n : ℝ) + 1) / (n : ℝ)
  let taper (q : ℕ) := full - GoldbachGRHConcreteFloor.normalized n Q q
  let wideLoss (q : ℕ) := full - GoldbachGRHConcreteFloor.normalized n H q
  let a (q : ℕ) := (coefficient q n).re
  have hn₀ : 0 < n := by omega
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn₀
  have hn₁ : 1 ≤ (n : ℝ) := by exact_mod_cast (show 1 ≤ n by omega)
  have hQH : Q ≤ H := hQU.trans (GoldbachGRHBudget.width_ge_cutoff n hQ)
  have hHn : H ≤ n := by change 24 * H ≤ n at hBudget; omega
  have hHpos : 0 < H := hQ.trans hQH
  have hQBudget : 24 * Q ≤ n := (Nat.mul_le_mul_left 24 hQH).trans hBudget
  have hM : Monotone taper := by
    intro q r hqr
    apply sub_le_sub_left
    unfold GoldbachGRHConcreteFloor.normalized
    apply div_le_div_of_nonneg_right _ hnR.le
    apply GoldbachGRHKernel.mass_mono
    · unfold radius; positivity
    · unfold radius
      apply div_le_div_of_nonneg_left (by positivity)
        (mul_pos (by exact_mod_cast (show 0 < max 1 q by omega)) hnR)
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast max_le_max (le_refl 1) hqr) hnR.le
  have hT₀ (q : ℕ) : 0 ≤ taper q :=
    (GoldbachGRHConcreteFloor.normalized_loss n Q q hn₀ hQ hQBudget).1
  have hT₂ : taper U ≤ 2 := by
    have hnrm : 0 ≤ GoldbachGRHConcreteFloor.normalized n Q U := by
      unfold GoldbachGRHConcreteFloor.normalized
      exact div_nonneg (GoldbachGRHKernel.mass_nonneg _ (by unfold radius; positivity)) hnR.le
    have hf : full ≤ 2 := (div_le_iff₀ hnR).2 (by linarith)
    unfold taper
    linarith
  have hSigned := GoldbachGRHSignedModel.weighted_suffix_lower a (ε / 4) (by positivity)
    (U - Q) Q taper hM (fun q _ => hT₀ q)
  rw [Nat.add_sub_of_le hQU] at hSigned
  have hT : -(ε / 2) ≤ ∑ q ∈ Ioc Q U, a q * taper q := by
    apply le_trans _ (hSigned ?_)
    · nlinarith [mul_le_mul_of_nonneg_left hT₂ (show 0 ≤ ε / 4 by positivity)]
    · intro k hk hkU
      have hh := hTail k (hQ₀.trans hk) n U hEven hkU
      refine hh.trans (le_of_eq (sum_congr rfl fun q hq => ?_))
      exact (GoldbachGRHSignedModel.coefficient_re_eq n q (by have := (mem_Ioc.mp hq).1; omega)).symm
  have hLoss (q : ℕ) (hq : q ∈ Ioc Q U) :
      |a q * wideLoss q| ≤ (1 / (2 * (H : ℝ))) * |BandTail.F n q| := by
    have hq₀ : 1 ≤ q := by have := (mem_Ioc.mp hq).1; omega
    have hqR : 0 < (q : ℝ) := by exact_mod_cast hq₀
    have ⟨hwl, hwu⟩ := GoldbachGRHConcreteFloor.normalized_loss n H q hn₀ hHpos hBudget
    rw [max_eq_right hq₀] at hwu
    change 0 ≤ wideLoss q at hwl
    change wideLoss q ≤ _ at hwu
    rw [abs_mul, abs_of_nonneg hwl, show a q = (coefficient q n).re from rfl,
      GoldbachGRHSignedModel.coefficient_re_eq n q hq₀, abs_div, abs_of_pos hqR]
    calc
      _ ≤ (|BandTail.F n q| / (q : ℝ)) * ((q : ℝ) / (2 * (H : ℝ))) :=
        mul_le_mul_of_nonneg_left hwu (by positivity)
      _ = _ := by field_simp
  have hErr : |∑ q ∈ Ioc Q U, a q * wideLoss q| ≤ ε / 2 := by
    have hQP : (2 * (|BandTail.universal| + 1) / ε : ℝ) ≤ (Q : ℝ) :=
      hP.trans (by exact_mod_cast hPQ)
    have hQR : 0 < (Q : ℝ) := by exact_mod_cast hQ
    have hUR : 0 < (U : ℝ) := by exact_mod_cast hQ.trans hQU
    calc
      _ ≤ ∑ q ∈ Ioc Q U, |a q * wideLoss q| := by simpa only [Real.norm_eq_abs] using
        (norm_sum_le (Ioc Q U) (fun q => a q * wideLoss q))
      _ ≤ ∑ q ∈ Ioc Q U, (1 / (2 * (H : ℝ))) * |BandTail.F n q| := sum_le_sum hLoss
      _ = (1 / (2 * (H : ℝ))) * ∑ q ∈ Ioc Q U, |BandTail.F n q| := by rw [mul_sum]
      _ ≤ (1 / (2 * (H : ℝ))) * (BandTail.universal * (U : ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply le_trans (sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => abs_nonneg _))
          (GoldbachGRHSignedModel.absolute_prefix_le n U)
        intro q hq
        obtain ⟨h₁, h₂⟩ := mem_Ioc.mp hq
        exact mem_Icc.mpr ⟨by omega, h₂⟩
      _ = BandTail.universal / (512 * (Q : ℝ)) := by
        unfold H width
        push_cast
        change 1 / (2 * (256 * (U : ℝ) * (Q : ℝ))) * (BandTail.universal * (U : ℝ)) = _
        field_simp [hUR.ne', hQR.ne']
        ring
      _ ≤ ε / 2 := by
        have hBound := (div_le_iff₀ hε).1 hQP
        apply (div_le_iff₀ (show 0 < 512 * (Q : ℝ) by positivity)).2
        nlinarith [le_abs_self BandTail.universal, mul_nonneg hε.le hQR.le]
  unfold signedModel
  rw [model_sum_re hQ hQH hHn]
  have hRewrite :
      (∑ q ∈ Ioc Q U, a q * (mass n (radius n H q) - mass n (radius n Q q))) =
        ((∑ q ∈ Ioc Q U, a q * taper q) - ∑ q ∈ Ioc Q U, a q * wideLoss q) * (n : ℝ) := by
    rw [← sum_sub_distrib, sum_mul]
    apply sum_congr rfl
    intro q hq
    have hq₁ : 1 ≤ q := by have := (mem_Ioc.mp hq).1; omega
    simp only [taper, wideLoss, GoldbachGRHConcreteFloor.normalized, max_eq_right hq₁]
    field_simp [hnR.ne']
    ring
  rw [hRewrite]
  exact mul_le_mul_of_nonneg_right (by linarith [(abs_le.mp hErr).2]) hnR.le

theorem estimation_error (hGRH : Goldbach.GRH) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      ‖(∫ t in (0 : ℝ)..1,
        (remaining n (narrow n) (cutoff n) (width n)).indicator (integrand n) t) -
        signedModel n‖ ≤ ε * (n : ℝ) := by
  filter_upwards [GoldbachGRHBudget.eventual_geometry,
    GoldbachGRHApproximation.eventual_cell_l2 hGRH,
    GoldbachGRHYoungBudget.eventually_young_budget ε hε] with n hg hErr hYoung
  obtain ⟨hn, hQ, hQU, _, _, hB⟩ := hg
  obtain ⟨hη, hBudget⟩ := hYoung
  let s := indices (narrow n) (cutoff n)
  let D := skirt n (narrow n) (width n)
  let osc (t : ℝ) := phase (-(n : ℝ) * t)
  have hOsc : Continuous osc := by unfold osc phase; fun_prop
  have hS : Continuous (primeSum n) := by unfold primeSum phase; fun_prop
  have hF : Continuous (integrand n) := (hS.pow 2).mul hOsc
  have hQH := hQU.trans (GoldbachGRHBudget.width_ge_cutoff n hQ)
  have hsub (i : ℕ × ℕ) : D i ⊆ Set.Ioc (0 : ℝ) 1 := Set.inter_subset_right
  have hEnergy : (∑ i ∈ s, ∫ t in D i, ‖primeSum n t - model n i t‖ ^ 2) ≤ (n : ℝ) ^ (5 / 6 : ℝ) := by
    apply le_trans _ hErr
    calc
      _ ≤ ∑ i ∈ s, ∫ t in cell n (narrow n) (width n) i, ‖primeSum n t - model n i t‖ ^ 2 := by
        apply sum_le_sum
        intro i _
        have hh := ((hS.sub (model_continuous n i)).norm.pow 2).intervalIntegrable
          (μ := volume) (0 : ℝ) 1
        exact setIntegral_mono_set (hh.1.mono_set Set.inter_subset_right)
          (Filter.Eventually.of_forall fun _ => by positivity)
          (skirt_subset_cell n (narrow n) (width n) i).eventuallySubset
      _ ≤ _ := by
        apply sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        intro i _ _
        exact integral_nonneg_of_ae (Filter.Eventually.of_forall fun _ => by positivity)
  rw [integral_remaining_eq_sum hQU hQH hB _ hF, signedModel, ← Finset.sum_sub_distrib]
  have hDiff (i : ℕ × ℕ) :
      (∫ t in D i, integrand n t) - (∫ t in D i, model n i t ^ 2 * osc t) =
        ∫ t in D i, (primeSum n t ^ 2 - model n i t ^ 2) * osc t := by
    have hm : Continuous (fun t => model n i t ^ 2 * osc t) := ((model_continuous n i).pow 2).mul hOsc
    have h₁ : IntegrableOn (integrand n) (D i) volume := (hF.intervalIntegrable 0 1).1.mono_set (hsub i)
    have h₂ : IntegrableOn (fun t => model n i t ^ 2 * osc t) (D i) volume :=
      (hm.intervalIntegrable 0 1).1.mono_set (hsub i)
    rw [← integral_sub h₁ h₂]
    simp [integrand, osc, sub_mul]
  dsimp only [D, osc] at hDiff
  simp_rw [hDiff]
  apply (norm_sum_le _ _).trans
  apply (GoldbachGRHWindowEnergy.sum_setIntegral_square_difference_le s D
    (fun i _ => measurable_skirt n (narrow n) (width n) i) (fun i _ => hsub i)
    (skirt_disjoint hB) (primeSum n) (model n) osc hS (fun i _ => model_continuous n i)
    hOsc (fun t => le_of_eq (Complex.norm_exp_ofReal_mul_I (2 * Real.pi * (-(n : ℝ) * t)))) hη).trans
  apply (add_le_add (mul_le_mul_of_nonneg_left hEnergy (by positivity : 0 ≤ 1 + 1 / ((n : ℝ) ^ (-1 / 12 : ℝ))))
    (mul_le_mul_of_nonneg_left (GoldbachGRHAnalytic.prime_sum_energy_le n hn) hη.le)).trans
  simpa only [mul_assoc] using hBudget

end GoldbachMediumModulusSkirt

theorem SkirtDiagnostic :
    Goldbach.GRH → let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0; let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (u : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (u k:ℂ)*E ((k:ℝ)*t)); let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let arcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))}; let f := fun (n : ℕ) (t : ℝ) => (S n w t)^2*E (-(n:ℝ)*t); let Q₁ := fun n : ℕ => ⌊(n:ℝ)^(1/3:ℝ)⌋₊; let H := fun n : ℕ => 256 * Q₁ n * Q n; let midArcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q₁ n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))}; let wideArcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q₁ n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (H n:ℝ)/((q:ℝ)*(n:ℝ))}; let lowWideArcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (H n:ℝ)/((q:ℝ)*(n:ℝ))}; let remSkirt := fun n : ℕ => intervalIntegral (fun t => ((wideArcs n \ midArcs n) \ (lowWideArcs n \ arcs n)).indicator (f n) t) (0:ℝ) 1 MeasureTheory.volume; ∀ e : ℝ, 0 < e → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n → -(e * (n : ℝ)) ≤ (remSkirt n).re := by
  intro hGRH
  dsimp only
  intro ε hε
  have he : 0 < ε / 2 := by positivity
  have h := (GoldbachMediumModulusSkirt.estimation_error hGRH (ε / 2) he).and
    (GoldbachMediumModulusSkirt.model_floor (ε / 2) he)
  obtain ⟨N, hN⟩ := eventually_atTop.1 h
  refine ⟨N, ?_⟩
  intro n hn hEven
  obtain ⟨hErr, hModel⟩ := hN n hn
  have hb := (abs_le.mp ((Complex.abs_re_le_norm _).trans hErr)).1
  rw [Complex.sub_re] at hb
  have hsum := add_le_add hb (hModel hEven)
  rw [sub_add_cancel] at hsum
  have hbudget : -(ε * (n : ℝ)) = -(ε / 2 * (n : ℝ)) + (-(ε / 2)) * (n : ℝ) := by ring
  have hResult := hbudget.le.trans hsum
  have integrand_eq : GoldbachGRHApproximation.integrand n = fun t =>
      GoldbachFourthMoment.primeSum n t ^ 2 * GoldbachFourthMoment.phase (-(n : ℝ) * t) := rfl
  rw [integrand_eq] at hResult
  simpa only [GoldbachMediumModulusSkirt.remaining, GoldbachGRHArcs.cap,
    GoldbachFourthGeometry.wide, GoldbachGRHBudget.narrow, GoldbachGRHBudget.cutoff,
    GoldbachGRHBudget.width, GoldbachFourthMoment.primeSum,
    GoldbachFourthMoment.primeWeight, GoldbachFourthMoment.phase] using hResult

end GoldbachMediumModulusSkirt
