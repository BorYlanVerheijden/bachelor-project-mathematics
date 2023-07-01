import tactic
import data.int.cast.basic
import ring_theory.prime
import number_theory.legendre_symbol.quadratic_reciprocity
import algebra.squarefree


noncomputable theory

open set
open set filter
open int
namespace int
.

/-Local obstruction and an example-/

open mv_polynomial

lemma local_obstruction (m n : ℕ) (F : mv_polynomial (fin m) ℤ)
(h : ∃ (k : fin m → ℤ), mv_polynomial.aeval k F = 0) :
∃ (k : fin m → zmod n), (mv_polynomial.aeval k F : zmod n) = 0 :=
begin
  cases h with k h,
  use (algebra_map ℤ (zmod n) ∘ k),
  simp only [h, mv_polynomial.aeval_algebra_map_apply, h, map_zero],
end

lemma local_obstruction' (m n : ℕ) (F : mv_polynomial (fin m) ℤ)
(h : ¬∃ (k : fin m → zmod n), mv_polynomial.aeval k F = (0 : zmod n)) :
¬∃ (k : fin m → ℤ), mv_polynomial.aeval k F = 0 :=
--contrapositive of local_obstruction
begin
  have hlocobstr := local_obstruction m n F,
  rw ← not_imp_not at hlocobstr,
  exact hlocobstr h,
end

lemma local_obstruction_example : ¬∃ (x y : ℤ), x ^ 4 - y ^ 2 = 3 :=
--example of a local obstruction
begin
  intro H, --proof by contradiction
  cases H with x H, --introduces x
  cases H with y heqn, --introduces y
  apply local_obstruction' 2 8 (X 0 ^ 4 - X 1 ^ 2 - 3),
  -- applies the lemma, with m = 2, n = 8 and F(x_0, x_1) = x_0 ^ 4 - x_1 ^ 2 - 3
  {push_neg, simp, dec_trivial}, --shows that x ^ 4 - y ^ 2 - 3 ≠ 0 for all x and y in zmod 8
  use ![x, y], --to show x ^ 4 - y ^ 2 - 3 = 0 in the integers
  simp [heqn], --uses x ^ 4 - y ^ 2 = 3 to close the goal
end
.

/-If nonnegative x is congruent to 3 mod 4, then it has a prime divisor also congruent to 3 mod 4-/

lemma prime_3_mod_4_step.eqn_mod_4 (a p : zmod 4) (ha : a ≠ 3) : p * a = 3 → p = 3 :=
by dec_trivial!

lemma prime_3_mod_4_step.p_mod_4 (a p : ℕ) (h : p * a % 4 = 3) (hcase: a % 4 ≠ 3) :
(p : zmod 4) = 3 :=
begin
  apply prime_3_mod_4_step.eqn_mod_4 a p,
  { have ha : a ≠ 3,
      intro ha,
      norm_num [ha] at hcase,
    intro ha1,
    simp only [zmod.nat_coe_zmod_eq_iff] at ha1,
    have : (3 : zmod 4).val = 3 := zmod.val_nat_cast 3,
    rw this at ha1,
    clear this,
    cases ha1 with k hak,
    norm_num [hak] at hcase },
  { have h1 : ↑(p * a % 4) = (↑3 : zmod 4) := by simp [h],
    norm_num at h1,
    exact h1 },
end

lemma prime_3_mod_4 {x : ℤ} (hxnonneg : 0 ≤ x) :
(x % 4 = 3) → ∃ (p : ℕ), prime p ∧ ↑p ∣ x ∧ p % 4 = 3 :=
begin
  have hnatx := eq_coe_of_zero_le hxnonneg,
  cases hnatx with n hxn,
  rw hxn,
  apply unique_factorization_monoid.induction_on_prime n,
  { intro h,
    exfalso,
    norm_num at h },
  { intros m hm h,
    simp at hm,
    exfalso,
    norm_num [hm] at h },
  intros a p hanotzero hp hbase h,
  by_cases hcase : (a : ℤ) % 4 = 3,
  { simp [hcase] at hbase,
    cases hbase with q hq,
    use q,
    cases hq with hq1 hq2,
    cases hq2 with hq2 hq3,
    simp [hq1, hq3, dvd_mul_of_dvd_right hq2] },
  { have hpmod : (p : zmod 4) = 3,
      apply prime_3_mod_4_step.p_mod_4 a,
      { exact_mod_cast h },
      { exact_mod_cast hcase },
    simp only [zmod.nat_coe_zmod_eq_iff] at hpmod,
    have : (3 : zmod 4).val = 3 := zmod.val_nat_cast 3,
    rw this at hpmod,
    clear this,
    cases hpmod with k hpk,
    use p,
    norm_num [hpk, hp] at hp ⊢ },
end
.

/-If nonnegative x is congruent to 2 mod 3, then it has a prime divisor also congruent to 2 mod 3-/

lemma prime_2_mod_3_step.eqn_mod_3 (a p : zmod 3) (ha : a ≠ 2) : p * a = 2 → p = 2 :=
by dec_trivial!

lemma prime_2_mod_3_step.p_mod_3 (a p : ℕ) (h : p * a % 3 = 2) (hcase: a % 3 ≠ 2) :
(p : zmod 3) = 2 :=
begin
  apply prime_2_mod_3_step.eqn_mod_3 a p,
  { have ha : a ≠ 2,
      intro ha,
      norm_num [ha] at hcase,
    intro ha1,
    simp only [zmod.nat_coe_zmod_eq_iff] at ha1,
    have : (2 : zmod 3).val = 2 := zmod.val_nat_cast 2,
    rw this at ha1,
    clear this,
    cases ha1 with k hak,
    norm_num [hak] at hcase },
  { have h1 : ↑(p * a % 3) = (↑2 : zmod 3) := by simp [h],
    norm_num at h1,
    exact h1 },
end

lemma prime_2_mod_3 {x : ℤ} (hxnonneg : 0 ≤ x) :
(x % 3 = 2) → ∃ (p : ℕ), prime p ∧ ↑p ∣ x ∧ p % 3 = 2 :=
begin
  have hnatx := eq_coe_of_zero_le hxnonneg,
  cases hnatx with n hxn,
  rw hxn,
  apply unique_factorization_monoid.induction_on_prime n,
  { intro h,
    exfalso,
    norm_num at h },
  { intros m hm h,
    simp at hm,
    exfalso,
    norm_num [hm] at h },
  intros a p hanotzero hp hbase h,
  by_cases hcase : (a : ℤ) % 3 = 2,
  { simp [hcase] at hbase,
    cases hbase with q hq,
    use q,
    cases hq with hq1 hq2,
    cases hq2 with hq2 hq3,
    simp [hq1, hq3, dvd_mul_of_dvd_right hq2] },
  { have hpmod : (p : zmod 3) = 2,
      apply prime_2_mod_3_step.p_mod_3 a,
      { exact_mod_cast h },
      { exact_mod_cast hcase },
    simp only [zmod.nat_coe_zmod_eq_iff] at hpmod,
    have : (2 : zmod 3).val = 2 := zmod.val_nat_cast 2,
    rw this at hpmod,
    clear this,
    cases hpmod with k hpk,
    use p,
    norm_num [hpk, hp] at hp ⊢ },
end
.

/-A condition on when -3 is a quadratic residue,
  counterpart to zmod.exists_sq_eq_neg_one_iff for -1-/

lemma val_exists (a : ℤ) (n : ℕ) [ne_zero n] : ∃ (k : ℤ), ↑(a : zmod n).val = a + n * k :=
begin
  have h : (a : zmod n) = a := rfl,
  rw zmod.int_coe_zmod_eq_iff at h,
  cases h with k hk,
  use (-k),
  nth_rewrite 1 hk,
  norm_num,
end

lemma abs_sub_le_two_of_eq_one_or_neg_one {a b : ℤ} (ha : a = 1 ∨ a = -1)
(hb : b = 1 ∨ b = -1) : |a - b| ≤ 2 :=
begin
  rw abs_sub_le_iff,
  cases ha,
  repeat {cases hb, repeat {norm_num [ha, hb]}},
end

lemma eq_zero_of_mul_abs_le_two (p : ℕ) (k : ℤ) (hp1 : nat.prime p) (hp2 : p ≠ 2)
(h : |↑p * k| ≤ 2) : k = 0 :=
begin
  norm_num [abs_mul] at h,
  have h2ltp : 2 < p := lt_of_le_of_ne' (nat.prime.two_le hp1) hp2,
  have hpk : 3 * |k| ≤ ↑p * |k|,
    apply mul_le_mul,
    repeat {linarith},
    simp,
  have h3kle2 : 3 * |k| ≤ 2 := by linarith,
  by_contra hk,
  have habsk : 0 < |k|,
    simp [hk],
  linarith,
end

lemma legendre_sym.at_neg_one_eq {p : ℕ} [fact (nat.prime p)] (hp : p ≠ 2) :
legendre_sym p (-1) = (-1) ^ (p / 2) :=
begin
  have hEuler := (legendre_sym.eq_pow p (-1)).symm,
  have hoptions : legendre_sym p (-1) = 1 ∨ legendre_sym p (-1) = -1 :=
    by norm_num [legendre_sym.eq_one_or_neg_one],
  have hoptions' := neg_one_pow_eq_or ℤ (p / 2),
  norm_cast at hEuler,
  rw zmod.int_coe_zmod_eq_iff at hEuler,
  cases hEuler with k hEuler,
  have hval := val_exists (legendre_sym p (-1)) p,
  cases hval with m hval,
  rw hval at hEuler,
  have h : ∃ (n : ℤ), legendre_sym p (-1) = (-1) ^ (p / 2) + p * n,
    use (-(m + k)),
    rw [hEuler],
    ring,
  cases h with n h,
  rw ← sub_eq_iff_eq_add' at h,
  have habs := congr_arg abs h,
  clear h,
  have hle2 : |↑p * n| ≤ 2,
    { rw ← habs,
      exact abs_sub_le_two_of_eq_one_or_neg_one hoptions hoptions' },
  have hn : n = 0 := eq_zero_of_mul_abs_le_two p n _ hp hle2,
  norm_num [hn, sub_eq_zero] at habs,
  exact habs,
  rwa fact_iff at _inst_1,
end

lemma zmod.exists_sq_eq_neg_three_iff {p : ℕ} [fact (nat.prime p)] (hp2 : p ≠ 2) :
is_square (-3 : zmod p) ↔ p % 3 ≠ 2 :=
begin
  by_cases hp3 : p = 3,
  { norm_num [hp3],
    use 0,
    norm_num,
    have : ∀ (a : ℕ), a = 3 → (3 : zmod a) = 0,
      intros a ha,
      rw ha,
      refl,
    apply this p hp3 },
  have hquadrec : (legendre_sym p (-3)) = legendre_sym 3 p,
    rw [← one_mul (3 : ℤ), ← neg_mul, legendre_sym.mul],
    norm_num [legendre_sym.quadratic_reciprocity' hp2, legendre_sym.eq_zero_iff],
    simp [legendre_sym.at_neg_one_eq hp2],
  have hnezero : ↑(-3 : ℤ) ≠ (0 : zmod p),
    intro h,
    norm_num at h,
    have : (3 : zmod p) = ↑(3 : ℕ) := by simp,
    rw this at h,
    clear this,
    rw [zmod.nat_coe_zmod_eq_zero_iff_dvd, nat.prime.dvd_iff_eq] at h,
    { apply hp3 h.symm },
    { norm_num },
    { exact nat.prime.ne_one (fact_iff.mp _inst_1) },
  split,
  { intro h,
    norm_cast at h,
    rw ← ne.def at hp3,
    rw [← legendre_sym.eq_one_iff _ hnezero, hquadrec] at h,
    have hmod : ↑(legendre_sym 3 ↑p) = (1 : zmod 3) := by simp [h],
    norm_num [legendre_sym.eq_pow] at hmod,
    have : p % 3 = 1,
      rw zmod.nat_coe_zmod_eq_iff at hmod,
      cases hmod with k hmod,
      have hval : (1 : zmod 3).val = 1 := rfl,
      norm_num [hmod, hval],
    simp [this],
     },
  { intro hpmod3,
    norm_cast,
    rw ← legendre_sym.eq_one_iff _ hnezero,
    by_contra h,
    rw [← legendre_sym.eq_neg_one_iff_not_one _ hnezero, hquadrec] at h,
    have hmod : ↑(legendre_sym 3 ↑p) = (-1 : zmod 3) := by simp [h],
    norm_num [legendre_sym.eq_pow] at hmod,
    have : p % 3 = 2,
      rw zmod.nat_coe_zmod_eq_iff at hmod,
      cases hmod with k hmod,
      have hval : (-1 : zmod 3).val = 2 := rfl,
      norm_num [hval, hmod],
    exact hpmod3 this },
end
.

/-This lemma used to be needed to solve a bug in norm_num. The bug is now fixed,
  but I kept the lemma-/

lemma int.squarefree_of_nat_squarefree {n : ℕ} (hn : squarefree n) : squarefree (n : ℤ) :=
begin
  intros x hxn,
  induction x with x,
  { simp at hxn,
    norm_cast at hxn,
    specialize hn x,
    simp [hxn] at hn,
    simp [hn] },
  { rw neg_succ_of_nat_eq at hxn ⊢,
    simp only [mul_neg, neg_mul, neg_neg] at hxn,
    specialize hn (x + 1),
    norm_cast at hxn,
    simp [hxn] at hn,
    simp [hn] },
end
.

/-An example of a Mordell equation with no integer solutions-/

lemma Mordell_example_step.eqn_mod_4 (x y : zmod 4) : y^2 = x^3 + 7 → x = 1 := by dec_trivial!

lemma le_of_odd_pow_le_odd_pow {x y : ℤ} (k : ℕ) (hk : odd k) (hxy : x ^ k ≤ y ^ k) : x ≤ y :=
begin
  by_cases hx : 0 ≤ x,
  { by_cases hy : 0 ≤ y,
    { have hxnat := eq_coe_of_zero_le hx,
      have hynat := eq_coe_of_zero_le hy,
      cases hxnat with m hm,
      cases hynat with n hn,
      rw [hm, hn] at hxy ⊢,
      norm_cast at hxy ⊢,
      exact le_of_pow_le_pow k (nat.zero_le n) (odd.pos hk) hxy },
    { simp at hy,
      exfalso,
      have hx3 : x ^ k ≥ 0 := pow_nonneg hx k,
      have hy3 : y ^ k < 0 := odd.pow_neg hk hy,
      linarith } },
  { by_cases hy : 0 ≤ y,
    { simp at hx,
      have hx3 : x ^ k < 0 := odd.pow_neg hk hx,
      have hy3 : y ^ k ≥ 0 := pow_nonneg hy k,
      linarith },
    { simp at hx hy,
      have hx3 : x ^ k < 0 := odd.pow_neg hk hx,
      have hy3 : y ^ k < 0 := odd.pow_neg hk hy,
      have hnegx : - x ≥ 0 := by linarith,
      have hnegy : - y ≥ 0 := by linarith,
      have hnegxnat := eq_coe_of_zero_le hnegx,
      have hnegynat := eq_coe_of_zero_le hnegy,
      cases hnegxnat with m hm,
      cases hnegynat with n hn,
      have hxm : x = -m := by linarith,
      have hyn : y = -n := by linarith,
      simp [hxm, hyn, hk, odd.neg_pow] at hxy ⊢,
      norm_cast at hxy ⊢,
      apply le_of_pow_le_pow k (nat.zero_le m) (odd.pos hk) hxy } },
end

lemma Mordell_example_step.x_add_two_nonneg {x y : ℤ} (heqn : y ^ 2 = x ^ 3 + 7) : 0 ≤ x + 2 :=
begin
  have hy : 0 ≤ y ^ 2 := sq_nonneg y,
  rw [heqn, ← neg_le_iff_add_nonneg] at hy,
  have hx8 : -8 ≤ x ^ 3 := by linarith,
  have h8 : (-8 : ℤ) = (-2) ^ 3 := by norm_num,
  rw h8 at hx8,
  have hx2 : -2 ≤ x := le_of_odd_pow_le_odd_pow 3 _ hx8,
  linarith,
  norm_num,
end

lemma Mordell_example_step.is_square_neg_one (y : ℤ) (p : ℕ)
(heqnmodp: (y ^ 2 + 1) % ↑p = 0) : is_square (-1 : zmod p) :=
begin
  have h : ↑((y ^ 2 + 1) % p) = (↑0 : zmod p) := by simp [heqnmodp],
  --casts the equation heqnmodp upwards to zmod p
  norm_num at h, --simplifies the new equation
  rw add_eq_zero_iff_eq_neg at h, --subtracts 1 from both sides of equation h
  use (y : zmod p), --to show ↑y squares to -1
  rw [← h, sq], --changes the -1 in the goal to ↑y ^ 2 and shows ↑y ^ 2 = ↑y * ↑y
end

lemma Mordell_example : ¬ ∃ (x y : ℤ), y ^ 2 = x ^ 3 + 7 :=
begin
  intro H,
  cases H with x H,
  cases H with y heqn,
  have hfactors : y ^ 2 + 1 = (x + 2) * (x ^ 2 - 2 * x + 4) := by linarith,
  have hxmod4 : (x : zmod 4) = 1,
    apply Mordell_example_step.eqn_mod_4 x y,
    exact_mod_cast (congr_arg coe heqn),
  rw zmod.int_coe_zmod_eq_iff at hxmod4,
  norm_num at hxmod4,
  cases hxmod4 with k hxk,
  have hxadd2 : (x + 2) % 4 = 3 := by norm_num [hxk, add_mod],
  have hp := prime_3_mod_4 (Mordell_example_step.x_add_two_nonneg heqn) hxadd2,
  cases hp with p hp,
  cases hp with hpprime hp,
  cases hp with hpdvdxadd2 hpmod4,
  have heqnmodp : (y ^ 2 + 1) % p = 0 := by simp [hfactors, dvd_mul_of_dvd_left hpdvdxadd2],
  have hsqnegone := Mordell_example_step.is_square_neg_one y p heqnmodp,
  have fact_prime_p : fact (nat.prime p) := fact_iff.mpr (prime.nat_prime hpprime),
  apply zmod.exists_sq_eq_neg_one_iff.mp,
  exact hsqnegone,
  exact hpmod4,
  exact fact_prime_p,
end
.

/-A more general family of Diophantine equations with no integer solutions-/

lemma is_square_neg_one_of_is_square_neg_sq (a : ℤ) {p : ℕ} (hp : fact (nat.prime p))
(hane0 : (a : zmod p) ≠ 0) (hnega : is_square (-a^2 : zmod p)) : is_square (-1 : zmod p) :=
begin
  have hnegasqne0 : ↑(-a ^ 2) ≠ (0 : zmod p) := by simp [hane0],
  rw [← cast_pow, ← cast_neg, ← legendre_sym.eq_one_iff p hnegasqne0, neg_eq_neg_one_mul,
        legendre_sym.mul, legendre_sym.sq_one' p hane0, mul_one] at hnega,
  simp [legendre_sym.eq_one_iff] at hnega,
  exact hnega,
end

lemma sq_add_sq_step.is_square_neg_one (a y : ℤ) {p : ℕ}
(ha : ¬∃ (p : ℕ), prime p ∧ ↑p ∣ a ∧ p % 4 = 3) (hpprime : prime p)
(fact_prime_p : fact (nat.prime p)) (hpmod4 : p % 4 = 3)
(hpdvdf : (y ^ 2 + a ^ 2) % p = 0) : is_square (-1 : zmod p) :=
-- shows -1 is quadratic residue mod p from (y ^ 2 + a ^ 2) % p = 0
begin
  apply is_square_neg_one_of_is_square_neg_sq a,
  { by_contra,
    rw char_p.int_cast_eq_zero_iff (zmod p) p a at h,
    simp at ha,
    specialize ha p,
    simp [hpprime, h] at ha,
    exact ha hpmod4 },
  { have h : ↑((y ^ 2 + a ^ 2) % p) = (↑0 : zmod p) := by simp [hpdvdf],
    norm_num at h,
    rw add_eq_zero_iff_eq_neg at h,
    use (y : zmod p),
    rw ← h,
    ring },
end

lemma sq_add_sq (a : ℤ) (f : ℤ → ℤ) (ha : ¬∃ (p : ℕ), prime p ∧ ↑p ∣ a ∧ p % 4 = 3) :
¬∃ (x y : ℤ), y ^ 2 + a ^ 2 = f x ∧ (∃ (d : ℤ), 0 ≤ d ∧ d ∣ f x ∧ d % 4 = 3) :=
begin
  intro H,
  cases H with x H,
  cases H with y H,
  cases H with heqn H,
  cases H with d H,
  cases H with hdpos hd,
  cases hd with hddvdf hd,
  have hp := prime_3_mod_4 hdpos hd,
  cases hp with p hp,
  cases hp with hpprime hp,
  cases hp with hpdvdd hpmod4,
  have hpdvdf : ↑p ∣ f x := dvd_trans hpdvdd hddvdf,
  rw [← heqn, ← euclidean_domain.mod_eq_zero] at hpdvdf,
  have fact_prime_p : fact (nat.prime p) := fact_iff.mpr (prime.nat_prime hpprime),
  have hnegonesq := sq_add_sq_step.is_square_neg_one a y ha hpprime fact_prime_p hpmod4 hpdvdf,
  apply zmod.exists_sq_eq_neg_one_iff.mp,
  exact hnegonesq,
  exact hpmod4,
end
.

/-The Mordell equation from before proved in a different way, making use of the previous lemma-/

lemma Mordell_example' : ¬ ∃ (x y : ℤ), y ^ 2 = x ^ 3 + 7 :=
begin
  intro H,
  cases H with x H,
  cases H with y heqn,
  have hfactors : y ^ 2 + 1 = (x + 2) * (x ^ 2 - 2 * x + 4) := by linarith,
  apply sq_add_sq 1 (λ (x : ℤ), (x + 2) * (x ^ 2 - 2 * x + 4)) _,
  use [x, y],
  simp [hfactors],
  { use x + 2,
    split,
    { exact Mordell_example_step.x_add_two_nonneg heqn },
    have hxmod4 : (x : zmod 4) = 1,
      apply Mordell_example_step.eqn_mod_4 x y,
      exact_mod_cast (congr_arg coe heqn),
    simp [zmod.int_coe_zmod_eq_iff] at hxmod4,
    cases hxmod4 with k hxk,
    norm_num [hxk, add_mod] },
  { by_contra,
    cases h with p hp,
    cases hp with hpprime hp,
    cases hp with hp1 hpmod4,
    norm_cast at hp1,
    revert hp1,
    apply prime.not_dvd_one hpprime },
end
.

/-A family of Mordell equations with no integer solutions with one parameter-/

lemma parameterized_Mordell_step.eqn_mod_4 (k : ℤ) (x y : zmod 4) :
y ^ 2 = x ^ 3 + 8 * (2 * k + 1) ^ 3 - 1 → x = 1 :=
begin
  have : (8 : zmod 4) * (2 * k + 1) ^ 3 = 0,
    have : (8 : zmod 4) = ↑(4 : ℕ) * 2 := by norm_num,
    rw [this, mul_assoc, zmod.nat_cast_self, zero_mul],
  norm_num [this],
  dec_trivial!,
end

lemma parameterized_Mordell_step.nonneg {x y k : ℤ}
(heqn : y ^ 2 = x ^ 3 + 8 * (2 * k + 1) ^ 3 - 1) : 0 ≤ x + 2 * (2 * k + 1) :=
begin
  have hy : 0 ≤ y ^ 2 := sq_nonneg y,
  rw [heqn, add_sub_assoc, ← neg_le_iff_add_nonneg] at hy,
  have hcubes : -8 * (2 * k + 1) ^ 3 ≤ x ^ 3 := by linarith,
  have h8 : (-8 : ℤ) = (-2) ^ 3 := by norm_num,
  rw [h8, ← mul_pow] at hcubes,
  have hx : (-2) * (2 * k + 1) ≤ x := le_of_odd_pow_le_odd_pow 3 _ hcubes,
  linarith,
  norm_num,
end

lemma parameterized_Mordell (k : ℤ) : ¬∃ (x y : ℤ), y ^ 2 = x ^ 3 + 8 * (2 * k + 1) ^ 3 - 1 :=
begin
  intro h,
  cases h with x h,
  cases h with y heqn,
  have hfactors : y ^ 2 + 1 = (x + 2 * (2 * k + 1)) *
      (x ^ 2 - 2 * (2 * k + 1) * x + 4 * (2 * k + 1) ^ 2) := by linarith,
  apply sq_add_sq 1 (λ (x : ℤ), (x + 2 * (2 * k + 1)) *
      (x ^ 2 - 2 * (2 * k + 1) * x + 4 * (2 * k + 1) ^ 2)) _,
  use [x, y],
  simp [hfactors],
  { use x + 2 * (2 * k + 1),
    split,
    { exact parameterized_Mordell_step.nonneg heqn },
    simp,
    have hxmod4 : (x : zmod 4) = 1,
      apply parameterized_Mordell_step.eqn_mod_4 k (x : zmod 4) (y : zmod 4),
      norm_cast,
      norm_num [heqn],
    simp [zmod.int_coe_zmod_eq_iff] at hxmod4,
    cases hxmod4 with m hxm,
    rw hxm,
    ring_nf,
    norm_num [add_mod] },
  { by_contra,
    cases h with p hp,
    cases hp with hpprime hp,
    cases hp with hp1 hpmod4,
    norm_cast at hp1,
    revert hp1,
    apply prime.not_dvd_one hpprime },
end
.

/-A more generalized family of Mordell equations with no integer solutions-/

lemma real.nonneg_quadratic (x c : ℝ) : 0 ≤ x ^ 2 - x * c +  c ^ 2 :=
begin
  set y := x - c / 2 with hy, --change of variables
  rw eq_sub_iff_add_eq at hy, --changes y = x - c / 2 into y + c / 2 = x
  rw ← hy, --substitutes y + c / 2 for x
  have h : (y + c / 2) ^ 2 - (y + c / 2) * c + c ^ 2 = y ^ 2 + 3 * (c / 2) ^ 2 := 
    by ring, --the ring tactic uses results from commutative rings to solve equations
  rw h, --simplifies the expression in the goal
  have h1 := sq_nonneg y, --0 ≤ y ^ 2
  have h2 := sq_nonneg (c / 2), --0 ≤ (c / 2) ^ 2
  linarith, --proves the inequality 0 ≤ y ^ 2 + 3 * (c / 2) ^ 2 using h1 and h2
end

lemma general_Mordell_step.even_x_mod {a b m x y : ℤ} (hbeven : even b)
(ha : a = 4 * m - 1) (heqn : y ^ 2 + b ^ 2 = x ^ 3 + a ^ 3) : (x : zmod 4) = 1 :=
begin
  have hxmod : ∀ (x y : zmod 4), y ^ 2 = x ^ 3 + -1 → x = 1 := by dec_trivial!,
  apply hxmod x y,
  have hbmod : (b : zmod 4) ^ 2 = 0,
    have hbmodeven : even (b : zmod 4),
      cases hbeven with n hbn,
      simp [hbn],
    have hevensq : ∀ (c : zmod 4), even c → c ^ 2 = 0,
      intros c hc,
      cases hc with n hcn,
      dec_trivial!,
    exact hevensq (b : zmod 4) hbmodeven,
  have hamod : (a : zmod 4) = -1,
    norm_num [ha],
    apply zero_mul,
  have heqnmod : (↑(y ^ 2 + b ^ 2) : zmod 4) = ↑(x ^ 3 + a ^ 3) := by simp [heqn],
  norm_num [hbmod, hamod] at heqnmod,
  exact heqnmod,
end

lemma general_Mordell_even (a b m : ℤ) (hbeven : even b)
(hb : ¬∃ (p : ℕ), prime p ∧ ↑p ∣ b ∧ p % 4 = 3) (ha : a = 4 * m - 1) :
¬∃ (x y : ℤ), y ^ 2 + b ^ 2 = x ^ 3 + a ^ 3 :=
begin
  intro H,
  cases H with x H,
  cases H with y heqn,
  apply sq_add_sq b (λ z, z ^ 3 + a ^ 3) hb,
  use [x, y],
  norm_num [heqn],
  use x ^ 2 - x * a + a ^ 2,
  split,
  { exact_mod_cast real.nonneg_quadratic (x : ℝ) (a : ℝ) },
  split,
  { have hfactors : x ^ 3 + a ^ 3 = (x + a) * (x ^ 2 - x * a + a ^ 2) := by ring,
    simp only [hfactors, dvd_mul_left, true_and] },
  { have hxmod := general_Mordell_step.even_x_mod hbeven ha heqn,
    rw zmod.int_coe_zmod_eq_iff at hxmod,
    norm_num at hxmod,
    cases hxmod with n hxn,
    have : x ^ 2 - x * a + a ^ 2 =
        4 * (4 * m ^ 2 - 4 * m * n - 3 * m + 4 * n ^ 2 + 3 * n) + 3,
      rw [hxn, ha],
      ring,
    norm_num [this, add_mod] },
end

lemma general_Mordell_step.odd_x_mod {a b m x y : ℤ} (hbodd : odd b)
(ha : a = 4 * m + 2) (heqn : y ^ 2 + b ^ 2 = x ^ 3 + a ^ 3) : (x : zmod 4) = 1 :=
begin
  have hxmod : ∀ (x y : zmod 4), y ^ 2 + 1 = x ^ 3 → x = 1 := by dec_trivial!,
  apply hxmod x y,
  have hbmod : (b : zmod 4) ^ 2 = 1,
    have hbmododd : odd (b : zmod 4),
      cases hbodd with n hbn,
      simp [hbn],
    have hoddsq : ∀ (c : zmod 4), odd c → c ^ 2 = 1,
      intros c hc,
      cases hc with n hcn,
      dec_trivial!,
    exact hoddsq (b : zmod 4) hbmododd,
  have hamod : (a : zmod 4) ^ 3 = 0,
    have : (a : zmod 4) = 2,
      norm_num [ha],
      apply zero_mul,
    norm_num [this],
    refl,
  have heqnmod : (↑(y ^ 2 + b ^ 2) : zmod 4) = ↑(x ^ 3 + a ^ 3) := by simp [heqn],
  norm_num [hbmod, hamod] at heqnmod,
  exact heqnmod,
end

lemma general_Mordell_odd (a b m : ℤ) (hbodd : odd b)
(hb : ¬∃ (p : ℕ), prime p ∧ ↑p ∣ b ∧ p % 4 = 3) (ha : a = 4 * m + 2) :
¬∃ (x y : ℤ), y ^ 2 + b ^ 2 = x ^ 3 + a ^ 3 :=
begin
  intro H,
  cases H with x H,
  cases H with y heqn,
  apply sq_add_sq b (λ z, z ^ 3 + a ^ 3) hb,
  use [x, y],
  norm_num [heqn],
  use x + a,
  split,
  { have hynonneg := sq_nonneg y,
    have hanonneg := sq_nonneg b,
    have hnonneg : 0 ≤ x ^ 3 + a ^ 3,
      rw ← heqn,
      linarith,
    rw ← neg_le_iff_add_nonneg at hnonneg ⊢,
    rw ← neg_pow_bit1 at hnonneg,
    norm_num [le_of_odd_pow_le_odd_pow 3 _ hnonneg] },
  split,
  { have hfactors : x ^ 3 + a ^ 3 = (x + a) * (x ^ 2 - x * a + a ^ 2) := by ring,
    simp only [hfactors, dvd_mul_right, true_and] },
  { have hxmod := general_Mordell_step.odd_x_mod hbodd ha heqn,
    rw zmod.int_coe_zmod_eq_iff at hxmod,
    norm_num at hxmod,
    cases hxmod with n hxn,
    have : x + a = 4 * (m + n) + 3,
      rw [hxn, ha],
      ring,
    norm_num [this, add_mod] },
end
.


end int