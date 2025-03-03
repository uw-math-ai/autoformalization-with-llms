theorem mathd_algebra_288
  (x y : ℝ)
  (n : NNReal)
  (h₀ : x < 0 ∧ y < 0)
  (h₁ : abs y = 6)
  (h₂ : Real.sqrt ((x - 8)^2 + (y - 3)^2) = 15)
  (h₃ : Real.sqrt (x^2 + y^2) = Real.sqrt n) :
  n = 52 := by sorry

theorem mathd_numbertheory_127 :
  (∑ k in (Finset.range 101), 2^k) % 7 = 3 := by sorry

theorem imo_1974_p3
  (n : ℕ) :
  ¬ 5∣∑ k in Finset.range (n + 1), (Nat.choose (2 * n + 1) (2 * k + 1)) * (2^(3 * k)) := by sorry

theorem aime_1991_p9
  (x : ℝ)
  (m : ℚ)
  (h₀ : 1 / Real.cos x + Real.tan x = 22 / 7)
  (h₁ : 1 / Real.sin x + 1 / Real.tan x = m) :
  ↑m.den + m.num = 44 := by sorry

theorem amc12a_2009_p6
  (m n p q : ℝ)
  (h₀ : p = 2 ^ m)
  (h₁ : q = 3 ^ n) :
  p^(2 * n) * (q^m) = 12^(m * n) := by sorry

theorem mathd_algebra_158
  (a : ℕ)
  (h₀ : Even a)
  (h₁ : ∑ k in Finset.range 8, (2 * k + 1) - ∑ k in Finset.range 5, (a + 2 * k) = (4:ℤ)) :
  a = 8 := by sorry

theorem algebra_absxm1pabsxpabsxp1eqxp2_0leqxleq1
  (x : ℝ)
  (h₀ : abs (x - 1) + abs x + abs (x + 1) = x + 2) :
  0 ≤ x ∧ x ≤ 1 := by sorry

theorem aime_1990_p4
  (x : ℝ)
  (h₀ : 0 < x)
  (h₁ : x^2 - 10 * x - 29 ≠ 0)
  (h₂ : x^2 - 10 * x - 45 ≠ 0)
  (h₃ : x^2 - 10 * x - 69 ≠ 0)
  (h₄ : 1 / (x^2 - 10 * x - 29) + 1 / (x^2 - 10 * x - 45) - 2 / (x^2 - 10 * x - 69) = 0) :
  x = 13 := by sorry

theorem mathd_numbertheory_541
  (m n : ℕ)
  (h₀ : 1 < m)
  (h₁ : 1 < n)
  (h₂ : m * n = 2005) :
  m + n = 406 := by sorry

theorem mathd_algebra_314
  (n : ℕ)
  (h₀ : n = 11) :
  (1 / 4)^(n + 1) * 2^(2 * n) = 1 / 4 := by sorry

theorem imosl_2007_algebra_p6
  (a : ℕ → NNReal)
  (h₀ : ∑ x in Finset.range 100, ((a (x + 1))^2) = 1) :
  ∑ x in Finset.range 99, ((a (x + 1))^2 * a (x + 2)) + (a 100)^2 * a 1 < 12 / 25 := by sorry

theorem amc12_2000_p20
  (x y z : ℝ)
  (h₀ : 0 < x ∧ 0 < y ∧ 0 < z)
  (h₁ : x + 1/y = 4)
  (h₂ : y + 1/z = 1)
  (h₃ : z + 1/x = 7/3) :
  x*y*z = 1 := by sorry

theorem mathd_algebra_302 :
  (Complex.I / 2)^2 = -(1 / 4) := by sorry

theorem aime_1983_p2
  (x p : ℝ)
  (f : ℝ → ℝ)
  (h₀ : 0 < p ∧ p < 15)
  (h₁ : p ≤ x ∧ x ≤ 15)
  (h₂ : f x = abs (x - p) + abs (x - 15) + abs (x - p - 15)) :
  15 ≤ f x := by sorry

theorem mathd_algebra_139
  (s : ℝ → ℝ → ℝ)
  (h₀ : ∀ x, ∀ y, x≠0 -> y≠0 -> s x y = (1/y - 1/x) / (x-y)) :
  s 3 11 = 1/33 := by sorry

theorem amc12a_2021_p25
  (N : ℕ)
  (f : ℕ → ℝ)
  (h₀ : ∀ n, 0 < n → f n = ((Nat.divisors n).card)/(n^((1:ℝ)/3)))
  (h₁ : ∀ n ≠ N, 0 < n → f n < f N) :
  (Nat.digits 10 N).sum = 9 := by sorry

theorem amc12a_2020_p25
  (a : ℚ)
  (S : Finset ℝ)
  (h₀ : ∀ (x : ℝ), x ∈ S ↔ ↑⌊x⌋ * (x - ↑⌊x⌋) = ↑a * x ^ 2)
  (h₁ : ∑ k in S, k = 420) :
  ↑a.den + a.num = 929 := by sorry

theorem mathd_numbertheory_150
  (n : ℕ)
  (h₀ : ¬ Nat.Prime (7 + 30 * n)) :
  6 ≤ n := by sorry

theorem aime_1989_p8
  (a b c d e f g : ℝ)
  (h₀ : a + 4 * b + 9 * c + 16 * d + 25 * e + 36 * f + 49 * g = 1)
  (h₁ : 4 * a + 9 * b + 16 * c + 25 * d + 36 * e + 49 * f + 64 * g = 12)
  (h₂ : 9 * a + 16 * b + 25 * c + 36 * d + 49 * e + 64 * f + 81 * g = 123) :
  16 * a + 25 * b + 36 * c + 49 * d + 64 * e + 81 * f + 100 * g = 334 := by sorry

theorem mathd_numbertheory_296
  (n : ℕ)
  (h₀ : 2 ≤ n)
  (h₁ : ∃ x, x^3 = n)
  (h₂ : ∃ t, t^4 = n) :
  4096 ≤ n := by sorry

theorem mathd_algebra_142
  (m b : ℝ)
  (h₀ : m * 7 + b = -1)
  (h₁ : m * (-1) + b = 7) :
  m + b = 5 := by sorry

theorem numbertheory_exk2powkeqapb2mulbpa2_aeq1
  (a b : ℕ)
  (h₀ : 0 < a ∧ 0 < b)
  (h₁ : ∃ k > 0, 2^k = (a + b^2) * (b + a^2)) :
  a = 1 := by sorry

theorem mathd_algebra_400
  (x : ℝ)
  (h₀ : 5 + 500 / 100 * 10 = 110 / 100 * x) :
  x = 50 := by sorry

theorem aime_1995_p7
  (k m n : ℕ)
  (t : ℝ)
  (h₀ : 0 < k ∧ 0 < m ∧ 0 < n)
  (h₁ : Nat.gcd m n = 1)
  (h₂ : (1 + Real.sin t) * (1 + Real.cos t) = 5/4)
  (h₃ : (1 - Real.sin t) * (1- Real.cos t) = m/n - Real.sqrt k):
  k + m + n = 27 := by sorry

theorem mathd_numbertheory_185
  (n : ℕ)
  (h₀ : n % 5 = 3) :
  (2 * n) % 5 = 1 := by sorry

theorem mathd_algebra_441
  (x : ℝ)
  (h₀ : x ≠ 0) :
  12 / (x * x) * (x^4 / (14 * x)) * (35 / (3 * x)) = 10 := by sorry

theorem mathd_numbertheory_582
  (n : ℕ)
  (h₀ : 0 < n)
  (h₁ : 3∣n) :
  ((n + 4) + (n + 6) + (n + 8)) % 9 = 0 := by sorry

theorem mathd_algebra_338
  (a b c : ℝ)
  (h₀ : 3 * a + b + c = -3)
  (h₁ : a + 3 * b + c = 9)
  (h₂ : a + b + 3 * c = 19) :
  a * b * c = -56 := by sorry
