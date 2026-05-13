import Mathlib

/-
  Final Project Math 300 - Bhanavi Senthil

  Main theorem:

  For every natural number n, 7^(12n) ≡ 1 (mod 13).

  In Lean notation, this is:

      7 ^ (12 * n) ≡ 1 [MOD 13]

  Why this is related to Euler's theorem:

      Euler's theorem says that if gcd(a, m) = 1, then

          a^φ(m) ≡ 1 (mod m).

      For this project, I decided to use the specific values

          a = 7
          m = 13

      Since 13 is prime, φ(13) = 12
      Because gcd(7, 13) = 1, Euler's theorem predicts

          7^12 ≡ 1 (mod 13).

      Then doing induction gives

          7^(12n) ≡ 1 (mod 13)

      for every natural number n.

  No full proof of general Euler theorem, but it
  proves a clean special case using the same
  elementary tools that appear in the textbook:

      * natural number induction
      * modular congruence
      * divisibility
      * algebraic rewriting
      * helper lemmas
      * examples

  The most important result is:

      theorem seven_power_twelve_n_mod_thirteen

  There is also an integer divisibility version:

      theorem thirteen_divides_seven_power_twelve_n_minus_one

  which says:

      13 ∣ 7^(12n) - 1.
-/


/-
  Section 1:
  Basic number-theory facts for the project.

  These facts explain why this theorem is a special case of Euler's theorem.
  They are not strictly necessary for the induction proof, but they make the
  project mathematically stronger and more connected to the usual statement
  of Euler's theorem.
-/


/-
  Proving that 13 is prime.

  This supports the Euler-theorem motivation, since if p is prime,
  then φ(p) = p - 1.

  Euler's Totient Function - number of positive and less than p values that are coprime to p
-/
lemma thirteen_is_prime :
    Nat.Prime 13 := by
  norm_num


/-
  Proving that 7 and 13 are coprime.

  This is the gcd condition needed in Euler's theorem.
-/
lemma seven_and_thirteen_are_coprime :
    Nat.Coprime 7 13 := by
  calc
    Nat.gcd 7 13 --coprime because gcd(7,13) = 1
        = 1 := by
          norm_num


/-
  The one-step congruence:

      7^12 ≡ 1 (mod 13).

  This is the special Euler/Fermat fact that drives the induction.
  Lean can verify this arithmetic computation directly.
-/
lemma seven_pow_twelve_mod_thirteen :
    7 ^ 12 ≡ 1 [MOD 13] := by
  calc
    7 ^ 12
        ≡ 1 [MOD 13] := by --proving that the remainder of 7^12 is one when divided by 13
          norm_num


/-
  A second version of the same one-step fact, written as divisibility
  over the integers:

      13 ∣ 7^12 - 1.

  This version will be used later for the divisibility theorem.
-/
lemma thirteen_divides_seven_pow_twelve_minus_one :
    13 ∣ ((7 : ℤ) ^ 12 - 1) := by
  norm_num


/-
  Section 2:
  Exponent rewriting lemmas.

  These lemmas keep the induction step readable.
-/


/-
  Algebraically,

      12 * (k + 1) = 12 * k + 12.

  In Lean, k + 1 is often written as Nat.succ k.
-/
lemma exponent_successor_twelve (k : ℕ) :
    12 * Nat.succ k = 12 * k + 12 := by
  calc
    12 * Nat.succ k
        = 12 * (k + 1) := by
          rw [Nat.succ_eq_add_one] -- k+1 is equal to Nat.succ k
    _ = 12 * k + 12 := by
          rw [mul_add] --distributing 12


/-
  This is the main exponent rewrite over natural numbers:

      7^(12(k+1)) = 7^(12k) * 7^12.

  This uses the exponent rule

      a^(r+s) = a^r * a^s.
-/
lemma power_successor_twelve_nat (k : ℕ) :--natural numbers
    7 ^ (12 * Nat.succ k)
      =
    7 ^ (12 * k) * 7 ^ 12 := by
  calc
    7 ^ (12 * Nat.succ k)
        = 7 ^ (12 * k + 12) := by
          rw [exponent_successor_twelve k] -- using previous lemma
    _ = 7 ^ (12 * k) * 7 ^ 12 := by
          rw [pow_add] -- multiplying powers with the same base


/-
  This is the same power rewrite, but over the integers.

  We need this version for the divisibility theorem involving

      13 ∣ ((7 : ℤ)^(12n) - 1).
-/
lemma power_successor_twelve_int (k : ℕ) : --integer
    (7 : ℤ) ^ (12 * Nat.succ k)
      =
    (7 : ℤ) ^ (12 * k) * (7 : ℤ) ^ 12 := by
  calc
    (7 : ℤ) ^ (12 * Nat.succ k)
        = (7 : ℤ) ^ (12 * k + 12) := by
          rw [exponent_successor_twelve k]
    _ = (7 : ℤ) ^ (12 * k) * (7 : ℤ) ^ 12 := by
          rw [pow_add]


/-
  Section 3:
  Main modular-congruence theorem.

  This is the central Euler-style statement of the project.
-/


/-
  Main theorem:

      For every natural number n,

          7^(12n) ≡ 1 (mod 13).

  Proof idea:

  Base case:
      n = 0.
      Then 7^(12*0) = 7^0 = 1.

  Induction step:
      Assume 7^(12k) ≡ 1 (mod 13).

      We prove

          7^(12(k+1)) ≡ 1 (mod 13).

      Rewrite:

          7^(12(k+1))
          = 7^(12k + 12)
          = 7^(12k) * 7^12.

      By the induction hypothesis,

          7^(12k) ≡ 1 (mod 13).

      By the one-step lemma,

          7^12 ≡ 1 (mod 13).

      Multiplying the two congruences gives

          7^(12k) * 7^12 ≡ 1 * 1 (mod 13),

      so

          7^(12(k+1)) ≡ 1 (mod 13).
-/
theorem seven_power_twelve_n_mod_thirteen ----main theorem
    (n : ℕ) :
    7 ^ (12 * n) ≡ 1 [MOD 13] := by
  induction n with
  | zero =>
      norm_num
  | succ k IH =>
      rw [power_successor_twelve_nat k] --using previous lemma
      calc
        7 ^ (12 * k) * 7 ^ 12
            ≡ 1 * 1 [MOD 13] := by
              exact Nat.ModEq.mul IH seven_pow_twelve_mod_thirteen
        _ = 1 := by
              ring


/-
  Section 4:
  Integer divisibility version.

  The congruence theorem above says

      7^(12n) ≡ 1 (mod 13).

  The equivalent divisibility statement is

      13 ∣ 7^(12n) - 1.
-/


/-
  Algebra identity used in the divisibility induction step.

  If x = 7^(12k), then

      x * 7^12 - 1
      =
      (x - 1) * 7^12 + (7^12 - 1).

  This identity is useful because:

      * x - 1 is divisible by 13 by the induction hypothesis.
      * 7^12 - 1 is divisible by 13 by the one-step lemma.
-/
lemma algebra_rewrite_for_divisibility (x : ℤ) :
    x * (7 : ℤ) ^ 12 - 1
      =
    (x - 1) * (7 : ℤ) ^ 12 + ((7 : ℤ) ^ 12 - 1) := by
  ring


/-
  If 13 divides x, then 13 divides x * 7^12.

  This is a small helper lemma that keeps the induction step readable.
-/
lemma thirteen_divides_mul_seven_pow_twelve
    (x : ℤ)
    (hx : 13 ∣ x) :
    13 ∣ x * (7 : ℤ) ^ 12 := by
  exact dvd_mul_of_dvd_left hx ((7 : ℤ) ^ 12)


/-
  Divisibility induction step.

  Assume:

      13 ∣ 7^(12k) - 1.

  Prove:

      13 ∣ 7^(12(k+1)) - 1.
-/
lemma divisibility_induction_step
    (k : ℕ)
    (IH : 13 ∣ ((7 : ℤ) ^ (12 * k) - 1)) :
    13 ∣ ((7 : ℤ) ^ (12 * Nat.succ k) - 1) := by
  /-
    First rewrite the power in the successor case.
  -/
  rw [power_successor_twelve_int k] -- 12(k+1) = 12k + 12 here
  /-
    Rewrite the expression into a sum of two terms.
  -/
  rw [algebra_rewrite_for_divisibility ((7 : ℤ) ^ (12 * k))] -- x = 7 ^ (12k)
  --(7^12k) * 7^12 - 1 = ((7^12k) - 1) * 7^12 + (7^12 - 1)
  /-
    The first term is divisible by 13 by the inductive hypothesis.
  -/
  have h_left : -- 13 | ((7^12k) - 1) * 7^12
      13 ∣ (((7 : ℤ) ^ (12 * k) - 1) * (7 : ℤ) ^ 12) := by
    exact thirteen_divides_mul_seven_pow_twelve
      (((7 : ℤ) ^ (12 * k)) - 1)
      IH -- 13 divides (7^(12k) - 1) by the induction hypothesis
  /-
    The second term is divisible by 13 because 7^12 ≡ 1 mod 13.
  -/
  have h_right :
      13 ∣ ((7 : ℤ) ^ 12 - 1) := by -- 13 divides (7^12 - 1) by the one-step lemma
    exact thirteen_divides_seven_pow_twelve_minus_one
  /-
    A divisor of each term divides their sum.
  -/
  exact dvd_add h_left h_right
  -- dvd_add:
  -- a divides b and a divides c implies a divides b + c (b = h_left, c = h_right)


/-
  Divisibility version of the main theorem:

      For every natural number n,

          13 ∣ 7^(12n) - 1.

  This is the same mathematical statement as

      7^(12n) ≡ 1 (mod 13),

  but written in divisibility language.
-/
theorem thirteen_divides_seven_power_twelve_n_minus_one
    (n : ℕ) :
    13 ∣ ((7 : ℤ) ^ (12 * n) - 1) := by
  induction n with
  | zero =>
      norm_num
  | succ k IH =>
      exact divisibility_induction_step k IH


/-
  Section 5:
  Existence form.

  This theorem says that for every n, there exists an integer q such that

      7^(12n) = 13q + 1.

  This is another way to write divisibility by 13.
-/


theorem seven_power_twelve_n_is_thirteen_times_something_plus_one
    (n : ℕ) :
    ∃ q : ℤ, (7 : ℤ) ^ (12 * n) = 13 * q + 1 := by
  /-
    Start from the divisibility theorem.
  -/
  have h_div :
      13 ∣ ((7 : ℤ) ^ (12 * n) - 1) := by
    exact thirteen_divides_seven_power_twelve_n_minus_one n
  /-
    Unpack divisibility.
  -/
  obtain ⟨q, hq⟩ := h_div
  /-
    The same q is the witness.
  -/
  use q
  /-
    The equation hq says:

        7^(12n) - 1 = 13q.

    Add 1 to both sides.
  -/
  calc
    (7 : ℤ) ^ (12 * n)
        = ((7 : ℤ) ^ (12 * n) - 1) + 1 := by
          ring
    _ = 13 * q + 1 := by
          rw [hq] -- hq: 7^(12n) - 1 = 13q, subsitute


/-
  Section 6:
  Concrete examples.

  These examples show that the theorem can be applied to specific values.
-/


example :
    7 ^ (12 * 0) ≡ 1 [MOD 13] := by
  exact seven_power_twelve_n_mod_thirteen 0


example :
    7 ^ (12 * 1) ≡ 1 [MOD 13] := by
  exact seven_power_twelve_n_mod_thirteen 1


example :
    7 ^ (12 * 2) ≡ 1 [MOD 13] := by
  exact seven_power_twelve_n_mod_thirteen 2


example :
    7 ^ (12 * 3) ≡ 1 [MOD 13] := by
  exact seven_power_twelve_n_mod_thirteen 3


example :
    13 ∣ ((7 : ℤ) ^ (12 * 0) - 1) := by
  exact thirteen_divides_seven_power_twelve_n_minus_one 0


example :
    13 ∣ ((7 : ℤ) ^ (12 * 1) - 1) := by
  exact thirteen_divides_seven_power_twelve_n_minus_one 1


example :
    13 ∣ ((7 : ℤ) ^ (12 * 2) - 1) := by
  exact thirteen_divides_seven_power_twelve_n_minus_one 2


example :
    ∃ q : ℤ, (7 : ℤ) ^ (12 * 4) = 13 * q + 1 := by
  exact seven_power_twelve_n_is_thirteen_times_something_plus_one 4


/-
  End of file.
-/
