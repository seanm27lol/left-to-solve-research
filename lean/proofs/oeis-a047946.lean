import OMAStatements.S_oeis_a047946

/-!
# Squares of Fibonacci numbers on arithmetic progressions

An index shift by n acts linearly on consecutive Fibonacci numbers. Squaring
the first coordinate gives a cubic recurrence whose signs are fixed by Cassini's
identity. The argument works for arbitrary starting pairs.
-/

open OMA.S_oeis_a047946

namespace FibSquareRecurrence

private def f (n : ℕ) : ℤ := n.fib

private theorem next (n : ℕ) : f (n + 2) = f n + f (n + 1) := by
  simp only [f, Nat.fib_add_two, Nat.cast_add]

private theorem addition (m n : ℕ) :
    f (m + n + 1) = f m * f n + f (m + 1) * f (n + 1) := by
  unfold f
  exact_mod_cast Nat.fib_add m n

private def pair (m : ℕ) : ℤ × ℤ := (f m, f (m + 1))

private def shift (a b : ℤ) (p : ℤ × ℤ) : ℤ × ℤ :=
  ((b - a) * p.1 + a * p.2, a * p.1 + b * p.2)

private theorem shiftPair (n k : ℕ) :
    shift (f n) (f (n + 1)) (pair (n * k)) = pair (n * (k + 1)) := by
  rw [Nat.mul_add, Nat.mul_one]
  let m := n * k
  change shift (f n) (f (n + 1)) (pair m) = pair (m + n)
  apply Prod.ext
  · change (f (n + 1) - f n) * f m + f n * f (m + 1) = f (m + n)
    have h := addition m (n + 1)
    rw [show m + (n + 1) + 1 = m + n + 2 by omega, next (m + n),
        next n, addition m n] at h
    nlinarith only [h]
  · change f n * f m + f (n + 1) * f (m + 1) = f (m + n + 1)
    rw [addition]
    ring

private def determinant (a b : ℤ) : ℤ := b ^ 2 - a * b - a ^ 2

private theorem cassini (n : ℕ) : determinant (f n) (f (n + 1)) = (-1 : ℤ) ^ n := by
  induction n with
  | zero => norm_num [determinant, f]
  | succ n ih =>
    change determinant (f (n + 1)) (f (n + 2)) = (-1 : ℤ) ^ (n + 1)
    rw [next, pow_succ, ← ih]
    unfold determinant
    ring

private theorem threeShifts (a b : ℤ) (p : ℤ × ℤ) :
    (shift a b (shift a b (shift a b p))).1 ^ 2 =
      (5 * a ^ 2 + 3 * determinant a b) * (shift a b (shift a b p)).1 ^ 2 -
      determinant a b * (5 * a ^ 2 + 3 * determinant a b) * (shift a b p).1 ^ 2 +
      (determinant a b) ^ 3 * p.1 ^ 2 := by
  rcases p with ⟨x, y⟩
  simp only [shift, determinant]
  ring

theorem recurrence : type_of% @OMA.S_oeis_a047946.main := by
  intro n _ k
  have h := threeShifts (f n) (f (n + 1)) (pair (n * k))
  simp only [shiftPair, cassini] at h
  change fibSquare n (k + 3) =
    coefficient n * fibSquare n (k + 2) -
    (-1 : ℤ) ^ n * coefficient n * fibSquare n (k + 1) +
    ((-1 : ℤ) ^ n) ^ 3 * fibSquare n k at h
  by_cases odd : n % 2 = 1
  · rw [if_pos odd]
    have e : n = 2 * (n / 2) + 1 := by omega
    have s : (-1 : ℤ) ^ n = -1 := by
      calc
        _ = (-1 : ℤ) ^ (2 * (n / 2) + 1) := congrArg (fun j : ℕ => (-1 : ℤ) ^ j) e
        _ = -1 := by rw [pow_succ, pow_mul]; norm_num
    rw [s] at h
    linear_combination h
  · rw [if_neg odd]
    have e : n = 2 * (n / 2) := by omega
    have s : (-1 : ℤ) ^ n = 1 := by
      calc
        _ = (-1 : ℤ) ^ (2 * (n / 2)) := congrArg (fun j : ℕ => (-1 : ℤ) ^ j) e
        _ = 1 := by rw [pow_mul]; norm_num
    rw [s] at h
    linear_combination h

end FibSquareRecurrence

theorem OMA.solution : type_of% @OMA.S_oeis_a047946.main :=
  FibSquareRecurrence.recurrence
