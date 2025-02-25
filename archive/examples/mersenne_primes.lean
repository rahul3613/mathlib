/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import number_theory.lucas_lehmer

/-!
# Explicit Mersenne primes

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We run some Lucas-Lehmer tests to prove some Mersenne primes are prime.

See the discussion at the end of [src/number_theory/lucas_lehmer.lean]
for ideas about extending this to larger Mersenne primes.
-/

example : (mersenne 13).prime :=
lucas_lehmer_sufficiency _ (by norm_num) (by lucas_lehmer.run_test).
example : (mersenne 17).prime :=
lucas_lehmer_sufficiency _ (by norm_num) (by lucas_lehmer.run_test).
example : (mersenne 19).prime :=
lucas_lehmer_sufficiency _ (by norm_num) (by lucas_lehmer.run_test).

/-- 2147483647.prime, Euler (1772) -/
example : (mersenne 31).prime :=
lucas_lehmer_sufficiency _ (by norm_num) (by lucas_lehmer.run_test).

/-!
The next four primality tests are too slow to run interactively with -T100000,
but work fine on the command line.
-/

-- /-- 2305843009213693951.prime, Pervouchine (1883), Seelhoff (1886) -/
-- example : (mersenne 61).prime :=
-- lucas_lehmer_sufficiency _ (by norm_num) (by lucas_lehmer.run_test).
-- /-- 618970019642690137449562111.prime, Powers (1911) -/
-- -- takes ~100s
-- example : (mersenne 89).prime :=
-- lucas_lehmer_sufficiency _ (by norm_num) (by lucas_lehmer.run_test).
-- /-- 162259276829213363391578010288127.prime, Power (1914) -/
-- -- takes ~190s
-- example : (mersenne 107).prime :=
-- lucas_lehmer_sufficiency _ (by norm_num) (by lucas_lehmer.run_test).
-- /-- 170141183460469231731687303715884105727.prime, Lucas (1876) -/
-- -- takes ~370s
-- example : (mersenne 127).prime :=
-- lucas_lehmer_sufficiency _ (by norm_num) (by lucas_lehmer.run_test).

/- This still doesn't get us over the big gap and into the computer era, unfortunately. -/

-- /-- (2^521 - 1).prime, Robinson (1954) -/
-- -- This has not been run successfully!
-- example : (mersenne 521).prime :=
-- lucas_lehmer_sufficiency _ (by norm_num) (by lucas_lehmer.run_test).

