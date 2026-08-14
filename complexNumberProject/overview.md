# to prove:

- Euler's Formula: e^ix = cos(x) + isin(x)
- Euler's Identity: e^iπ = -1
- DeMoivre's Theorem: [r(cos(x) + isin(x))]^n = r^n * (cos(xn) + sin(xn))
- Roots of unity: Roots of z^n = 1 are z_k = cos(2πk/n) + isin(2πk/n) 
    for k = 0, 1, 2, ... (n - 1)

# definitions

=== functions on n : Nat ===
sin : ∑​_n (-1)^n * z^(2n+1) / (2n+1)!
cos : ∑​_n (-1)^n * z^(2n) / (2n)!
=== functions on n : Com ===
e : ∑​_n z^n / n!

In library:
sin : Complex.sin_eq_tsum
cos : Complex.cos_eq_tsum
e : Complex.exp'

okay actually ignore this part because i had to make some changes in the actual lean file